package main

import (
	"errors"
	"flag"
	"fmt"
	"github.com/dedis/crypto/abstract"
	"github.com/dedis/crypto/anon"
	"github.com/dedis/crypto/nist"
	"github.com/dedis/crypto/proof"
	"github.com/dedis/crypto/shuffle"
	"github.com/dedis/protobuf"
	"net"
	"reflect"
	"strconv"
	"time"
)

var aPoint abstract.Point
var tPoint = reflect.TypeOf(&aPoint).Elem()

var aSecret abstract.Secret
var tSecret = reflect.TypeOf(&aSecret).Elem()

type decryptionProof struct {
	T abstract.Point
	S abstract.Secret
}

// Permutation of El Gamal encrypted keys along with a proof of
// the permutation's correctness.
type shuffleState struct {
	G         abstract.Point
	X, Y, Dec []abstract.Point
	Prf       []byte `protobuf:"opt"`
	DecPrf    []*decryptionProof
}

// Aggregation of key permutations, plus a nonce identifying the
// current run of the protocol.
type stateVector struct {
	Nonce  abstract.Secret
	States []*shuffleState
}

func (v *stateVector) addShuffle(suite abstract.Suite, shuf *shuffler,
	rand abstract.Cipher) error {

	// Get the previous shuffle state.
	i := len(v.States)
	prev := v.States[i-1]
	X, Y := prev.X, prev.Dec

	// Compute the new base using the public keys of the remaining
	// servers.
	H := suite.Point().Null()
	for j := i - 1; j < shuf.N; j++ {
		H = suite.Point().Add(H, shuf.HH[j])
	}

	// Do a key-shuffle.
	Xbar, Ybar, prover := shuffle.Shuffle(suite, nil, H, X, Y, rand)
	prf, err := proof.HashProve(suite, "PairShuffle", rand, prover)
	if err != nil {
		return err
	}

	// Seeded random for the decryption proof.
	seed := abstract.Sum(suite, prf)
	prfRand := suite.Cipher(seed)

	// Scratch space for calculations.
	zs := suite.Secret()
	zp := suite.Point()

	// Peel off a layer of encryption.
	dec := make([]abstract.Point, len(Xbar))
	decPrf := make([]*decryptionProof, len(Xbar))
	for j := range Xbar {
		// Decryption.
		zp.Mul(Xbar[j], shuf.h)
		dec[j] = suite.Point().Sub(Ybar[j], zp)

		// Decryption proof.
		t := suite.Secret().Pick(rand)
		T := suite.Point().Mul(Xbar[j], t)
		c := suite.Secret().Pick(prfRand)
		s := suite.Secret().Add(t, zs.Mul(c, shuf.h))
		decPrf[j] = &decryptionProof{T, s}
	}

	// Append the new state to the state vector.
	state := &shuffleState{H, Xbar, Ybar, dec, prf, decPrf}
	v.States = append(v.States, state)
	return nil
}

type shuffler struct {
	suite    abstract.Suite
	id, k, N int
	h        abstract.Secret
	H        abstract.Point

	HH []abstract.Point

	cons protobuf.Constructors

	X, Y []abstract.Point
	gm   abstract.Point
}

func NewShuffler(suite abstract.Suite, id, k, N int) *shuffler {
	rand := suite.Cipher([]byte(fmt.Sprintf("key%d", id)))

	// This server's own keypair.
	h := suite.Secret().Pick(rand)
	H := suite.Point().Mul(nil, h)

	// The keypairs for the other servers.
	HH := make([]abstract.Point, N)
	for i := 0; i < N; i++ {
		r := suite.Cipher([]byte(fmt.Sprintf("key%d", i)))
		x := suite.Secret().Pick(r)
		HH[i] = suite.Point().Mul(nil, x)
	}

	// Constructors for use with protobuf.
	cons := func(t reflect.Type) interface{} {
		switch t {
		case tSecret:
			return suite.Secret()
		case tPoint:
			return suite.Point()
		default:
			return nil
		}
	}

	s := &shuffler{suite, id, k, N, h, H, HH, cons, nil, nil, nil}
	return s
}

type ByteConn struct {
	net.Conn
	buf []byte
}

func (b *ByteConn) ReadByte() (c byte, err error) {
	_, err = b.Read(b.buf)
	return b.buf[0], err
}

func (s *shuffler) initialState() *stateVector {
	rand := s.suite.Cipher([]byte("example"))

	// Create a set of ephemeral "client" keypairs to shuffle.
	// In practice, these would be Crypto-Book keys for members
	// of a Facebook group, for example.
	c := make([]abstract.Secret, s.k)
	C := make([]abstract.Point, s.k)

	for i := 0; i < s.k; i++ {
		c[i] = s.suite.Secret().Pick(rand)
		C[i] = s.suite.Point().Mul(nil, c[i])
	}

	// Use the public keys of the servers to compute a collective
	// server key for the onion encryption.
	P := s.suite.Point().Null()
	for i := range s.HH {
		P = s.suite.Point().Add(P, s.HH[i])
	}

	// ElGamal-encrypt the keypairs with the "server" key.
	X := make([]abstract.Point, s.k)
	Y := make([]abstract.Point, s.k)
	r := s.suite.Secret() // temporary
	for i := 0; i < s.k; i++ {
		r.Pick(rand)
		X[i] = s.suite.Point().Mul(nil, r)
		Y[i] = s.suite.Point().Mul(P, r) // ElGamal blinding factor
		Y[i].Add(Y[i], C[i])             // Encrypted client public key
	}

	nonce := s.suite.Secret().Pick(rand)
	initialState := []*shuffleState{&shuffleState{nil, X, nil, Y, nil, nil}}
	return &stateVector{nonce, initialState}
}

func (s *shuffler) ListenAndServe() error {
	addr := fmt.Sprintf(":%d", 8080+s.id)
	server, err := net.Listen("tcp", addr)
	if err != nil {
		return err
	}
	for {
		rwc, err := server.Accept()
		if err != nil {
			fmt.Println(err.Error())
			continue
		}
		bc := &ByteConn{rwc, make([]byte, 1)}
		go s.Handle(bc)
	}
	return nil
}

func (s *shuffler) Handle(bc *ByteConn) error {
	defer bc.Close()

	var state stateVector
	err := protobuf.Read(bc, &state, s.cons)
	if err != nil {
		return err
	}

	if len(state.States) <= s.N {
		fmt.Println("Got shuffle request.")
		if err := s.HandleShuffle(&state); err != nil {
			panic(err.Error())
		}
		return err
	} else if s.id == 0 {
		fmt.Println("Got final vector.")
		return s.getSignOffs(&state)
	} else {
		fmt.Println("Got signature request.")
		sig, err := s.signStateVector(&state)
		if err != nil {
			panic(err.Error())
			return err
		}
		return protobuf.Write(bc, &signature{s.id, sig})
	}
	return nil
}

func (s *shuffler) sendState(id int, state *stateVector) error {
	port := 8080 + (id % s.N)
	addr := fmt.Sprintf("localhost:%d", port)
	conn, err := net.Dial("tcp", addr)
	if err != nil {
		return err
	}
	defer conn.Close()
	return protobuf.Write(conn, state)
}

func (s *shuffler) HandleShuffle(state *stateVector) error {
	rand := s.suite.Cipher(abstract.RandomKey)
	if err := state.addShuffle(s.suite, s, rand); err != nil {
		return err
	}
	return s.sendState(s.id+1, state)
}

type signature struct {
	Id int
	S  []byte
}

func (s *shuffler) signStateVector(state *stateVector) ([]byte, error) {
	rand := s.suite.Cipher(abstract.RandomKey)

	st := state.States
	for i := 1; i < len(st); i++ {
		S, Sbar := st[i-1], st[i]

		X, Y := S.X, S.Dec
		Xbar, Ybar := Sbar.X, Sbar.Y
		H, prf := Sbar.G, Sbar.Prf

		// Verify the shuffle.
		verifier := shuffle.Verifier(s.suite, nil, H, X, Y, Xbar, Ybar)
		err := proof.HashVerify(s.suite, "PairShuffle", verifier, prf)
		if err != nil {
			panic("verify failed")
			return nil, err
		}

		// Verify the decryption.
		seed := abstract.Sum(s.suite, prf)
		verRand := s.suite.Cipher(seed)

		dec, decPrf := Sbar.Dec, Sbar.DecPrf

		// Scratch space for calculations.
		pair, c := s.suite.Point(), s.suite.Secret()
		zp := s.suite.Point()

		for j := range dec {
			pair.Sub(Ybar[j], dec[j])
			c.Pick(verRand)

			T := decPrf[j].T
			ss := decPrf[j].S
			if !zp.Mul(Xbar[j], ss).Equal(T.Add(T, pair.Mul(pair, c))) {
				return nil, errors.New("invalid decryption proof")
			}
		}
	}

	bytes, _ := protobuf.Encode(state)
	return anon.Sign(s.suite, rand, bytes, anon.Set{s.H}, nil, 0, s.h), nil
}

func (s *shuffler) getSignOffs(state *stateVector) error {
	replies := make(chan *signature)
	for i := 1; i < s.N; i++ {
		go func(id int) {
			port := 8080 + (id % s.N)
			addr := fmt.Sprintf("localhost:%d", port)
			rwc, err := net.Dial("tcp", addr)
			if err != nil {
				replies <- nil
				return
			}
			defer rwc.Close()

			bc := &ByteConn{rwc, make([]byte, 1)}
			if err = protobuf.Write(bc, state); err != nil {
				replies <- nil
				return
			}
			rwc.(*net.TCPConn).CloseWrite()

			var sig signature
			if err = protobuf.Read(bc, &sig); err != nil {
				replies <- nil
				return
			}
			replies <- &sig
		}(i)
	}

	sigs := make([][]byte, s.N)
	sig, err := s.signStateVector(state)
	if err != nil {
		return err
	}
	sigs[0] = sig

	for i := 0; i < s.N-1; i++ {
		reply := <-replies
		if reply != nil {
			X := s.HH[reply.Id]
			bytes, _ := protobuf.Encode(state)
			_, err := anon.Verify(s.suite, bytes, anon.Set{X}, nil, reply.S)
			if err != nil {
				return err
			}
			sigs[reply.Id] = reply.S
		}
	}

	fmt.Println("Got all signatures.")
	return s.checkKeys(state.States[len(state.States)-1])
}

func (s *shuffler) checkKeys(finalState *shuffleState) error {
	rand := s.suite.Cipher([]byte("example"))

	Y := finalState.Dec
	for i := range Y {
		fmt.Println(Y[i])
	}

	for i := 0; i < s.k; i++ {
		x := s.suite.Secret().Pick(rand)
		X := s.suite.Point().Mul(nil, x)
		fmt.Println(X)
	}
	return nil
}

func (s *shuffler) initiateShuffle() error {
	time.Sleep(time.Second)
	state := s.initialState()
	if err := s.HandleShuffle(state); err != nil {
		panic("Couldn't initiate shuffle: " + err.Error())
	}
	return nil
}

func main() {
	flag.Parse()
	if flag.NArg() < 3 {
		panic("usage: main.go id k N")
	}
	id, _ := strconv.Atoi(flag.Arg(0))
	k, _ := strconv.Atoi(flag.Arg(1))
	N, _ := strconv.Atoi(flag.Arg(2))

	suite := nist.NewAES128SHA256P256()
	s := NewShuffler(suite, id, k, N)

	if id == 0 {
		go s.initiateShuffle()
	}
	s.ListenAndServe()
}
