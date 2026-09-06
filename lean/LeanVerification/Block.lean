/-
The block model: a single blocklace block and its well-formedness
conditions (author, parents, payload).

Mirrors the Rust types:
  - `BlockIdentity` → `BlockId`       (types/identity_id.rs)
  - `BlockContent`  → `BlockContent`  (types/content_id.rs)
  - `Block`         → `Block`         (block.rs)

The cryptographic hash is abstracted by an executable injective encoding for
the standalone formal examples.  Trace replay uses a compact injective
interning table from Rust hash strings to `BlockId`; recursively encoding a
whole predecessor DAG into a natural number is mathematically convenient but
not an executable representation of a fixed-width cryptographic digest.

Owned by Issue 02 (KR1 — Blocklace Core).
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Equiv.Finset

namespace CordialMiners

/-! ### Primitive identifiers -/

/-- Opaque node identifier — corresponds to `NodeId` in node_id.rs. -/
abbrev NodeId := Nat

/-- Opaque block identifier.
In Rust this is represented by `BlockIdentity`, which contains the
content hash, creator, and signature. At the Lean abstraction level,
we treat it as an opaque natural number.
-/
abbrev BlockId := Nat

/-! ### Block Content -/

/-- Block content `C = (v, P)`.

`payload` corresponds to the arbitrary value `v`, while `predecessors`
is the set `P` of predecessor block identities.
-/
structure BlockContent where
  payload      : List Nat
  predecessors : Finset BlockId
  deriving DecidableEq

private def blockContentEquiv : BlockContent ≃ List Nat × Finset BlockId where
  toFun content := (content.payload, content.predecessors)
  invFun data := { payload := data.1, predecessors := data.2 }
  left_inv _ := rfl
  right_inv _ := rfl

instance : Encodable BlockContent :=
  Encodable.ofEquiv (List Nat × Finset BlockId) blockContentEquiv

/-! ### Block Identity / Hash -/

/-- Executable injective abstraction of the signed content hash.

Corresponds to paper §2.2: i = signedhash((v, P), k_p).
The concrete Rust digest remains an external identifier in the trace adapter;
this encoding supplies the collision-free identifier used by the formal DAG.
-/
def hashContent (creator : NodeId) (content : BlockContent) : BlockId :=
  Encodable.encode (creator, content)

/--
Hash injectivity for the executable abstraction. Unlike a cryptographic
collision-resistance assumption, this follows from `Encodable.encode`.
-/
theorem hashInj {n1 n2 : NodeId} {c1 c2 : BlockContent}
    (h : hashContent n1 c1 = hashContent n2 c2) : n1 = n2 ∧ c1 = c2 := by
  have hp : (n1, c1) = (n2, c2) := Encodable.encode_injective h
  exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩

/-! ### Block -/

/--
A single blocklace block.

`id` is opaque at the protocol-model layer.  Standalone examples may choose
`hashContent creator content`; replay instead interns the externally verified
Rust digest and rejects duplicate digest declarations.  The correspondence
between a concrete digest and signed Rust content is therefore an explicit
adapter/cryptography trust boundary, not an enormous recursively encoded Nat.
-/
structure Block where
  id        : BlockId
  creator   : NodeId
  content   : BlockContent
  deriving DecidableEq

/-- Optional model-side condition for clients that construct identifiers with
`hashContent`.  The DAG safety development itself needs only fresh opaque IDs,
which is exactly the abstraction used for real cryptographic hashes. -/
def HashFaithful (block : Block) : Prop :=
  block.id = hashContent block.creator block.content

end CordialMiners
