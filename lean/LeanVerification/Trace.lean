/-
Trace schema and parser (Lean track, Step 5).

Mirrors the `TraceEvent` enum in `crates/cordial-miners-core/src/trace.rs`.

Parsing strategy: only `String.splitOn` and `String.startsWith` are used
— both return plain `String` in all Lean 4 versions, avoiding the
`String.Slice` type-mismatch issues with `takeWhile`, `trim`, `drop`, etc.

Owned by Issue 05 (KR5 — Proof-to-Test Mapping and Trace Replay).
Rust: `crates/cordial-miners-core/src/trace.rs`
-/

namespace CordialMiners

/-! ### Trace event payload types -/

structure FinalityEvent where
  nodeId    : String
  wave      : Nat
  blockHash : String
  /-- `"finalized"` or `"not_finalized"` -/
  decision  : String
  deriving Repr

structure InsertEvent where
  nodeId       : String
  round        : Nat
  blockHash    : String
  parentHashes : List String
  creator      : String
  deriving Repr

structure EquivocationEvent where
  nodeId                 : String
  equivocator            : String
  round                  : Nat
  conflictingBlockHashes : List String
  deriving Repr

structure ValidateEvent where
  nodeId    : String
  round     : Nat
  blockHash : String
  outcome   : String
  errors    : List String
  deriving Repr

structure TauOrderEvent where
  nodeId           : String
  wave             : Nat
  latestLeaderHash : String
  outputLen        : Nat
  deriving Repr

structure EmitOutputEvent where
  nodeId           : String
  wave             : Nat
  blockHash        : String
  outputIndex      : Nat
  outputPrefixHash : String
  deriving Repr

inductive TraceEvent where
  | insertBlock        : InsertEvent       → TraceEvent
  | validateBlock      : ValidateEvent     → TraceEvent
  | computeFinality    : FinalityEvent     → TraceEvent
  | detectEquivocation : EquivocationEvent → TraceEvent
  | runTauOrder        : TauOrderEvent     → TraceEvent
  | emitOutput         : EmitOutputEvent   → TraceEvent
  | other              : String            → TraceEvent
  deriving Repr

/-! ### JSON field extractors (splitOn-only, no String.Slice) -/

/-- Extract `"key":"<value>"` → `value`. Returns `""` if absent. -/
private def extractStr (key : String) (line : String) : String :=
  let needle := "\"" ++ key ++ "\":\""
  match line.splitOn needle with
  | [_, rest] => match rest.splitOn "\"" with
    | v :: _ => v
    | []     => ""
  | _ => ""

/-- Extract `"key":<n>` → `n`.  Returns `0` if absent or `null`. -/
private def extractNat (key : String) (line : String) : Nat :=
  let needle := "\"" ++ key ++ "\":"
  match line.splitOn needle with
  | [_, rest] =>
    -- Take the token before the next `,` or `}`
    let tok := match rest.splitOn "," with
      | t :: _ => t
      | []     => rest
    let tok' := match tok.splitOn "}" with
      | t :: _ => t
      | []     => tok
    tok'.toNat!
  | _ => 0

/-- Pick every element at an odd index (1, 3, 5, …) from a list. -/
private def oddElements : List String → List String
  | []            => []
  | [_]           => []
  | _ :: v :: rest => v :: oddElements rest

/-- Extract a JSON array of strings `"key":["v1","v2"]` → `["v1","v2"]`.
Splits on `"` and takes every odd-indexed fragment (the actual values). -/
private def extractStrList (key : String) (line : String) : List String :=
  let needle := "\"" ++ key ++ "\":["
  match line.splitOn needle with
  | [_, rest] =>
    match rest.splitOn "]" with
    | inner :: _ =>
      -- inner = `"v1","v2"` or `` (empty array)
      -- splitOn `"` gives: ["", "v1", ",", "v2", ""] for `"v1","v2"`
      oddElements (inner.splitOn "\"")
    | [] => []
  | _ => []

/-! ### Line → TraceEvent parser -/

def parseLine (line : String) : TraceEvent :=
  let k := extractStr "event" line
  match k with
  | "insert_block" => .insertBlock {
      nodeId       := extractStr     "node_id"      line
      round        := extractNat     "round"        line
      blockHash    := extractStr     "block_hash"   line
      parentHashes := extractStrList "parent_hashes" line
      creator      := extractStr     "creator"      line }
  | "validate_block" => .validateBlock {
      nodeId    := extractStr     "node_id"    line
      round     := extractNat     "round"      line
      blockHash := extractStr     "block_hash" line
      outcome   := extractStr     "outcome"    line
      errors    := extractStrList "errors"     line }
  | "compute_finality" => .computeFinality {
      nodeId    := extractStr "node_id"    line
      wave      := extractNat "wave"       line
      blockHash := extractStr "block_hash" line
      decision  := extractStr "decision"   line }
  | "detect_equivocation" => .detectEquivocation {
      nodeId                 := extractStr     "node_id"                   line
      equivocator            := extractStr     "equivocator"               line
      round                  := extractNat     "round"                     line
      conflictingBlockHashes := extractStrList "conflicting_block_hashes"  line }
  | "run_tau_order" => .runTauOrder {
      nodeId           := extractStr "node_id"            line
      wave             := extractNat "wave"               line
      latestLeaderHash := extractStr "latest_leader_hash" line
      outputLen        := extractNat "output_len"         line }
  | "emit_output" => .emitOutput {
      nodeId           := extractStr "node_id"            line
      wave             := extractNat "wave"               line
      blockHash        := extractStr "block_hash"         line
      outputIndex      := extractNat "output_index"       line
      outputPrefixHash := extractStr "output_prefix_hash" line }
  | _ => .other k

/-! ### File reader -/

/-- Read `path` and return one `TraceEvent` per non-empty line. -/
def readTraceFile (path : String) : IO (List TraceEvent) := do
  let content ← IO.FS.readFile path
  let lines   := content.splitOn "\n"
  return lines
    |>.filter (fun l => match l.splitOn "{" with | _ :: _ :: _ => true | _ => false)
    |>.map    parseLine

end CordialMiners
