module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Relations

/-!
# The local order-32 centralizer in the crossing-fusion argument

The centralizer of pi, mu and either marked xi has binary words on
(pi, mu, xi, tau*lambda, mu-prime). Its only nontrivial generator
commutator is [tau*lambda, mu-prime] = pi*mu. Thus it is a dihedral
group of order eight times an elementary four-group.

We compute multiplication and the action induced by alpha on these words.
An action of exponent three that has the prescribed action on the center
must send tau*lambda to itself times one of 1, mu, xi, mu*xi. The cube
calculation is performed on binary coordinates; the word identities and
the local absence of three-torsion are checked on concrete permutations.
Both independent markings are retained throughout.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Sections 2.13--2.15 and 4.1, pp.231--232.
These computations support a proof of crossing fusion from the supplied
Section 4.1 seed, without a normalizer-order assumption.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion.CrossFusion
open Coordinates
local instance : DecidableEq H := inferInstance

public abbrev QCode := Bit × Bit × Bit × Bit × Bit
local instance : DecidableEq QCode := inferInstance
@[expose] public def qWord (b d : Bit) (v : QCode) : H :=
  Coordinates.pi ^ v.1.val * Coordinates.mu ^ v.2.1.val *
    normalizedXi d ^ v.2.2.1.val * coreTau b ^ v.2.2.2.1.val * mup ^ v.2.2.2.2.val

@[expose] public def qImage (d : Bit) (s r : H) (v : QCode) : H :=
  (Coordinates.pi * normalizedXi d) ^ v.1.val *
    (Coordinates.mu * normalizedXi d) ^ v.2.1.val *
    Coordinates.mu ^ v.2.2.1.val * s ^ v.2.2.2.1.val * r ^ v.2.2.2.2.val

@[expose] public def qRead (c : Code) : QCode :=
  (c.1.1 + c.1.2.2.1 * c.2.1, c.1.2.1 + c.1.2.2.1 * c.2.1,
    c.1.2.2.2, c.2.1, c.1.2.2.1)

-- The word coordinates change when either marking is changed.
@[expose] public def qRecode (b d : Bit) (v : QCode) : QCode :=
  (v.1 + d * v.2.2.1 + b * v.2.2.2.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
public theorem centralizer_table : ∀ d : Bit, ∀ c : Code,
    word c * Coordinates.mu = Coordinates.mu * word c →
    word c * normalizedXi d = normalizedXi d * word c →
    qWord 0 0 (qRead c) = word c := by decide +kernel

public theorem recode_table : ∀ b d v,
    qWord b d (qRecode b d v) = qWord 0 0 v := by decide +kernel

@[expose] public def qMul (v w : QCode) : QCode :=
  (v.1 + w.1 + v.2.2.2.2 * w.2.2.2.1,
   v.2.1 + w.2.1 + v.2.2.2.2 * w.2.2.2.1,
   v.2.2.1 + w.2.2.1, v.2.2.2.1 + w.2.2.2.1, v.2.2.2.2 + w.2.2.2.2)
@[expose] public def qScale (v : QCode) (c : Bit) : QCode := if c = 0 then 0 else v
@[expose] public def qAction (s r v : QCode) : QCode :=
  qMul (qMul (qMul (qMul
    (qScale (1,0,1,0,0) v.1) (qScale (0,1,1,0,0) v.2.1))
    (qScale (0,1,0,0,0) v.2.2.1)) (qScale s v.2.2.2.1))
    (qScale r v.2.2.2.2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
public theorem qWord_mul : ∀ b d v w, qWord b d (qMul v w) = qWord b d v * qWord b d w := by
  decide +kernel

public theorem qWord_scale : ∀ b d v c,
    qWord b d (qScale v c) = qWord b d v ^ c.val := by decide +kernel

public theorem qWord_action (b d : Bit) (s r v : QCode) :
    qWord b d (qAction s r v) = qImage d (qWord b d s) (qWord b d r) v := by
  have h : ∀ b d,
      qWord b d (1,0,1,0,0) = Coordinates.pi * normalizedXi d ∧
      qWord b d (0,1,1,0,0) = Coordinates.mu * normalizedXi d ∧
      qWord b d (0,1,0,0,0) = Coordinates.mu := by decide +kernel
  simp only [qAction, qWord_mul, qWord_scale, (h b d).1, (h b d).2.1, (h b d).2.2,
    qImage]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
public theorem action_table : ∀ s r : QCode,
    qMul s s = 0 → qMul r r = 0 →
    qAction s r (qAction s r s) = (0,0,0,1,0) →
    qAction s r (qAction s r r) = (0,0,0,0,1) →
    s = (0,0,0,1,0) ∨ s = (0,1,0,1,0) ∨ s = (0,0,1,1,0) ∨ s = (0,1,1,1,0) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
public theorem qWord_injective : ∀ b d, Function.Injective (qWord b d) := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
public theorem local_cube : ∀ b : Bit, ∀ c : Code,
    word c * coreTau b = coreTau b * word c → (word c) ^ 3 = 1 → word c = 1 := by
  decide +kernel

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.FaithfulExclusion.CrossFusion
