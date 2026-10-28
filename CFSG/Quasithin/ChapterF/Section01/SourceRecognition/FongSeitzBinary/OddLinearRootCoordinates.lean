module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootGeneratedQuotient
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearRootCoordinates
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas

/-!
# One actual field on the odd-dihedral source roots

When the actual Weyl rotation order is odd, opposition conjugates the first
simple root to the second. Transport the first factor's original PSL₂ field
coordinates through that explicit conjugation, then through the chosen
representatives of every Weyl class. This gives injective additive maps over
ONE field onto all canonical Weyl roots, including literal formulas for
opposition and conjugation. No model for the second local factor is assumed.

On the both-perfect branch these root maps generate the entire same finite
quotient, by the proved root-span theorem. The mixed positive/negative
commutator laws and any assertion that the actual Weyl order is 3 remain
unproved source obligations. Additive coordinates alone are not an A₂
recognition theorem.

Source: Carter 2.5.10–2.5.17, refs/KGroup/GLS3/Chapter2Ca2.tex;
DGS, Groups and Graphs, Part II, pp.80–81 and Theorem D, p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootGeneration
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

private def rootConjugation {Y : Type*} [Group Y] (A : Subgroup Y) (n : Y) :
    A ≃* rightConjugate A n where
  toEquiv := rightConjugateEquiv A n
  map_mul' := by
    intro a b
    apply Subtype.ext
    change (rightConjugateEquiv A n (a*b) : Y) =
      (rightConjugateEquiv A n a : Y) * (rightConjugateEquiv A n b : Y)
    simp only [rightConjugateEquiv_apply, Subgroup.coe_mul, mul_assoc, mul_inv_cancel_left]

variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : Odd (rotationOrder Q))

/-- The actual odd-opposition lift conjugates the two marked simple roots. -/
def simpleRootOppositionEquiv : simpleRoot Q split 0 ≃* simpleRoot Q split 1 :=
  (rootConjugation (simpleRoot Q split 0)
    (representative (Q.simple 0*longest Q) : X ⧸ Q.D)).trans
    (MulEquiv.subgroupCongr (simpleRoot_conjugate_of_odd Q split hm _ (representative_spec _)))

omit [Field F] [Finite F] [CharP F 2] in
@[simp] theorem simpleRootOppositionEquiv_apply (r : simpleRoot Q split 0) :
    (simpleRootOppositionEquiv Q split hm r : X ⧸ Q.D) =
      (representative (Q.simple 0*longest Q) : X ⧸ Q.D)⁻¹ * r *
        (representative (Q.simple 0*longest Q) : X ⧸ Q.D) := by
  change (rightConjugateEquiv (simpleRoot Q split 0)
    (representative (Q.simple 0*longest Q) : X ⧸ Q.D) r : X ⧸ Q.D) = _
  exact rightConjugateEquiv_apply _ _ _

/-- Choose the identity at the original first root and actual opposition at the second. -/
def simpleRootOpposition (i : Fin 2) : simpleRoot Q split 0 ≃* simpleRoot Q split i :=
  if hi : i = 0 then MulEquiv.subgroupCongr (by rw [hi])
  else (simpleRootOppositionEquiv Q split hm).trans
    (MulEquiv.subgroupCongr (by
      have hi' : i = 1 := by omega
      rw [hi']))

omit [Field F] [Finite F] [CharP F 2] in
@[simp] theorem simpleRootOpposition_zero (r : simpleRoot Q split 0) :
    simpleRootOpposition Q split hm 0 r = r := by
  simp only [simpleRootOpposition, dite_true]
  rfl

omit [Field F] [Finite F] [CharP F 2] in
@[simp] theorem simpleRootOpposition_one (r : simpleRoot Q split 0) :
    simpleRootOpposition Q split hm 1 r = simpleRootOppositionEquiv Q split hm r := by
  simp only [simpleRootOpposition, show (1 : Fin 2) ≠ 0 by decide, dite_false]
  rfl

variable [Finite (L 0)] (hp : Group.IsPerfect (L 0))
  (T : Sylow 2 (L 0)) (hT : (T : Subgroup (L 0)).map (L 0).subtype = S ⊓ L 0)
  (μ : ((L 0) ⧸ pCore 2 (L 0)) ≃* PSL(2,F))

/-- Both actual simple roots use the original first-factor field. -/
def oddSimpleRootFieldEquiv (i : Fin 2) : Multiplicative F ≃* simpleRoot Q split i :=
  (simpleRootLinearEquiv Q e h split 0 hp T hT μ).symm.trans
    (simpleRootOpposition Q split hm i)

/-- Parameters on every actual Weyl root, using the same field and chosen Weyl lifts. -/
def oddWeylRootParameter (j : Fin 2 × Weyl Q) : Multiplicative F →* X ⧸ Q.D :=
  (MulAut.conj (representative j.2 : X ⧸ Q.D)⁻¹).toMonoidHom.comp
    ((simpleRoot Q split j.1).subtype.comp
      (oddSimpleRootFieldEquiv Q e h split hm hp T hT μ j.1).toMonoidHom)

@[simp] theorem oddWeylRootParameter_apply (j : Fin 2 × Weyl Q) (a : Multiplicative F) :
    oddWeylRootParameter Q e h split hm hp T hT μ j a =
      (representative j.2 : X ⧸ Q.D)⁻¹ *
        (oddSimpleRootFieldEquiv Q e h split hm hp T hT μ j.1 a : X ⧸ Q.D) *
          (representative j.2 : X ⧸ Q.D) := by
  change (representative j.2 : X ⧸ Q.D)⁻¹ *
    (oddSimpleRootFieldEquiv Q e h split hm hp T hT μ j.1 a : X ⧸ Q.D) *
    ((representative j.2 : X ⧸ Q.D)⁻¹)⁻¹ = _
  rw [inv_inv]

theorem oddWeylRootParameter_range (j : Fin 2 × Weyl Q) :
    (oddWeylRootParameter Q e h split hm hp T hT μ j).range =
      rightConjugate (simpleRoot Q split j.1) (representative j.2 : X ⧸ Q.D) := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    rw [oddWeylRootParameter_apply]
    change (representative j.2 : X ⧸ Q.D) * _ * (representative j.2 : X ⧸ Q.D)⁻¹ ∈ simpleRoot Q split j.1
    simpa only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using
      (oddSimpleRootFieldEquiv Q e h split hm hp T hT μ j.1 a).property
  · intro hx
    let r : simpleRoot Q split j.1 :=
      ⟨(representative j.2 : X ⧸ Q.D)*x*(representative j.2 : X ⧸ Q.D)⁻¹,hx⟩
    obtain ⟨a,ha⟩ := (oddSimpleRootFieldEquiv Q e h split hm hp T hT μ j.1).surjective r
    refine ⟨a, ?_⟩
    rw [oddWeylRootParameter_apply, ha]
    dsimp only [r]
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]

theorem oddWeylRootParameter_injective (j : Fin 2 × Weyl Q) :
    Function.Injective (oddWeylRootParameter Q e h split hm hp T hT μ j) :=
  (MulAut.conj (representative j.2 : X ⧸ Q.D)⁻¹).injective.comp
    ((simpleRoot Q split j.1).subtype_injective.comp
      (oddSimpleRootFieldEquiv Q e h split hm hp T hT μ j.1).injective)

/-- Every parametrized root has the addition law of the SAME actual field. -/
theorem oddWeylRootParameter_add (j : Fin 2 × Weyl Q) (a b : F) :
    oddWeylRootParameter Q e h split hm hp T hT μ j (Multiplicative.ofAdd (a+b)) =
      oddWeylRootParameter Q e h split hm hp T hT μ j (Multiplicative.ofAdd a) *
        oddWeylRootParameter Q e h split hm hp T hT μ j (Multiplicative.ofAdd b) :=
  map_mul _ _ _

/-- At the first simple root the original model map is unchanged. -/
theorem oddSimpleRootFieldEquiv_first_model (a : Multiplicative F) :
    μ (simpleRootProjection Q e h split 0 hp
      (oddSimpleRootFieldEquiv Q e h split hm hp T hT μ 0 a)) =
      (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive (linearModelSylow 0 T μ) a : PSL(2,F)) := by
  have he := simpleRootLinearEquiv_model Q e h split 0 hp T hT μ
    ((simpleRootLinearEquiv Q e h split 0 hp T hT μ).symm a)
  rw [MulEquiv.apply_symm_apply] at he
  simpa only [oddSimpleRootFieldEquiv, MulEquiv.trans_apply, simpleRootOpposition_zero] using he.symm

/-- The second simple root is obtained by the literal odd-opposition conjugation. -/
theorem oddSimpleRootFieldEquiv_second (a : Multiplicative F) :
    (oddSimpleRootFieldEquiv Q e h split hm hp T hT μ 1 a : X ⧸ Q.D) =
      (representative (Q.simple 0*longest Q) : X ⧸ Q.D)⁻¹ *
        (oddSimpleRootFieldEquiv Q e h split hm hp T hT μ 0 a : X ⧸ Q.D) *
          (representative (Q.simple 0*longest Q) : X ⧸ Q.D) := by
  simp only [oddSimpleRootFieldEquiv, MulEquiv.trans_apply, simpleRootOpposition_one,
    simpleRootOppositionEquiv_apply, simpleRootOpposition_zero]

/-- These constructed one-field root maps generate the entire perfect-source quotient. -/
theorem oddWeylRootParameter_generate (hpall : ∀ i, Group.IsPerfect (L i)) :
    closure {g | ∃ j a, g = oddWeylRootParameter Q e h split hm hp T hT μ j a} = ⊤ := by
  apply root_parameters_generate Q e h hpall split
  intro i w
  refine ⟨(i,w), ?_⟩
  rw [← oddWeylRootParameter_range Q e h split hm hp T hT μ (i,w)]
  exact Set.Subset.rfl

omit [Finite (L 0)] in
include e h hm in
/-- The source first-factor witness constructs a single field and generating
parameters on all actual Weyl roots; no model for the second factor is needed. -/
theorem exists_odd_linear_root_parameters {n : ℕ}
    (hpall : ∀ i, Group.IsPerfect (L i))
    (hmodel : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 (2^n)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2^n ∧
      ∃ x : (Fin 2 × Weyl Q) → Multiplicative K →* X ⧸ Q.D,
        (∀ j, (x j).range = rightConjugate (simpleRoot Q split j.1)
          (representative j.2 : X ⧸ Q.D)) ∧
        (∀ j, Function.Injective (x j)) ∧
        closure {g | ∃ j a, g = x j a} = ⊤ := by
  let := h.finite_local 0
  obtain ⟨K,hK,hf,hcard,⟨μ⟩⟩ := hmodel
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨T,hT⟩ := h.sylow 0
  exact ⟨K,hK,hf,inferInstance,hcard,
    oddWeylRootParameter Q e h split hm (hpall 0) T hT μ,
    oddWeylRootParameter_range Q e h split hm (hpall 0) T hT μ,
    oddWeylRootParameter_injective Q e h split hm (hpall 0) T hT μ,
    oddWeylRootParameter_generate Q e h split hm (hpall 0) T hT μ hpall⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- Single-field parameters and generation on the literal original source quotient. -/
theorem quotient_odd_linear_root_parameters (h : HypothesisF11 L S)
    (hp : ∀ i, Group.IsPerfect (L i)) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hm : Odd (rotationOrder Q)) {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 (2^n)) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
      Nat.card K = 2^n ∧
      ∃ x : (Fin 2 × Weyl Q) → Multiplicative K →* (generated L S) ⧸ Q.D,
        (∀ j, (x j).range = rightConjugate (simpleRoot Q split j.1)
          (representative j.2 : (generated L S) ⧸ Q.D)) ∧
        (∀ j, Function.Injective (x j)) ∧
        closure {g | ∃ j a, g = x j a} = ⊤ :=
  MarkedLocal.exists_odd_linear_root_parameters Q (originalMarkedIso Q) h split hm hp hmodel

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
