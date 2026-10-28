module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.LinearRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.UnequalOrderRecognition
public import Mathlib.Algebra.Field.Shrink
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.Data.Fintype.Shrink

/-!
# The complete linear quadrangle alternative from original factor quotients

The actual original PSL₂ quotient marks give both faithful local actions
and both remainder-to-kernel containments. For equal field orders,
Cartan irreducibility and derived-radical normality select a commuting
root orientation. The rank-three recognition constructs full Sp₄,
including Sp₄(2), without any independent natural-module profile.

Sylow alignment simultaneously identifies the unipotent group, whole
Borel and both standard parabolics. The original endpoint isomorphisms
and every element of their intersection use that same equivalence.
The original SourceQuotient specialization retains the literal Q.q.

Combining this C₂ result with the proved unequal-linear U₄ theorem
exhausts every pair of original linear factors at rotation order four.
No core structure, commuting-root, exact field-ratio or endpoint-perfectness
premise is added. LinearQuadrangleApplications is the literal Chapter 12
consumer. Earlier source producers retain F.1.1, quotient and Weyl-order
selection; nonlinear rows and final seven-row assembly remain separate.

Source: Fong--Seitz I (6A), pp.37--38; II (7C), p.193 and (8A)--(8B),
pp.197--202; DGS Theorem D, p.224; AS F.1.1--3 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.LinearQuadrangle
open Chapter6.Source.RankOneGeneric
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (mark : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include mark h split in
private theorem local_model {F : Type*} [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F)) :
    simpleRemainder Q split i ≤ localKernel Q i ∧
      Nonempty (localGroup Q split i ≃* PSL(2,F)) := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hV := MarkedLocal.linear_remainder_le_kernel Q mark h split i T hT μ
  obtain ⟨f,hf,hk,_⟩ := MarkedLocal.linear_actor_quotient_of_factor Q mark h split i μ
  let A := (S ⊔ L i).subgroupOf (parabolic L S i)
  let : A.Normal := QuadrangleStructure.marked_sylow_factor_normal Q mark h split i
  obtain ⟨_,ν,_,_⟩ := QuadrangleStructure.marked_linear_localGroup Q mark h split i
    (UnitarySource.actorReflection Q split i) hV A (subgroupOf_mono _ le_sup_left) f hf hk
  exact ⟨hV,⟨ν⟩⟩

include mark h split in
/-- The original equal linear factors recognize the same full quotient,
with its unipotent group, whole Borel and both parabolics simultaneously marked. -/
theorem marked_equal_linear_symplectic_equiv
    {E F : Type*} [Field E] [Finite E] [CharP E 2]
    [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4)
    (μ₀ : ((L 0) ⧸ pCore 2 (L 0)) ≃* PSL(2,E))
    (μ₁ : ((L 1) ⧸ pCore 2 (L 1)) ≃* PSL(2,F))
    (hcard : Nat.card E = Nat.card F) :
    ∃ e : (X ⧸ Q.D) ≃* Sp E,
      split.U.map e.toMonoidHom = unipotent (F := E) ∧
      Q.tits.B.map e.toMonoidHom = Theory.SpecificGroups.SymplecticFour.borel (F := E) ∧
      (((Q.tits.standardParabolic {Q.simple 0}).map e.toMonoidHom = pointParabolic (F := E) ∧
        (Q.tits.standardParabolic {Q.simple 1}).map e.toMonoidHom = planeParabolic (F := E)) ∨
       ((Q.tits.standardParabolic {Q.simple 0}).map e.toMonoidHom = planeParabolic (F := E) ∧
        (Q.tits.standardParabolic {Q.simple 1}).map e.toMonoidHom = pointParabolic (F := E))) := by
  obtain ⟨hV₀,⟨ν₀⟩⟩ := local_model Q mark h split 0 μ₀
  obtain ⟨hV₁,⟨ν₁⟩⟩ := local_model Q mark h split 1 μ₁
  let := Fintype.ofFinite E
  let := Fintype.ofFinite F
  let θ : F ≃+* E := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card] using hcard.symm)
  let ν : ∀ i, localGroup Q split i ≃* PSL(2,E) :=
    fun i => if hi : i = 0 then hi ▸ ν₀ else
      (show i = 1 by omega) ▸ (ν₁.trans (Atlas.fieldEquivPSL 2 θ))
  have hV : ∀ i, simpleRemainder Q split i ≤ localKernel Q i := by
    intro i
    fin_cases i
    · exact hV₀
    · exact hV₁
  obtain ⟨e⟩ := Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.symplectic_equiv_of_equal_linear_factors
    Q split hm hV ν (MarkedLocal.parabolic_core_selfCentralizing Q mark h)
    (MarkedLocal.unipotentClosure_eq_top_of_source Q mark h split)
  obtain ⟨g,e',_,hU⟩ := C2RankThree.exists_unipotent_aligned Q split e
  have hB := C2RankThree.map_borel_of_unipotent Q split e' hU
  exact ⟨e',hU,hB,C2RankThree.map_parabolics_of_borel Q
    (MarkedLocal.parabolic_core_selfCentralizing Q mark h) e' hB⟩

include mark h split in
/-- Both marked endpoint squares and all elements of the full Borel use
one symplectic equivalence, including the binary, nonperfect case. -/
theorem marked_equal_linear_symplectic_comparison
    {E F : Type*} [Field E] [Finite E] [CharP E 2]
    [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4)
    (μ₀ : ((L 0) ⧸ pCore 2 (L 0)) ≃* PSL(2,E))
    (μ₁ : ((L 1) ⧸ pCore 2 (L 1)) ≃* PSL(2,F))
    (hcard : Nat.card E = Nat.card F) :
    ∃ e : (X ⧸ Q.D) ≃* Sp E,
      (∃ c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (C2RankThree.flagAmalgam E),
        (∀ a : parabolic L S 0, (c.left a : Sp E) = e (mark.left a : X ⧸ Q.D)) ∧
        (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
          (c.middle a : Sp E) = e (mark.middle a : X ⧸ Q.D)) ∧
        (∀ a : parabolic L S 1, (c.right a : Sp E) = e (mark.right a : X ⧸ Q.D))) ∨
      (∃ c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (C2RankThree.flagAmalgam E).reverse,
        (∀ a : parabolic L S 0, (c.left a : Sp E) = e (mark.left a : X ⧸ Q.D)) ∧
        (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
          (c.middle a : Sp E) = e (mark.middle a : X ⧸ Q.D)) ∧
        (∀ a : parabolic L S 1, (c.right a : Sp E) = e (mark.right a : X ⧸ Q.D))) := by
  obtain ⟨e,_,hB,hP⟩ := marked_equal_linear_symplectic_equiv Q mark h split hm μ₀ μ₁ hcard
  refine ⟨e,?_⟩
  rcases hP with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · refine Or.inl ⟨mark.trans (Q.markedIso.symm.trans (C2RankThree.quotientMarkedIso Q e hB h0 h1)), ?_,?_,?_⟩
    · intro a
      change ((C2RankThree.quotientMarkedIso Q e hB h0 h1).left
        (Q.markedIso.left.symm (mark.left a)) : Sp E) = _
      rw [(C2RankThree.quotientMarkedIso_apply Q e hB h0 h1).1]
      congr 1
      rw [←Q.markedIso_left_apply,MulEquiv.apply_symm_apply]
    · intro a
      change ((C2RankThree.quotientMarkedIso Q e hB h0 h1).middle
        (Q.markedIso.middle.symm (mark.middle a)) : Sp E) = _
      rw [(C2RankThree.quotientMarkedIso_apply Q e hB h0 h1).2.1]
      congr 1
      rw [←Q.markedIso_middle_apply,MulEquiv.apply_symm_apply]
    · intro a
      change ((C2RankThree.quotientMarkedIso Q e hB h0 h1).right
        (Q.markedIso.right.symm (mark.right a)) : Sp E) = _
      rw [(C2RankThree.quotientMarkedIso_apply Q e hB h0 h1).2.2]
      congr 1
      rw [←Q.markedIso_right_apply,MulEquiv.apply_symm_apply]
  · refine Or.inr ⟨mark.trans (Q.markedIso.symm.trans (C2RankThree.quotientReversedMarkedIso Q e hB h0 h1)), ?_,?_,?_⟩
    · intro a
      change ((C2RankThree.quotientReversedMarkedIso Q e hB h0 h1).left
        (Q.markedIso.left.symm (mark.left a)) : Sp E) = _
      rw [(C2RankThree.quotientReversedMarkedIso_apply Q e hB h0 h1).1]
      congr 1
      rw [←Q.markedIso_left_apply,MulEquiv.apply_symm_apply]
    · intro a
      change ((C2RankThree.quotientReversedMarkedIso Q e hB h0 h1).middle
        (Q.markedIso.middle.symm (mark.middle a)) : Sp E) = _
      rw [(C2RankThree.quotientReversedMarkedIso_apply Q e hB h0 h1).2.1]
      congr 1
      rw [←Q.markedIso_middle_apply,MulEquiv.apply_symm_apply]
    · intro a
      change ((C2RankThree.quotientReversedMarkedIso Q e hB h0 h1).right
        (Q.markedIso.right.symm (mark.right a)) : Sp E) = _
      rw [(C2RankThree.quotientReversedMarkedIso_apply Q e hB h0 h1).2.2]
      congr 1
      rw [←Q.markedIso_right_apply,MulEquiv.apply_symm_apply]

include mark h split in
/-- All original linear quadrangles give C₂ or U₄, without natural-module,
core-structure, commuting-root or field-ratio premises. -/
theorem marked_linear_quadrangle_catalogue
    {E F : Type*} [Field E] [Finite E] [CharP E 2]
    [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4)
    (μ₀ : ((L 0) ⧸ pCore 2 (L 0)) ≃* PSL(2,E))
    (μ₁ : ((L 1) ⧸ pCore 2 (L 1)) ≃* PSL(2,F)) :
    Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) := by
  rcases lt_trichotomy (Nat.card E) (Nat.card F) with hlt | heq | hlt
  · exact UnitarySource.marked_unequal_linear_unitaryFour_catalogue Q mark h split hm
      1 0 (by decide) μ₁ μ₀ hlt
  · let K := Shrink.{0} E
    let θ : E ≃+* K := (Shrink.ringEquiv.{0,_} E).symm
    let : CharP K 2 := (θ.toRingHom.charP_iff_charP 2).mp inferInstance
    let := Fintype.ofFinite K
    obtain ⟨n,_,hn⟩ := FiniteField.card K 2
    have hK : Nat.card K = 2^(n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hn
    obtain ⟨e,hc⟩ := marked_equal_linear_symplectic_comparison Q mark h split hm
      (μ₀.trans (Atlas.fieldEquivPSL 2 θ)) μ₁ ((Nat.card_congr θ.toEquiv).symm.trans heq)
    apply Global.ConcreteAmalgamComparison.symplectic K n n.pos hK
    rcases hc with ⟨c,_⟩ | ⟨c,_⟩
    · exact Or.inl ⟨c⟩
    · exact Or.inr ⟨c⟩
  · exact UnitarySource.marked_unequal_linear_unitaryFour_catalogue Q mark h split hm
      0 1 (by decide) μ₀ μ₁ hlt

include mark h split in
/-- The original PSL₂ quotient assertions suffice for the whole linear
quadrangle alternative; no perfectness is imposed on either factor. -/
theorem marked_linear_quadrangle_of_factor_types
    (hm : rotationOrder Q = 4) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h₀ : ClassicalGroup.IsPSL ((L 0) ⧸ pCore 2 (L 0)) 2 (2^a))
    (h₁ : ClassicalGroup.IsPSL ((L 1) ⧸ pCore 2 (L 1)) 2 (2^b)) :
    Global.ConcreteAmalgamComparison
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right) := by
  obtain ⟨E,hE,hfinE,hcardE,⟨μ₀⟩⟩ := h₀
  obtain ⟨F,hF,hfinF,hcardF,⟨μ₁⟩⟩ := h₁
  let := Fintype.ofFinite E
  let := Fintype.ofFinite F
  let : NeZero a := ⟨ha.ne'⟩
  let : NeZero b := ⟨hb.ne'⟩
  let : CharP E 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardE)
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcardF)
  exact marked_linear_quadrangle_catalogue Q mark h split hm μ₀ μ₁

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.LinearQuadrangle

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.LinearQuadrangle
variable {G E F : Type*} [Group G]
  [Field E] [Finite E] [CharP E 2] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 4)
  (μ₀ : ((L 0) ⧸ pCore 2 (L 0)) ≃* PSL(2,E))
  (μ₁ : ((L 1) ⧸ pCore 2 (L 1)) ≃* PSL(2,F))
  (hcard : Nat.card E = Nat.card F)

include h split hm μ₀ μ₁ hcard in
/-- The original equal-linear C₂ comparison evaluates at the literal quotient
map on both endpoints and every element of their whole intersection. -/
theorem original_equal_linear_symplectic_comparison :
    ∃ e : ((generated L S) ⧸ Q.D) ≃* Sp E,
      (∃ c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (C2RankThree.flagAmalgam E),
        (∀ a : parabolic L S 0, (c.left a : Sp E) = e (Q.q ⟨a,parabolic_le_generated 0 a.property⟩)) ∧
        (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
          (c.middle a : Sp E) = e (Q.q ⟨a,parabolic_le_generated 0 a.property.1⟩)) ∧
        (∀ a : parabolic L S 1, (c.right a : Sp E) = e (Q.q ⟨a,parabolic_le_generated 1 a.property⟩))) ∨
      (∃ c : RankTwoAmalgam.Iso
        (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
          (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
        (C2RankThree.flagAmalgam E).reverse,
        (∀ a : parabolic L S 0, (c.left a : Sp E) = e (Q.q ⟨a,parabolic_le_generated 0 a.property⟩)) ∧
        (∀ a : (parabolic L S 0 ⊓ parabolic L S 1 : Subgroup G),
          (c.middle a : Sp E) = e (Q.q ⟨a,parabolic_le_generated 0 a.property.1⟩)) ∧
        (∀ a : parabolic L S 1, (c.right a : Sp E) = e (Q.q ⟨a,parabolic_le_generated 1 a.property⟩))) := by
  simpa only [originalMarkedIso_left_apply,originalMarkedIso_middle_apply,originalMarkedIso_right_apply]
    using marked_equal_linear_symplectic_comparison Q (originalMarkedIso Q) h split hm μ₀ μ₁ hcard

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.LinearQuadrangle
