module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryScalarSections
public import Theory.GroupAction.InvariantSectionImage
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.UnitaryPropagation
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.UnitaryDerived
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.SmallSpecialUnitary
import all Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.OctagonStructure.SmallProjectiveUnitary

/-!
# Persistence of scalar-fixed unitary sections

The scalar-fixed part of each actual lower-central term has its original
rank-one conjugation action and full Cartan normalization. If its preceding
term has non-two action and the relative quotient is smaller than 2^(8b),
the next term still has non-two action: otherwise the subgroup-and-quotient
automorphism argument would make the preceding image a two-group. The
projective bound excludes such a small moving quotient.

Relative normality, the literal lower-central filtration, both scalar
conventions and degree one are retained. The original-source companion
supplies the numerical budget and excludes containment in the nine-b group.
This proves the action form of the persistence step in Fong--Seitz I (6F),
printed p.47; no irreducibility of an entire Frattini quotient is assumed.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)

private theorem numerator_two_of_section_two {j : Fin 2}
    (d : RootSection Q split j) (hd : d.denominator=⊥)
    (ht : IsPGroup 2 d.action.range) : IsPGroup 2 d.numeratorAction.range := by
  rintro ⟨_,a,rfl⟩
  obtain ⟨n,hn⟩ := ht (d.action.rangeRestrict a)
  refine ⟨n,Subtype.ext ?_⟩
  change (d.numeratorAction a)^(2^n)=1
  rw [←map_pow]
  apply MulEquiv.ext
  intro x
  have he : d.action (a^(2^n))=1 := by
    rw [map_pow]
    exact congrArg Subtype.val hn
  have hh := congrArg (fun f : MulAut d.Carrier => f (QuotientGroup.mk x)) he
  rw [d.action_mk] at hh
  have hx := QuotientGroup.eq_iff_div_mem.mp hh
  rw [hd,mem_bot] at hx
  exact div_eq_one.mp hx

private theorem section_two_of_numerator_two {j : Fin 2}
    (d : RootSection Q split j) (ht : IsPGroup 2 d.numeratorAction.range) :
    IsPGroup 2 d.action.range := by
  rintro ⟨_,a,rfl⟩
  obtain ⟨n,hn⟩ := ht (d.numeratorAction.rangeRestrict a)
  refine ⟨n,Subtype.ext ?_⟩
  change (d.action a)^(2^n)=1
  rw [←map_pow]
  have he : d.numeratorAction (a^(2^n))=1 := by
    rw [map_pow]
    exact congrArg Subtype.val hn
  ext z
  induction z using QuotientGroup.induction_on with
  | H x => rw [d.action_mk,he]; rfl

/-- A scalar-fixed action with non-two image survives in a relatively normal
subgroup when the quotient has order below the projective degree bound. -/
theorem unitary_scalar_section_persistence
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hodd : Odd b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (j : Fin 2) (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (μ : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hroot : Nat.card (simpleRoot Q split j)=(2^b)^3)
    (hsmall : b=1 → Nonempty (rankOne Q split j ≃* J.specialSubgroup) ∨
      Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (d c : RootSection Q split j) (hcden : c.denominator=⊥)
    (_hcd : c.numerator ≤ d.numerator)
    [(c.numerator.subgroupOf d.numerator).Normal]
    (hd : d.numerator ≤ centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D)))
    (hnot : ¬ IsPGroup 2 d.action.range)
    (hsize : Nat.card (d.numerator ⧸ c.numerator.subgroupOf d.numerator) < 2^(8*b)) :
    ¬ IsPGroup 2 c.action.range := by
  let qd : RootSection Q split j := {
    numerator := d.numerator
    le_radical := d.le_radical
    normalized := d.normalized
    denominator := c.numerator.subgroupOf d.numerator
    invariant r := by
      apply le_antisymm
      · rintro x ⟨y,hy,rfl⟩
        exact (mem_normalizer_iff.mp (c.normalized r.property) _).mp hy
      · intro x hx
        let a := d.numeratorAction r
        refine ⟨a.symm x,?_,a.apply_symm_apply x⟩
        exact (mem_normalizer_iff.mp (c.normalized (inv_mem r.property)) _).mp hx }
  have hqtwo : IsPGroup 2 qd.action.range := by
    by_contra hn
    have hl := unitary_scalar_section_card_bound Q split J hb hodd hcard hconj j hKj
      μ σ hσ hroot hsmall qd hd hn
    have hq : Nat.card qd.EffectiveCarrier ≤ Nat.card qd.Carrier :=
      index_antitone (show qd.denominator ≤ qd.effectiveDenominator from by
        rw [qd.effectiveDenominator_eq]; exact le_sup_right)
    exact (not_lt_of_ge (hl.trans hq)) hsize
  intro hctwo
  have hcntwo := numerator_two_of_section_two Q split c hcden hctwo
  have ht := (QuotientGroup.mk' qd.denominator).isPGroup_range_of_kernel_and_quotient
    (by rw [QuotientGroup.ker_mk']; exact d.isTwo.to_subgroup _)
    d.numeratorAction qd.action c.numeratorAction
    (fun r w => rfl) (fun r hr w => ?_) hqtwo hcntwo
  · exact hnot (section_two_of_numerator_two Q split d ht)
  · apply Subtype.ext
    have hw : (w.val : X ⧸ Q.D) ∈ c.numerator :=
      (QuotientGroup.eq_one_iff (N:=qd.denominator) w.val).mp w.property
    exact congrArg (fun a : MulAut c.numerator => (a ⟨w.val,hw⟩ : X ⧸ Q.D)) hr

/-- Crossed-root movement supplies the non-two action needed to start the
section recurrence, including the solvable degree-one actors. -/
theorem unitary_scalar_crossed_action_not_two
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {b : ℕ} (hb : 0 < b) (hcard : Nat.card F=(2^b)^2)
    (hconj : ∀ x,J.conj x=x^(2^b))
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i ≠ j)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j)
    (σ : J.specialSubgroup →* rankOne Q split j) (hσ : Function.Surjective σ)
    (hroot : Nat.card (simpleRoot Q split j)=(2^b)^3)
    (hsmall : b=1 → Nonempty (rankOne Q split j ≃* J.specialSubgroup) ∨
      Nonempty (rankOne Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (d : RootSection Q split j) (hden : d.denominator=⊥)
    (a : rootAt Q split j (Q.simple i)) (ha : a ≠ 1)
    (hax : (a : X ⧸ Q.D) ∈ d.numerator) :
    ¬ IsPGroup 2 d.action.range := by
  by_cases he : b=1
  · have hc : Nat.card F=4 := by simpa only [he,pow_one,Nat.reducePow] using hcard
    have hj : ∀ x,J.conj x=x^2 := by simpa only [he,pow_one] using hconj
    have hr : Nat.card (simpleRoot Q split j)=8 := by
      simpa only [he,pow_one,Nat.reducePow] using hroot
    rcases hsmall he with ⟨⟨ν⟩⟩ | ⟨⟨ν⟩⟩
    · obtain ⟨hT,hcenter⟩ := small_special_cartan Q split j J hc hj hKj ν hr
      exact small_special_section_not_two Q split j hT.le hcenter hr hm i hij
        (UnitarySource.actorReflection Q split j) d hden a ha hax
    · have hR : Nat.card (rankOne Q split j)=72 := (Nat.card_congr ν.toEquiv).trans
        (HermitianForm.FixedFieldTwo.card_projective J hc hj)
      exact nine_section_action_not_two Q split j hR hr hm i hij
        (UnitarySource.actorReflection Q split j) d hden a ha hax
  · let : Group.IsPerfect J.specialSubgroup :=
      Representation.SU3.BinaryDegree.isPerfect_specialSubgroup J (by omega) hcard hconj
    let : Group.IsPerfect (rankOne Q split j) := Group.IsPerfect.ofSurjective hσ
    let : Group.IsPerfect d.action.range := Group.IsPerfect.range d.action
    have hmove := cross_root_moves_section Q split hm i j hij
      (UnitarySource.actorReflection Q split j) d hden a a.property hax
        (fun h => ha (Subtype.ext h))
    intro ht
    have htriv : d.action=1 := by
      apply MonoidHom.ext
      intro r
      have hs : Subsingleton d.action.range := by
        by_contra! hn
        exact Group.IsPerfect.not_isNilpotent d.action.range ht.isNilpotent
      exact congrArg Subtype.val (Subsingleton.elim (d.action.rangeRestrict r) 1)
    exact hmove htriv

/-- The full source parabolic normalizes every actual lower-central term. -/
theorem unitary_radical_lower_normalized (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) (n : ℕ) :
    Q.tits.standardParabolic {Q.simple j} ≤ normalizer
      ((simpleRemainder Q split j).lowerCentralSeries n : Set (X ⧸ Q.D)) := by
  intro r hr
  rw [mem_normalizer_iff_map_conj_eq,map_lowerCentralSeries,
    mem_normalizer_iff_map_conj_eq.mp (remainder_parabolic_normalizes Q split j hKj hr)]

/-- The scalar-fixed part of each lower-central term, starting at the derived radical. -/
@[expose] def unitaryScalarLowerSection (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) (n : ℕ) : RootSection Q split j where
  numerator := (simpleRemainder Q split j).lowerCentralSeries (n+1) ⊓
    centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D))
  le_radical := inf_le_left.trans ((simpleRemainder Q split j).lowerCentralSeries_le_self _)
  normalized := (le_inf ((rankOne_le_parabolic Q split j).trans
    (unitary_radical_lower_normalized Q split j hKj _))
      ((le_centralizer_iff.mp (scalar_centralizes_rankOne Q split j)).trans
        (centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D))).le_normalizer)).trans
          inf_normalizer_le_normalizer_inf
  denominator := ⊥
  invariant _ := map_bot _

/-- The whole Cartan preserves the literal scalar-fixed lower-central terms. -/
theorem unitary_scalar_lower_cartan_normalized (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) (n : ℕ) :
    Q.tits.B ⊓ Q.tits.N ≤ normalizer
      ((unitaryScalarLowerSection Q split j hKj n).numerator : Set (X ⧸ Q.D)) := by
  have hH : Q.tits.B ⊓ Q.tits.N ≤
      normalizer (rankOneScalar Q split j : Set (X ⧸ Q.D)) :=
    (rankOne_torus_normalizes Q split j).trans
      (normalizer_le_normalizer_characteristic_image _ (center _))
  exact (le_inf (inf_le_left.trans ((Q.tits.B_le_standardParabolic _).trans
    (unitary_radical_lower_normalized Q split j hKj _)))
      (hH.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf

/-- These scalar-fixed terms form a descending series. -/
theorem unitary_scalar_lower_le (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) (n : ℕ) :
    (unitaryScalarLowerSection Q split j hKj (n+1)).numerator ≤
      (unitaryScalarLowerSection Q split j hKj n).numerator :=
  inf_le_inf_right _ ((simpleRemainder Q split j).lowerCentralSeries_antitone (by omega))

/-- Normality is relative to the preceding scalar-fixed term. -/
instance unitary_scalar_lower_normal (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) (n : ℕ) :
    ((unitaryScalarLowerSection Q split j hKj (n+1)).numerator.subgroupOf
      (unitaryScalarLowerSection Q split j hKj n).numerator).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  exact (le_inf
    ((unitaryScalarLowerSection Q split j hKj n).le_radical.trans
      ((simpleRemainder Q split j).self_le_normalizer_lowerCentralSeries _))
    (inf_le_right.trans (centralizer (rankOneScalar Q split j : Set (X ⧸ Q.D))).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

/-- The scalar-fixed quotient has no more cosets than the full derived quotient. -/
theorem unitary_scalar_lower_quotient_le (j : Fin 2)
    (hKj : simpleRemainder Q split j ≤ localKernel Q j) (n : ℕ) :
    Nat.card ((unitaryScalarLowerSection Q split j hKj n).numerator ⧸
      (unitaryScalarLowerSection Q split j hKj (n+1)).numerator.subgroupOf
        (unitaryScalarLowerSection Q split j hKj n).numerator) ≤
    ((simpleRemainder Q split j).lowerCentralSeries (n+2)).relIndex
      ⁅simpleRemainder Q split j,simpleRemainder Q split j⁆ := by
  let V := simpleRemainder Q split j
  let d := unitaryScalarLowerSection Q split j hKj n
  have he : (unitaryScalarLowerSection Q split j hKj (n+1)).numerator.subgroupOf d.numerator =
      (V.lowerCentralSeries (n+2)).subgroupOf d.numerator := by
    ext x
    exact ⟨fun h => h.1, fun h => ⟨h,x.property.2⟩⟩
  change ((unitaryScalarLowerSection Q split j hKj (n+1)).numerator.subgroupOf d.numerator).index ≤ _
  rw [he]
  exact relIndex_le_of_le_right
    (inf_le_left.trans (V.lowerCentralSeries_antitone (show 1 ≤ n+1 by omega)))
    (Nat.card_pos (α:=(⁅V,V⁆ : Subgroup (X ⧸ Q.D)) ⧸ (V.lowerCentralSeries (n+2)).subgroupOf ⁅V,V⁆)).ne'

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.OctagonStructure
