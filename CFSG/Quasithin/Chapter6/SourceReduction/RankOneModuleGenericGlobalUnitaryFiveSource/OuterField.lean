module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.FieldTransfer
public import Theory.FieldTheory.BinaryTorusTwoPower

/-!
# The actual quotient coefficient of an original outer U₅(4) involution

The proved field-action kernel is exactly S. Hence an original involution
of T outside S induces a nonidentity field involution on L/O₂(L). Over the
sixteen-element field this coefficient is exactly x ↦ x⁴. Choose coordinates
on that original quotient and apply the proved PSL₂ semilinear descent to
identify its full quotient action with an inner conjugate of this field map.

Source: the local restriction in F.4.29(2), printed p.289 of refs/quasithin.pdf.
This constrains the selected actor but does not lift its quotient formula to
a unitary matrix action on the full PSU₅ carrier. That lifting step remains
necessary before the conditional graph/flag descent can be applied to it.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
variable (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (U : Model 4)
    (hc : Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) U.amalgam.reverse))
include d h hH hp hc


/-- Every original involution outside S has exactly the fourth-power field
coefficient on the actual PSL₂(16) quotient. -/
theorem Preparation.unitaryFive_outer_involution_field_coefficient
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F=16)
    (e : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F)
    (t : T) (ht : orderOf t=2) (htS : t.val∉sourceS L H) :
    ∀ x:F, unitaryFiveSylowFieldAction h.sylow_normalizes e t x=x^4 := by
  let phi := unitaryFiveSylowFieldAction h.sylow_normalizes e
  have hne : phi t≠1 := by
    intro he
    have hm : t∈phi.ker := he
    change t∈(unitaryFiveSylowFieldAction h.sylow_normalizes e).ker at hm
    rw [d.unitaryFive_sylow_field_kernel h hH hp U hc e] at hm
    exact htS hm
  have hs : (phi t)^2=1 := by
    have ht2 : t^2=1 := by simpa only [ht] using pow_orderOf_eq_one t
    rw [←map_pow,ht2,map_one]
  obtain ⟨m,_,hm,hformula⟩ := FiniteField.BinaryTorusTwoPower.involution_eq_half_frobenius
    (show Nat.card F=2^4 from hF) (phi t) hs hne
  have hm2 : m=2 := by omega
  intro x
  have hh := hformula x
  rw [hm2] at hh
  norm_num only at hh
  exact hh

/-- Choose actual coordinates on the original left quotient. Every original
outer involution acts there as an inner conjugate of the fourth-power field
involution. This is a quotient statement, not a representation on PSU₅. -/
theorem Preparation.unitaryFive_outer_involution_quotient_coordinates :
    ∃ e : (L ⧸ pCore 2 L) ≃* Theory.PSL2.BinaryGroup 4,
      ∀ (t : T), orderOf t=2 → t.val∉sourceS L H →
        (∀ x : Theory.PSL2.BinaryField 4,
          unitaryFiveSylowFieldAction h.sylow_normalizes e t x=x^4) ∧
        ∃ c : Theory.PSL2.BinaryGroup 4,
          MulAut.congr (MulAut.conj c) (Theory.PSL2.fieldAut (Theory.PSL2.binaryHalfFrobenius 4)) =
            MulAut.congr e (pCoreJoinAction 2 h.sylow_normalizes (inclusion le_sup_right t)) := by
  have hn4 : n=4 := by
    rcases hc with ho | hr
    · exact (d.not_unitaryFive_unreversed h hH.1.1.2 hp U ho).elim
    exact (d.unitaryFive_local_structure h hH.1.1.2 hp U hr.some).1
  obtain ⟨F,_,_,hF,⟨e₀⟩⟩ := h.linear
  let := Fintype.ofFinite F
  let : Fintype (Theory.PSL2.BinaryField 4) := Fintype.ofFinite _
  let b : F ≃+* Theory.PSL2.BinaryField 4 := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hF,hn4,
      GaloisField.card 2 4 (by decide)])
  let e := e₀.trans (Theory.PSL2.OuterSolvable.projectiveRingEquiv b)
  refine ⟨e,?_⟩
  intro t ht htS
  have hcoeff := d.unitaryFive_outer_involution_field_coefficient h hH hp U hc
    (GaloisField.card 2 4 (by decide)) e t ht htS
  refine ⟨hcoeff,?_⟩
  let a := MulAut.congr e (pCoreJoinAction 2 h.sylow_normalizes (inclusion le_sup_right t))
  have ha : a^2=1 := by
    change ((MulAut.congr e).toMonoidHom.comp
      ((pCoreJoinAction 2 h.sylow_normalizes).comp (inclusion le_sup_right)) t)^2=1
    have ht2 : t^2=1 := by simpa only [ht] using pow_orderOf_eq_one t
    rw [←map_pow,ht2,map_one]
  have ho : a∉Theory.PSL2.inner (Theory.PSL2.BinaryField 4) := by
    intro ha
    have he : unitaryFiveSylowFieldAction h.sylow_normalizes e t=1 := by
      change a∈(Theory.PSL2.fieldProjection (Theory.PSL2.BinaryField 4)).ker
      rwa [Theory.PSL2.fieldProjection_ker]
    have hm : t∈(unitaryFiveSylowFieldAction h.sylow_normalizes e).ker := he
    rw [d.unitaryFive_sylow_field_kernel h hH hp U hc e] at hm
    exact htS hm
  exact (Theory.PSL2.outer_involution_halfFrobenius (by decide : 2≤4) a ha ho).2.2.2

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
