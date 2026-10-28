module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockA5LinearThreeQuotient
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSParabolicMarking
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesDegrees
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters

/-!
# The original A₅ linear-three star row has field order four

The reconstructed full quotient marks the original L-image as a point or
line parabolic residual. Its projection kernel is a two-group, so the
original L/O₂(L) is SL₂ over that same field. Comparison with the original
A₅ quotient forces the field to have order four and degree two.

No block hypothesis or whole-core MS alternatives are used. The field,
quotient map and original component are retained throughout.
Source: Aschbacher–Smith C.2.7, pp.145–147, and original 4.3.8, p.616.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open ChapterB.QuasisimpleSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

private def local_core_equiv (c : SourceConfiguration T L)
    {F : Type*} [Field F] [Finite F]
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (B : Subgroup SL(3,F)) (he : (L.subgroupOf (K c)).map (linearThreeActor e) = B) :
    (L ⧸ pCore 2 L) ≃* (B ⧸ pCore 2 B) := by
  let A := L.subgroupOf (K c)
  let a : A ≃* L := subgroupOfEquivOfLe c.le_component
  let f := linearThreeActor e
  let q : L →* B := (MulEquiv.subgroupCongr he).toMonoidHom.comp
    ((f.subgroupMap A).comp a.symm.toMonoidHom)
  have hq : Function.Surjective q := (MulEquiv.subgroupCongr he).surjective.comp
    ((f.subgroupMap_surjective A).comp a.symm.surjective)
  let i : L →* K c := A.subtype.comp a.symm.toMonoidHom
  have hi : Function.Injective i := A.subtype_injective.comp a.symm.injective
  have hk : q.ker = (pCore 2 (K c)).comap i := by
    ext l
    change q l = 1 ↔ i l ∈ pCore 2 (K c)
    rw [Subtype.ext_iff]
    change e (QuotientGroup.mk' (pCore 2 (K c)) (i l)) = 1 ↔ _
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff (i l)
  exact q.pCoreQuotientEquiv hq (by
    rw [hk]
    exact pCore_isPGroup.comap_of_injective i hi)

/-- The same original local group has the SL₂ quotient over the field
selected by its actual SL₃ star row. -/
theorem linearThree_originalLocal_sl2_of_a5_star
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (F : BinaryField)
    (e : starImage (K c) (c.I.pCoreIn 2) (K c) ≃* SL(3,F.Carrier)) :
    Nonempty ((L ⧸ pCore 2 L) ≃* SL(2,F.Carrier)) := by
  let E := linearThree_fullQuotientEquiv_of_a5 d c hf F e
  have hn := linearThree_degree_gt_one_of_a5 d c hf F e
  obtain ⟨a,ha | ha⟩ := nonblock_linearThree_local_frame d.chosen hf hn F.card_eq E
  · exact ⟨(local_core_equiv c _ _ ha).trans (pointLocalSLCoreQuotientEquiv F.Carrier)⟩
  · exact ⟨(local_core_equiv c _ _ ha).trans (lineLocalSLCoreQuotientEquiv F.Carrier)⟩

/-- Comparing the literal original A₅ quotient with its marked parabolic
quotient forces the same star field to have degree two and order four. -/
theorem linearThree_field_four_of_a5_star
    (d : Chapter13.Section05.A5Source.Context T L V V₁ V₂ V₃)
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (F : BinaryField)
    (e : starImage (K c) (c.I.pCoreIn 2) (K c) ≃* SL(3,F.Carrier)) :
    F.degree = 2 ∧ Nat.card F.Carrier = 4 := by
  obtain ⟨a⟩ := linearThree_originalLocal_sl2_of_a5_star d c hf F e
  have hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^2) :=
    ⟨GaloisField 2 2,inferInstance,inferInstance,
      by rw [GaloisField.card 2 2 (by decide)],
      ⟨d.quotient.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩
  have hcard : Nat.card F.Carrier = 2^2 := original_local_field_card hpsl a
  exact ⟨Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) (F.card_eq.symm.trans hcard),hcard⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
