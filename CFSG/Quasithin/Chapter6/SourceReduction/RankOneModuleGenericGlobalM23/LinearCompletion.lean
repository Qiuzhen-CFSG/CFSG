module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.CubicNormalizerConjugacy
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.LinearTransport
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.LinearInvolutions
public import Theory.GroupTheory.Recognition.QuasithinM23.CubicInvolutions

/-!
# The actual generated PSL₃(4) in the nonmaximal linear branch

Construct the native four-field completion of the original two parabolics,
retaining the full compatible overlap. Its common cubic lies in the original
left normalizer, so the proved source 5.2.15 identifies its full ambient
normalizer as ΓL₂(4). The cubic adjustment gives endpoint involutions with
product order at most three, without changing either endpoint or the whole
Borel. The coset-geometric bound makes this order exactly three. The existing
F.4.26 specialization then gives the actual PSL₃(4) equivalence, preserving
both original parabolics and their entire intersection in either orientation.

This proves original source 5.2.16(1): the domain is literally G₁ ∨ G₂,
which `ChapterF.Source.parabolics_generate` identifies with the source G₀.
The extension by T in 5.2.16(2) and ambient M₂₃ recognition are further
obligations. No generation, involution, or recognition premise is added here.

Source: Aschbacher–Smith 5.2.15–16, printed pp.654–655 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.LinearThreeFour
open Matrix.PSL3.LinearThree
open Representation.SL2FourNatural.SemilinearNormalizer

/-- Source 5.2.16(1): recognize the literal generated completion, preserving
both endpoint ranges and their full Borel in either amalgam orientation. -/
theorem Preparation.linear_nonmaximal_generated_equiv
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (E : Type) [Field E] [Finite E] [CharP E 2]
    {m : ℕ} (hm : 0 < m) (hE : Nat.card E = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam E).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
    let Q := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
    ∃ e : (P ⊔ Q : Subgroup G) ≃* Matrix.PSL3Four.PSL,
      (((P.subgroupOf (P ⊔ Q)).map e.toMonoidHom = pointParabolic Matrix.PSL3Four.F ∧
        (Q.subgroupOf (P ⊔ Q)).map e.toMonoidHom = lineParabolic Matrix.PSL3Four.F) ∨
       ((Q.subgroupOf (P ⊔ Q)).map e.toMonoidHom = pointParabolic Matrix.PSL3Four.F ∧
        (P.subgroupOf (P ⊔ Q)).map e.toMonoidHom = lineParabolic Matrix.PSL3Four.F)) ∧
      ((P ⊓ Q).subgroupOf (P ⊔ Q)).map e.toMonoidHom = borel Matrix.PSL3Four.F := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let Q := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  let X := P ⊔ Q
  have hfour := (d.linear_nonmaximal_core_geometry h hH hp E hm hE he hnonmax).2.2.1
  obtain ⟨c,hc,hmid⟩ := M23Completion.native_completion P Q E hfour he
  obtain ⟨b,s,t,hb,hb3,hs,ht,hsout,htout,hs2,ht2,his,hit⟩ := M23Completion.completion_seeds c
  have hPM : P ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show L ≤ P from le_sup_left.trans le_sup_left)).mp
      ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic 0)
  have hbM : (b:G) ∈ normalizer (L : Set G) := by
    have hh : b ∈ (P ⊓ Q).subgroupOf X := hmid ▸ hb
    exact hPM hh.1
  obtain ⟨eN⟩ := d.linear_nonmaximal_cubic_normalizer_of_mem_left
    h hH hp E hm hE he hnonmax (b:G) ((Subgroup.orderOf_coe b).trans hb3) hbM
  obtain ⟨a,ha,has,hast⟩ := QuasithinM23.cubic_adjustment_of_normalizer_equiv
    (b:G) (s:G) (t:G) ((Subgroup.orderOf_coe b).trans hb3) eN
    ((Subgroup.orderOf_coe s).trans hs2) ((Subgroup.orderOf_coe t).trans ht2)
    (congrArg Subtype.val his) (congrArg Subtype.val hit)
  obtain ⟨k,rfl⟩ := ha
  have hak : b^k ∈ c.middle.range := c.middle.range.zpow_mem hb k
  have hs' : b^k*s ∈ c.left.range := c.left.range.mul_mem (c.middle_le_left hak) hs
  have hsout' : b^k*s ∉ c.middle.range := by
    intro hh
    apply hsout
    have hh' := c.middle.range.mul_mem (c.middle.range.inv_mem hak) hh
    simpa only [inv_mul_cancel_left] using hh'
  have has' : orderOf (b^k*s)=2 := by
    have hh := Subgroup.orderOf_coe (b^k*s)
    exact hh.symm.trans has
  have hast' : orderOf ((b^k*s)*t) ≤ 3 := by
    have hh := Subgroup.orderOf_coe ((b^k*s)*t)
    exact hh.symm.le.trans hast
  have hexact := M23Completion.endpoint_product_order c (b^k*s) t hs' ht hsout' htout has' ht2 hast'
  obtain ⟨e,hel,her⟩ := c.exists_parabolic_preserving_equiv_of_involutions
    (b^k*s) t hs' ht hsout' htout has' ht2 hexact
  refine ⟨e,?_,?_⟩
  · rcases hc with ⟨hleft,hright⟩ | ⟨hleft,hright⟩
    · exact Or.inl ⟨hleft ▸ hel,hright ▸ her⟩
    · exact Or.inr ⟨hleft ▸ hel,hright ▸ her⟩
  · rw [←hmid,←c.overlap,Subgroup.map_inf _ _ _ e.injective,hel,her]
    exact ChapterF.GreenBook.LieModels.LinearThree.parabolic_intersection Matrix.PSL3Four.F
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
