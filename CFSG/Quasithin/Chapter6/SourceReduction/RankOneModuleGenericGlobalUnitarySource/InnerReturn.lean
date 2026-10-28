module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ResidualReturn
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedCentralizers
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.MarkedAction

/-!
# Ambient long-root returns with inner endpoint image

Retain any one full-normalizer marking of the prepared unitary-four row.
An element of the left normalizer has inner image precisely when it lies
in the reduced native parabolic. Every two-subgroup of that parabolic is
in its solvable residual, the original L. The proved residual-return theorem
then puts every ambient long-root return with inner image in O₂(L).

If the same extension has odd degree over its inner group, its two-subgroups
are inner. Thus every two-subgroup of N_G(L) lies in L, including the original
ambient Sylow. The following fixed-coset module uses this consequence to
supply the return-fusion premise in the first part of F.4.42. Odd outer degree
itself remains the F.4.37–38 transfer obligation; it is not assumed silently.

Both orientations, degree-two input rows and q=4 remain included.
Source: Aschbacher–Smith F.4.35–38,42, printed pp.292–295.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour ChapterF.SourceCompletion.UnitaryNonbinary
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

private theorem reduced_two_subgroup
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (S : Subgroup G) (hS : IsPGroup 2 S)
    (hSP : S ≤ ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0) :
    S ≤ L := by
  obtain ⟨hmgt,_,he⟩ := d.unitary_reduced_native_comparison h hH.1.1.2 hp m hm hc
  have hr := d.reduced_parabolic_residuals h hH.1.1.2 hp
    (hc.elim (.unitary m hm) (.unitaryExtension m hm)) 0
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · exact UnitarySource.two_subgroup_transport hr hS hSP e.left
      (UnitarySource.point_two_subgroup m hm hmgt)
  · exact UnitarySource.two_subgroup_transport hr hS hSP e.left
      (UnitarySource.plane_two_subgroup m hm)

omit [Finite G] in
private theorem endpoint_inner_preimage
    (m : ℕ) (hm : 1 ≤ m)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm)
    (a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L)
      (amalgam m hm).reverse)
    (F : RankTwoAmalgam.Iso (normalizerDiagram L (residual H)) r.extension.amalgam.reverse)
    (h0 : ∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val)
    (x : normalizer (L : Set G)) :
    (F.left x).val ∈ inner (ProjectiveGroup m hm) ↔
      x.val ∈ ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 := by
  constructor
  · intro hx
    have hh := r.extension.right_inner.le ⟨(F.left x).property,hx⟩
    obtain ⟨b,hb,he⟩ := hh
    let y := a.comparison.left.symm ⟨b,hb⟩
    have hy : inclusion r.left_le y = x := by
      apply F.left.injective
      apply Subtype.ext
      rw [h0]
      exact (congrArg (fun q : planeParabolic m hm => MulAut.conj q.val)
        (a.comparison.left.apply_symm_apply ⟨b,hb⟩)).trans he
    exact (congrArg Subtype.val hy) ▸ y.property
  · intro hx
    have he : x = inclusion r.left_le ⟨x.val,hx⟩ := rfl
    rw [he,h0]
    exact ⟨_,rfl⟩

/-- An ambient long-root return whose marked endpoint image is inner lies
in the original two-core, for any fixed full-normalizer realization. -/
theorem Preparation.unitary_long_inner_return
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm) :
    ∃ a : UnitarySource.MarkedMiddleAction L (residual H) ((T : Subgroup G) ⊓ L) (amalgam m hm).reverse,
    ∃ f : UnitaryNativeLift.Four.LiftReverse m hm a,
    ∃ F : RankTwoAmalgam.Iso (normalizerDiagram L (residual H)) r.extension.amalgam.reverse,
      (∀ x, (F.left (inclusion r.left_le x)).val = MulAut.conj (a.comparison.left x).val) ∧
      (∀ x, (F.right (inclusion r.right_le x)).val = MulAut.conj (a.comparison.right x).val) ∧
      (∀ z, (F.middle z).val = (f.action z).val) ∧
      ∀ z ∈ (center (residual H)).map (residual H).subtype, orderOf z = 2 →
        ∀ x : normalizer (L : Set G), IsConj z x.val →
          (F.left x).val ∈ inner (ProjectiveGroup m hm) → x.val ∈ L.pCoreIn 2 := by
  obtain ⟨a,f,F,h0,h1,hD,_,_⟩ := d.unitaryFour_marked_centralizers h hH hp m hm hc r
  refine ⟨a,f,F,h0,h1,hD,?_⟩
  intro z hz hz2 x hx hi
  have hzsq : z ^ 2 = 1 := hz2 ▸ pow_orderOf_eq_one z
  have hx2 : x.val ^ 2 = 1 := isConj_one_right.mp (hzsq ▸ hx.pow 2)
  have hxP := (endpoint_inner_preimage m hm r a F h0 x).mp hi
  have hxL : x.val ∈ L := reduced_two_subgroup d h hH hp m hm hc (zpowers x.val)
    (IsPGroup.of_card_dvd_pow (n := 1) (by
      rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hx2))
    (zpowers_le.mpr hxP) (mem_zpowers _)
  exact mem_map_of_mem L.subtype
    (d.unitary_long_residual_return h hH hp m hm hc z hz hz2 ⟨x.val,hxL⟩ hx)

private theorem two_subgroup_le_of_odd_index
    {X : Type*} [Group X] [Finite X] (N P : Subgroup X) [N.Normal]
    (hP : IsPGroup 2 P) (hodd : ¬ 2 ∣ N.index) : P ≤ N := by
  have hi : N.relIndex P = 1 := by
    obtain ⟨k,hk⟩ := hP.index (N.subgroupOf P)
    have hn : ¬ 2 ∣ 2^k := fun hd => hodd
      ((hk ▸ hd).trans (N.relIndex_dvd_index_of_normal P))
    have hk0 : k = 0 := by
      by_contra hh
      exact hn (dvd_pow_self 2 hh)
    change (N.subgroupOf P).index = 1
    rw [hk,hk0,pow_zero]
  exact (relIndex_eq_one.mp hi)

/-- Odd outer degree on the same extension puts every original left-normalizer
two-subgroup in L; in particular it identifies the original ambient Sylow
with the reduced Sylow. The parity premise is the still-required F.4.38 input. -/
theorem Preparation.unitaryFour_two_subgroups_of_odd_outer
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (r : UnitaryFourNormalizerMarking L (residual H) ((T : Subgroup G) ⊓ L) m hm)
    (hodd : ¬ 2 ∣ (inner (ProjectiveGroup m hm)).relIndex r.extension.carrier) :
    (∀ S : Subgroup G, IsPGroup 2 S → S ≤ normalizer (L : Set G) → S ≤ L) ∧
      (T : Subgroup G) ⊓ L = T := by
  obtain ⟨a,f,F,h0,h1,hD,_,_⟩ := d.unitaryFour_marked_centralizers h hH hp m hm hc r
  let I := (inner (ProjectiveGroup m hm)).subgroupOf r.extension.carrier
  let : (inner (ProjectiveGroup m hm)).Normal := by
    constructor
    rintro _ ⟨b,rfl⟩ g
    refine ⟨g b,?_⟩
    ext x
    simp [MulAut.conj_apply,map_mul]
  let : I.Normal := inferInstance
  have hall (S : Subgroup G) (hS : IsPGroup 2 S) (hSN : S ≤ normalizer (L : Set G)) : S ≤ L := by
    let j := (inclusion r.extension.right_le).comp F.left.toMonoidHom
    have hi := two_subgroup_le_of_odd_index I ((S.subgroupOf (normalizer (L : Set G))).map j)
      (hS.comap_subtype.map j) hodd
    apply reduced_two_subgroup d h hH hp m hm hc S hS
    intro x hx
    apply (endpoint_inner_preimage m hm r a F h0 ⟨x,hSN hx⟩).mp
    exact hi (mem_map_of_mem j hx)
  exact ⟨hall,inf_eq_left.mpr (hall T T.isPGroup' h.sylow_normalizes)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
