module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompsonPlanes
public import Theory.Representation.GoldschmidtONan.Basic

/-!
# Full preimages of normal Thompson plane factors

For a normal split binary-plane subgroup of the original Thompson image,
Sylow normal generation prevents the original Sylow Thompson subgroup from
fixing its moved plane. The two-residual normalizing that Sylow Thompson
subgroup therefore fixes the plane. Splitting then makes the plane actor
centralize the residual commutator on the whole reduced module.

The original paired-plane supplement puts the actor's full inverse image
in M. The symmetric-three case supplies splitting by the binary-plane
theorem, and the odd-order case by averaging. All normality here is inside
the full action quotient; permuted factors require a further argument.
The actual chosen-module application is
NonFFSourceDoubledBinaryThompsonNormalPlanes.
Source: Aschbacher–Smith, proof of 7.7.3, printed p.707,
refs/quasithin.pdf. The remaining mixed and component branches and final
assembly belong to qt-d-1222-nonff-doubled.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompsonNormalPlanes
open ChapterB.QuasisimpleSource ChapterB.InternalThompsonAction DoubledBinaryThompson
open DoubledBinaryThompsonPlanes

private theorem coinvariants_moved {H X : Type*} [Group H]
    [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (A : Subgroup H) :
    Coinvariants.ker (ρ.comp A.subtype) = moved ρ A := by
  apply congrArg (Submodule.span (ZMod 2))
  ext v
  constructor
  · rintro ⟨⟨g,w⟩,rfl⟩
    exact ⟨g.val,g.property,w,Submodule.mem_top,rfl⟩
  · rintro ⟨g,hg,w,_,rfl⟩
    exact ⟨(⟨g,hg⟩,w),rfl⟩

/-- A normal split-plane factor of the actual Thompson image has full
inverse image centralizing the original residual commutator. -/
theorem normal_splitPlane_preimage_centralizes_commutator
    {H : Type*} [Group H] [Finite H]
    (Y : Subgroup H) [Y.Normal] [IsElementaryAbelian 2 Y]
    (S : Sylow 2 H) (R : Subgroup H) (hR : IsPPerfect 2 R)
    (hRN : R ≤ normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H))
    (A : Subgroup (ActionQuotient Y)) [A.Normal]
    (hAJ : A ≤ thompsonImage Y)
    (hd : Module.finrank (ZMod 2) (moved (action Y) A) = 2)
    (hs : moved (action Y) A ⊔ fixedSpace (action Y) A = ⊤) :
    A.comap (actionMk Y) ≤ centralizer ((⁅Y,R⁆ : Subgroup H) : Set H) := by
  let q := actionMk Y
  let ρ := NormalElementaryQuotient.originalAction Y
  let F := A.comap q
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hρ : ρ = (action Y).comp q := by
    apply MonoidHom.ext
    intro a
    apply LinearMap.ext
    intro w
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (NormalElementaryQuotient.originalAction_apply Y a w).trans
      (action_apply Y a w).symm
  have hm : moved ρ F = moved (action Y) A := by
    rw [hρ]
    unfold moved
    rw [subspaceCommutator_comp_map,map_comap_eq_self_of_surjective hq]
  have hf : fixedSpace ρ F = fixedSpace (action Y) A := by
    rw [hρ,fixedSpace_comp_map,map_comap_eq_self_of_surjective hq]
  have hsplit : moved ρ F ⊔ fixedSpace ρ F = ⊤ := by
    rw [hm,hf]
    exact hs
  have hFJ : F ≤ elementaryAbelianMaxJ (⊤ : Subgroup H) ⊔ ρ.ker := by
    have hh := comap_mono (f := q) hAJ
    change F ≤ ((elementaryAbelianMaxJ (⊤ : Subgroup H)).map q).comap q at hh
    rw [comap_map_eq] at hh
    simpa only [q,actionMk,QuotientGroup.ker_mk',ρ,
      NormalElementaryQuotient.originalAction_kernel] using hh
  have hh := normal_plane_centralizes_residual ρ S R F hR hRN hFJ
    (hm ▸ hd) hsplit
  intro a ha
  exact (NormalElementaryQuotient.original_moved_centralizer Y R a).mpr
    (fun w hw => hh hw ⟨a,ha⟩)

/-- Containment concerns the full inverse images of the normal plane factors,
with the literal centralizer quotient of the specified reduced subgroup. -/
@[expose] def NormalPlaneFactorsContained
    {H : Type*} [Group H] (Y : Subgroup H) (hY : Theory.GroupTheory.IsPReduced 2 Y)
    (M : Subgroup H) : Prop :=
  let := hY.normal
  let := hY.elementary
  ∀ (A : Subgroup (ActionQuotient Y)), A.Normal → A ≤ thompsonImage Y →
    Module.finrank (ZMod 2) (moved (action Y) A) = 2 →
    moved (action Y) A ⊔ fixedSpace (action Y) A = ⊤ →
    A.comap (actionMk Y) ≤ M

/-- The original residual supplement puts every normal split binary
plane factor's full preimage in M. No ambient centralizer containment is assumed. -/
theorem normal_plane_preimages_contained
    {G : Type*} [Group G] [Finite G]
    (H Y W U R M : Subgroup G) (S : Sylow 2 H)
    (hYH : Y ≤ H) (hWY : W ≤ Y) (hRH : R ≤ H)
    (hY : Theory.GroupTheory.IsPReduced 2 (Y.subgroupOf H))
    (hR : IsPPerfect 2 R)
    (hRN : R ≤ normalizer
      (elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) : Set G))
    (hsupp : U ⊔ ⁅W,R⁆ = W) (hHC : H ≤ centralizer (U : Set G))
    (hWM : centralizer (W : Set G) ≤ M) :
    NormalPlaneFactorsContained (Y.subgroupOf H) hY (M.subgroupOf H) := by
  let := hY.normal
  let := hY.elementary
  intro A hA hAJ hd hs
  let := hA
  have hR' : IsPPerfect 2 (R.subgroupOf H) := hR.of_surjective
    (subgroupOfEquivOfLe hRH).symm.toMonoidHom (subgroupOfEquivOfLe hRH).symm.surjective
  have heP : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
      elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) :=
    (elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective _).symm
  have hRN' : R.subgroupOf H ≤
      normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H) := by
    have hh := subgroupOf_mono H hRN
    rw [← heP,subgroupOf_normalizer_eq (map_subtype_le _)] at hh
    simpa only [subgroupOf,comap_map_eq_self_of_injective H.subtype_injective] using hh
  have hc := normal_splitPlane_preimage_centralizes_commutator
    (Y.subgroupOf H) S (R.subgroupOf H) hR' hRN' A hAJ hd hs
  let F := A.comap (actionMk (Y.subgroupOf H))
  have hh := congrArg (Subgroup.map H.subtype)
    (commutator_eq_bot_iff_le_centralizer.mpr hc)
  rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hYH,
    map_subgroupOf_eq_of_le hRH,Subgroup.map_bot] at hh
  have hFW : F.map H.subtype ≤ centralizer (W : Set G) := by
    apply le_centralizer_iff.mpr
    rw [← hsupp]
    apply sup_le
    · exact le_centralizer_iff.mp ((map_subtype_le F).trans hHC)
    · exact (commutator_mono hWY le_rfl).trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh))
  exact map_le_iff_le_comap.mp (hFW.trans hWM)

/-- The symmetric-three plane clause needs no additional splitting premise. -/
theorem NormalPlaneFactorsContained.symmetricThree
    {H : Type*} [Group H] [Finite H]
    (Y : Subgroup H) (hY : Theory.GroupTheory.IsPReduced 2 Y) (M : Subgroup H)
    (hc : NormalPlaneFactorsContained Y hY M) :
    let := hY.normal
    let := hY.elementary
    ∀ (A : Subgroup (ActionQuotient Y)), A.Normal → A ≤ thompsonImage Y →
      Nonempty (A ≃* Equiv.Perm (Fin 3)) →
      Module.finrank (ZMod 2) (moved (action Y) A) = 2 →
      A.comap (actionMk Y) ≤ M := by
  let := hY.normal
  let := hY.elementary
  dsimp only
  intro A hn hAJ ⟨e⟩ hd
  have hs := BinaryPlaneNormalizer.symmetric_three_split ((action Y).comp A.subtype)
    ((action_faithful Y).comp A.subtype_injective) e
    (by rwa [coinvariants_moved])
  rw [coinvariants_moved] at hs
  exact hc A hn hAJ hd hs.sup_eq_top

/-- Odd-order averaging discharges the split-plane premise for the original
normal cubic factors, without identifying their full preimages as odd groups. -/
theorem NormalPlaneFactorsContained.odd
    {H : Type*} [Group H] [Finite H]
    (Y : Subgroup H) (hY : Theory.GroupTheory.IsPReduced 2 Y) (M : Subgroup H)
    (hc : NormalPlaneFactorsContained Y hY M) :
    let := hY.normal
    let := hY.elementary
    ∀ (A : Subgroup (ActionQuotient Y)), A.Normal → A ≤ thompsonImage Y →
      Odd (Nat.card A) →
      Module.finrank (ZMod 2) (moved (action Y) A) = 2 →
      A.comap (actionMk Y) ≤ M := by
  let := hY.normal
  let := hY.elementary
  dsimp only
  intro A hn hAJ ho hd
  have he : RegularCyclicNormalClosure.displacementSpan (action Y) A ⊤ =
      moved (action Y) A := by
    unfold moved subspaceCommutator RegularCyclicNormalClosure.displacementSpan
    congr 1
    ext v
    simp only [eq_comm]
  have hs := GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := action Y) ho
  rw [he] at hs
  exact hc A hn hAJ hd hs.symm.sup_eq_top

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompsonNormalPlanes
