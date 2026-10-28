module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompsonNormalPlanes
public import Theory.GroupTheory.ElementaryThompsonSpan
public import Theory.GroupTheory.ConjugateSpanSupplement

/-!
# Plane factors permuted by the ambient quotient

The Thompson subgroup is generated internally by conjugates of the original
Sylow Thompson subgroup. Thus a split binary plane normalized by the Thompson
subgroup must be moved by its Sylow Thompson subgroup. When the original
two-residual also normalizes the plane actor, it fixes the plane, and the
original residual supplement puts the actor's full preimage in M.

For odd plane actors with at most two ambient conjugates, two-perfectness
supplies residual normalization and averaging supplies the fixed complement.
Ambient normality of an individual factor is unnecessary. Identifying the
source odd-core factors and proving their orbit bound remain with the final
assembly in qt-d-1222-nonff-doubled, as do the quotient-component exclusions.
The actual chosen-module application is
NonFFSourceDoubledBinaryThompsonRelativePlanes.
Source: Aschbacher–Smith, proof of 7.7.3, printed p.707, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompsonRelativePlanes
open ChapterB.QuasisimpleSource DoubledBinaryThompsonPlanes

private theorem thompson_inner_span {H : Type*} [Group H] [Finite H] (S : Sylow 2 H) :
    conjugateSpanBy (elementaryAbelianMaxJ (S : Subgroup H))
      (elementaryAbelianMaxJ (⊤ : Subgroup H)) = elementaryAbelianMaxJ (⊤ : Subgroup H) := by
  let J := elementaryAbelianMaxJ (⊤ : Subgroup H)
  let P := elementaryAbelianMaxJ (S : Subgroup H)
  let : J.Characteristic := elementaryAbelianMaxJ_top_characteristic
  have ht : J ⊔ normalizer (P : Set H) = ⊤ := by
    rw [sup_comm]
    exact elementaryAbelianMaxJ_frattini S
  have he := elementaryAbelianMaxJ_eq_conjugateSpan_sylow S
  have hh := conjugateSpanBy_sup_of_normalizes_seed P J (normalizer (P : Set H))
    le_rfl le_normalizer_of_normal
  rw [ht] at hh
  exact hh.symm.trans he.symm

private theorem kernel_normalized {H X : Type*} [Group H]
    [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (D : Submodule (ZMod 2) X) (J : Subgroup H)
    (hJ : J ≤ subspaceStabilizer ρ D) :
    J ≤ normalizer (subspaceKernel ρ D ⊤ : Set H) := by
  apply le_normalizer_iff.mpr
  intro j hj k hk
  refine ⟨mem_top _,?_⟩
  intro x hx
  have hi : ρ j⁻¹ x ∈ D := (hJ (J.inv_mem hj) x).2 hx
  change ρ (j*k*j⁻¹) x = x
  rw [map_mul,map_mul]
  change ρ j (ρ k (ρ j⁻¹ x)) = x
  rw [hk.2 _ hi]
  rw [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,Module.End.one_apply]

/-- Normality in the Thompson subgroup suffices for its Sylow subgroup to
move any nontrivial split plane; ambient normality is unnecessary. -/
private theorem thompson_moves_relative_plane
    {H X : Type*} [Group H] [Finite H] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (S : Sylow 2 H) (A : Subgroup H)
    (hJA : elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ normalizer (A : Set H))
    (hAJ : A ≤ elementaryAbelianMaxJ (⊤ : Subgroup H) ⊔ ρ.ker)
    (hd : Module.finrank (ZMod 2) (moved ρ A) = 2)
    (hsplit : moved ρ A ⊔ fixedSpace ρ A = ⊤) :
    ∃ p : elementaryAbelianMaxJ (S : Subgroup H),
      ∃ x : moved ρ A, ρ p x ≠ x := by
  by_contra! hn
  let J := elementaryAbelianMaxJ (⊤ : Subgroup H)
  let P := elementaryAbelianMaxJ (S : Subgroup H)
  let K := subspaceKernel ρ (moved ρ A) ⊤
  have hPK : P ≤ K := fun p hp => ⟨mem_top _,fun x hx => hn ⟨p,hp⟩ ⟨x,hx⟩⟩
  have hJD : J ≤ subspaceStabilizer ρ (moved ρ A) :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hJA
  have hJK : J ≤ K := by
    change elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ K
    rw [← thompson_inner_span S]
    exact conjugateSpanBy_le hPK (kernel_normalized ρ _ J hJD)
  have hker : ρ.ker ≤ K := fun a ha => ⟨mem_top _,fun x _ => LinearMap.congr_fun ha x⟩
  have hAK := hAJ.trans (sup_le hJK hker)
  have htriv : ∀ a : A, ρ a = 1 := by
    intro a
    apply LinearMap.ext
    intro x
    obtain ⟨u,hu,v,hv,rfl⟩ := Submodule.mem_sup.mp
      (hsplit.ge (Submodule.mem_top (x := x)))
    change ρ a (u+v) = u+v
    have hf : ρ a v = v := hv a
    rw [map_add,(hAK a.property).2 u hu,hf]
  have hz : moved ρ A = ⊥ := by
    apply bot_unique
    apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,x,_,rfl⟩
    change ρ a x - x = 0
    rw [htriv ⟨a,ha⟩,Module.End.one_apply,sub_self]
  rw [hz,finrank_bot] at hd
  omega

theorem relative_plane_centralizes_residual
    {H X : Type*} [Group H] [Finite H] [AddCommGroup X] [Module (ZMod 2) X]
    [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (S : Sylow 2 H) (R A : Subgroup H)
    (hR : IsPPerfect 2 R)
    (hRP : R ≤ normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H))
    (hJA : elementaryAbelianMaxJ (⊤ : Subgroup H) ≤ normalizer (A : Set H))
    (hRA : R ≤ normalizer (A : Set H))
    (hAJ : A ≤ elementaryAbelianMaxJ (⊤ : Subgroup H) ⊔ ρ.ker)
    (hd : Module.finrank (ZMod 2) (moved ρ A) = 2)
    (hsplit : moved ρ A ⊔ fixedSpace ρ A = ⊤) :
    moved ρ R ≤ fixedSpace ρ A := by
  let P := elementaryAbelianMaxJ (S : Subgroup H)
  have hP : IsPGroup 2 P := S.isPGroup'.to_le (sSup_le fun _ hA => hA.1)
  exact relative_moved_fixed ρ A R P hR hP hRP hRA
    ((elementaryAbelianMaxJ_sylow_le_top S).trans hJA) hd hsplit
    (thompson_moves_relative_plane ρ S A hJA hAJ hd hsplit)

private theorem twoPerfect_le_of_index_le_two
    {G : Type*} [Group G] [Finite G] (R N : Subgroup G)
    (hR : IsPPerfect 2 R) (hi : N.index ≤ 2) : R ≤ N := by
  let : MulAction R (G ⧸ N) := MulAction.compHom (G ⧸ N) R.subtype
  intro r hr
  have hh := MulAction.fixed_of_twoPerfect_of_card_le_two hR hi
    (⟨r,hr⟩ : R) ((1 : G) : G ⧸ N)
  change ((r*1 : G) : G ⧸ N) = ((1 : G) : G ⧸ N) at hh
  have he := QuotientGroup.eq.mp hh.symm
  simpa only [inv_one,one_mul,mul_one] using he

open ChapterB.InternalThompsonAction DoubledBinaryThompson

/-- A split-plane factor normalized by the actual Thompson image and
residual has full preimage centralizing the residual commutator. -/
theorem relative_splitPlane_preimage_centralizes_commutator
    {H : Type*} [Group H] [Finite H]
    (Y : Subgroup H) [Y.Normal] [IsElementaryAbelian 2 Y]
    (S : Sylow 2 H) (R : Subgroup H) (hR : IsPPerfect 2 R)
    (hRN : R ≤ normalizer (elementaryAbelianMaxJ (S : Subgroup H) : Set H))
    (A : Subgroup (ActionQuotient Y))
    (hJA : thompsonImage Y ≤ normalizer (A : Set (ActionQuotient Y)))
    (hRA : R.map (actionMk Y) ≤ normalizer (A : Set (ActionQuotient Y)))
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
  have hJF := (map_le_iff_le_comap.mp hJA).trans (A.le_normalizer_comap q)
  have hRF := (map_le_iff_le_comap.mp hRA).trans (A.le_normalizer_comap q)
  have hh := relative_plane_centralizes_residual ρ S R F hR hRN hJF hRF hFJ
    (hm ▸ hd) hsplit
  intro a ha
  exact (NormalElementaryQuotient.original_moved_centralizer Y R a).mpr
    (fun w hw => hh hw ⟨a,ha⟩)

/-- Full preimages of plane factors normalized by the Thompson image and
the specified residual lie in the specified target subgroup. -/
@[expose] def RelativePlaneFactorsContained
    {H : Type*} [Group H] (Y : Subgroup H) (hY : Theory.GroupTheory.IsPReduced 2 Y)
    (R M : Subgroup H) : Prop :=
  let := hY.normal
  let := hY.elementary
  ∀ (A : Subgroup (ActionQuotient Y)),
    thompsonImage Y ≤ normalizer (A : Set (ActionQuotient Y)) →
    R.map (actionMk Y) ≤ normalizer (A : Set (ActionQuotient Y)) →
    A ≤ thompsonImage Y →
    Module.finrank (ZMod 2) (moved (action Y) A) = 2 →
    moved (action Y) A ⊔ fixedSpace (action Y) A = ⊤ →
    A.comap (actionMk Y) ≤ M

/-- The original residual supplement puts the full preimage of each
relatively normal split plane factor in M. -/
theorem relative_plane_preimages_contained
    {G : Type*} [Group G] [Finite G]
    (H Y W U R M : Subgroup G) (S : Sylow 2 H)
    (hYH : Y ≤ H) (hWY : W ≤ Y) (hRH : R ≤ H)
    (hY : Theory.GroupTheory.IsPReduced 2 (Y.subgroupOf H))
    (hR : IsPPerfect 2 R)
    (hRN : R ≤ normalizer
      (elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) : Set G))
    (hsupp : U ⊔ ⁅W,R⁆ = W) (hHC : H ≤ centralizer (U : Set G))
    (hWM : centralizer (W : Set G) ≤ M) :
    RelativePlaneFactorsContained (Y.subgroupOf H) hY (R.subgroupOf H) (M.subgroupOf H) := by
  let := hY.normal
  let := hY.elementary
  intro A hJA hRA hAJ hd hs
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
  have hc := relative_splitPlane_preimage_centralizes_commutator
    (Y.subgroupOf H) S (R.subgroupOf H) hR' hRN' A hJA hRA hAJ hd hs
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


/-- For an odd plane actor normal in the Thompson image, at most two
ambient conjugates force residual normalization. Averaging supplies the
fixed complement. The full preimage, including the action kernel, lies in M. -/
theorem RelativePlaneFactorsContained.smallOrbitOdd
    {H : Type*} [Group H] [Finite H]
    (Y : Subgroup H) (hY : Theory.GroupTheory.IsPReduced 2 Y) (R M : Subgroup H)
    (hR : IsPPerfect 2 R) (hc : RelativePlaneFactorsContained Y hY R M) :
    let := hY.normal
    let := hY.elementary
    ∀ (A : Subgroup (ActionQuotient Y)),
      thompsonImage Y ≤ normalizer (A : Set (ActionQuotient Y)) →
      (normalizer (A : Set (ActionQuotient Y))).index ≤ 2 → A ≤ thompsonImage Y →
      Odd (Nat.card A) →
      Module.finrank (ZMod 2) (moved (action Y) A) = 2 →
      A.comap (actionMk Y) ≤ M := by
  let := hY.normal
  let := hY.elementary
  dsimp only
  intro A hJA hi hAJ ho hd
  have he : RegularCyclicNormalClosure.displacementSpan (action Y) A ⊤ =
      moved (action Y) A := by
    unfold moved subspaceCommutator RegularCyclicNormalClosure.displacementSpan
    congr 1
    ext v
    simp only [eq_comm]
  have hs := GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := action Y) ho
  rw [he] at hs
  have hRim : IsPPerfect 2 (R.map (actionMk Y)) := hR.of_surjective
    ((actionMk Y).subgroupMap R) ((actionMk Y).subgroupMap_surjective R)
  exact hc A hJA (twoPerfect_le_of_index_le_two _ _ hRim hi) hAJ hd hs.symm.sup_eq_top

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryThompsonRelativePlanes
