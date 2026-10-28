module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.ModuleChoice.QuietTensorModels
public import Theory.GroupTheory.SylowInvariantThreeFree.Automorphism
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.ThreePrimeOvergroups
public import Theory.GroupTheory.RankTwoDisjointAction
/-!
# Three-free control for the ambient Held alternative

Keep the Held component allowed by the adequate intrinsic embedding theorem.
Conjugation on the original K_z/O₂(K_z) contains its inner automorphisms,
and its outer group is a two-group. The checked Held Sylow calculation
therefore makes every three-free T-invariant subgroup act through a two-group.
Its two-residual acts trivially. Residual recovery makes the full action
kernel normalize the original X, so the previously proved N_{G_z}(X) bound
places that kernel, and then the entire three-free subgroup, in M.

For a nonzero subspace U of the original full module, a faithful elementary
nine normalizing U excludes three from C_G(U). This uses quasithin rank in
the actual two-local N_G(U), without asserting an ambient rank bound on G.
If z belongs to U and T normalizes U, the Held branch thus gives C_G(U) ≤ M.
These are the literal clauses (a)--(c) of the subsequent source argument.
Constructing that fixed-space geometry, proving 8.3.9, and finally excluding
Held remain with this owner, as do tensor recognition and both quiet rows.

Source: Aschbacher--Smith A.1.27 and 8.3.7--9, printed pp.26,724--725,
with Held retained from the corrected intrinsic 1.3.4 catalogue.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02 ChapterE Chapter8.Section03 Chapter1
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)

/-- In the actual Held row, every three-free subgroup of G_z normalized by
T lies in M. The quotient-action kernel is controlled through the original
residual X, without identifying it with an ordinary centralizer. -/
theorem quiet_tensor_held_three_free_le
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    (c : XiQuotient (CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩) ≃* Held.He)
    (Y : Subgroup G) (hY : Y ≤ centralizer ({z} : Set G))
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hthree : ¬ 3 ∣ Nat.card Y) : Y ≤ D.maximalLocal := by
  let d : CentralizerSetup G := ⟨T,localOrbit T L,z⟩
  have hi := quiet_tensor_point_localInput D hn e hbase hzV hz1 hzT P
  have hKn : d.Gz ≤ normalizer (d.Kz : Set G) := le_normalizer_conjugateSpanBy _ _
  let f : d.Gz →* MulAut (XiQuotient d.Kz) :=
    (pCoreNormalizerAction 2 d.Kz).comp (inclusion hKn)
  have hinner : MulAut.innerSubgroup (XiQuotient d.Kz) ≤ f.range := by
    rintro a ⟨q,rfl⟩
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 d.Kz) q
    exact ⟨⟨k,d.Kz_le_Gz k.property⟩,pCoreNormalizerAction_on_component 2 d.Kz k⟩
  have hz : center (XiQuotient d.Kz) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh : c x ∈ center Held.He := (centerCongr c ⟨x,hx⟩).property
    rw [Held.LocalPairs.center_eq_bot] at hh
    exact c.injective ((mem_bot.mp hh).trans (map_one c).symm)
  have ho : IsPGroup 2 (MulAut.Outer (XiQuotient d.Kz)) := by
    have hh : IsPGroup 2 (MulAut.Outer Held.He) :=
      Subgroup.isPGroup_outer_of_normalizer Held.permutationGroup 2
        Held.Realization.normalizer_surjective Held.isPGroup_permutationNormalizerQuotient
    exact hh.of_injective (MulAut.outerCongr c).toMonoidHom (MulAut.outerCongr c).injective
  have hYz : Y ≤ d.Gz := hY
  let R : Sylow 2 d.Gz := T.subtype hzT
  let Y' := Y.subgroupOf d.Gz
  have hnorm : (R : Subgroup d.Gz) ≤ normalizer (Y' : Set d.Gz) := by
    change (T : Subgroup G).subgroupOf d.Gz ≤ normalizer (Y.subgroupOf d.Gz : Set d.Gz)
    rw [←subgroupOf_normalizer_eq hYz]
    exact comap_mono hTY
  have hthree' : ¬ 3 ∣ Nat.card Y' := by
    change ¬ 3 ∣ Nat.card (Y.subgroupOf d.Gz)
    rw [Nat.card_congr (subgroupOfEquivOfLe hYz).toEquiv]
    exact hthree
  have hbound := le_ker_sup_sylow_of_three_free_automorphism_model R f hinner hz ho Y'
    hnorm hthree' c Held.LocalPairs.SylowGeometry.inner_normalized_three_prime_isPGroup
  have hcoreH : d.Gz.pCoreIn 2 ≤ normalizer (d.X : Set G) := by
    rw [←hi.residual]
    exact le_sup_left.trans (le_normalizer_embedded_pResidual 2 _)
  have hcore : d.Kz.pCoreIn 2 ≤ normalizer (d.X : Set G) :=
    (pCoreIn_mono_of_normalizes d.Kz_le_Gz hKn).trans hcoreH
  have hker : f.ker.map d.Gz.subtype ≤ D.maximalLocal := by
    rintro g ⟨x,hx,rfl⟩
    apply quiet_tensor_point_normalizer_le D hmany hmin hn hJ cL e hbase hzV hz1 hzT
    refine ⟨x.property,?_⟩
    apply mem_normalizer_of_pCoreNormalizerAction_preserves_image d.Kz d.X d.X_le_Kz
      hi.perfect hcore (inclusion hKn x)
    change pCoreNormalizerAction 2 d.Kz (inclusion hKn x) = 1 at hx
    rw [hx]
    exact map_id _
  have hTM : (T : Subgroup G) ≤ D.maximalLocal :=
    le_sup_right.trans (D.lemma_3_2_3_uniqueness (source_module_nonsolvable_uniqueness D)).2.1
  have hm := map_mono (f := d.Gz.subtype) hbound
  have hmap : Y'.map d.Gz.subtype = Y := map_subgroupOf_eq_of_le hYz
  rw [hmap,Subgroup.map_sup] at hm
  have hR : (R : Subgroup d.Gz).map d.Gz.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hzT
  rw [hR] at hm
  exact hm.trans (sup_le hker hTM)

/-- The Held branch of 8.3.8 reduces to the original fixed space's
three-free centralizer. Its full ambient centralizer, not just its
intersection with K_z T, is contained in M. -/
theorem quiet_tensor_held_centralizer_le
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    (c : XiQuotient (CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩) ≃* Held.He)
    (U : Subgroup G) (hzU : z ∈ U)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hthree : ¬ 3 ∣ Nat.card (centralizer (U : Set G))) :
    centralizer (U : Set G) ≤ D.maximalLocal :=
  quiet_tensor_held_three_free_le D hmany hmin hn hJ cL e hbase hzV hz1 hzT P c
    (centralizer (U : Set G)) (centralizer_le (Set.singleton_subset_iff.mpr hzU))
    (hTU.trans (normalizer_le_normalizer_centralizer U)) hthree

/-- Source A.1.27 inside the actual two-local normalizer of the chosen
fixed space: a faithful elementary nine excludes three from its ambient
centralizer. Only the local quasithin rank bound is used. -/
theorem quiet_fixed_space_centralizer_three_free
    (U : Subgroup G) (hUV : U ≤ D.fullModule) (hne : U ≠ ⊥)
    (A : Subgroup G) [IsElementaryAbelian 3 A] (hcard : Nat.card A = 9)
    (hAU : A ≤ normalizer (U : Set G))
    (hfaith : Function.Injective (U.normalizerMonoidHom.comp (inclusion hAU))) :
    ¬ 3 ∣ Nat.card (centralizer (U : Set G)) := by
  let N := normalizer (U : Set G)
  let C := centralizer (U : Set G)
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have htwo : IsPGroup 2 U := T.isPGroup'.to_le
    (hUV.trans (D.fullModule_le_sylow (source_module_nonsolvable_uniqueness D)))
  have hsq := D.simpleQTKE.twoLocal_sqtk (show IsTwoLocal N from ⟨U,hne,htwo,rfl⟩)
  let A' := A.subgroupOf N
  let C' := C.subgroupOf N
  let : IsElementaryAbelian 3 A' := IsElementaryAbelian.subgroupOf hAU
  have hcard' : Nat.card A' = 3^2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAU).toEquiv,hcard]
    decide
  have hn : A' ≤ normalizer (C' : Set N) := by
    rw [←subgroupOf_normalizer_eq hCN]
    exact comap_mono (hAU.trans (normalizer_le_normalizer_centralizer U))
  have hd : Disjoint A' C' := by
    apply disjoint_def.mpr
    intro x hxA hxC
    have hk : U.normalizerMonoidHom.comp (inclusion hAU) ⟨x.val,hxA⟩ = 1 := by
      change (⟨x.val,hAU hxA⟩ : normalizer (U : Set G)) ∈ U.normalizerMonoidHom.ker
      rw [normalizerMonoidHom_ker]
      exact hxC
    have hx : x.val = 1 := congrArg A.subtype (hfaith (hk.trans (map_one _).symm))
    exact Subtype.ext hx
  have hc := coprime_card_of_normalized_disjoint_plane
    (hsq.stronglyQuasithin 3 (by decide) (by decide)) A' C' hcard' hn hd
  have hc' : Nat.Coprime 3 (Nat.card C) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv] at hc
  exact Nat.prime_three.coprime_iff_not_dvd.mp hc'

/-- The ambient Held branch under the literal source clauses (a)--(c)
of 8.3.8: the fixed space contains z, is T-invariant, and has a faithful
elementary-nine actor. Its three-free centralizer is derived from QTKE. -/
theorem quiet_tensor_held_fixed_space_control
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmin : D.IsMinimalFullModule)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G))
    (cL : (L ⧸ pCore 2 L) ≃* Matrix.PSL3Two.SL)
    (e : Additive D.fullModule ≃ₗ[ZMod 2] BinaryTensorThree.Space)
    (hbase : ((localOrbit T L).subgroupOf (localJoin T L)).map
      (quietTensorLinearAction D e) = BinaryTensorThree.baseAction.range)
    {z : G} (hzV : z ∈ D.fullModule) (hz1 : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (P : Sylow 3 (CentralizerSetup.X ⟨T,localOrbit T L,z⟩))
    (c : XiQuotient (CentralizerSetup.Kz ⟨T,localOrbit T L,z⟩) ≃* Held.He)
    (U : Subgroup G) (hUV : U ≤ D.fullModule) (hzU : z ∈ U)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (A : Subgroup G) [IsElementaryAbelian 3 A] (hcard : Nat.card A = 9)
    (hAU : A ≤ normalizer (U : Set G))
    (hfaith : Function.Injective (U.normalizerMonoidHom.comp (inclusion hAU))) :
    centralizer (U : Set G) ≤ D.maximalLocal := by
  have hne : U ≠ ⊥ := fun he => hz1 (mem_bot.mp (he ▸ hzU))
  exact quiet_tensor_held_centralizer_le D hmany hmin hn hJ cL e hbase hzV hz1 hzT P c
    U hzU hTU (quiet_fixed_space_centralizer_three_free D U hUV hne A hcard hAU hfaith)

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
