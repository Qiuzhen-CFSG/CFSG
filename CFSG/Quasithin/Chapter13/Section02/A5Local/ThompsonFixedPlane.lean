module

public import CFSG.Quasithin.Chapter13.Section02.A5Local.FullAction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.FixedPlane
public import Theory.Representation.BinaryOffender.FixedCodimTransport
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# The fixed plane of the original Thompson action

The original five-point module has at least four elements fixed by J(T).
Map each maximal elementary subgroup through the actual local action. Its
nontrivial image is a best offender, so all these images lie in a common
conjugate of the disjoint-transposition group. The resulting fixed plane is
transported through the marked module coordinates and the inclusion LT→G.

The center-free outside-group argument uses this lower bound to exclude the
single natural factor in E.2.3, without assuming the exact Thompson image.
Source: Aschbacher–Smith 13.2.4(2b) and 13.2.11, printed pp.879 and 881.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem four_le_card_thompson_fixed :
    4 ≤ Nat.card (V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) : Subgroup G) := by
  let K := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf K
  let := d.reduced.normal
  let := d.reduced.elementary
  let q := d.localActor.rangeRestrict
  have hk : q.ker = centralizer (U : Set K) :=
    d.localActor.ker_rangeRestrict.trans d.localActor_kernel
  let ρ := NormalElementaryQuotient.representation U q d.localActor.rangeRestrict_surjective hk
  let σ := BinaryPermutation.coreRepresentation (Fin 5)
  let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
  have hUS : U ≤ (S : Subgroup K) := fun _ hv => d.chosen.le_sylow hv
  have he : ∀ g v, d.localModuleCoordinates.symm (ρ g v) =
      σ g.val (d.localModuleCoordinates.symm v) := by
    intro g v
    obtain ⟨g, rfl⟩ := d.localActor.rangeRestrict_surjective g
    apply d.localModuleCoordinates.injective
    rw [LinearEquiv.apply_symm_apply]
    have hh := d.localModuleCoordinates_equivariant g (d.localModuleCoordinates.symm v)
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh
  obtain ⟨D₀, hd, hbound⟩ := ChapterB.Offenders.exists_five_offender_bound
    ((S : Subgroup K).map d.localActor) (S.isPGroup'.map d.localActor)
  have hjbound : (elementaryAbelianMaxJ (S : Subgroup K)).map d.localActor ≤ D₀ := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro A hA
    apply map_le_iff_le_comap.mp
    have hmap : (A.map q).map d.localActor.range.subtype = A.map d.localActor := by
      rw [Subgroup.map_map]
      rfl
    by_cases hb : A.map q = ⊥
    · rw [← hmap, hb, Subgroup.map_bot]
      exact bot_le
    have hbA : IsBestOffender ρ (A.map q) :=
      Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
      U q d.localActor.rangeRestrict_surjective hk (S : Subgroup K) A hUS hA hb
    have hmodel := hbA.map_of_fixedCodim ρ σ d.localActor.range.subtype
      d.localActor.range.subtype_injective
      (fixedCodim_map_equivariant ρ σ d.localActor.range.subtype d.localModuleCoordinates.symm he)
    rw [hmap] at hmodel
    exact hbound _ hmodel (map_mono hA.1)
  have hdim : 2 ≤ Module.finrank (ZMod 2)
      (fixedSpace σ ((elementaryAbelianMaxJ (S : Subgroup K)).map d.localActor)) := by
    have hmono := Submodule.finrank_mono (fixedSpace_antitone σ hjbound)
    have hsum := fixedCodim_add_finrank σ D₀
    rw [BinaryPermutation.FiveGeometry.finrank_core] at hsum
    change fixedCodim σ D₀ = 2 at hd
    omega
  have hfixedmap := fixedSpace_map_equivariant ρ σ d.localActor.range.subtype
    d.localModuleCoordinates.symm he ((elementaryAbelianMaxJ (S : Subgroup K)).map q)
  have hmap : ((elementaryAbelianMaxJ (S : Subgroup K)).map q).map
      d.localActor.range.subtype = (elementaryAbelianMaxJ (S : Subgroup K)).map d.localActor := by
    rw [Subgroup.map_map]
    rfl
  rw [hmap] at hfixedmap
  have hdimρ : 2 ≤ Module.finrank (ZMod 2)
      (fixedSpace ρ ((elementaryAbelianMaxJ (S : Subgroup K)).map q)) := by
    rw [← hfixedmap] at hdim
    rwa [LinearEquiv.finrank_map_eq] at hdim
  have hc : 4 ≤ Nat.card (U ⊓ centralizer (elementaryAbelianMaxJ (S : Subgroup K) : Set K) : Subgroup K) := by
    rw [← Nat.card_congr (NormalElementaryQuotient.fixedSpaceEquiv U q
      d.localActor.rangeRestrict_surjective hk (elementaryAbelianMaxJ (S : Subgroup K))),
      Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hdimρ
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup K)).map K.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective K.subtype K.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le le_sup_right
  have hVK : V ≤ K := d.chosen.le_sylow.trans le_sup_right
  have hcmap : (U ⊓ centralizer (elementaryAbelianMaxJ (S : Subgroup K) : Set K)).map
      K.subtype = V ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    rw [← map_inf_centralizer_of_injective K.subtype K.subtype_injective,
      hJmap, map_subgroupOf_eq_of_le hVK]
  rw [← hcmap, card_map_of_injective K.subtype_injective]
  exact hc

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
