module
public import CFSG.Quasithin.Chapter13.Section02.A5Local.ThompsonFixedPlane

/-!
# An odd element in the original Thompson image

If J(T) moves the chosen five-point module, one of its maximum elementary
subgroups has nontrivial image in the literal local action. That image is a
best offender. Transport through the original module coordinates makes it
an offender on the five-point core, hence it contains an odd permutation.
This identifies an odd element inside the actual Thompson image, as needed
for the disjoint-transposition marking in 13.2.11(2).
Source: Aschbacher–Smith 13.2.4(2b) and 13.2.11(2), pp.879 and881.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem local_thompson_image_not_le_alternating
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    ¬ (elementaryAbelianMaxJ (T.subtype
      (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right) :
        Subgroup ↥(L ⊔ (T : Subgroup G)))).map d.localActor ≤ alternatingGroup (Fin 5) := by
  let K := L ⊔ (T : Subgroup G)
  let U := V.subgroupOf K
  let := d.reduced.normal
  let := d.reduced.elementary
  let q := d.localActor.rangeRestrict
  have hk : q.ker = centralizer (U : Set K) :=
    d.localActor.ker_rangeRestrict.trans d.localActor_kernel
  let ρ := NormalElementaryQuotient.representation U q d.localActor.rangeRestrict_surjective hk
  let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
  have hm : (elementaryAbelianMaxJ (S : Subgroup K)).map K.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective K.subtype K.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le le_sup_right
  have hj : ¬ elementaryAbelianMaxJ (S : Subgroup K) ≤ q.ker := by
    intro hc
    apply hJ
    rw [← hm]
    rintro x ⟨x,hx,rfl⟩ v hv
    have hc' := hk ▸ hc hx
    exact congrArg K.subtype (hc' ⟨v,(le_sup_right : (T : Subgroup G) ≤ K) (d.chosen.le_sylow hv)⟩ hv)
  have hUS : U ≤ (S : Subgroup K) := fun _ hv => d.chosen.le_sylow hv
  have hsome : ∃ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup K), A.map q ≠ ⊥ := by
    by_contra hnone
    push Not at hnone
    apply hj
    apply sSup_le
    intro A hA a ha
    have hh := mem_map_of_mem q ha
    rw [hnone A hA] at hh
    exact mem_bot.mp hh
  obtain ⟨A,hA,hne⟩ := hsome
  have hbA : IsBestOffender ρ (A.map q) :=
    Chapter15.Section03.CharacteristicTwo.StarSelection.maxElementary_isBestOffender
      U q d.localActor.rangeRestrict_surjective hk (S : Subgroup K) A hUS hA hne
  have he : ∀ g v, d.localModuleCoordinates.symm (ρ g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g.val (d.localModuleCoordinates.symm v) := by
    intro g v
    obtain ⟨g,rfl⟩ := d.localActor.rangeRestrict_surjective g
    apply d.localModuleCoordinates.injective
    rw [LinearEquiv.apply_symm_apply]
    have hh := d.localModuleCoordinates_equivariant g (d.localModuleCoordinates.symm v)
    rw [LinearEquiv.apply_symm_apply] at hh
    exact hh
  have hmodel := hbA.map_of_fixedCodim ρ (BinaryPermutation.coreRepresentation (Fin 5))
    d.localActor.range.subtype d.localActor.range.subtype_injective
    (fixedCodim_map_equivariant ρ (BinaryPermutation.coreRepresentation (Fin 5))
      d.localActor.range.subtype d.localModuleCoordinates.symm he)
  have hmap : (A.map q).map d.localActor.range.subtype = A.map d.localActor := by
    rw [Subgroup.map_map]
    rfl
  rw [hmap] at hmodel
  have hnot := ChapterB.Offenders.core_offender_not_le_alternating (Or.inl rfl) hmodel.isOffender
  intro hle
  exact hnot ((map_mono (le_sSup hA)).trans hle)

end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
