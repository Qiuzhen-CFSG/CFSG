module
public import CFSG.Quasithin.Chapter13.Section02.A5Local.FullAction
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import Theory.SpecificGroups.FivePointSylowParabolic

/-!
# The literal minimal parabolic and full module action in the A5 source

The original LT action has a two-group kernel and contains A5, so the
five-point Sylow-overgroup theorem makes LT a minimal parabolic. The
original coordinates intertwine the full S5 quotient whenever J(T) moves V.
These are the literal input maps for the E.2.3 saturation step in 5.1.7.
-/
@[expose] public section
open Subgroup Stellmacher Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter5.A5Source
open Chapter13.Section05.A5Source ChapterB
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

theorem local_minimal_parabolic :
    IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)) ⊤ := by
  let R := T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)
  obtain ⟨hm,hn⟩ := Theory.SpecificGroups.FivePointSylowParabolic.unique_maximal_of_five_point_map
    d.localActor (d.localActor_kernel_isTwo d.normalizes_L) d.alternating_le_localActor R
  exact (isMinimalParabolicOver_top_iff R).mpr ⟨hm,hn⟩

omit [Finite G] d in
theorem local_thompson_image :
    (elementaryAbelianMaxJ
      (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right) :
        Subgroup ↥(L ⊔ (T : Subgroup G)))).map (L ⊔ (T : Subgroup G)).subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
  rw [←elementaryAbelianMaxJ_map_injective _ (L ⊔ (T : Subgroup G)).subtype_injective]
  congr 1
  exact map_subgroupOf_eq_of_le le_sup_right

theorem local_thompson_moves
    (hJ : ¬elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    ¬elementaryAbelianMaxJ
      (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right) :
        Subgroup ↥(L ⊔ (T : Subgroup G))) ≤
      centralizer (V.subgroupOf (L ⊔ (T : Subgroup G)) : Set ↥(L ⊔ (T : Subgroup G))) := by
  intro hc
  apply hJ
  rw [←local_thompson_image (T := T) (L := L)]
  rintro x ⟨x,hx,rfl⟩ v hv
  exact congrArg (L ⊔ (T : Subgroup G)).subtype
    (hc hx ⟨v,(le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G))
      (d.chosen.le_sylow hv)⟩ hv)

theorem local_full_equivariant (hq : Function.Surjective d.localActor) :
    letI := d.reduced.normal
    letI := d.reduced.elementary
    ∀ g v, d.localModuleCoordinates.symm
      (NormalElementaryQuotient.representation (V.subgroupOf (L ⊔ (T : Subgroup G)))
        d.localActor hq d.localActor_kernel g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (d.localModuleCoordinates.symm v) := by
  let := d.reduced.normal
  let := d.reduced.elementary
  intro g v
  obtain ⟨g,rfl⟩ := hq g
  apply d.localModuleCoordinates.injective
  rw [LinearEquiv.apply_symm_apply]
  have hh := d.localModuleCoordinates_equivariant g (d.localModuleCoordinates.symm v)
  rw [LinearEquiv.apply_symm_apply] at hh
  rw [←hh]
  apply Additive.toMul.injective
  apply Subtype.ext
  exact NormalElementaryQuotient.representation_apply _ d.localActor hq d.localActor_kernel g v |>.trans
    (NormalElementaryQuotient.representation_apply _ d.localActor.rangeRestrict
      d.localActor.rangeRestrict_surjective
      (d.localActor.ker_rangeRestrict.trans d.localActor_kernel) g v).symm

end CFSG.Quasithin.Chapter5.A5Source
