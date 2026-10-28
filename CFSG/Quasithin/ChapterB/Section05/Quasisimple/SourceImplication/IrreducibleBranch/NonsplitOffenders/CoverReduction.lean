module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.EasyCases
public import Theory.Representation.FirstCohomologyDuality

/-!
# The literal local covering map for the last B.5.1 branch

The map [V,L] -> [V,L]/C_[V,L](L) is equivariant for every local overgroup D.
Its restriction to L.subgroupOf D is a covering: Irr+ supplies commutator
generation, and the kernel is exactly the original L-fixed subspace.
No assertion that the kernel is fixed by all of D is made.

Best offenders on V remain best on the invariant submodule [V,L], by the
restriction weight inequality. The last theorem applies both facts to the
same LT and the same original Sylow offenders, preparing the actual input
for the remaining symplectic natural-cover calculation.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), B.5.1,
printed p.100; B.1.5(1), printed p.69; covering convention I.1.5, p.408.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
open Representation.OneCohomology
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The actual quotient map, equivariant for every subgroup of the ambient group. -/
noncomputable def localMovedProjection (s : MovedSection ρ L) (D : Subgroup G) :
    Representation.IntertwiningMap (s.space.toRepresentation.comp D.subtype)
      (s.action.comp D.subtype) :=
  s.central.toSubmodule.mkQ.intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)

/-- Restrict that same quotient map to the component embedded in D. -/
noncomputable def componentMovedProjection (s : MovedSection ρ L) (D : Subgroup G) :
    Representation.IntertwiningMap
      ((s.space.toRepresentation.comp D.subtype).comp (L.subgroupOf D).subtype)
      ((s.action.comp D.subtype).comp (L.subgroupOf D).subtype) :=
  (localMovedProjection s D).toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (fun _ _ => rfl)

/-- The component restriction retains exactly the original central kernel. -/
theorem componentMovedProjection_ker (s : MovedSection ρ L) (D : Subgroup G) :
    (componentMovedProjection s D).toLinearMap.ker = s.central.toSubmodule :=
  Submodule.ker_mkQ _

/-- Irr+ makes the literal moved projection a covering for the relative component. -/
theorem componentMovedProjection_isCover (s : MovedSection ρ L) (D : Subgroup G)
    (hLD : L ≤ D) (hi : IsIrrPlus ρ L s.space.toSubmodule) :
    IsCover (componentMovedProjection s D) := by
  refine ⟨Submodule.mkQ_surjective _, ?_, ?_⟩
  · intro v hv g
    have hmem := (Submodule.Quotient.mk_eq_zero _).mp hv
    rw [s.central_eq] at hmem
    exact hmem ⟨g.val, g.property⟩
  · let τ := (s.space.toRepresentation.comp D.subtype).comp (L.subgroupOf D).subtype
    have hm : s.space.toSubmodule ≤ (Coinvariants.ker τ).map s.space.toSubmodule.subtype := by
      conv_lhs => rw [← hi.choose_spec.1]
      apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, v, hv, rfl⟩
      let x : L.subgroupOf D := ⟨⟨g, hLD hg⟩, hg⟩
      exact ⟨τ x ⟨v, hv⟩ - ⟨v, hv⟩, Coinvariants.sub_mem_ker _ _, rfl⟩
    apply top_unique
    intro v _
    obtain ⟨w, hw, he⟩ := hm v.property
    rwa [show w = v from Subtype.ext he] at hw

/-- Original best offenders remain best on the moved submodule before quotienting. -/
theorem bestOffender_on_movedSpace [FiniteDimensional (ZMod 2) V]
    (s : MovedSection ρ L) {A : Subgroup G} (hA : IsBestOffender ρ A) :
    IsBestOffender s.space.toRepresentation A := by
  refine ⟨hA.1, fun B hBA => ?_⟩
  have hle := hA.restriction_weight_le ρ hBA s.space.toSubmodule
  unfold weight
  rw [(subrepresentationFixedEquiv ρ s.space B).finrank_eq,
    (subrepresentationFixedEquiv ρ s.space A).finrank_eq]
  exact hle

/-- The same offender in the literal local overgroup acts as a best offender on the cover. -/
theorem local_bestOffender_on_movedSpace [FiniteDimensional (ZMod 2) V]
    (s : MovedSection ρ L) {A D : Subgroup G} (hAD : A ≤ D)
    (hA : IsBestOffender ρ A) :
    IsBestOffender (s.space.toRepresentation.comp D.subtype) (A.subgroupOf D) :=
  (bestOffender_on_movedSpace s hA).subgroupOf s.space.toRepresentation hAD

/-- Application to the exact LT cover: no ambient-fixed-kernel assertion is needed. -/
theorem local_cover_data [FiniteDimensional (ZMod 2) V]
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (T : Sylow 2 G) (hz : s.central.toSubmodule ≠ ⊥) :
    IsCover (componentMovedProjection s (L ⊔ (T : Subgroup G))) ∧
      (componentMovedProjection s (L ⊔ (T : Subgroup G))).toLinearMap.ker ≠ ⊥ ∧
      ∀ A ≤ (T : Subgroup G), IsBestOffender ρ A →
        IsBestOffender (s.space.toRepresentation.comp (L ⊔ (T : Subgroup G)).subtype)
          (A.subgroupOf (L ⊔ (T : Subgroup G))) := by
  refine ⟨componentMovedProjection_isCover s _ le_sup_left hi, ?_, ?_⟩
  · rwa [componentMovedProjection_ker]
  · intro A hAT hA
    exact local_bestOffender_on_movedSpace s (hAT.trans le_sup_right) hA
end CFSG.Quasithin.ChapterB.QuasisimpleSource.IrreducibleBranch
