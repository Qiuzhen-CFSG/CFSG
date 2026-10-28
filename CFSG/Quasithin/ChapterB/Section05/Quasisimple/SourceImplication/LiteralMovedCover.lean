module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedCover
public import Theory.Representation.FirstCohomologyDuality
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# The literal moved section as a central cover

The projection from `[V,L]` to its quotient by `C_[V,L](L)` has fixed
kernel. The commutator-generation clause of Irr⁺ makes it a cover in the
cohomological sense. Subspaces retain their local commutator identity and
fixed-space containment when restricted to the literal moved carrier.

These interfaces allow the concrete natural-cover calculations to be applied
without changing the projection or discarding its central kernel. The
original marked-action cover API is re-exported unchanged; the literal
projection has its own name.

Source: Aschbacher--Smith, B.5.1(2), printed pp.99--103, and the cover
argument in 9.4.1, printed p.735 (combined 1 March 2004 manuscript).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The original projection on the moved carrier, with the literal L-action. -/
noncomputable def MovedSection.literalCoverProjection (s : MovedSection ρ L) :
    Representation.IntertwiningMap (s.space.toRepresentation.comp L.subtype)
      (s.action.comp L.subtype) :=
  s.central.toSubmodule.mkQ.intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)

/-- Irr⁺ supplies the full commutator generation required of a central cover. -/
theorem MovedSection.literalCoverProjection_isCover (s : MovedSection ρ L)
    (hi : IsIrrPlus ρ L s.space.toSubmodule) : IsCover s.literalCoverProjection := by
  refine ⟨Submodule.mkQ_surjective _, ?_, ?_⟩
  · intro v hv g
    have hmem := (Submodule.Quotient.mk_eq_zero _).mp hv
    rw [s.central_eq] at hmem
    exact hmem g
  · let τ := s.space.toRepresentation.comp L.subtype
    have hm : s.space.toSubmodule ≤ (Coinvariants.ker τ).map s.space.toSubmodule.subtype := by
      conv_lhs => rw [← hi.choose_spec.1]
      apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, v, hv, rfl⟩
      exact ⟨τ ⟨g, hg⟩ ⟨v, hv⟩ - ⟨v, hv⟩, Coinvariants.sub_mem_ker _ _, rfl⟩
    apply top_unique
    intro v _
    obtain ⟨w, hw, he⟩ := hm v.property
    rwa [show w = v from Subtype.ext he] at hw

/-- Restriction to the moved carrier preserves the exact local commutator. -/
theorem MovedSection.subspaceCommutator_comap (s : MovedSection ρ L)
    (A : Submodule (ZMod 2) V) (hA : A ≤ moved ρ L) (B : Subgroup L)
    (hm : subspaceCommutator (ρ.comp L.subtype) A B = A) :
    subspaceCommutator (s.space.toRepresentation.comp L.subtype)
      (A.comap s.space.toSubmodule.subtype) B = A.comap s.space.toSubmodule.subtype := by
  have ha : (A.comap s.space.toSubmodule.subtype).map s.space.toSubmodule.subtype = A := by
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right]
    simpa only [s.space_eq] using hA
  apply Submodule.map_injective_of_injective s.space.toSubmodule.subtype_injective
  have hmap := subspaceCommutator_map_embedding (ρ.comp L.subtype)
    (s.space.toRepresentation.comp L.subtype) (MonoidHom.id L)
    s.space.toSubmodule.subtype (fun _ _ => rfl) B (A.comap s.space.toSubmodule.subtype)
  simpa only [ha, Subgroup.map_id, hm] using hmap.symm

/-- Fixedness is preserved on the actual moved carrier. -/
theorem MovedSection.comap_le_fixedSpace (s : MovedSection ρ L)
    (A : Submodule (ZMod 2) V) (B : Subgroup L)
    (hA : A ≤ fixedSpace (ρ.comp L.subtype) B) :
    A.comap s.space.toSubmodule.subtype ≤
      fixedSpace (s.space.toRepresentation.comp L.subtype) B := by
  intro v hv b
  exact Subtype.ext (hA hv b)

end CFSG.Quasithin.ChapterB.QuasisimpleSource
