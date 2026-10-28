module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry
public import Theory.Representation.BinaryPermutationSixCover.Universal

/-!
# The universal cover of an actual natural A₆ moved section

The Irr⁺ condition makes the literal moved space commutator-generated. Its
projection to the central quotient therefore becomes a perfect central cover
of the natural A₆ module under the specified action equivalence. The universal
six-letter augmentation cover surjects onto this original space, retaining
both the alternating actor and the quotient map. In particular the moved
space has binary dimension at most five; no splitting is assumed.

Source: Aschbacher–Smith, B.5.1 and I.1.5–6, printed pp.99–103 and408.
-/

public section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) D V} {L : Subgroup D}

/-- A marked universal augmentation cover of the original moved space. -/
theorem MovedSection.alternatingSix_core_quotient
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (e : ActionEquiv (s.action.comp L.subtype) (alternatingNatural 6)) :
    ∃ f : BinaryPermutation.core (Fin 6) →ₗ[ZMod 2] s.space.toSubmodule,
      Function.Surjective f ∧
      (∀ g : alternatingGroup (Fin 6), ∀ v,
        f (BinaryPermutation.coreRepresentation (Fin 6) g.val v) =
          s.space.toRepresentation (e.groupEquiv.symm g) (f v)) ∧
      ∀ v, e.linearEquiv (s.central.toSubmodule.mkQ (f v)) =
        BinaryPermutation.coreToNatural (Fin 6) v := by
  let σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) s.space.toSubmodule :=
    s.space.toRepresentation.comp (L.subtype.comp e.groupEquiv.symm.toMonoidHom)
  let p := e.linearEquiv.toLinearMap.comp s.central.toSubmodule.mkQ
  let P : σ.IntertwiningMap (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) :=
    p.intertwiningMap_of_isIntertwiningMap _ _ (fun g v => by
      change e.linearEquiv ((s.action.comp L.subtype) (e.groupEquiv.symm g) (s.central.toSubmodule.mkQ v)) = _
      rw [e.intertwines,e.groupEquiv.apply_symm_apply]
      rfl)
  have hP : IsCover P := by
    refine ⟨e.linearEquiv.surjective.comp (Submodule.mkQ_surjective _), ?_, ?_⟩
    · intro v hv g
      have hz : s.central.toSubmodule.mkQ v = 0 :=
        e.linearEquiv.injective (hv.trans e.linearEquiv.map_zero.symm)
      have hmem := (Submodule.Quotient.mk_eq_zero _).mp hz
      rw [s.central_eq] at hmem
      exact hmem (e.groupEquiv.symm g)
    · have hm : s.space.toSubmodule ≤ (Coinvariants.ker σ).map s.space.toSubmodule.subtype := by
        conv_lhs => rw [←hi.choose_spec.1]
        apply Submodule.span_le.mpr
        rintro _ ⟨g,hg,v,hv,rfl⟩
        let a : L := ⟨g,hg⟩
        refine ⟨σ (e.groupEquiv a) ⟨v,hv⟩ - ⟨v,hv⟩,
          Coinvariants.sub_mem_ker _ _, ?_⟩
        change (ρ (e.groupEquiv.symm (e.groupEquiv a)) v - v) = ρ g v - v
        rw [e.groupEquiv.symm_apply_apply]
      apply top_unique
      intro v _
      obtain ⟨w,hw,he⟩ := hm v.property
      rwa [show w = v from Subtype.ext he] at hw
  exact BinaryPermutation.SixCover.core_quotient_of_alternating_cover σ P hP

/-- Central attachments add at most one dimension to the natural four-space. -/
theorem MovedSection.alternatingSix_finrank_le_five
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (e : ActionEquiv (s.action.comp L.subtype) (alternatingNatural 6)) :
    Module.finrank (ZMod 2) s.space.toSubmodule ≤ 5 := by
  obtain ⟨f,hf,_,_⟩ := s.alternatingSix_core_quotient hi e
  have h := LinearMap.finrank_le_finrank_of_surjective (f := f) hf
  simpa only [BinaryPermutation.finrank_core, Fintype.card_fin] using h
end CFSG.Quasithin.ChapterB.QuasisimpleSource
