module

public import Theory.Representation.SymplecticFourOrthogonalCover.DualRatio
public import Theory.Representation.BinaryOffender.DualFixedSupplement
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.QuasisimpleContract

/-!
# Symplectic natural covers in the B.5.13 dual bound

The literal central quotient of an Irr⁺ moved section is a covering of its
natural symplectic module. Transport the explicit root calculation along
that same quotient marking, and then along the original component inclusion.
The dual of the actual moved submodule has quadratic ratio at most two.

A fixed supplement transfers this bound to the original representation.
The last theorem takes the corrected full B.5.1 conclusion and retains that
supplement as an explicit premise. It covers the commutator-generated case;
it does not supply the six-dimensional orthogonal envelope required when
the whole module has a further trivial top quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.13,
printed pp.110–112, and I.1.5–6, printed p.408.
-/

public section

open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterB.SourceB513
open QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) D V} {L : Subgroup D}

/-- The actual moved natural central cover has the required dual ratio bound. -/
theorem symplectic_moved_dual_ratio_le_two
    (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : ActionEquiv (s.action.comp L.subtype) (binarySymplectic F)) :
    quadraticRatio s.space.toRepresentation.dual ≤ 2 := by
  have hcard : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hF
  have hall (g : Sp F.Carrier) : g ∈ commutator (Sp F.Carrier) := by
    rw [Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top hcard]
    trivial
  let f : SymplecticFourOrthogonalCover.L (K := F.Carrier) →* D :=
    L.subtype.comp (e.groupEquiv.symm.toMonoidHom.comp (commutator (Sp F.Carrier)).subtype)
  have hf : Function.Injective f :=
    L.subtype_injective.comp (e.groupEquiv.symm.injective.comp Subtype.val_injective)
  let σ := s.space.toRepresentation.comp f
  let p := e.linearEquiv.toLinearMap.comp s.central.toSubmodule.mkQ
  let P : Representation.IntertwiningMap σ
      (SymplecticFourOrthogonalCover.binaryNatural (K := F.Carrier)) :=
    p.intertwiningMap_of_isIntertwiningMap _ _ (fun g v => by
      change e.linearEquiv ((s.action.comp L.subtype) (e.groupEquiv.symm g.val)
        (s.central.toSubmodule.mkQ v)) = _
      rw [e.intertwines, e.groupEquiv.apply_symm_apply]
      rfl)
  have hP : IsCover P := by
    refine ⟨e.linearEquiv.surjective.comp (Submodule.mkQ_surjective _), ?_, ?_⟩
    · intro v hv g
      have hz : s.central.toSubmodule.mkQ v = 0 :=
        e.linearEquiv.injective (hv.trans e.linearEquiv.map_zero.symm)
      have hm := (Submodule.Quotient.mk_eq_zero _).mp hz
      rw [s.central_eq] at hm
      exact hm (e.groupEquiv.symm g.val)
    · have hm : s.space.toSubmodule ≤ (Coinvariants.ker σ).map s.space.toSubmodule.subtype := by
        conv_lhs => rw [← hi.choose_spec.1]
        apply Submodule.span_le.mpr
        rintro _ ⟨g, hg, v, hv, rfl⟩
        let a : L := ⟨g, hg⟩
        let b : SymplecticFourOrthogonalCover.L (K := F.Carrier) :=
          ⟨e.groupEquiv a, hall _⟩
        refine ⟨σ b ⟨v, hv⟩ - ⟨v, hv⟩, Coinvariants.sub_mem_ker _ _, ?_⟩
        change ρ (e.groupEquiv.symm (e.groupEquiv a)) v - v = ρ g v - v
        rw [e.groupEquiv.symm_apply_apply]
      apply top_unique
      intro v _
      obtain ⟨w, hw, he⟩ := hm v.property
      rwa [show w = v from Subtype.ext he] at hw
  have hq := SymplecticFourOrthogonalCover.Roots.dual_cover_ratio_le_two hcard P hP
  apply (quadraticRatio_le_of_injective_equivariant (Representation.dual σ)
    s.space.toRepresentation.dual f hf (LinearEquiv.refl _ _) ?_).trans hq
  intro g v
  ext w
  change v (s.space.toRepresentation (f g⁻¹) w) =
    v (s.space.toRepresentation ((f g)⁻¹) w)
  rw [map_inv]

/-- Fixed vectors supplementing the original dual moved space complete this case. -/
theorem quadraticRatio_le_two_of_symplectic_moved_supplement [Finite D]
    (ρ : Representation (ZMod 2) D V) (s : MovedSection ρ.dual L)
    (hi : IsIrrPlus ρ.dual L s.space.toSubmodule)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : ActionEquiv (s.action.comp L.subtype) (binarySymplectic F))
    (hs : s.space.toSubmodule ⊔ ρ.dual.invariants = ⊤) :
    quadraticRatio ρ ≤ 2 := by
  exact quadraticRatio_le_two_of_dual_fixed_supplement ρ s.space hs
    (symplectic_moved_dual_ratio_le_two s hi F hF e)

/-- The corrected B.5.1 source conclusion supplies Irr⁺; the supplement remains explicit. -/
theorem quadraticRatio_le_two_of_symplectic_source_supplement [Finite D]
    (ρ : Representation (ZMod 2) D V)
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ.dual L)
    (hn : ¬ IsCompl c.sectionData.space.toSubmodule (fixedSpace ρ.dual L))
    (F : BinaryField) (hF : 1 < F.degree)
    (e : ActionEquiv (c.sectionData.action.comp L.subtype) (binarySymplectic F))
    (hs : c.sectionData.space.toSubmodule ⊔ ρ.dual.invariants = ⊤) :
    quadraticRatio ρ ≤ 2 := by
  exact quadraticRatio_le_two_of_symplectic_moved_supplement ρ c.sectionData
    (c.clause_two hn).1 F hF e hs

end CFSG.Quasithin.ChapterB.SourceB513
