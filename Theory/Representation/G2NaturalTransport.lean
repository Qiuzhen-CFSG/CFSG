module

public import Theory.Representation.G2NaturalTransitivity
public import Theory.Representation.FirstCohomologyG2Natural.Commutant
public import Theory.Representation.CentralCoverOriginalAction.Quadratic

/-!
# Transport of the natural derived G₂ action

The additive scalar-commutant calculation forces every binary normalizer to
be semilinear over the coefficient field. We transport this conclusion and
nonzero-vector transitivity through an actual group and module isomorphism.
For an ambient normal subgroup, its conjugation action supplies the normalizer
hypothesis; no automorphism of the model is substituted for the original actor.
The actual derived group is used throughout, including over F₂.

Source: Aschbacher--Smith, I.2.3, printed p.413, and the natural-module
applications in B.4.6, pp.88--90. The imported octonion model and commutant
calculations retain their ATLAS attribution.
-/

@[expose] public section

open Representation
open Representation.OneCohomology.CentralCoverOriginalAction
namespace Atlas.G2.Natural.Transport
variable {F H N : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group H] [AddCommGroup N] [Module (ZMod 2) N]
noncomputable section

omit [Algebra (ZMod 2) F] in
theorem fixed_eq_zero [Finite F] (v : Space F)
    (hv : ∀ g : commutator (Model F), derivedAction F g v = v) : v = 0 := by
  by_contra hv0
  have hs : (⊤ : Submodule F (Space F)) ≤ F ∙ v := by
    intro w _
    by_cases hw : w = 0
    · subst w; exact Submodule.zero_mem _
    · obtain ⟨g, hg⟩ := derivedAction_transitive F v w hv0 hw
      rw [← hg, hv]
      exact Submodule.mem_span_singleton_self v
  have hd := Submodule.finrank_mono hs
  rw [finrank_top, finrank_space, finrank_span_singleton hv0] at hd
  omega

variable (ρ : Representation (ZMod 2) H N)
  (e : H ≃* commutator (Model F)) (E : N ≃ₗ[ZMod 2] Space F)
  (hE : ∀ h v, E (ρ h v) = derivedAction F (e h) (E v))

include hE in
theorem scalar_commutant (f : N →+ N) (hf : ∀ h v, f (ρ h v) = ρ h (f v)) :
    ∃ c : F, ∀ v, E (f v) = c • E v := by
  let f' : Space F →+ Space F :=
    E.toAddEquiv.toAddMonoidHom.comp (f.comp E.symm.toAddEquiv.toAddMonoidHom)
  have hinv (g : commutator (Model F)) (v : Space F) :
      E.symm (derivedAction F g v) = ρ (e.symm g) (E.symm v) := by
    apply E.injective
    simp only [E.apply_symm_apply, hE, e.apply_symm_apply]
  obtain ⟨c, hc⟩ := exists_scalar_of_additive_commutes_derived f' (by
    intro g v
    change E (f (E.symm (derivedAction F g v))) =
      derivedAction F g (E (f (E.symm v)))
    rw [hinv, hf, hE, e.apply_symm_apply])
  refine ⟨c, fun v => ?_⟩
  have hh := hc (E v)
  change E (f (E.symm (E v))) = c • E v at hh
  simpa only [E.symm_apply_apply] using hh

include hE in
theorem marked_semilinear [Finite F] (a : MulAut H) (u : N ≃ₗ[ZMod 2] N)
    (hu : ∀ h v, u (ρ h v) = ρ (a h) (u v)) :
    ∃ s : F ≃+* F, ∀ c v,
      E (u (E.symm (c • E v))) = s c • E (u v) := by
  let : Nontrivial (Space F) := Module.nontrivial_of_finrank_pos
    (by rw [finrank_space]; decide : 0 < Module.finrank F (Space F))
  let a' : MulAut (commutator (Model F)) := e.symm.trans (a.trans e)
  let u' : Space F ≃ₗ[ZMod 2] Space F := E.symm.trans (u.trans E)
  have hu' : ∀ g v, u' (derivedAction F g v) = derivedAction F (a' g) (u' v) := by
    intro g v
    have hinv : E.symm (derivedAction F g v) = ρ (e.symm g) (E.symm v) := by
      apply E.injective
      simp only [E.apply_symm_apply, hE, e.apply_symm_apply]
    change E (u (E.symm (derivedAction F g v))) = _
    rw [hinv, hu, hE]
    rfl
  obtain ⟨s, hs⟩ := normalizer_semilinear (derivedAction F)
    exists_scalar_of_additive_commutes_derived a' u' hu'
  refine ⟨s, fun c v => ?_⟩
  simpa only [u', LinearEquiv.trans_apply, E.symm_apply_apply] using hs c (E v)
end
end Atlas.G2.Natural.Transport

namespace Atlas.G2.Natural.Transport
open Representation
open Representation.OneCohomology.CentralCoverOriginalAction
noncomputable section
variable {F H N : Type*} [Field F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group H] [AddCommGroup N] [Module (ZMod 2) N]
variable (ρ : Representation (ZMod 2) H N)
  (e : H ≃* commutator (Model F)) (E : N ≃ₗ[ZMod 2] Space F)
  (hE : ∀ h v, E (ρ h v) = derivedAction F (e h) (E v))
include hE

theorem transitive [Finite F] {v w : N} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ h : H, ρ h v = w := by
  obtain ⟨g, hg⟩ := derivedAction_transitive F (E v) (E w)
    (fun hh => hv (E.map_eq_zero_iff.mp hh))
    (fun hh => hw (E.map_eq_zero_iff.mp hh))
  refine ⟨e.symm g, E.injective ?_⟩
  rw [hE, e.apply_symm_apply, hg]


end
end Atlas.G2.Natural.Transport

namespace Atlas.G2.Natural.Transport
open Representation Representation.OneCohomology.CentralCoverOriginalAction
noncomputable section
variable {F G N : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group G] [AddCommGroup N] [Module (ZMod 2) N]

theorem ambient_semilinear (H : Subgroup G) [H.Normal]
    (η : Representation (ZMod 2) G N)
    (e : H ≃* commutator (Model F)) (E : N ≃ₗ[ZMod 2] Space F)
    (hE : ∀ h : H, ∀ v, E (η h v) = derivedAction F (e h) (E v)) (g : G) :
    ∃ s : F ≃+* F, ∀ c v,
      E (η g (E.symm (c • E v))) = s c • E (η g v) := by
  apply marked_semilinear (η.comp H.subtype) e E hE (normalConjugation H g) (actorEquiv η g)
  intro h v
  change η g (η h v) = η (g * h * g⁻¹) (η g v)
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  group
end
end Atlas.G2.Natural.Transport
