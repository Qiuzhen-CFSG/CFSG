module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.Basic

/-!
# Conjugation and the original crossing element

Source: Aschbacher–Smith, proof of 2.5.24, printed p.568. A Frattini
argument corrects x by an element of S. The equalities below recover the
required orbit for the original x, without imposing any new condition on
its square. The same transport proves that x preserves Φ(S), Φ(Φ(S))
and Ω₁(C_S(Φ(S))).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore
universe u
variable {G : Type u} [Group G] {κ : GroupClass.{u}}

/-- Right conjugation is a right action, with the source's multiplication order. -/
theorem rightConjugate_mul (a b : G) (Q : Subgroup G) :
    rightConjugate (a * b) Q = rightConjugate b (rightConjugate a Q) := by
  change Q.conjBy ((a * b)⁻¹) = (Q.conjBy a⁻¹).conjBy b⁻¹
  rw [mul_inv_rev, conjBy_mul]

theorem rightConjugate_one (Q : Subgroup G) : rightConjugate 1 Q = Q := by
  change Q.conjBy ((1 : G)⁻¹) = Q
  rw [inv_one, conjBy_one]

theorem rightConjugate_inv_cancel (a : G) (Q : Subgroup G) :
    rightConjugate a⁻¹ (rightConjugate a Q) = Q := by
  rw [← rightConjugate_mul, mul_inv_cancel, rightConjugate_one]

/-- Correcting x on the right by s gives an orbit witness s⁻¹ for the original x. -/
theorem orbit_eq_of_right_correction {x s : G} {Q : Subgroup G}
    (h : x * s ∈ normalizer (Q : Set G)) :
    rightConjugate x Q = rightConjugate s⁻¹ Q := by
  have he : rightConjugate (x * s) Q = Q :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (Q : Set G)).inv_mem h)
  have hi := congrArg (rightConjugate s⁻¹) he
  rwa [rightConjugate_mul, rightConjugate_inv_cancel] at hi

/-- The converse makes the Frattini correction explicit, with no square hypothesis. -/
theorem right_correction_mem_normalizer {x s : G} {Q : Subgroup G}
    (h : rightConjugate x Q = rightConjugate s Q) :
    x * s⁻¹ ∈ normalizer (Q : Set G) := by
  have he : rightConjugate (x * s⁻¹) Q = Q := by
    rw [rightConjugate_mul, h, rightConjugate_inv_cancel]
  exact (normalizer (Q : Set G)).inv_mem_iff.mp
    (mem_normalizer_iff_map_conj_eq.mpr he)

variable [Finite G]

theorem hasNormalizerOrbit_of_correction (d : EarlierSetup κ G)
    (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) [IsKleinFour E]
    (s : G) (hs : s ∈ d.S) (hx : d.x * s ∈ normalizer (localCore d E : Set G)) :
    HasNormalizerOrbit d :=
  ⟨E, hE, inferInstance, s⁻¹, d.S.inv_mem hs, orbit_eq_of_right_correction hx⟩

omit [Finite G] in
theorem phi_map (A : Subgroup G) (e : G ≃* G) :
    (phi A).map e.toMonoidHom = phi (A.map e.toMonoidHom) := by
  let eA : A ≃* A.map e.toMonoidHom := e.subgroupMap A
  calc
    (phi A).map e.toMonoidHom =
        ((frattini A).map eA.toMonoidHom).map (A.map e.toMonoidHom).subtype := by
      unfold phi
      rw [map_map, map_map]
      rfl
    _ = phi (A.map e.toMonoidHom) :=
      congrArg (Subgroup.map (A.map e.toMonoidHom).subtype) (frattini_map_equiv eA)

omit [Finite G] in
theorem rightConjugate_phi (a : G) (A : Subgroup G) :
    rightConjugate a (phi A) = phi (rightConjugate a A) :=
  phi_map A (MulAut.conj a⁻¹)

omit [Finite G] in
private theorem centralizer_map (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set G) := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩ c ⟨c, hc, rfl⟩
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e (hb c hc)
  · intro ha
    refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
    intro b hb
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using ha (e b) ⟨b, hb, rfl⟩

omit [Finite G] in
/-- Transport the actual relative centralizer in S. -/
theorem rightConjugate_relativeCentralizer (a : G) (S A : Subgroup G) :
    rightConjugate a (S ⊓ centralizer (A : Set G)) =
      rightConjugate a S ⊓ centralizer (rightConjugate a A : Set G) := by
  unfold rightConjugate
  rw [map_inf _ _ _ (MulAut.conj a⁻¹).injective, centralizer_map]

theorem crossing_phi (d : EarlierSetup κ G) :
    rightConjugate d.x (phi d.S) = phi d.S := by
  rw [rightConjugate_phi, d.rightConjugate_s]

theorem crossing_phi_phi (d : EarlierSetup κ G) :
    rightConjugate d.x (phi (phi d.S)) = phi (phi d.S) := by
  rw [rightConjugate_phi, crossing_phi]

theorem crossing_plus (d : EarlierSetup κ G) : rightConjugate d.x (plus d) = plus d := by
  change (omegaOneAmbient _).map (MulAut.conj d.x⁻¹).toMonoidHom = _
  rw [map_omegaOneAmbient_injective _ (MulAut.conj d.x⁻¹).injective]
  change omegaOneAmbient (rightConjugate d.x _) = _
  rw [rightConjugate_relativeCentralizer, d.rightConjugate_s, crossing_phi]
  rfl

/-- Equality of the orbits of a subgroup implies equality of the orbits
of its relative centralizer. This handles the E₁S_C branch of the source. -/
theorem centralizer_orbit (d : EarlierSetup κ G) (A : Subgroup G)
    (s : G) (hs : s ∈ d.S)
    (h : rightConjugate d.x A = rightConjugate s A) :
    rightConjugate d.x (d.S ⊓ centralizer (A : Set G)) =
      rightConjugate s (d.S ⊓ centralizer (A : Set G)) := by
  have hsS : rightConjugate s d.S = d.S :=
    mem_normalizer_iff_map_conj_eq.mp (d.S.le_normalizer (d.S.inv_mem hs))
  rw [rightConjugate_relativeCentralizer, rightConjugate_relativeCentralizer,
    d.rightConjugate_s, hsS, h]

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore
