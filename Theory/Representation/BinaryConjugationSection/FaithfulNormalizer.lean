module
public import Theory.Representation.BinaryConjugationSection
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Centralizing normalizers on marked binary sections

A centralizer of the original numerator acts trivially on every marked
quotient, including quotients with nonzero fixed kernel. If such an element
normalizes the actor, its commutators with that actor also centralize the
numerator. Faithfulness of the marked action can therefore detect those
commutators in an actor quotient without discarding any fixed vectors.
-/

public section
namespace Representation.BinaryConjugationSection
open Subgroup
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {L W Z : Subgroup G} {ρ : Representation (ZMod 2) L V}
  (s : BinaryConjugationSection L W Z ρ)
include s

/-- Centralizing the numerator kills the action on its marked quotient. -/
theorem action_eq_one_of_centralizes {l : L}
    (hl : (l : G) ∈ centralizer (W : Set G)) : ρ l = 1 := by
  apply LinearMap.ext
  intro v
  obtain ⟨w,hw⟩ := s.onto (Multiplicative.ofAdd v)
  have hc : (⟨(l : G)*w*(l : G)⁻¹,
      (mem_normalizer_iff.mp (s.normalized l.property) w).mp w.property⟩ : W) = w := by
    apply Subtype.ext
    change (l : G)*w*(l : G)⁻¹ = (w : G)
    rw [←hl w w.property,mul_inv_cancel_right]
  have he := s.equivariant l w
  rw [hc,hw] at he
  exact he.symm

/-- A centralizing normalizer has trivial commutator action on the section. -/
theorem normalizer_commutator_action_eq_one {y : G}
    (hyL : y ∈ normalizer (L : Set G)) (hyW : y ∈ centralizer (W : Set G))
    (l : L) :
    ρ ⟨y*l*y⁻¹*(l : G)⁻¹,
      L.mul_mem ((mem_normalizer_iff.mp hyL l).mp l.property) (L.inv_mem l.property)⟩ = 1 := by
  apply s.action_eq_one_of_centralizes
  have hn := normalizer_le_normalizer_centralizer W (s.normalized l.property)
  have hh := (centralizer (W : Set G)).mul_mem hyW
    ((mem_normalizer_iff.mp hn y⁻¹).mp ((centralizer _).inv_mem hyW))
  simpa only [mul_assoc] using hh
end Representation.BinaryConjugationSection
