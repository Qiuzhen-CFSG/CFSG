module

public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore
public import Mathlib.GroupTheory.Nilpotent

/-!
# The characteristic preimage of the center modulo a prime core

Inside a subgroup B, take the preimage of Z(B/Oₚ(B)), then embed it in
the ambient group. Every normalizer of B preserves this subgroup. Thus
commutators with a subgroup central modulo Oₚ(B) remain in this preimage.
If a second bound places those commutators in a subgroup meeting the
preimage only in Oₚ(B), the required prime-core bound follows.

This separates the characteristic-subgroup argument from any calculation
of a Levi quotient. Source application: Aschbacher–Smith, E.6.25,
printed p.255 of the combined manuscript (1 March 2004).
-/

@[expose] public section

open scoped commutatorElement
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- The preimage of the center modulo the intrinsic prime core, embedded in G. -/
def coreCenterIn (p : ℕ) (B : Subgroup G) : Subgroup G :=
  (upperCentralSeriesStep (pCore p B)).map B.subtype

theorem coreCenterIn_le (p : ℕ) (B : Subgroup G) : B.coreCenterIn p ≤ B :=
  map_subtype_le _

/-- Its defining commutator condition uses only elements of B. -/
theorem mem_coreCenterIn_iff (p : ℕ) (B : Subgroup G) (x : G) :
    x ∈ B.coreCenterIn p ↔ x ∈ B ∧ ∀ b ∈ B, ⁅x, b⁆ ∈ B.pCoreIn p := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, fun b hb => ⟨⁅x, (⟨b, hb⟩ : B)⁆, hx ⟨b, hb⟩, rfl⟩⟩
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    intro b
    obtain ⟨c, hc, he⟩ := hc b b.property
    have he' : c = ⁅(⟨x, hx⟩ : B), b⁆ := Subtype.ext he
    exact he' ▸ hc

/-- Normalization of B suffices; B need not be ambient normal. -/
theorem normalizer_le_normalizer_coreCenterIn (p : ℕ) (B : Subgroup G) :
    normalizer (B : Set G) ≤ normalizer (B.coreCenterIn p : Set G) :=
  normalizer_le_normalizer_characteristic_image B (upperCentralSeriesStep (pCore p B))

/-- Faithful embeddings preserve the characteristic central preimage. -/
theorem map_coreCenterIn_of_injective (p : ℕ) (B : Subgroup G)
    (f : G →* H) (hf : Function.Injective f) :
    (B.coreCenterIn p).map f = (B.map f).coreCenterIn p := by
  have hcore := map_pCoreIn_of_injective p B f hf
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxB, hc⟩ := (mem_coreCenterIn_iff p B x).mp hx
    apply (mem_coreCenterIn_iff p (B.map f) _).mpr
    refine ⟨mem_map_of_mem f hxB, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← hcore, ← map_commutatorElement]
    exact mem_map_of_mem f (hc b hb)
  · intro x hx
    obtain ⟨hxB, hc⟩ := (mem_coreCenterIn_iff p (B.map f) x).mp hx
    obtain ⟨b, hb, rfl⟩ := hxB
    refine ⟨b, (mem_coreCenterIn_iff p B b).mpr ⟨hb, ?_⟩, rfl⟩
    intro c hcB
    have hm := hc (f c) (mem_map_of_mem f hcB)
    rw [← hcore, ← map_commutatorElement] at hm
    obtain ⟨d, hd, he⟩ := hm
    exact (hf he) ▸ hd

/-- An additional kernel bound completes a core bound for central quotient lifts. -/
theorem commutator_le_core_of_coreCenterIn {p : ℕ} {A B Y C : Subgroup G}
    (hA : A ≤ normalizer (B : Set G)) (hY : Y ≤ B.coreCenterIn p)
    (hC : ⁅A, Y⁆ ≤ C) (hsep : B.coreCenterIn p ⊓ C ≤ B.pCoreIn p) :
    ⁅A, Y⁆ ≤ B.pCoreIn p := by
  apply le_trans (le_inf ?_ hC) hsep
  exact (commutator_mono le_rfl hY).trans
    (le_normalizer_iff_commutator_le_right.mp
      (hA.trans (normalizer_le_normalizer_coreCenterIn p B)))

end Subgroup
