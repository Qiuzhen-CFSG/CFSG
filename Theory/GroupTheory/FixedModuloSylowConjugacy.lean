module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Aligning a vector fixed modulo a normal subgroup

Two relative Sylow subgroups of K are conjugate by an element of K.
If one fixes u modulo a K-invariant subgroup Z, the conjugate of u is
fixed modulo Z by the other. All conjugation is left conjugation.
We also transport a Sylow subgroup centralizing a conjugate of u back
into its own centralizer.

Source application: Aschbacher--Smith 14.6.17, printed p.1036.
-/

public section
open Subgroup
open scoped Pointwise commutatorElement
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Sylow conjugacy aligns a fixed vector in the same original ambient group. -/
theorem exists_relative_sylow_fixed_conjugate
    (K : Subgroup G) (P Q : Sylow p K) (Z : Subgroup G)
    (hn : K ≤ normalizer (Z : Set G)) (u : G)
    (hfixed : ∀ q ∈ (Q : Subgroup K).map K.subtype, ⁅u,q⁆ ∈ Z) :
    ∃ g ∈ K, ∀ s ∈ (P : Subgroup K).map K.subtype,
      ⁅(MulAut.conj g) u,s⁆ ∈ Z := by
  obtain ⟨g,rfl⟩ := MulAction.exists_smul_eq K Q P
  refine ⟨g,g.property,?_⟩
  rintro s ⟨s,hs,rfl⟩
  obtain ⟨q,hq,rfl⟩ := hs
  change ⁅(MulAut.conj (g : G)) u,(MulAut.conj (g : G)) (q : G)⁆ ∈ Z
  have hm : (MulAut.conj (g : G)) ⁅u,(q : G)⁆ ∈ Z :=
    ((hn g.property) _).mp (hfixed _ (mem_map_of_mem K.subtype hq))
  have he : ⁅(MulAut.conj (g : G)) u,(MulAut.conj (g : G)) (q : G)⁆ =
      (MulAut.conj (g : G)) ⁅u,(q : G)⁆ := by
    simp only [commutatorElement_def, map_mul, map_inv]
  rwa [he]

omit [Finite G] [Fact p.Prime] in
/-- Conjugacy to a Sylow-central element makes an element p-central. -/
theorem exists_sylow_le_centralizer_of_isConj
    (T : Sylow p G) (u z : G)
    (hz : z ∈ centralizer (T : Set G)) (hc : IsConj u z) :
    ∃ S : Sylow p G, (S : Subgroup G) ≤ centralizer ({u} : Set G) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  refine ⟨g⁻¹ • T, ?_⟩
  intro x hx
  obtain ⟨y,hy,rfl⟩ := hx
  apply mem_centralizer_singleton_iff.mpr
  have hzy := hz y hy
  change y * z = z * y at hzy
  rw [← hg] at hzy
  change (g⁻¹ * y * (g⁻¹)⁻¹) * u = u * (g⁻¹ * y * (g⁻¹)⁻¹)
  simp only [inv_inv]
  calc
    _ = g⁻¹ * (y * (g * u * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * u * g⁻¹) * y) * g := by rw [hzy]
    _ = _ := by group

end Theory.GroupTheory
