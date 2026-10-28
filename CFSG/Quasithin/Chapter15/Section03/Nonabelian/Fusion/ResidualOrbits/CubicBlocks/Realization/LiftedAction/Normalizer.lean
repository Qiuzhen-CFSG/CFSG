module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.Splitting
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
/-!
# Lifting the two linear factors through a cubic normalizer

Each complementary cubic is normal in the product actor. The coprime
quotient normalizer theorem therefore makes its actual normalizer in I
surject onto that actor. The kernel is the actual P, giving I = P N_I(D).
This is the Frattini step in the lifted tensor action, not an assumption
that a chosen abstract extension splits.

Source: Aschbacher–Smith, 15.3.54 and 15.3.61(2), pp.1146,1150–1151.
-/

public section
open Subgroup Matrix
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization

theorem complementaryCubic_normal (i : Fin 2) : (complementaryCubic i).Normal := by
  have hc : ∀ (j : Fin 2) (a : Actor),
      a * complementaryRotation j * a⁻¹ = complementaryRotation j ∨
      a * complementaryRotation j * a⁻¹ = (complementaryRotation j)⁻¹ := by decide +kernel
  refine ⟨?_⟩
  intro x hx a
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hx
  change MulAut.conj a (complementaryRotation i ^ n) ∈ _
  rw [map_zpow]
  change (a * complementaryRotation i * a⁻¹) ^ n ∈ _
  rcases hc i a with h | h <;> rw [h]
  · exact zpow_mem (mem_zpowers _) _
  · exact zpow_mem (inv_mem (mem_zpowers _)) _

variable {G : Type*} [Group G] [Finite G] {I Y P V : Subgroup G}
  {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
  [(V.subgroupOf P).Normal]

theorem exists_normalizer_actor (d : LayerActions I Y P V hIP hIV)
    (hPI : P ≤ I) (hVP : V ≤ P) (i : Fin 2) (D : Subgroup G)
    (hDI : D ≤ I) (hD : Nat.card D = 3)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i) (a : Actor) :
    ∃ n : I, (n : G) ∈ normalizer (D : Set G) ∧ d.actor n = a := by
  have hcard : Nat.card (D.subgroupOf I) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hDI).toEquiv).trans hD
  let _ : Fact (IsPGroup 3 (D.subgroupOf I)) :=
    ⟨IsPGroup.of_card (p := 3) (n := 1) (by simpa using hcard)⟩
  have hcop : Nat.Coprime 3 (Nat.card d.actor.ker) := by
    rw [d.kernel, Nat.card_congr (subgroupOfEquivOfLe hPI).toEquiv, d.card_core hVP]
    decide
  have hn := normalizer_map_eq_of_coprime_kernel 3 (D.subgroupOf I) d.actor d.onto hcop
  rw [himage] at hn
  let _ := complementaryCubic_normal i
  rw [normalizer_eq_top] at hn
  obtain ⟨n, hn, he⟩ := (show a ∈ (normalizer (D.subgroupOf I : Set I)).map d.actor by
    rw [← hn]; trivial)
  refine ⟨n, ?_, he⟩
  exact (show n ∈ (normalizer (D : Set G)).subgroupOf I from
    (subgroupOf_normalizer_eq hDI).symm ▸ hn)

theorem factor_through_cubic_normalizer (d : LayerActions I Y P V hIP hIV)
    (hPI : P ≤ I) (hVP : V ≤ P) (i : Fin 2) (D : Subgroup G)
    (hDI : D ≤ I) (hD : Nat.card D = 3)
    (himage : (D.subgroupOf I).map d.actor = complementaryCubic i) (g : I) :
    ∃ p : P, ∃ n : I, (n : G) ∈ normalizer (D : Set G) ∧ (g : G) = p * n := by
  obtain ⟨n, hn, he⟩ := exists_normalizer_actor d hPI hVP i D hDI hD himage (d.actor g)
  have hp : (g / n : I) ∈ d.actor.ker := by
    change d.actor (g / n) = 1
    rw [map_div, he, div_self']
  rw [d.kernel] at hp
  exact ⟨⟨(g : G) / n, hp⟩, n, hn, (div_mul_cancel (g : G) n).symm⟩
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
