module

public import Theory.GroupTheory.Commutator.PTimesQ
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.Frattini.PGroup

/-!
# Coprime movement and an irreducible Frattini quotient

A prime-to-p actor B commuting with a p-actor U cannot centralize C_T(U)
unless it centralizes the p-group T. When B fixes the Frattini subgroup,
C_T(U) therefore has nonzero image in the Frattini quotient. An irreducible
normalizing action makes that image the whole quotient, and the Frattini
nongenerator property gives C_T(U) = T.

Irreducibility is expressed by its subgroup lattice criterion, using the
actual conjugation action and the ambient image of the Frattini subgroup.
Source: GLS, volume 4, Chapter 2, Lemma 13.4.
-/

namespace Subgroup

/-- The A×B argument followed by irreducibility and Frattini lifting. -/
public theorem commute_of_coprime_frattini_irreducible
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (T U B D : Subgroup G) (hT : IsPGroup p T) (hU : IsPGroup p U)
    (hB : Nat.Coprime p (Nat.card B))
    (hUT : U ≤ normalizer T) (hBT : B ≤ normalizer T)
    (hUB : ⁅U, B⁆ = ⊥) (hmoves : ⁅T, B⁆ ≠ ⊥)
    (hphi : (frattini T).map T.subtype ≤ centralizer (B : Set G))
    (hDT : D ≤ normalizer T) (hDU : D ≤ normalizer U)
    (hirr : ∀ W : Subgroup G, W ≤ T → D ≤ normalizer W →
      W ≤ (frattini T).map T.subtype ∨ W ⊔ (frattini T).map T.subtype = T) :
    ⁅T, U⁆ = ⊥ := by
  let C := T ⊓ centralizer (U : Set G)
  have hDC : D ≤ normalizer C :=
    (le_inf hDT (hDU.trans (normalizer_le_normalizer_centralizer U))).trans
      inf_normalizer_le_normalizer_inf
  have hnphi : ¬ C ≤ (frattini T).map T.subtype := by
    intro h
    exact hmoves (p_times_q_centralizer U B T hU hT hB hUT hBT hUB (h.trans hphi))
  have hsup := (hirr C inf_le_left hDC).resolve_left hnphi
  have hsub : C.subgroupOf T ⊔ frattini T = ⊤ := by
    apply (map_injective T.subtype_injective)
    rw [map_sup, map_subgroupOf_eq_of_le inf_le_left, ← MonoidHom.range_eq_map, range_subtype]
    exact hsup
  have hCT : T ≤ C := subgroupOf_eq_top.mp (frattini_nongenerating hsub)
  exact commutator_eq_bot_iff_le_centralizer.mpr (hCT.trans inf_le_right)


end Subgroup
