module

public import FeitThompson.BGsection1.Defs
public import Theory.PGroupCore

/-!
# Hypotheses of Glauberman's nonabelian Suzuki characterization

These are the nonabelian-Sylow specialization of Corollary 5.1, p. 92, of
Glauberman, *A Characterization of the Suzuki Groups* (1968). The fusion and
centralizer assumptions are exactly conditions (a) and (b), p. 76. Fusion
concerns individual elements, not conjugacy of subgroups.

The elementary reduction below excludes a normal two-complement: it would
lie in the trivial odd core, making the whole group a two-group and its
Sylow subgroup normal. The primary source is stored at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

namespace Glauberman.SuzukiCharacterization

/-- The explicit local assumptions for the nonabelian case of Corollary 5.1. -/
public structure Hypotheses {G : Type*} [Group G] (P : Sylow 2 G) : Prop where
  oddCore_eq_bot : pPrimeCore 2 G = ⊥
  not_normal : ¬ (P : Subgroup G).Normal
  not_commutative : ¬ IsMulCommutative P
  fusion : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), IsConj x y →
    ∃ n ∈ Subgroup.normalizer (P : Set G), n * x * n⁻¹ = y
  involution_complement : ∀ x ∈ (P : Subgroup G), orderOf x = 2 →
    HasNormalPComplement 2 (Subgroup.centralizer ({x} : Set G))

/-- A group satisfying the characterization hypotheses has no normal
two-complement. -/
public theorem Hypotheses.not_hasNormalPComplement {G : Type*} [Group G]
    (P : Sylow 2 G) (h : Hypotheses P) : ¬ HasNormalPComplement 2 G := by
  rintro ⟨N, hN, hcop, hquot⟩
  have hle : N ≤ pPrimeCore 2 G := le_sSup ⟨hN, hcop⟩
  have hbot : N = ⊥ := eq_bot_iff.mpr (h.oddCore_eq_bot ▸ hle)
  subst N
  have hG : IsPGroup 2 G := hquot.of_equiv QuotientGroup.quotientBot
  have hP : (P : Subgroup G) = ⊤ := (P.is_maximal' (hG.to_subgroup ⊤) le_top).symm
  exact h.not_normal (hP ▸ Subgroup.normal_top)

end Glauberman.SuzukiCharacterization
