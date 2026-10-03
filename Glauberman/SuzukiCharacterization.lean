module

public import Glauberman.SuzukiCharacterization.Hypotheses
public import Glauberman.SuzukiCharacterization.CentralizerContainment
public import Glauberman.SuzukiCharacterization.Recognition
public import Theory.GroupTheory.SylowCentralizerTrivialIntersection

/-!
# Glauberman's Suzuki characterization for nonabelian Sylow subgroups

For a finite group with trivial odd core and a nonnormal, nonabelian Sylow
two-subgroup, normalizer control of element fusion and normal two-complements
in involution centralizers imply that the group is a Suzuki matrix group.

The character argument supplies centralizer containment. This implies
two-group centralizers and trivial Sylow intersections; the Sylow action
then supplies Suzuki recognition. The nonabelian hypothesis excludes the
elementary-abelian exception in Corollary 5.1.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
Theorem 4.1 and Corollary 5.1, pp. 88–92.
-/

namespace Glauberman.SuzukiCharacterization

/-- The two local geometric consequences of Theorem 4.1(v). -/
public theorem local_geometry_of_centralizer_le
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ (P : Subgroup G)) :
    (∀ x ∈ (P : Subgroup G), x ≠ 1 →
      IsPGroup 2 (Subgroup.centralizer ({x} : Set G))) ∧
    (∀ Q : Sylow 2 G, Q ≠ P → (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥) := by
  exact ⟨fun x hx hne => P.isPGroup'.to_le (hcent x hx hne),
    fun Q hne => P.inf_eq_bot_of_ne_of_centralizer_le Q hcent hne⟩

/-- Glauberman's Corollary 5.1 for a nonabelian Sylow two-subgroup. -/
public theorem Hypotheses.exists_suzuki_equiv
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (h : Hypotheses P) :
    ∃ m : ℕ, 0 < m ∧ Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
  exists_suzuki_equiv_of_centralizer_le P h.oddCore_eq_bot h.not_normal
    h.not_commutative (h.centralizer_le P)

/-- Explicit local hypotheses for the nonabelian case of Glauberman's
Corollary 5.1. The fusion condition concerns individual elements of `P`. -/
public theorem exists_suzuki_equiv
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G)
    (hcore : pPrimeCore 2 G = ⊥)
    (hn : ¬ (P : Subgroup G).Normal)
    (hcomm : ¬ IsMulCommutative P)
    (hfusion : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), IsConj x y →
      ∃ n ∈ Subgroup.normalizer (P : Set G), n * x * n⁻¹ = y)
    (hcomplement : ∀ x ∈ (P : Subgroup G), orderOf x = 2 →
      HasNormalPComplement 2 (Subgroup.centralizer ({x} : Set G))) :
    ∃ m : ℕ, 0 < m ∧ Nonempty (G ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) :=
  Hypotheses.exists_suzuki_equiv P ⟨hcore, hn, hcomm, hfusion, hcomplement⟩

end Glauberman.SuzukiCharacterization
