module
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus

/-!
# Borel and residual quotients at a specified symplectic Sylow subgroup

Conjugating the standard unipotent subgroup onto a specified Sylow subgroup
conjugates its full normalizer and its two-residual as well. The standard
character quotient therefore gives genuine multiplicative equivalences for
both quotients by their two-cores. In the ambient matrix group, these cores
are respectively S and S ∩ O²(N(S)).

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954. This module retains
the residual as defined, without requiring an additional generation proof
that the Borel equals its two-residual.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
variable {F : Type*} [Field F] [Finite F]

/-- The Borel containing a specified Sylow subgroup, as its actual normalizer. -/
abbrev borelAt (S : Sylow 2 (Sp F)) : Subgroup (Sp F) := normalizer (S : Set (Sp F))

/-- The source residual at the specified Sylow subgroup. -/
abbrev residualAt (S : Sylow 2 (Sp F)) : Subgroup (Sp F) :=
  (pResidual 2 (borelAt S)).map (borelAt S).subtype

omit [Finite F] in
private theorem core_map (V : Subgroup (Sp F)) (a : MulAut (Sp F)) :
    (V.pCoreIn 2).map a.toMonoidHom = (V.map a.toMonoidHom).pCoreIn 2 := by
  calc
    _ = ((pCore 2 V).map (V.equivMapOfInjective a.toMonoidHom a.injective).toMonoidHom).map
        (V.map a.toMonoidHom).subtype := by
      rw [pCoreIn, map_map, map_map]
      rfl
    _ = _ := by rw [pCore_map_iso]; rfl

theorem borel_twoCoreIn {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    (borel (F := F)).pCoreIn 2 = unipotent := by
  rw [pCoreIn, twoCore_eq_unipotent hF, map_subgroupOf_eq_of_le]
  intro g hg
  exact (mem_unipotent_iff g).mp hg |>.1

theorem residual_twoCoreIn {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    (residual (F := F)).pCoreIn 2 = unipotent ⊓ residual := by
  rw [pCoreIn, residual_twoCore hF, subgroupOf_map_subtype]

/-- Sylow alignment transports both the Borel and its actual residual. -/
theorem residualAt_conjugate {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) :
    ∃ g : Sp F,
      unipotent.map (MulAut.conj g).toMonoidHom = (S : Subgroup (Sp F)) ∧
      borel.map (MulAut.conj g).toMonoidHom = borelAt S ∧
      residual.map (MulAut.conj g).toMonoidHom = residualAt S := by
  obtain ⟨g, hU, hB⟩ := sylow_normalizer_conjugate hF hn S
  refine ⟨g, hU, hB, ?_⟩
  change ((pResidual 2 borel).map borel.subtype).map _ = _
  rw [map_embedded_pResidual, hB]

theorem borelAt_twoCoreIn {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) : (borelAt S).pCoreIn 2 = (S : Subgroup (Sp F)) := by
  obtain ⟨g, hU, hB⟩ := sylow_normalizer_conjugate hF hn S
  change (normalizer (S : Set (Sp F))).pCoreIn 2 = _
  rw [← hB, ← core_map, borel_twoCoreIn hF, hU]

theorem residualAt_twoCoreIn {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) :
    (residualAt S).pCoreIn 2 = (S : Subgroup (Sp F)) ⊓ residualAt S := by
  obtain ⟨g, hU, _, hR⟩ := residualAt_conjugate hF hn S
  rw [← hR, ← core_map, residual_twoCoreIn hF,
    Subgroup.map_inf _ _ (MulAut.conj g).toMonoidHom (MulAut.conj g).injective, hU]

def residualAtEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) : residualAt S ≃* residual (F := F) := by
  let g := Classical.choose (residualAt_conjugate hF hn S)
  have hR := (Classical.choose_spec (residualAt_conjugate hF hn S)).2.2
  exact (((MulAut.conj g).subgroupMap residual).trans (MulEquiv.subgroupCongr hR)).symm

/-- A genuine multiplicative equivalence for the quotient at the specified Sylow. -/
def borelAtQuotientEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) : borelAt S ⧸ pCore 2 (borelAt S) ≃* (Fˣ × Fˣ) :=
  (QuotientGroup.congr _ _ (sylowNormalizerEquiv hF hn S)
    (pCore_map_iso 2 _)).trans (quotientTorusEquiv hF)

/-- The two-residual at the specified Sylow has the full split torus quotient. -/
def residualAtQuotientEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) : residualAt S ⧸ pCore 2 (residualAt S) ≃* (Fˣ × Fˣ) :=
  (QuotientGroup.congr _ _ (residualAtEquiv hF hn S)
    (pCore_map_iso 2 _)).trans (residualQuotientTorusEquiv hF)

end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
