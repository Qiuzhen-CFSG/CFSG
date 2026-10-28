module
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction.Action
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.Alignment
public import Theory.GroupAction.CyclicCommutatorTransport

/-!
# Torus action at an arbitrary symplectic Sylow subgroup

An actual inner conjugation aligns the standard unipotent group with the given
Sylow. It transports the Borel, its two-residual, the embedded three-residual
and two-core, and the cyclic automorphism commutator. Composing conjugation of
actors with the standard quotient action defines the torus action at this
Sylow. The concrete residual-fixer condition and the lower bound for the actual
commutator quotient are preserved by the same alignment.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction

private theorem map_coreIn {G H : Type*} [Group G] [Group H]
    (p : ℕ) (B : Subgroup G) (e : G ≃* H) :
    (B.pCoreIn p).map e.toMonoidHom = (B.map e.toMonoidHom).pCoreIn p := by
  calc
    _ = ((pCore p B).map (B.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom).map
        (B.map e.toMonoidHom).subtype := by
      rw [pCoreIn, Subgroup.map_map, Subgroup.map_map]
      rfl
    _ = _ := by rw [pCore_map_iso]; rfl

/-- Transport the literal displacement formulation, including both embedded cores. -/
theorem fixes_residual_transport {G H : Type*} [Group G] [Group H] [Finite G]
    (e : G ≃* H) (a : MulAut G) (B : Subgroup G) :
    (∀ b ∈ (pResidual 3 B).map B.subtype ⊔ B.pCoreIn 2,
      b⁻¹ * a b ∈ B.pCoreIn 2) ↔
    (∀ b ∈ (pResidual 3 (B.map e.toMonoidHom)).map (B.map e.toMonoidHom).subtype ⊔
        (B.map e.toMonoidHom).pCoreIn 2,
      b⁻¹ * MulAut.congr e a b ∈ (B.map e.toMonoidHom).pCoreIn 2) := by
  have hd : ((pResidual 3 B).map B.subtype ⊔ B.pCoreIn 2).map e.toMonoidHom =
      (pResidual 3 (B.map e.toMonoidHom)).map (B.map e.toMonoidHom).subtype ⊔
        (B.map e.toMonoidHom).pCoreIn 2 := by
    rw [Subgroup.map_sup, map_embedded_pResidual, map_coreIn]
  have he (b : G) : e (b⁻¹ * a b) = (e b)⁻¹ * MulAut.congr e a (e b) := by
    simp [MulAut.congr]
  constructor
  · intro h y hy
    obtain ⟨b, hb, rfl⟩ := hd.ge hy
    change (e b)⁻¹ * MulAut.congr e a (e b) ∈ (B.map e.toMonoidHom).pCoreIn 2
    rw [← he]
    exact (map_coreIn 2 B e).le (mem_map_of_mem e.toMonoidHom (h b hb))
  · intro h b hb
    have hm := h (e b) (hd.le (mem_map_of_mem e.toMonoidHom hb))
    rw [← he] at hm
    exact (mem_map_iff_mem e.injective).mp ((map_coreIn 2 B e).ge hm)

variable {F : Type*} [Field F] [Finite F]

/-- Stabilizer of the specified Sylow subgroup in the actual automorphism group. -/
abbrev stabilizerAt (S : Sylow 2 (Sp F)) : Subgroup (MulAut (Sp F)) :=
  MulAction.stabilizer (MulAut (Sp F)) (S : Subgroup (Sp F))

omit [Finite F] in
theorem map_borelAt (S : Sylow 2 (Sp F)) (a : stabilizerAt S) :
    (borelAt S).map a.val.toMonoidHom = borelAt S := by
  have h : (S : Subgroup (Sp F)).map a.val.toMonoidHom = S := a.property
  change (normalizer ((S : Subgroup (Sp F)) : Set (Sp F))).map a.val.toMonoidHom = _
  rw [map_equiv_normalizer_eq, h]
  rfl

theorem map_residualAt (S : Sylow 2 (Sp F)) (a : stabilizerAt S) :
    (residualAt S).map a.val.toMonoidHom = residualAt S := by
  rw [residualAt, map_embedded_pResidual, map_borelAt]

/-- A fixed, actual inner conjugation aligning the standard Sylow with the specified one. -/
def alignment {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) : MulAut (Sp F) :=
  MulAut.conj (Classical.choose (residualAt_conjugate hF hn S))

theorem alignment_unipotent {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) :
    unipotent.map (alignment hF hn S).toMonoidHom = (S : Subgroup (Sp F)) :=
  (Classical.choose_spec (residualAt_conjugate hF hn S)).1

theorem alignment_residual {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) :
    residual.map (alignment hF hn S).toMonoidHom = residualAt S :=
  (Classical.choose_spec (residualAt_conjugate hF hn S)).2.2

theorem alignment_symm_residual {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) :
    (residualAt S).map (alignment hF hn S).symm.toMonoidHom = residual :=
  Theory.GroupAction.OddCommutatorImage.map_symm_of_map_eq _ _ _ (alignment_residual hF hn S)

/-- Conjugation transports the whole Sylow stabilizer, preserving multiplication of actors. -/
def alignActorHom {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) : stabilizerAt S →* stabilizer (F := F) where
  toFun a := ⟨MulAut.congr (alignment hF hn S).symm a.val,
    Theory.GroupAction.OddCommutatorImage.congr_symm_stabilizes _ _ _ _
      (alignment_unipotent hF hn S) a.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

/-- The induced torus action at a specified Sylow subgroup. -/
def torusActionAt {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) : stabilizerAt S →* MulAut (Fˣ × Fˣ) :=
  (torusAction hF).comp (alignActorHom hF hn S)

/-- The concrete source fixer at S transports to the torus three-residual fixer. -/
theorem fixes_residualAt_iff {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (a : stabilizerAt S) :
    (∀ b ∈ (pResidual 3 (residualAt S)).map (residualAt S).subtype ⊔ (residualAt S).pCoreIn 2,
      b⁻¹ * a.val b ∈ (residualAt S).pCoreIn 2) ↔
    ∀ x ∈ pResidual 3 (Fˣ × Fˣ), torusActionAt hF hn S a x = x := by
  rw [fixes_residual_transport (alignment hF hn S).symm a.val (residualAt S),
    alignment_symm_residual]
  exact fixes_residual_iff hF (alignActorHom hF hn S a)

/-- Alignment preserves the actual cyclic commutator quotient for every actor. -/
theorem displacementAt_card_le {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (S : Sylow 2 (Sp F)) (a : stabilizerAt S) :
    Nat.card (torusDisplacement (torusActionAt hF hn S a)).range ≤
      Nat.card (commutatorSubgroup (zpowers a.val) (Sp F) (residualAt S) ⧸
        pCore 2 (commutatorSubgroup (zpowers a.val) (Sp F) (residualAt S))) := by
  have he := Theory.GroupAction.OddCommutatorImage.card_cyclic_commutator_quotient
    (alignment hF hn S).symm a.val (residualAt S)
  dsimp only at he
  rw [alignment_symm_residual] at he
  rw [he]
  exact displacement_card_le hF (alignActorHom hF hn S a)

end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction
