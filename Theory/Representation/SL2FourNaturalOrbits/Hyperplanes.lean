module

public import Theory.Representation.SL2FourNaturalOrbits.SelfDual
/-!
# Hyperplane transitivity on the binary natural SL₂(4) module

The invariant trace-determinant pairing identifies the module with its dual.
Every hyperplane is the kernel paired with a nonzero vector, so transitivity
on nonzero vectors gives transitivity on the actual hyperplanes under the
same determinant-one matrices. Both dimension and cardinality formulations
are supplied for consumers.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, proof of
§6.2.5(6), printed p.681 (PDF p.698). This is the natural-module calculation;
the uniqueness of an ambient conjugate containing a hyperplane is separate.
-/

@[expose] public section
noncomputable section
namespace Representation.SL2FourNatural

/-- A binary hyperplane is the kernel paired with a nonzero natural vector. -/
lemma hyperplane_eq_pairing_ker (H : Submodule (ZMod 2) V)
    (hH : Module.finrank (ZMod 2) H = 3) :
    ∃ v : V, v ≠ 0 ∧ H = (selfDual v).ker := by
  have ht : H < ⊤ := by
    apply lt_of_le_of_ne le_top
    intro he
    have hh := hH
    rw [he, finrank_top, finrank_vector] at hh
    omega
  obtain ⟨f,hf,hle⟩ := H.exists_le_ker_of_lt_top ht
  obtain ⟨v,rfl⟩ := selfDual.surjective f
  refine ⟨v, ?_, Submodule.eq_of_le_of_finrank_eq hle ?_⟩
  · intro hv; exact hf (by simp [hv])
  · have hd := Module.Dual.finrank_ker_add_one_of_ne_zero hf
    rw [finrank_vector] at hd
    omega

/-- Actual determinant-one matrices act transitively on binary hyperplanes. -/
lemma transitive_hyperplanes (H K : Submodule (ZMod 2) V)
    (hH : Module.finrank (ZMod 2) H = 3) (hK : Module.finrank (ZMod 2) K = 3) :
    ∃ A : SL, H.map (action A).toLinearMap = K := by
  obtain ⟨v,hv,rfl⟩ := hyperplane_eq_pairing_ker H hH
  obtain ⟨w,hw,rfl⟩ := hyperplane_eq_pairing_ker K hK
  obtain ⟨A,hA⟩ := transitive_nonzero v w hv hw
  refine ⟨A, ?_⟩
  ext z
  constructor
  · rintro ⟨y,hy,rfl⟩
    change selfDual w (action A y) = 0
    rw [← hA, selfDual_equivariant]
    simpa using hy
  · intro hz
    refine ⟨action A⁻¹ z, ?_, by simp⟩
    change selfDual v (action A⁻¹ z) = 0
    change selfDual w z = 0 at hz
    rw [← hA, selfDual_equivariant] at hz
    exact hz

lemma transitive_hyperplanes_card (H K : Submodule (ZMod 2) V)
    (hH : Nat.card H = 8) (hK : Nat.card K = 8) :
    ∃ A : SL, H.map (action A).toLinearMap = K := by
  have rank (U : Submodule (ZMod 2) V) (hU : Nat.card U = 8) :
      Module.finrank (ZMod 2) U = 3 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := U)
    rw [hU, Nat.card_eq_fintype_card, ZMod.card] at hc
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))
      (show 2 ^ 3 = 2 ^ Module.finrank (ZMod 2) U from hc)).symm
  exact transitive_hyperplanes H K (rank H hH) (rank K hK)
end Representation.SL2FourNatural
