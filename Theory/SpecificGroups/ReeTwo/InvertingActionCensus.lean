module

public import Theory.SpecificGroups.ReeTwo.InvertingActionRepresentatives

/-!
# Exhaustive census of inverting squaring actions on the Ree core

There are exactly twenty automorphisms squaring the specified order-five
action and taking root 2 to its inverse. They are the explicit root tables
in `InvertingActionRepresentatives`; each also has fourth power one.

The reconstruction theorem reduces an arbitrary action to the image of
root 0. Among the 1024 possible coordinate codes, its square, the square
relation for root 1, and the identity `c (root 1) = root 3` restrict that
image to twenty codes. Both this exhaustive finite check and the agreement
of the reconstructed root images with the displayed tables are checked by
the kernel. Exhaustion is literal equality, so the requested conjugation
classification follows using the identity conjugator.

Source: direct finite certificates in the verified Shinoda (1975), (2.3),
core coordinates and complement action from `Core` and `RootAction`.
-/

@[expose] public section
namespace ReeTwo.Core.InvertingActionCensus
open CensusPacked

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem seed_exhaustion : ∀ n : Fin 1024,
    pmul n.val n.val = 0 →
    pmul (imageCodes n.val 1) (imageCodes n.val 1) = imageCodes n.val 5 →
    imageCodes n.val 3 = (cAct^[2]) (imageCodes n.val 1) →
    ∃ i : Fin 20, n.val = seedCode i := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
private theorem imageCodes_seed : ∀ (i : Fin 20) (j : CoreRoot),
    imageCodes (seedCode i) j = representativeCodes i j := by
  decide +kernel

/-- Every squaring action that inverts the middle root is literally one of the
listed twenty automorphisms. The fourth-power condition is automatic. -/
theorem exhaustive_of_conj_c_root_two (β : MulAut Core)
    (hc : β * c * β⁻¹ = c ^ 2) (ht : β (root 2) = (root 2)⁻¹) :
    ∃ i : Fin 20, β = representative i := by
  have hi := aut_images_code β hc ht
  have hs0 : pmul (code (β (root 0))) (code (β (root 0))) = 0 := by
    rw [pmul_code, ← map_mul, show root 0 * root 0 = 1 from by decide +kernel, map_one]
    rfl
  have hs1 : pmul (imageCodes (code (β (root 0))) 1)
      (imageCodes (code (β (root 0))) 1) = imageCodes (code (β (root 0))) 5 := by
    rw [← hi 1, ← hi 5, pmul_code, ← map_mul]
    congr 2
  have hc1 : imageCodes (code (β (root 0))) 3 =
      (cAct^[2]) (imageCodes (code (β (root 0))) 1) := by
    have hroot : c (root 1) = root 3 := by
      apply code_injective
      exact (cRoots_eq 1).symm
    calc
      imageCodes (code (β (root 0))) 3 = code (β (root 3)) := (hi 3).symm
      _ = code (β (c (root 1))) := (congrArg (fun x => code (β x)) hroot).symm
      _ = code ((c ^ 2) (β (root 1))) := congrArg code (squaring_apply β c hc (root 1))
      _ = (cAct^[2]) (code (β (root 1))) := (cAct_iterate_code 2 _).symm
      _ = (cAct^[2]) (imageCodes (code (β (root 0))) 1) := congrArg (cAct^[2]) (hi 1)
  obtain ⟨i, hi0⟩ := seed_exhaustion ⟨code (β (root 0)), code_lt _⟩ hs0 hs1 hc1
  change code (β (root 0)) = seedCode i at hi0
  refine ⟨i, aut_ext (fun j => code_injective ?_)⟩
  rw [hi j, hi0, imageCodes_seed, representative_root, representativeRoots_code]

/-- Exhaustion with exactly the hypotheses of an inverting squaring action. -/
theorem exhaustive (β : MulAut Core) (_hfour : β ^ 4 = 1)
    (hc : β * c * β⁻¹ = c ^ 2) (ht : β (root 2) = (root 2)⁻¹) :
    ∃ i : Fin 20, β = representative i :=
  exhaustive_of_conj_c_root_two β hc ht

/-- The census also supplies the requested conjugation orientation. -/
theorem exhaustive_conjugate (β : MulAut Core) (hfour : β ^ 4 = 1)
    (hc : β * c * β⁻¹ = c ^ 2) (ht : β (root 2) = (root 2)⁻¹) :
    ∃ (i : Fin 20) (γ : MulAut Core), γ * β * γ⁻¹ = representative i := by
  obtain ⟨i, rfl⟩ := exhaustive β hfour hc ht
  exact ⟨i, 1, by simp⟩

/-- The twenty displayed actions are pairwise distinct. -/
theorem representative_injective : Function.Injective representative := by
  intro i j hij
  have he := congrArg (fun f : MulAut Core => code (f (root 0))) hij
  simp only [representative_root, representativeRoots_code] at he
  exact (by decide +kernel : ∀ i j : Fin 20,
    representativeCodes i 0 = representativeCodes j 0 → i = j) i j he

end ReeTwo.Core.InvertingActionCensus
