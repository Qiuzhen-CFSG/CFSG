module

public import Theory.PPrimeCore
public import Theory.GroupAction.NormalComplement

/-!
# The prime-complement core and normal complements

A normal p-complement lies in the p′-core, so the quotient by the core is
an image of a p-group. Extracted from the normal-complement lemmas in
`FeitThompson/BGsection1/PLengthLemmas.lean`, preserving the public interface.
-/

variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
/-- If a finite group has a normal `p`-complement, then quotienting by `𝒪_{p'}(G)` is a `p`-group. -/
public theorem isPGroup_quotient_pPrimeCore_of_hasNormalPComplement
    (H : Type*) [Group H] [Finite H] (hcomp : HasNormalPComplement p H) :
    IsPGroup p (H ⧸ pPrimeCore p H) := by
  let _ := (inferInstance : Finite H)
  rcases hcomp with ⟨N, hNnorm, hNcop, hQp⟩
  let : N.Normal := hNnorm
  have hN_le_core : N ≤ pPrimeCore p H := by
    exact le_sSup ⟨hNnorm, hNcop⟩
  have hN_le_core' : N ≤ (pPrimeCore p H).comap (MonoidHom.id H) := by
    simpa [Subgroup.comap_id] using hN_le_core
  let f : H ⧸ N →* H ⧸ pPrimeCore p H :=
    QuotientGroup.map N (pPrimeCore p H) (MonoidHom.id H) hN_le_core'
  have hf_surj : Function.Surjective f := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro x
    refine ⟨(x : H ⧸ N), ?_⟩
    simp [f]
  exact IsPGroup.of_surjective (hG := hQp) f hf_surj

