module

public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.FixedSpaceCodimension

/-!
# Dimension bounds from conjugate subgroups

Suppose a finite family of conjugates of A generates a subgroup containing L,
and L has no fixed vectors. The fixed spaces of those conjugates have zero
intersection and equal codimension. The codimension inequality for an
intersection therefore bounds the degree by the number of conjugates times
the fixed codimension of A. The conjugates and fixed spaces all belong to the
original ambient action; A need not lie in L.

This is the subgroup form of the conjugate-generation estimate used in
Guralnick–Malle, *Classification of 2F-modules I*, §2, and in
Aschbacher–Smith K.1, printed pp.451–452.
-/

public section
namespace Representation.BinaryOffender
open Subgroup

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Generation by conjugate subgroups bounds the degree through their actual
ambient fixed spaces. -/
theorem finrank_le_card_mul_fixedCodim_of_subgroup_conjugates
    {ι : Type*} [Fintype ι]
    (ρ : Representation (ZMod 2) G V) (L A : Subgroup G)
    (hfix : fixedSpace ρ L = ⊥) (g : ι → G)
    (hgen : L ≤ ⨆ i, A.map (MulAut.conj (g i)).toMonoidHom) :
    Module.finrank (ZMod 2) V ≤ Fintype.card ι * fixedCodim ρ A := by
  let X (i : ι) := A.map (MulAut.conj (g i)).toMonoidHom
  have hz : fixedSpace ρ (⨆ i, X i) = ⊥ := by
    apply le_bot_iff.mp
    rw [← hfix]
    exact ρ.invariants_comp_subtype_antitone hgen
  have he : fixedSpace ρ (⨆ i, X i) = ⨅ i, fixedSpace ρ (X i) :=
    ρ.invariants_comp_iSup X
  have hd := Submodule.finrank_quotient_iInf_le_sum (fun i => fixedSpace ρ (X i))
  rw [← he, hz, Submodule.finrank_quotient] at hd
  simp only [finrank_bot, Nat.sub_zero] at hd
  change Module.finrank (ZMod 2) V ≤ ∑ i, fixedCodim ρ (X i) at hd
  simpa only [X, fixedCodim_map_conj, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_id] using hd

end Representation.BinaryOffender
