module

public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The marked residual obstruction in the six-point natural module

Both residual cores of an incident parabolic pair contain a conjugate of
`(23)(45)`. This permutation moves the even-weight vector supported on `{0,2}`
even modulo constants. Thus its fixed space is proper in the four-dimensional
natural module. The literal embedded residual is transported through the same
ambient conjugation as the parabolics.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), final proof of
15.3.1, printed p.1155; the concrete parabolic geometry is I.5.
-/

@[expose] public section

open Subgroup Module Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
namespace BinaryPermutation.LocalResidualSeed

private theorem map_core {G : Type*} [Group G] (e : G ≃* G) (L : Subgroup G) :
    (L.pCoreIn 2).map e.toMonoidHom = (L.map e.toMonoidHom).pCoreIn 2 := by
  let eL : L ≃* L.map e.toMonoidHom := e.subgroupMap L
  rw [pCoreIn, pCoreIn, ← pCore_map_iso 2 eL, map_map, map_map]
  rfl

private def testCore : core (Fin 6) :=
  ⟨Pi.single 0 1 + Pi.single 2 1, by simp [mem_core]; decide⟩

private theorem six_not_fixed (K : Subgroup S6)
    (hk : Equiv.swap 2 3 * Equiv.swap 4 5 ∈ K) :
    fixedSpace (naturalRepresentation (Fin 6)) K ≠ ⊤ := by
  intro h
  let v : natural (Fin 6) :=
    ⟨(constants (Fin 6)).mkQ testCore.val, ⟨testCore.val, testCore.property, rfl⟩⟩
  have hv : v ∈ fixedSpace (naturalRepresentation (Fin 6)) K := by rw [h]; trivial
  obtain ⟨c, hc⟩ := (mem_natural_fixedSpace_iff K testCore).mp hv _ hk
  have h0 := hc 0
  have h2 := hc 2
  norm_num [testCore, Equiv.Perm.mul_apply] at h0 h2
  exact zero_ne_one (h0.trans h2.symm)

private theorem six_fixed_bound (L : Subgroup S6)
    (hL : L = duadHom.range ∨ L = synthemeHom.range) :
    finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6)) (L.pCoreIn 2)) < 4 := by
  have hne : fixedSpace (naturalRepresentation (Fin 6)) (L.pCoreIn 2) ≠ ⊤ := by
    apply six_not_fixed
    rcases hL with rfl | rfl
    · rw [core_range duadHom duadHom_injective]
      decide
    · rw [core_range synthemeHom synthemeHom_injective]
      decide
  have hd := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne le_top hne)
  simpa only [finrank_top, finrank_natural_even (Fin 6) (by decide), Fintype.card_fin] using hd

private theorem six_mapped_bound (g : S6) (H : Subgroup S6)
    (hH : H = duadStabilizer ∨ H = synthemeStabilizer) :
    let P := H.map (MulAut.conj g).toMonoidHom
    finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6))
      (((pResidual 2 P).map P.subtype).pCoreIn 2)) < 4 := by
  dsimp only
  rw [← map_embedded_pResidual 2 H (MulAut.conj g).toMonoidHom, ← map_core]
  rw [← (fixedSpaceConjEquiv (naturalRepresentation (Fin 6))
    (((pResidual 2 H).map H.subtype).pCoreIn 2) g).finrank_eq]
  apply six_fixed_bound
  rcases hH with rfl | rfl
  · exact Or.inl residual_duad
  · exact Or.inr residual_syntheme

/-- The literal residual core of either index-three parabolic fixes fewer than
four dimensions in the natural six-point module. -/
theorem six_residual_fixed_bound (T : Sylow 2 S6) (P₁ P₂ : Subgroup S6)
    (h₁ : (T : Subgroup S6) ≤ P₁) (h₂ : (T : Subgroup S6) ≤ P₂)
    (hi₁ : (T : Subgroup S6).relIndex P₁ = 3)
    (hi₂ : (T : Subgroup S6).relIndex P₂ = 3) (hgen : P₁ ⊔ P₂ = ⊤) :
    finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 6))
      (((pResidual 2 P₁).map P₁.subtype).pCoreIn 2)) < 4 := by
  obtain ⟨g, h | h⟩ := pair_conjugate T P₁ P₂ h₁ h₂ hi₁ hi₂ hgen
  · rcases h with ⟨rfl, rfl⟩
    exact six_mapped_bound g _ (Or.inl rfl)
  · rcases h with ⟨rfl, rfl⟩
    exact six_mapped_bound g _ (Or.inr rfl)

/-- There is no four-dimensional marked residual seed in the natural S₆ module. -/
theorem six (T : Sylow 2 (Equiv.Perm (Fin 6)))
    (P₁ P₂ : Subgroup (Equiv.Perm (Fin 6)))
    (h₁ : (T : Subgroup _) ≤ P₁) (h₂ : (T : Subgroup _) ≤ P₂)
    (hi₁ : (T : Subgroup _).relIndex P₁ = 3)
    (hi₂ : (T : Subgroup _).relIndex P₂ = 3) (hgen : P₁ ⊔ P₂ = ⊤)
    (U : Submodule (ZMod 2) (natural (Fin 6))) (hdim : finrank (ZMod 2) U = 4)
    (hfix : U ≤ fixedSpace (naturalRepresentation (Fin 6))
      (((pResidual 2 P₁).map P₁.subtype).pCoreIn 2))
    (_hcomm : subspaceCommutator (naturalRepresentation (Fin 6)) U
      ((pResidual 2 P₁).map P₁.subtype) = U) : False := by
  have hb := six_residual_fixed_bound T P₁ P₂ h₁ h₂ hi₁ hi₂ hgen
  have hu := Submodule.finrank_mono hfix
  exact (not_le_of_gt hb) (hdim ▸ hu)
end BinaryPermutation.LocalResidualSeed
