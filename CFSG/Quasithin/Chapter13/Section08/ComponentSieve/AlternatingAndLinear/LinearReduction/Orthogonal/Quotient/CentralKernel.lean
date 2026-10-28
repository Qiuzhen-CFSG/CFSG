module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.Models
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.SubrepresentationLattice

/-!
# The central kernel when the quotient is the natural A₈ module

The natural A₈ module has no fixed vectors: its irreducibility would otherwise
make a fixed binary line the whole six-dimensional space. Consequently, if K
centralizes W and U/W has the compatible natural model, then C_U(K)=W. This
identifies the literal quotient by fixed vectors, with its induced K-action,
with U/W.

This is the linear-algebra part of the application of 13.7.6(3) in 13.8.25.
It does not replace Ũ_K by Ũ_H or assume the source nontriviality conclusion.
The subgroup commutator identification and the universal source application
remain separate obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.938–939 and pp.959–960.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient
open Representation Representation.BinaryOffender

private theorem invariants_eq_bot_of_irreducible
    {K E : Type*} [Group K] [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) K E) (hi : τ.IsIrreducible)
    (hdim : Module.finrank (ZMod 2) E ≠ 1) : τ.invariants = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  by_contra hv0
  let S : Subrepresentation τ := {
    toSubmodule := Submodule.span (ZMod 2) {v}
    apply_mem_toSubmodule g := by
      intro x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [map_smul, hv g]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v) }
  have hSne : S ≠ ⊥ := by
    intro he
    have hh : v ∈ S := Submodule.mem_span_singleton_self v
    have hz : v ∈ (⊥ : Subrepresentation τ) := he ▸ hh
    exact hv0 hz
  have hSt : S = ⊤ := (hi.eq_bot_or_eq_top S).resolve_left hSne
  have hs : Submodule.span (ZMod 2) {v} = (⊤ : Submodule (ZMod 2) E) :=
    congrArg Subrepresentation.toSubmodule hSt
  apply hdim
  rw [← finrank_top, ← hs]
  exact finrank_span_singleton hv0

/-- No K*-fixed vectors survive in the actual natural eight-point quotient. -/
theorem eightNatural_fixedSpace_eq_bot
    {H E : Type*} [Group H] [AddCommGroup E] [Module (ZMod 2) E]
    (τ : Representation (ZMod 2) H E) (eH : H ≃* Equiv.Perm (Fin 8))
    (K : Subgroup H) (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hnatural : IsEightNatural τ eH) : fixedSpace τ K = ⊥ := by
  have hzero : fixedSpace (BinaryPermutation.naturalRepresentation (Fin 8))
      (alternatingGroup (Fin 8)) = ⊥ := by
    apply invariants_eq_bot_of_irreducible (BinaryPermutation.alternatingNaturalRepresentation _)
      (BinaryPermutation.alternatingNatural_isIrreducible (by decide))
    rw [BinaryPermutation.finrank_natural_even _ (by decide)]
    decide
  obtain ⟨e, he⟩ := hnatural
  have hm := fixedSpace_map_equivariant τ (BinaryPermutation.naturalRepresentation (Fin 8))
    eH.toMonoidHom e he K
  rw [hK, hzero] at hm
  apply le_bot_iff.mp
  intro v hv
  have hh : e v ∈ (⊥ : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 8))) :=
    hm ▸ Submodule.mem_map_of_mem hv
  apply e.injective
  exact (show e v = 0 from hh).trans (map_zero e).symm

/-- The centralization assumption determines the kernel; it is not assumed
that the extension splits. -/
theorem fixedSpace_eq_of_centralized_submodule
    {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ) (K : Subgroup H)
    (hW : ∀ k ∈ K, ∀ w : W.toSubmodule, W.toRepresentation k w = w)
    (hQ : fixedSpace W.quotientRepresentation K = ⊥) : fixedSpace ρ K = W.toSubmodule := by
  apply le_antisymm
  · intro v hv
    have hq : W.toSubmodule.mkQ v ∈ fixedSpace W.quotientRepresentation K := by
      intro k
      change W.toSubmodule.mkQ (ρ k v) = W.toSubmodule.mkQ v
      exact congrArg W.toSubmodule.mkQ (hv k)
    rw [hQ, Submodule.mem_bot] at hq
    exact (Submodule.Quotient.mk_eq_zero _).mp hq
  · intro v hv k
    exact congrArg Subtype.val (hW k k.property ⟨v, hv⟩)

/-- The actual subrepresentation of K-fixed vectors, for the restricted action. -/
noncomputable def centralKernel
    {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (K : Subgroup H) :
    Subrepresentation (ρ.comp K.subtype) where
  toSubmodule := fixedSpace ρ K
  apply_mem_toSubmodule g v hv := by
    change ρ (g : H) v ∈ fixedSpace ρ K
    have hg : ρ (g : H) v = v := hv g
    rw [hg]
    exact hv

/-- Equivalence of the literal central quotient with the selected quotient,
including equivariance for the same subgroup K. -/
theorem central_quotient_equiv_of_natural
    {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (W : Subrepresentation ρ)
    (eH : H ≃* Equiv.Perm (Fin 8)) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (hnatural : IsEightNatural W.quotientRepresentation eH)
    (hW : ∀ k ∈ K, ∀ w : W.toSubmodule, W.toRepresentation k w = w) :
    ∃ e : (U ⧸ (centralKernel ρ K).toSubmodule) ≃ₗ[ZMod 2] (U ⧸ W.toSubmodule),
      ∀ k : K, ∀ v, e ((centralKernel ρ K).quotientRepresentation k v) =
        W.quotientRepresentation k (e v) := by
  have hfix := fixedSpace_eq_of_centralized_submodule ρ W K hW
    (eightNatural_fixedSpace_eq_bot W.quotientRepresentation eH K hK hnatural)
  let e := Submodule.quotEquivOfEq (centralKernel ρ K).toSubmodule W.toSubmodule hfix
  refine ⟨e, ?_⟩
  intro k v
  obtain ⟨u, rfl⟩ := (centralKernel ρ K).toSubmodule.mkQ_surjective v
  rfl

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient
