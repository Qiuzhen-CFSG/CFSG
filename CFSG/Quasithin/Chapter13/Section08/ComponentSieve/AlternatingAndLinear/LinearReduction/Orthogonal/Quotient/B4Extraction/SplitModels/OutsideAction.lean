module

public import Theory.Alternating.Aut
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Orthogonal.Quotient.Models

/-!
# Outside conjugation in the marked symmetric-eight extension

For the given identifications H ≃ S₈ and K ≃ GL₄(2), an element outside K
acts on K by inverse transpose times an inner automorphism. The identification
of K is kept fixed, and the conjugating element is t⁻¹, as required for the
action on the exchanged constituent of a split restriction.

The three-cycle support argument in `Theory.Alternating.Aut` gives
C_S₈(A₈) = 1. Transporting it to H makes conjugation on K faithful, so an
outside element cannot induce an inner automorphism. The proved binary
linear automorphism coverage then supplies the graph-times-inner formula.

Source: the compatible natural/dual split in Aschbacher–Smith, proof of
13.8.25, printed pp.959–960 (combined manuscript of 1 March 2004).
The automorphism coverage is GLS3, Theorem 2.5.12 and §2.7, as formalized in
`BinaryLinear.OuterCyclic`; see `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction.SplitModels

variable {H : Type*} [Group H]

private theorem centralizer_eq_bot
    (eH : H ≃* Equiv.Perm (Fin 8)) (K : Subgroup H)
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8)) :
    Subgroup.centralizer (K : Set H) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply eH.injective
  rw [map_one]
  apply Subgroup.mem_bot.mp
  rw [← GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 8 (by decide), ← hK]
  exact Subgroup.map_centralizer_le_centralizer_image (K : Set H) eH.toMonoidHom
    (Subgroup.mem_map_of_mem eH.toMonoidHom hx)

/-- Conjugation by t⁻¹ is not inner in the specified GL₄(2) marking when
t lies outside the marked alternating subgroup. -/
theorem outside_conjNormal_ne_inner
    (eH : H ≃* Equiv.Perm (Fin 8)) (K : Subgroup H) [K.Normal]
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (eK : K ≃* BinaryLinear.GL FourSpace) (t : H) (ht : t ∉ K)
    (g : BinaryLinear.GL FourSpace) :
    MulAut.congr eK ((MulAut.conjNormal : H →* MulAut K) t⁻¹) ≠ MulAut.conj g := by
  intro h
  have heq : (MulAut.conjNormal : H →* MulAut K) t⁻¹ =
      MulAut.conj (eK.symm g) := by
    apply (MulAut.congr eK).injective
    rw [MulAut.congr_conj, eK.apply_symm_apply]
    exact h
  have htinv : t⁻¹ = (eK.symm g : H) :=
    MulAut.conjNormal_injective_of_centralizer_eq_bot K (centralizer_eq_bot eH K hK)
      (heq.trans MulAut.conjNormal_val.symm)
  apply ht
  exact K.inv_mem_iff.mp (htinv ▸ (eK.symm g).property)

/-- The precise outside action on the exchanged constituent: with the given
K ≃ GL₄(2) identification, conjugation by t⁻¹ is inverse transpose times inner. -/
theorem outside_conjugation_eq_graph_mul_inner
    (eH : H ≃* Equiv.Perm (Fin 8)) (K : Subgroup H) [K.Normal]
    (hK : K.map eH.toMonoidHom = alternatingGroup (Fin 8))
    (eK : K ≃* BinaryLinear.GL FourSpace) (t : H) (ht : t ∉ K) :
    ∃ g : BinaryLinear.GL FourSpace,
      MulAut.congr eK ((MulAut.conjNormal : H →* MulAut K) t⁻¹) =
        BinaryLinear.OuterCyclic.graphLinear 4 * MulAut.conj g := by
  obtain ⟨g, hg⟩ := BinaryLinear.OuterCyclic.inner_graph (Or.inl rfl)
    (MulAut.congr eK ((MulAut.conjNormal : H →* MulAut K) t⁻¹))
  exact ⟨g, hg.resolve_left (outside_conjNormal_ne_inner eH K hK eK t ht g)⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.OrthogonalQuotient.B4Extraction.SplitModels
