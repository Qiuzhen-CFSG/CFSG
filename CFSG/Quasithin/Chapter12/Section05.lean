module

public import Theory.GroupTheory.ElementFusionTransport

/-!
# Eliminating L₅(2) on the ten-dimensional module: fusion transport

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, §12.5, printed pp. 816–822 (PDF pp. 833–839).
The proof of Theorem 12.5.1 continues onto p. 822.

The terminal source theorem says that, under Hypothesis 12.2.3, if
`L/O₂(L)` is L₅(2), then `V` is its natural module. Its proof eliminates the
ten-dimensional exterior-square alternative of Theorem 12.2.2.

This module currently supplies the transport step of Lemma 12.5.9(4) and its
local-core consequence used on p. 822. Fusion in the orbit of the involution
`z` is controlled by `L`; adjusting a conjugator by `L` makes it centralize
`z`. Abelian generation and local normality then give commutation and
containment. In the source, `V₁ = ⟨z⟩`, `G₁ = C_G(z)`,
`U = ⟨V^{G₁}⟩` and the local core is `O₂(G₁)`.

The fusion premise is supplied by 12.5.9(3), and the abelian-generation and
core-containment premises by 12.5.8. These results, the exterior-square
calculations, the local-overgroup analysis and the final contradiction still
require proof. The theorem below is a conditional group-theoretic helper,
not an assertion of Theorem 12.5.1 or of the full Lemma 12.5.9.
-/

namespace CFSG.Quasithin.Chapter12.Section05

open Subgroup

/-- The simultaneous transport, commutation and local-core consequence needed
in 12.5.9(4) and the terminal argument. Normality is relative to `C_G(z)`. -/
public theorem conjugate_transport_of_controlled_fusion
    {G : Type*} [Group G] {V L Q : Subgroup G} {z g : G}
    (hL : L ≤ normalizer (V : Set G))
    (hfusion : ∀ a : G, MulAut.conj a z ∈ V →
      ∃ l ∈ L, MulAut.conj a z = MulAut.conj l z)
    [IsMulCommutative (centralizerConjugateClosure V z)]
    (hVQ : V ≤ Q)
    (hQ : centralizer ({z} : Set G) ≤ normalizer (Q : Set G))
    (hg : z ∈ V.map (MulAut.conj g).toMonoidHom) :
    (∃ c : centralizer ({z} : Set G),
      V.map (MulAut.conj (c : G)).toMonoidHom =
        V.map (MulAut.conj g).toMonoidHom) ∧
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
    V.map (MulAut.conj g).toMonoidHom ≤ Q := by
  have hf : ∀ a : G, MulAut.conj a z ∈ V →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n z = MulAut.conj a z := by
    intro a ha
    obtain ⟨l, hl, he⟩ := hfusion a ha
    exact ⟨l, hL hl, he.symm⟩
  exact ⟨exists_centralizer_conjugator_of_element_fusion hf hg,
    commutator_eq_bot_of_element_fusion_of_abelian_closure hf hg,
    conjugate_le_of_element_fusion_of_normalized hf hVQ hQ hg⟩

end CFSG.Quasithin.Chapter12.Section05
