module

public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!+# Covering a residual by a subgroup with a matching core quotient

If K/Oₚ(K) is p-perfect, Oᵖ(K) surjects onto this quotient. Its order
therefore bounds the quotient order from below. Since the embedded Oᵖ(K)
lies in Oᵖ(G), equality of the latter's order with |K/Oₚ(K)| forces
Oᵖ(G) ≤ K. No normality of K is needed.

For an actual image I⁺ in G/Oₚ(G), the restriction I → I⁺ has p-group
kernel. The induced isomorphism modulo the p-cores transfers the preceding
argument. In particular, matching isomorphisms of Oᵖ(G/Oₚ(G)) and
I/Oₚ(I) to a p-perfect model give the literal quotient cover.

Source application: Aschbacher–Smith, *The Classification of Quasithin
Groups*, combined manuscript (1 March 2004), Lemma 8.2.9, printed p.720
(PDF p.737), the L₂(4) alternative in the M₂₄ cocode branch.
-/

public section
namespace Subgroup
noncomputable section
variable {G : Type*} [Group G] [Finite G] {p : ℕ}

/-- A p-perfect core quotient as large as the ambient residual covers that residual. -/
theorem pResidual_le_of_pCoreQuotient_card (K : Subgroup G)
    (hp : pResidual p (K ⧸ pCore p K) = ⊤)
    (hc : Nat.card (pResidual p G) ≤ Nat.card (K ⧸ pCore p K)) :
    pResidual p G ≤ K := by
  let q := QuotientGroup.mk' (pCore p K)
  let f := q.comp (pResidual p K).subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype,
      map_pResidual_of_surjective p q (QuotientGroup.mk'_surjective _), hp]
  have hcard := Nat.card_le_card_of_surjective f hf
  let D := (pResidual p K).map K.subtype
  have hD : D = pResidual p G := by
    apply eq_of_le_of_card_ge (map_pResidual_le p K.subtype)
    rw [card_map_of_injective K.subtype_injective]
    exact hc.trans hcard
  exact hD ▸ map_subtype_le _

/-- Matching actual model isomorphisms give a cover in the literal p-core quotient. -/
theorem quotient_residual_le_of_matching_pPerfect_model
    (I : Subgroup G) {S : Type*} [Group S] [Fact p.Prime]
    (hS : pResidual p S = ⊤)
    (eI : (I ⧸ pCore p I) ≃* S)
    (eR : pResidual p (G ⧸ pCore p G) ≃* S) :
    pResidual p (G ⧸ pCore p G) ≤ I.map (QuotientGroup.mk' (pCore p G)) := by
  let q := QuotientGroup.mk' (pCore p G)
  let f := q.subgroupMap I
  have hf : Function.Surjective f := q.subgroupMap_surjective I
  have hk : IsPGroup p f.ker := by
    rw [show f = q.subgroupMap I from rfl, ker_subgroupMap, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let es : (I.map q ⧸ pCore p (I.map q)) ≃* S :=
    (f.pCoreQuotientEquiv hf hk).symm.trans eI
  apply pResidual_le_of_pCoreQuotient_card (I.map q)
  · rw [eq_top_iff]
    intro x _
    have hm := map_pResidual p es
    rw [hS] at hm
    have hy : es x ∈
        (pResidual p (I.map q ⧸ pCore p (I.map q))).map es := by
      change es x ∈ map es.toMonoidHom
        (pResidual p (I.map q ⧸ pCore p (I.map q)))
      rw [hm]
      trivial
    rcases hy with ⟨z, hz, hzy⟩
    exact (es.injective hzy) ▸ hz
  · exact le_of_eq ((Nat.card_congr eR.toEquiv).trans (Nat.card_congr es.toEquiv).symm)

end
end Subgroup
