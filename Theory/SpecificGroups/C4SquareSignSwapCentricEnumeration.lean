module

public import Theory.SpecificGroups.C4SquareSignSwapCentricEnumeration.Certificate

/-!
# Completeness of the centric candidates

Every subgroup of the sign-and-swap group is conjugate to one of 84 checked
nodes: the trivial subgroup is a node, and the family is closed under adjoining
one element. Right-coset factorizations reduce the extension check to 915
word certificates. The general finite-generation argument then gives
completeness without assuming any automorphism property of the subgroup.

The checked filter discards nodes lying in `transfer` and nodes with an
explicit centralizing element outside them. All remaining nodes are exactly
the 32 numbered candidates of `C4SquareSignSwapCentricData`.

Source: elementary subgroup enumeration in the explicit model described in
`C4SquareSignSwap`, supporting Stellmacher (8.6)(a).
-/

namespace C4SquareSignSwap
open Theory.GroupTheory Theory.GroupTheory.SubgroupEnumeration

namespace EnumerationCertificate

private theorem extension_sound (e : Fin 915) :
    (node (source e) ⊔ Subgroup.zpowers (representative e)).map
      (MulAut.conj (conjugator e)).toMonoidHom = node (target e) := by
  rw [node_eq_word (source e), node_eq_word (target e)]
  exact (extensionWords e).sound (gen (source e)) invLetter (gen_inv (source e))
    (gen (target e)) invLetter (gen_inv (target e)) (representative e)
    (MulAut.conj (conjugator e)).toMonoidHom (extensionWords_valid e)

/-- The checked nodes are closed, up to conjugacy, under adjoining any element. -/
public theorem extensionClosed : ExtensionClosed node := by
  refine ⟨⟨0, ?_⟩, fun i x => ?_⟩
  · ext g
    exact bot_valid g
  · obtain ⟨hs, hx⟩ := coset_valid i x
    have he := extension_sound (edgeFor i x)
    rw [hs] at he
    refine ⟨target (edgeFor i x), conjugator (edgeFor i x), ?_⟩
    have hmem : evalWord (gen i) (factorWord i x) ∈ node i := by
      rw [node_eq_word]
      exact ⟨factorWord i x, rfl⟩
    have hsup := congrArg (fun y => node i ⊔ Subgroup.zpowers y) hx
    rw [extension_mul_left (node i) hmem] at hsup
    rw [hsup]
    exact he

private theorem filtered (i : Fin 84)
    (hc : Subgroup.centralizer (node i : Set Model) ≤ node i)
    (hout : ¬node i ≤ transfer) : node i = centricCandidate (candidateIndex i) := by
  obtain ⟨h0, h1, h2⟩ := filter_valid i
  have hk : kind i = 0 ∨ kind i = 1 ∨ kind i = 2 := by omega
  rcases hk with hk | hk | hk
  · exact (hout (h0 hk)).elim
  · obtain ⟨hz, hcenz⟩ := h1 hk
    exact (hz (hc hcenz)).elim
  · exact Subgroup.ext (h2 hk)

end EnumerationCertificate

private theorem centric_map (X : Subgroup Model)
    (hc : Subgroup.centralizer (X : Set Model) ≤ X) (e : Model ≃* Model) :
    Subgroup.centralizer (X.map e.toMonoidHom : Set Model) ≤ X.map e.toMonoidHom := by
  intro x hx
  refine Subgroup.mem_map.mpr ⟨e.symm x, hc ?_, e.apply_symm_apply x⟩
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using
    hx (e y) (Subgroup.mem_map_of_mem e.toMonoidHom hy)

private theorem outside_map (X : Subgroup Model) (hout : ¬X ≤ transfer) (g : Model) :
    ¬ X.map (MulAut.conj g).toMonoidHom ≤ transfer := by
  intro h
  apply hout
  intro x hx
  have ht := h (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
  have hi := (inferInstance : transfer.Normal).conj_mem _ ht g⁻¹
  simpa [MulAut.conj_apply, mul_assoc] using hi

/-- Every centric subgroup outside `transfer` is conjugate to one of the
32 candidates, with the numbering fixed by `centricCandidateMask`. -/
public theorem centricCandidate_complete (X : Subgroup Model)
    (hc : Subgroup.centralizer (X : Set Model) ≤ X) (hout : ¬X ≤ transfer) :
    ∃ i : Fin 32, ∃ g : Model,
      X.map (MulAut.conj g).toMonoidHom = centricCandidate i := by
  obtain ⟨i, g, hg⟩ := EnumerationCertificate.extensionClosed.complete
    EnumerationCertificate.node X
  have hcent := centric_map X hc (MulAut.conj g)
  have hnot := outside_map X hout g
  rw [hg] at hcent hnot
  exact ⟨EnumerationCertificate.candidateIndex i, g,
    hg.trans (EnumerationCertificate.filtered i hcent hnot)⟩

end C4SquareSignSwap
