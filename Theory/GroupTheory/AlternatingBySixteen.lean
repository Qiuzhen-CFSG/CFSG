module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Alternating extensions by an elementary abelian group of order sixteen

The extension shape A_n/E_16 means an actual normal elementary abelian
subgroup of order sixteen with alternating quotient. It does not specify
splitting. Multiplicative equivalences transport the normal subgroup, its
exponent and order, and the quotient equivalence.

This is the extension convention of Aschbacher–Smith, Lemma 2.3.9(7)(f),
printed p.525 of the combined manuscript of 1 March 2004.
-/

@[expose] public section

namespace Theory.GroupTheory
open Subgroup

variable {K P : Type*} [Group K] [Group P]

/-- An actual elementary abelian normal kernel of order sixteen and alternating quotient. -/
def AlternatingBySixteen (K : Type*) [Group K] (n : ℕ) : Prop :=
  ∃ U : Subgroup K, ∃ _ : U.Normal,
    IsElementaryAbelian 2 U ∧ Nat.card U = 16 ∧
      Nonempty ((K ⧸ U) ≃* alternatingGroup (Fin n))

/-- Transport the kernel and quotient through a group isomorphism. -/
theorem AlternatingBySixteen.of_equiv {n : ℕ} (h : AlternatingBySixteen K n)
    (e : K ≃* P) : AlternatingBySixteen P n := by
  obtain ⟨U, hU, he, hc, ⟨eq⟩⟩ := h
  let := hU
  let := he
  let V := U.map e.toMonoidHom
  let : V.Normal := Subgroup.Normal.map hU e.toMonoidHom e.surjective
  have hv : IsElementaryAbelian 2 V := IsElementaryAbelian.map e.toMonoidHom
  refine ⟨V, inferInstance, hv, ?_, ?_⟩
  · exact (Nat.card_congr (e.subgroupMap U).toEquiv).symm.trans hc
  · exact ⟨(QuotientGroup.congr U V e rfl).symm.trans eq⟩

end Theory.GroupTheory

end
