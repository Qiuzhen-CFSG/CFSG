module

public import Theory.SpecificGroups.PSL3Three.Basic
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Mathlib.Algebra.Field.ZMod

/-!
# Inner involutory automorphisms of PSL₃(3)

The canonical SL₃(3) → PSL₃(3) map is an isomorphism. Transport the inner
automorphism to SL₃(3), use the trivial center to detect the conjugator's order,
and apply the explicit GL₂(3) block-centralizer equivalence.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, inner case of Lemma 16.1.5(1), printed p.1171.
The outer-automorphism case is not asserted here.
-/

public section

namespace Matrix.PSL3Three
/-- The actual fixed subgroup of an inner involutory automorphism of PSL₃(3). -/
noncomputable def innerInvolutoryAutFixedEquiv (r : MulAut PSL) (hr : orderOf r = 2)
    (hi : ∃ g : PSL, r = MulAut.conj g) :
    r.fixedSubgroup ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) := by
  refine Classical.choice ?_
  obtain ⟨g, hg⟩ := (MulAut.congr_inner_iff equiv.symm r).mpr hi
  have ha : orderOf (MulAut.conj g) = 2 := hg ▸ ((MulAut.congr equiv.symm).orderOf_eq r).trans hr
  have hgo : orderOf g = 2 :=
    (orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot center_eq_bot) g).symm.trans ha
  let ce := MulAut.fixedSubgroupCongr equiv.symm r
  exact ⟨ce.trans ((MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup hg)).trans
    ((MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj g)).trans
      (Matrix.SL3.involutionCentralizerEquiv (ZMod 3) g hgo (by decide))))⟩
end Matrix.PSL3Three
