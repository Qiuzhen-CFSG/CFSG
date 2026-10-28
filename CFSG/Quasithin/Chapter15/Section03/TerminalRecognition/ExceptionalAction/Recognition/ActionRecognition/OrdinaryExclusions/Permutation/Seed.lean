module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Reduction
public import Theory.GroupAction.ComplementQuotientCentralizer
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# The marked seed survives a central quotient

The normal two-core of Y_F fixes V and has quotient C₃. An odd complement
therefore acts coprimely on the abelian V. Since V = [V,Y_F], its fixed
space vanishes. In the faithful quotient representation, V is consequently
disjoint from the fixed space of every subgroup containing the image of Y_F.
The same group commutator identity gives its literal linear commutator span.

Only the seed is separated from the central kernel: no splitting of the
whole module is asserted. This is the central-quotient transport needed in
the final proof of 15.3.1, Aschbacher–Smith, printed p.1155, using the
nonsplit alternatives of B.5.1, printed p.99 (1 March 2004 manuscript).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation

open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- Coprime splitting on the seed removes its first-residual fixed vectors. -/
theorem vector_inf_centralizer_first : V ⊓ centralizer (d.YF : Set H) = ⊥ := by
  let _ : IsMulCommutative V := ⟨⟨fun x y => Subtype.ext (congrArg (fun z : moduleClosure V => (z : H))
    (mul_comm (⟨x, le_normalClosure x.property⟩ : moduleClosure V)
      (⟨y, le_normalClosure y.property⟩ : moduleClosure V)))⟩⟩
  obtain ⟨e⟩ := d.first_odd_quotient
  have hidx : (pCore 2 d.YF).index = 3 := by
    change Nat.card (d.YF ⧸ pCore 2 d.YF) = 3
    exact (Nat.card_congr e.toEquiv).trans (by simp)
  have hcop : Nat.Coprime (Nat.card (pCore 2 d.YF)) (pCore 2 d.YF).index := by
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := d.YF)).exists_card_eq
    rw [hk, hidx]
    exact (by decide : Nat.Coprime 2 3).pow_left k
  obtain ⟨A, hA⟩ := exists_right_complement'_of_coprime hcop
  let C : Subgroup H := A.map d.YF.subtype
  have hCY : C ≤ d.YF := map_subtype_le _
  have hCcard : Nat.card C = 3 := by
    rw [card_map_of_injective d.YF.subtype_injective, ← hA.symm.index_eq_card, hidx]
  have hgen : d.YF = d.YF.pCoreIn 2 ⊔ C := by
    have hh := congrArg (fun B : Subgroup d.YF => B.map d.YF.subtype) hA.sup_eq_top
    simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, pCoreIn, C] using hh.symm
  have hnormal : d.YF ≤ normalizer (V : Set H) :=
    le_normalizer_iff_commutator_le_left.mpr d.vector_commutator.symm.le
  have hcentral : d.YF.pCoreIn 2 ≤ centralizer (V : Set H) :=
    le_sup_right.trans (d.core_bound.trans d.centralizer_eq.le)
  have hzero := centralizer_le_layer_of_coprime_generating_complement
    d.YF (d.YF.pCoreIn 2) C V ⊥ hgen hnormal le_normalizer_of_normal
    d.vector_commutator.symm
    ((commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hcentral)).le)
    (show Nat.Coprime (Nat.card C) (Nat.card (V ⧸ (⊥ : Subgroup H).subgroupOf V)) by
      simpa only [bot_subgroupOf, Nat.card_congr (QuotientGroup.quotientBot (G := V)).toEquiv,
        hCcard, d.vector_card] using (by decide : Nat.Coprime 3 16))
  exact le_bot_iff.mp ((inf_le_inf_left V (centralizer_le hCY)).trans hzero)

/-- A containing actor has no fixed vector in the marked seed. -/
theorem vector_disjoint_fixed (K : Subgroup (coreQuotient H))
    (hK : d.YF.map coreProjection ≤ K) :
    Disjoint (planeSubspace V V)
      (fixedSpace (quotientAction V d.centralizer_isTwoGroup d.core_centralizes) K) := by
  apply Submodule.disjoint_def.mpr
  intro v hv hf
  have hc : (v.toMul : H) ∈ centralizer (d.YF : Set H) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    have hh := congrArg (fun w : Additive (moduleClosure V) => (w.toMul : H))
      (hf ⟨coreProjection y, hK (mem_map_of_mem coreProjection hy)⟩)
    change ((quotientAction V d.centralizer_isTwoGroup d.core_centralizes
      (coreProjection y) v).toMul : H) = (v.toMul : H) at hh
    rw [quotientAction_apply] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hh : (v.toMul : H) = 1 :=
    (vector_inf_centralizer_first d).le ⟨hv, hc⟩
  exact Subtype.ext hh

omit [Finite H] in
/-- The exact linear version of the marked commutator identity. -/
theorem vector_subspaceCommutator :
    subspaceCommutator (quotientAction V d.centralizer_isTwoGroup d.core_centralizes)
      (planeSubspace V V) (d.YF.map coreProjection) = planeSubspace V V := by
  let ρ := quotientAction V d.centralizer_isTwoGroup d.core_centralizes
  let P := planeSubspace V V
  let C : Subgroup (moduleClosure V) :=
    (subspaceCommutator ρ P (d.YF.map coreProjection)).toAddSubgroup.toSubgroup'
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨y, hy, rfl⟩, v, hv, rfl⟩
    change ((ρ (coreProjection y) v).toMul : H) / (v.toMul : H) ∈ V
    change ((quotientAction V d.centralizer_isTwoGroup d.core_centralizes
      (coreProjection y) v).toMul : H) / (v.toMul : H) ∈ V
    rw [quotientAction_apply, div_eq_mul_inv]
    change ⁅y, (v.toMul : H)⁆ ∈ V
    exact d.vector_commutator.ge ((commutator_comm d.YF V).le
      (commutator_mem_commutator hy hv))
  · have hVC : V ≤ C.map (moduleClosure V).subtype := by
      conv_lhs => rw [d.vector_commutator, commutator_comm]
      apply commutator_le.mpr
      intro y hy v hv
      let w : Additive (moduleClosure V) := Additive.ofMul ⟨v, le_normalClosure hv⟩
      refine ⟨(ρ (coreProjection y) w - w).toMul, ?_, ?_⟩
      · change ρ (coreProjection y) w - w ∈
          subspaceCommutator ρ P (d.YF.map coreProjection)
        exact Submodule.subset_span ⟨coreProjection y,
          mem_map_of_mem coreProjection hy, w, hv, rfl⟩
      · change ((quotientAction V d.centralizer_isTwoGroup d.core_centralizes
          (coreProjection y) w).toMul : H) / v = ⁅y, v⁆
        rw [quotientAction_apply, div_eq_mul_inv]
        rfl
    intro w hw
    obtain ⟨v, hv, he⟩ := hVC hw
    have heq : v = w.toMul := Subtype.ext he
    subst v
    exact hv

omit [Finite H] in
/-- The seed lies in each moved section whose actor contains the first residual. -/
theorem vector_le_moved (K : Subgroup (coreQuotient H))
    (hK : d.YF.map coreProjection ≤ K) :
    planeSubspace V V ≤ moved
      (quotientAction V d.centralizer_isTwoGroup d.core_centralizes) K := by
  rw [← vector_subspaceCommutator d]
  apply Submodule.span_mono
  rintro _ ⟨a, ha, v, _, rfl⟩
  exact ⟨a, hK ha, v, Submodule.mem_top, rfl⟩

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.Permutation
