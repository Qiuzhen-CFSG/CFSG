module

public import Stellmacher.MainDefs
public import Stellmacher.Recognition.NormalEightSeparatedClosureEightLocalData
public import Stellmacher.Recognition.NormalEightSeparatedClosureEightActionCore
public import Stellmacher.Recognition.NormalEightSeparatedClosureEightOddSplitting
public import Theory.GroupTheory.ElementaryEightCoreFreeAction
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# The local splitting of the order-eight closure

The action of the selected supplement on its elementary eight has trivial
two-core by normal generation from the Sylow central omega. Its Sylow action
is nontrivial, since otherwise the eight would lie in the prescribed central
omega of order four. The N₂ hypothesis gives solvability, and the elementary
eight automizer bound now gives order six. Trivial two-core also rules out
an abelian action image. The order-six action then supplies the moving plane
and the odd actor whose fixed subgroup complements it in the closure centralizer.

These are the intrinsic automizer inputs for the odd-action splitting in
Janko–Thompson, Math. Z. 113 (1970), Lemma 3.1, printed p.388;
refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf.
The final theorem discharges the action hypothesis and constructs the concrete
`LocalSplitting` from the original local setup.
-/

namespace Stellmacher.Recognition.NormalEightSeparatedClosureEight
open Subgroup NormalEightSeparatedCentralizers
variable {G : Type*} [Group G] [Finite G]

/-- The actual closure action has order six, without an assumed automizer
or odd-order actor. -/
public theorem closure_action_card_eq_six (hN : IsNTwoGroup G) {S : Sylow 2 G} {W : Subgroup S}
    (hW : Nat.card W = 4) {i : S} (hi : orderOf i = 2)
    (d : CentralizerSetup S W i) (hc : Nat.card d.closure = 8) :
    Nat.card (MulAut.conjNormal (H := d.closure) : d.H →* MulAut d.closure).range = 6 := by
  let : Group.IsSolvable (centralizer ({(i : G)} : Set G)) :=
    hN _ (Theory.GroupTheory.isTwoLocal_involution_centralizer ((orderOf_coe i).trans hi))
  let : Group.IsSolvable d.H := inferInstance
  let f : d.H →* MulAut d.closure := MulAut.conjNormal
  let : Group.IsSolvable f.range :=
    Group.isSolvable_of_surjective f.rangeRestrict_surjective
  let : IsElementaryAbelian 2 d.closure := d.elementary
  exact card_eq_six_of_elementary_eight_automorphisms_twoCore_eq_bot hc f.range
    (closure_action_twoCore_eq_bot d) (two_dvd_card_closure_action hW d hc)

private theorem not_commutative_of_core_free {p : ℕ} [Fact p.Prime] {H : Type*} [Group H] [Finite H]
    (hcore : pCore p H = ⊥) (hp : p ∣ Nat.card H) : ¬ IsMulCommutative H := by
  intro hcomm
  let := hcomm
  let P : Sylow p H := Classical.choice inferInstance
  let : (P : Subgroup H).Normal := Subgroup.normal_of_isMulCommutative _
  have hle : (P : Subgroup H) ≤ pCore p H := le_sSup ⟨inferInstance, P.isPGroup'⟩
  have he : (P : Subgroup H) = ⊥ := le_antisymm (hcore ▸ hle) bot_le
  have hcard : Nat.card P = 1 := card_eq_one.mpr he
  have hd := P.dvd_card_of_dvd_card hp
  rw [hcard] at hd
  exact (Fact.out : p.Prime).not_dvd_one hd
/-- The actual closure action is nonabelian. This part does not need
solvability or the N₂ hypothesis. -/
public theorem closure_action_not_isMulCommutative
    {S : Sylow 2 G} {W : Subgroup S} (hW : Nat.card W = 4)
    {i : S} (d : CentralizerSetup S W i) (hc : Nat.card d.closure = 8) :
    ¬ IsMulCommutative
      (MulAut.conjNormal (H := d.closure) : d.H →* MulAut d.closure).range :=
  not_commutative_of_core_free (closure_action_twoCore_eq_bot d)
    (two_dvd_card_closure_action hW d hc)

/-- The order-eight closure admits the moving-plane and fixed-factor splitting
from the original local hypotheses, with no assumed automizer or odd actor. -/
public theorem nonempty_localSplitting
    (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (z : S) (hzW : z ∈ W) (hzC : z ∈ center S)
    (hz : orderOf z = 2)
    (i : S) (hiW : i ∈ W) (hi : orderOf i = 2)
    (hiC : i ∉ center S)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (d : CentralizerSetup S W i) (hc : Nat.card d.closure = 8) :
    Nonempty (LocalSplitting d z) :=
  localSplitting_of_action_card_six S W hW z hzW hzC hz i hiW hi hiC hno d hc
    (closure_action_card_eq_six hN hW hi d hc)

end Stellmacher.Recognition.NormalEightSeparatedClosureEight
