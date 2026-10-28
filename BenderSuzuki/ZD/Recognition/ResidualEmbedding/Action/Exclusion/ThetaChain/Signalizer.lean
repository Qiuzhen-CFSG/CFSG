module

public import BenderSuzuki.SE.Section7Signalizer.CoreSupplement
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Action.Exclusion.Generation.CorePlacement

/-!
# Distinguished Lemma 7.6

The already proved Proposition 3.8(d) makes the triple stabilizer E a
supplement to the odd core of the two-point stabilizer D. The generic
signalizer comparison applies in W₁ O_{2'}(D), which has odd order even
when D does not. This discharges the second theta inclusion used by the
minimal-theta argument in Proposition 7.2.

Source: GLS, Volume 4, Chapter 2, Lemma 7.6, printed p.48.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The local signalizer input to the distinguished theta chain. The
nonbase point need not satisfy any additional fixed-set hypothesis. -/
public theorem action_lemma76
    (h : IsProductDisconnected Z M) (h3 : ActionSectionThree Z M)
    (d : ActionCounterexample Z M) {beta : G ⧸ M}
    (hne : beta ≠ QuotientGroup.mk 1)
    (W₁ : Subgroup (theorem4bSection7D M beta)) (hW₁p : IsPGroup d.p W₁)
    (hW₁E : W₁ ⊔ Subgroup.centralizer (W₁ : Set (theorem4bSection7D M beta)) ≤
      (theorem4bSection7E M d.z beta).subgroupOf (theorem4bSection7D M beta)) :
    corollary64Theta d.p (theorem4bSection7E M d.z beta) ≤
      corollary64Theta d.p (theorem4bSection7D M beta) := by
  let : Fact d.p.Prime := ⟨d.hp⟩
  have hpodd : d.p ≠ 2 := by
    intro he
    have hh := d.hpOdd
    rw [he] at hh
    exact (by decide : ¬ Odd (2 : ℕ)) hh
  exact theta_le_of_pgroup_centralizer_le_supplement hpodd inf_le_left
    (action_tripleStabilizer_supplement h h3 d.hzZ d.hzM hne) W₁ hW₁p hW₁E

end BenderSuzuki.ZD
