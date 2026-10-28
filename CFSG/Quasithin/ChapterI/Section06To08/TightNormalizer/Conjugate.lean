module

public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.Completion
public import CFSG.Quasithin.ChapterI.Section06To08.TightPGroup

/-!
# The nontrivial normalizer criterion

In the setup of I.7, two distinct conjugates of the Sylow intersection
contained in the same 2-subgroup commute as soon as their relative normalizer
is nontrivial. Split on the Frattini subgroup: I.7.5 handles the nontrivial
case; in the elementary case apply the 2-group TI-pair theorem inside `S`.
Multiplication then identifies their join with their direct product.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined 1 March 2004 manuscript, I.7.6, printed p.427 (PDF p.438).
Conjugation is left conjugation, as in `TightPGroup.Intersection`.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
/-- I.7.6: distinct conjugates with nontrivial relative normalizer are disjoint
and centralize each other. -/
theorem lemma_I_7_6_commuting {K H Q S : Subgroup G}
    (h : TightPGroupSetup K H Q S) {g : G} (hg : g ∈ H)
    (hne : conjSubgroup Q g ≠ Q) (hQgS : conjSubgroup Q g ≤ S)
    (hn : conjSubgroup Q g ⊓ normalizer (Q : Set G) ≠ ⊥) :
    Disjoint Q (conjSubgroup Q g) ∧ Q ≤ centralizer (conjSubgroup Q g : Set G) := by
  by_cases hΦ : frattini Q = ⊥
  · let : Fact (IsPGroup 2 Q) := ⟨h.hQp⟩
    let : IsElementaryAbelian 2 Q :=
      (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hΦ
    let : IsElementaryAbelian 2 (conjSubgroup Q g) :=
      IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
    let V := (conjSubgroup Q g).subgroupOf S
    let A := Q.subgroupOf S
    let : IsElementaryAbelian 2 V := IsElementaryAbelian.subgroupOf hQgS
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf h.hQS
    have hd : Disjoint V A := by
      apply disjoint_iff.mpr
      ext x
      change ((x : G) ∈ conjSubgroup Q g ∧ (x : G) ∈ Q) ↔ x = 1
      constructor
      · intro hx
        apply Subtype.ext
        exact (disjoint_iff.mpr (lemma_I_7_2_2 h hg hQgS hne)).le_bot ⟨hx.2, hx.1⟩
      · rintro rfl
        exact ⟨one_mem _, one_mem _⟩
    have hcard : Nat.card V = Nat.card A := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hQgS).toEquiv,
        Nat.card_congr (subgroupOfEquivOfLe h.hQS).toEquiv, card_conjSubgroup]
    have hn' : V ⊓ normalizer (A : Set S) ≠ ⊥ := by
      obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hn
      apply Subgroup.ne_bot_iff_exists_ne_one.mpr
      refine ⟨⟨⟨x, hQgS x.property.1⟩, x.property.1, ?_⟩, ?_⟩
      · rw [← subgroupOf_normalizer_eq h.hQS]
        exact x.property.2
      · intro heq
        exact hx (Subtype.ext (congrArg (fun z : ↥(V ⊓ normalizer (A : Set S)) => ((z : S) : G)) heq))
    have hfull := ti_pair_full_normalizer_of_isPGroup V A hd
      (h.conjugate hg h.hSp h.hSH hQgS).isTISubgroup h.isTISubgroup
      hcard hn' (h.hSp.to_subgroup (V ⊔ A))
    apply lemma_I_7_4_commuting h hg hne
    refine le_inf hQgS ?_
    intro x hx
    have hxV : (⟨x, hQgS hx⟩ : S) ∈ V := hx
    have hxN := (show (⟨x, hQgS hx⟩ : S) ∈ V ⊓ normalizer (A : Set S) from hfull.symm ▸ hxV).2
    rw [← subgroupOf_normalizer_eq h.hQS] at hxN
    exact hxN
  · exact lemma_I_7_5_commuting h hΦ h.mem_family ⟨hQgS, g, hg, rfl⟩ hne.symm
/-- I.7.6 with the actual multiplication isomorphism and both embeddings. -/
theorem lemma_I_7_6 {K H Q S : Subgroup G}
    (h : TightPGroupSetup K H Q S) {g : G} (hg : g ∈ H)
    (hne : conjSubgroup Q g ≠ Q) (hQgS : conjSubgroup Q g ≤ S)
    (hn : conjSubgroup Q g ⊓ normalizer (Q : Set G) ≠ ⊥) :
    ∃ e : Q × conjSubgroup Q g ≃* ↥(Q ⊔ conjSubgroup Q g),
      ∀ q r, (e (q, r) : G) = (q : G) * (r : G) := by
  obtain ⟨hd, hc⟩ := lemma_I_7_6_commuting h hg hne hQgS hn
  exact Subgroup.exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hc

end CFSG.Quasithin.ChapterI.Section06To08
