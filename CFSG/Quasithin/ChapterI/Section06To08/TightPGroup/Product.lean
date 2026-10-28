module

public import CFSG.Quasithin.ChapterI.Section06To08.TightPGroup.Intersection
public import Theory.GroupTheory.TIIndex
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The index bound and the normalizing-conjugate product

I.7.3 follows from the TI index bound inside the finite 2-group `S`.
For I.7.4, the two disjoint conjugates generate a 2-group of order `|Q|²`.
I.7.3 makes the second factor normal in this join as well as the first.
Their commutator lies in their trivial intersection, and multiplication gives
an actual direct-product isomorphism retaining both factors.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, I.7.3--I.7.4, printed p.426.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterI.Section06To08
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The restriction of `Q` to `S` is a TI-subgroup of `S`. -/
theorem TightPGroupSetup.isTISubgroup {K H Q S : Subgroup G}
    (h : TightPGroupSetup K H Q S) : IsTISubgroup (Q.subgroupOf S) := by
  rw [isTISubgroup_iff]
  intro g hg x hx hconj
  have hgn : (g : G) ∉ normalizer (Q : Set G) := by
    intro hn
    apply hg
    rw [← subgroupOf_normalizer_eq h.hQS]
    exact hn
  have hbot := lemma_I_7_2_3 h (S.le_normalizer g.property) hgn
  have hm : (g : G) * (x : G) * (g : G)⁻¹ ∈ Q ⊓ conjSubgroup Q g :=
    ⟨hconj, ⟨x, hx, rfl⟩⟩
  rw [hbot] at hm
  have hx1 : (x : G) = 1 := by
    have hh := congrArg (fun y : G => (g : G)⁻¹ * y * g) (mem_bot.mp hm)
    simpa [mul_assoc] using hh
  exact Subtype.ext hx1

/-- I.7.3. The index is the relative index `|S : Q|`, and the conclusion is
normality in `S`, not ambient normality in `G`. -/
theorem lemma_I_7_3 {K H Q S : Subgroup G}
    (h : TightPGroupSetup K H Q S) (hindex : Q.relIndex S ≤ Nat.card Q) :
    (Q.subgroupOf S).Normal := by
  let : Group.IsNilpotent S := h.hSp.isNilpotent
  apply Subgroup.normal_of_trivial_intersections_of_index_le_card
    Group.normalizerCondition_of_isNilpotent
  · intro g hg
    apply eq_bot_iff.mpr
    rintro x ⟨hx, y, hy, rfl⟩
    exact h.isTISubgroup g hg ⟨hx, ⟨y, hy, rfl⟩⟩
  · change (Q.subgroupOf S).index ≤ _ at hindex
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.hQS).toEquiv]

/-- I.7.4, commutation and trivial-intersection clauses. -/
theorem lemma_I_7_4_commuting {K H Q S : Subgroup G}
    (h : TightPGroupSetup K H Q S) {g : G} (hg : g ∈ H)
    (hne : conjSubgroup Q g ≠ Q)
    (hQgN : conjSubgroup Q g ≤ S ⊓ normalizer (Q : Set G)) :
    Disjoint Q (conjSubgroup Q g) ∧ Q ≤ centralizer (conjSubgroup Q g : Set G) := by
  let R := conjSubgroup Q g
  let U := Q ⊔ R
  have hdisj : Disjoint Q R := disjoint_iff.mpr
    (lemma_I_7_2_2 h hg (hQgN.trans inf_le_left) hne)
  have hRN : R ≤ normalizer (Q : Set G) := hQgN.trans inf_le_right
  have hUS : U ≤ S := sup_le h.hQS (hQgN.trans inf_le_left)
  have hc := h.conjugate hg (h.hSp.to_le hUS) (hUS.trans h.hSH)
    (le_sup_right : R ≤ U)
  have hcard : Nat.card U = Nat.card Q * Nat.card R :=
    Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint Q R hRN hdisj
  have hindex : R.relIndex U = Nat.card R := by
    have hm := (R.subgroupOf U).index_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : R ≤ U)).toEquiv] at hm
    change R.relIndex U * Nat.card R = Nat.card U at hm
    rw [hcard, ← card_conjSubgroup Q g] at hm
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hm
  have hnormal := lemma_I_7_3 hc hindex.le
  have hUN : U ≤ normalizer (R : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right : R ≤ U)).mp hnormal
  refine ⟨hdisj, Subgroup.commutator_eq_bot_iff_le_centralizer.mp ?_⟩
  apply le_bot_iff.mp
  rw [← hdisj.eq_bot]
  exact le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hRN)
    (Subgroup.le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hUN))

/-- I.7.4: the join of the two factors is their internal direct product.
The displayed equivalence is multiplication in the ambient group. -/
theorem lemma_I_7_4 {K H Q S : Subgroup G}
    (h : TightPGroupSetup K H Q S) {g : G} (hg : g ∈ H)
    (hne : conjSubgroup Q g ≠ Q)
    (hQgN : conjSubgroup Q g ≤ S ⊓ normalizer (Q : Set G)) :
    ∃ e : Q × conjSubgroup Q g ≃* ↥(Q ⊔ conjSubgroup Q g),
      ∀ q r, (e (q, r) : G) = (q : G) * (r : G) := by
  obtain ⟨hd, hc⟩ := lemma_I_7_4_commuting h hg hne hQgN
  exact Subgroup.exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd hc

end CFSG.Quasithin.ChapterI.Section06To08
