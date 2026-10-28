module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsOppositeAction
public import Theory.GroupTheory.ThreeConjugateInvolutionSubgroups
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The three-arm quotient of the opposite source group

The three actual radius-four stabilizers contain the common radius-three
core. Their quotient subgroups have order two, conjugate according to the
branch action, and generate a symmetric group of degree three. The exact
branch-action kernel is therefore the core, giving the opposite group order
192 and a cubic actor permuting all three branches.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the last
paragraph of (6.12), printed p.406.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup SimpleGraph Theory.GroupAction.CubicTree Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem perm_three_eq_swap : ∀ (p : Equiv.Perm (Fin 3)) (i j k : Fin 3),
    i ≠ j → i ≠ k → j ≠ k → p i = i → p j = k → p = Equiv.swap j k := by
  have hcover : ∀ i j k l : Fin 3, i ≠ j → i ≠ k → j ≠ k →
      l = i ∨ l = j ∨ l = k := by decide +kernel
  intro p i j k hij hik hjk hi hj
  have hk : p k = j := by
    rcases hcover i j k (p k) hij hik hjk with he | he | he
    · exact (hik (p.injective (hi.trans he.symm))).elim
    · exact he
    · exact (hjk (p.injective (hj.trans he.symm))).elim
  apply Equiv.ext
  intro l
  rcases hcover i j k l hij hik hjk with rfl | rfl | rfl
  · simpa only [Equiv.swap_apply_def, if_neg hij, if_neg hik] using hi
  · simpa only [Equiv.swap_apply_left] using hj
  · simpa only [Equiv.swap_apply_right] using hk

private theorem neighbor_side (d : CanonicalLabelSetup F s)
    {v a : RankTwo.Vertex F} (hv : v.type ≠ d.side)
    (ha : (RankTwo.graph F).Adj v a) : a.type = d.side := by
  have hn := ha.1
  cases h0 : v.type <;> cases h1 : a.type <;> cases h2 : d.side <;> simp_all

/-- The source opposite group has order192 as soon as its three labelled
radius-four neighbours have their proved source order192. -/
theorem LocalRelations.oppositeGroup_card_and_action_kernel
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (v : RankTwo.Vertex F) (hv : v.type ≠ d.side)
    (hcards : ∀ a, (RankTwo.graph F).Adj v a → Nat.card (d.labelBall a 4) = 192)
    (f : BranchFrame F v) :
    Nat.card (oppositeGroup d v) = 192 ∧
      (f.branchAction.comp (Subgroup.inclusion (oppositeGroup_le_stabilizer d v))).ker =
        (d.labelBall v 3).subgroupOf (oppositeGroup d v) := by
  classical
  let t := h.action.toCubicTreeAction
  let H := oppositeGroup d v
  let Q : Subgroup H := (d.labelBall v 3).subgroupOf H
  let A : Fin 3 → Subgroup H := fun i =>
    (oppositeGenerator d v (f.e i).val).subgroupOf H
  let : Finite (RankTwo.stabilizer F v) := t.finite_stabilizer v
  let : Finite H := Finite.of_injective
    (Subgroup.inclusion (oppositeGroup_le_stabilizer d v)) (Subgroup.inclusion_injective _)
  let : Q.Normal := radiusThree_normal_oppositeGroup d t hr (by have := h.five_le; omega) v
  let q := QuotientGroup.mk' Q
  let P : Fin 3 → Subgroup (H ⧸ Q) := fun i => (A i).map q
  have hAH (i : Fin 3) : oppositeGenerator d v (f.e i).val ≤ H :=
    oppositeGenerator_le d (f.e i).property
  have hQA (i : Fin 3) : Q ≤ A i := fun x hx =>
    radiusThree_le_oppositeGenerator d t hr (by have := h.five_le; omega)
      (f.e i).property hx
  have hQcard : Nat.card Q = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe (radiusThree_le_oppositeGroup d t hr
      (by have := h.five_le; omega) v)).toEquiv).trans (r.radiusThree_card hr v hv)
  have hAcard (i : Fin 3) : Nat.card (A i) = 64 :=
    (Nat.card_congr (subgroupOfEquivOfLe (hAH i)).toEquiv).trans
      (r.oppositeGenerator_card_of_radiusFour_card hr
        (neighbor_side d hv (f.e i).property) (f.e i).property
          (hcards _ (f.e i).property))
  have hPcard (i : Fin 3) : Nat.card (P i) = 2 := by
    have hc := (Q.subgroupOf (A i)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (hQA i)).toEquiv, hQcard, hAcard] at hc
    have hi : Q.relIndex (A i) = Nat.card (P i) := by
      simpa only [q, QuotientGroup.ker_mk'] using (A i).relIndex_ker q
    change 32 * Q.relIndex (A i) = 64 at hc
    rw [hi] at hc
    omega
  have hmapA (i : Fin 3) : (A i).map H.subtype = oppositeGenerator d v (f.e i).val :=
    Subgroup.map_subgroupOf_eq_of_le (hAH i)
  have hAgen : iSup A = ⊤ := by
    apply (Subgroup.map_injective H.subtype_injective)
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, H.range_subtype]
    simp_rw [hmapA]
    apply le_antisymm
    · exact iSup_le hAH
    · apply iSup_le
      intro a
      obtain ⟨i, rfl⟩ := f.e.surjective a
      exact le_iSup (fun i => oppositeGenerator d v (f.e i).val) i
  have hPgen : iSup P = ⊤ := by
    rw [show iSup P = (iSup A).map q from (Subgroup.map_iSup q A).symm,
      hAgen, Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective Q)]
  let ψ : H →* Equiv.Perm (Fin 3) :=
    f.branchAction.comp (Subgroup.inclusion (oppositeGroup_le_stabilizer d v))
  have hψeval (g : H) (i : Fin 3) :
      (f.e (ψ g i)).val = g.val • (f.e i).val :=
    f.branchAction_eval (Subgroup.inclusion (oppositeGroup_le_stabilizer d v) g) i
  have hQker : Q ≤ ψ.ker := by
    intro g hg
    change ψ g = 1
    apply Equiv.ext
    intro i
    apply f.e.injective
    apply Subtype.ext
    rw [hψeval]
    apply d.labelBall_le_ballKernel t v 3 1 (by omega) (by have := h.five_le; omega) hg
    apply (RankTwo.mem_ball_iff F t.generated _ _ _).mpr
    exact le_of_eq (dist_eq_one_iff_adj.mpr (f.e i).property)
  let ρ : (H ⧸ Q) →* Equiv.Perm (Fin 3) := QuotientGroup.lift Q ψ hQker
  have hρq (g : H) : ρ (q g) = ψ g := rfl
  have hfixA (i : Fin 3) (g : H) (hg : g ∈ A i) : ψ g i = i := by
    apply f.e.injective
    apply Subtype.ext
    rw [hψeval]
    exact d.labelBall_le_stabilizer (f.e i).val 4 (by omega)
      (by have := h.five_le; omega) hg.1
  have hfix (i : Fin 3) (g : H ⧸ Q) (hg : g ∈ P i) : ρ g i = i := by
    obtain ⟨x, hx, rfl⟩ := hg
    exact hfixA i x hx
  have hmove (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) :
      ∃ g ∈ P i, ρ g j = k := by
    have hne (u w : Fin 3) (huw : u ≠ w) : (f.e u).val ≠ (f.e w).val :=
      fun he => huw (f.e.injective (Subtype.ext he))
    obtain ⟨x, hx, he⟩ := r.oppositeGenerator_neighbor_transitive hr
      (neighbor_side d hv (f.e i).property) (f.e i).property
      (f.e j).property (f.e k).property (hne i j hij) (hne i k hik)
    let g : H := ⟨x, hAH i hx⟩
    refine ⟨q g, mem_map.mpr ⟨g, hx, rfl⟩, ?_⟩
    rw [hρq]
    apply f.e.injective
    apply Subtype.ext
    exact (hψeval g j).trans he
  have hρsurj : Function.Surjective ρ := by
    apply MonoidHom.range_eq_top.mp
    have hswap (j k : Fin 3) : Equiv.swap j k ∈ ρ.range := by
      by_cases hjk : j = k
      · subst k
        rw [Equiv.swap_self]
        exact ρ.range.one_mem
      obtain ⟨i, hij, hik⟩ := Fin.exists_ne_and_ne_of_two_lt j k (by decide : 2 < 3)
      obtain ⟨g, hg, he⟩ := hmove i j k hij hik
      exact ⟨g, perm_three_eq_swap (ρ g) i j k hij hik hjk (hfix i g hg) he⟩
    apply top_unique
    intro σ
    induction σ using Equiv.Perm.swap_induction_on with
    | one => intro _; exact ρ.range.one_mem
    | swap_mul σ i j hij hσ =>
      intro _
      exact ρ.range.mul_mem (hswap i j) (hσ (mem_top σ))
  have hconj (g : H ⧸ Q) (i : Fin 3) :
      (P i).map (MulAut.conj g).toMonoidHom = P (ρ g i) := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Q g
    have hconjA : (A i).map (MulAut.conj g).toMonoidHom = A (ψ g i) := by
      apply (Subgroup.map_injective H.subtype_injective)
      rw [Subgroup.map_map]
      have hm : H.subtype.comp (MulAut.conj g).toMonoidHom =
          (MulAut.conj g.val).toMonoidHom.comp H.subtype := rfl
      rw [hm, ← Subgroup.map_map]
      simp_rw [hmapA]
      rw [oppositeGenerator_map_conj, show g.val • v = v from
        oppositeGroup_le_stabilizer d v g.property, ← hψeval]
    change ((A i).map q).map (MulAut.conj (q g)).toMonoidHom = (A (ψ g i)).map q
    rw [← hconjA, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hquot : Nat.card (H ⧸ Q) = 6 :=
    Theory.GroupTheory.ThreeConjugateInvolutionSubgroups.card_eq_six P hPcard hPgen ρ hρsurj hconj hmove
  have hc := Q.card_mul_index
  rw [hQcard, Subgroup.index_eq_card, hquot] at hc
  have hρinj : Function.Injective ρ :=
    (hρsurj.bijective_of_nat_card_le (by
      rw [hquot, Nat.card_perm, Nat.card_fin]
      decide)).injective
  exact ⟨hc.symm, ((QuotientGroup.injective_lift_iff Q ψ hQker).mp hρinj).symm⟩

/-- The quotient calculation gives the actual opposite source order192. -/
theorem LocalRelations.oppositeGroup_card_of_radiusFour_card
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (v : RankTwo.Vertex F) (hv : v.type ≠ d.side)
    (hcards : ∀ a, (RankTwo.graph F).Adj v a → Nat.card (d.labelBall a 4) = 192) :
    Nat.card (oppositeGroup d v) = 192 := by
  obtain ⟨f⟩ := h.action.toCubicTreeAction.exists_branchFrame v
  exact (r.oppositeGroup_card_and_action_kernel hr v hv hcards f).1

private theorem cubic_perm_three_no_fixed : ∀ p : Equiv.Perm (Fin 3),
    p ^ 3 = 1 → p ≠ 1 → ∀ i, p i ≠ i := by
  decide +kernel

/-- A literal element of order three cycles the three branches of `H`.
The action-kernel identity rules out its disappearing into the two-core. -/
theorem LocalRelations.exists_oppositeGroup_cubic
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    (v : RankTwo.Vertex F) (hv : v.type ≠ d.side)
    (hcards : ∀ a, (RankTwo.graph F).Adj v a → Nat.card (d.labelBall a 4) = 192) :
    ∃ C ∈ oppositeGroup d v, C ^ 3 = 1 ∧
      ∀ a, (RankTwo.graph F).Adj v a → C • a ≠ a := by
  let t := h.action.toCubicTreeAction
  obtain ⟨f⟩ := t.exists_branchFrame v
  obtain ⟨hcard, hker⟩ := r.oppositeGroup_card_and_action_kernel hr v hv hcards f
  let H := oppositeGroup d v
  let Q := (d.labelBall v 3).subgroupOf H
  let : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; decide)
  let ψ : H →* Equiv.Perm (Fin 3) :=
    f.branchAction.comp (Subgroup.inclusion (oppositeGroup_le_stabilizer d v))
  have hQcard : Nat.card Q = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe (radiusThree_le_oppositeGroup d t hr
      (by have := h.five_le; omega) v)).toEquiv).trans (r.radiusThree_card hr v hv)
  obtain ⟨C, hC⟩ := exists_prime_orderOf_dvd_card' 3
    (show 3 ∣ Nat.card H by rw [hcard]; decide)
  have hC3 : C ^ 3 = 1 := by simpa only [hC] using pow_orderOf_eq_one C
  have hψC : ψ C ≠ 1 := by
    intro he
    have hm : C ∈ Q := by
      change C ∈ (d.labelBall v 3).subgroupOf (oppositeGroup d v)
      rw [← hker]
      exact he
    have hd := Q.orderOf_dvd_natCard hm
    rw [hC, hQcard] at hd
    norm_num at hd
  have hψC3 : (ψ C) ^ 3 = 1 := by rw [← map_pow, hC3, map_one]
  refine ⟨C.val, C.property, congrArg Subtype.val hC3, ?_⟩
  intro a ha he
  obtain ⟨i, hi⟩ := f.e.surjective ⟨a, ha⟩
  have hi' : (f.e i).val = a := congrArg Subtype.val hi
  apply cubic_perm_three_no_fixed (ψ C) hψC3 hψC i
  apply f.e.injective
  apply Subtype.ext
  change (f.e (f.branchAction (Subgroup.inclusion (oppositeGroup_le_stabilizer d v) C) i)).val = _
  rw [f.branchAction_eval, hi']
  exact he

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
