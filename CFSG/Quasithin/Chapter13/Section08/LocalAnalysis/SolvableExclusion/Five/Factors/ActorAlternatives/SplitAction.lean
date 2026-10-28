module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.ActorAlternatives.Kernels
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.ActorAlternatives.Reindex
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.ActorAlternatives.SplitAction.SupportCalculation
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.FixedIndex
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Factors.Alternatives

/-!
# The normalized five-actor alternatives on the whole quotient

For a faithful action on the actual quotient UH/V₁, the elementary abelian
actor normalizes one or two supplied five-factors and is jointly faithful
on them. The involution-kernel theorem gives order two, or two complementary
pure involutions of total order four.

In the first case, one moved support already realizes a displacement plane.
The global offender bound exhausts the full displacement there, so disjointness
rules out movement of any other factor. An explicit permutation places the
moved factor first. In the second case, the cross-fixed supports realize the
product of two planes. The same global bound exhausts the paired displacement
map. We then apply `split_planes_equality_case` to obtain separately the full
displacement order sixteen and the whole-quotient fixed index sixteen.

The output retains both split-support identities, the cross-fixed supports,
the common fixed index on their sum, and fixation of the P-fixed complement.
No triviality on that complement or action order is assumed. The two-factor
output uses the original factor ordering (the identity permutation).

This is the conditional algebraic step in Aschbacher–Smith, combined
manuscript (1 March 2004), 13.8.13, printed p.951 / PDF p.968. The source
assembly still owes normalization and faithfulness and the later exclusion
of the order-four alternative; F.9.16 is not used here.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.ActorAlternatives.SplitAction
variable {G : Type*} [Group G]
variable {H UH V₁ P Uγ : Subgroup G} [(V₁.subgroupOf UH).Normal]
variable {a : StarAction H UH V₁}

/-- The full-support identity and fixed-complement consequences in the
order-two alternative. This is output data, not an assumed action profile. -/
structure RankOneSplitData (r : RankOneFactors a P Uγ) : Prop where
  full : commutatorSubgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)
    (r.factors.support ⟨0, r.factors.count_pos⟩) =
      commutatorAction (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)
  supported : commutatorAction (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH) ≤
    r.factors.support ⟨0, r.factors.count_pos⟩
  remaining_fixed : ∀ i : Fin r.factors.count, i.val ≠ 0 →
    r.factors.support i ≤ FixedPoints.subgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)
  complement_fixed : FixedPoints.subgroup (a.actors P) (UH ⧸ V₁.subgroupOf UH) ≤
    FixedPoints.subgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)

/-- Both pure involutions realize their full displacement on their own support,
fix the other support, and jointly fix the P-fixed complement. -/
structure RankTwoSplitData (r : RankTwoFactors a P Uγ) : Prop where
  support_fixed_index : (FixedPoints.subgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)).relIndex
    (r.factors.support ⟨0, r.factors.count_pos⟩ ⊔
      r.factors.support ⟨1, by have := r.count_eq_two; omega⟩) = 16
  first_full : commutatorSubgroup (r.first.map a.action) (UH ⧸ V₁.subgroupOf UH)
    (r.factors.support ⟨0, r.factors.count_pos⟩) =
      commutatorAction (r.first.map a.action) (UH ⧸ V₁.subgroupOf UH)
  second_full : commutatorSubgroup (r.second.map a.action) (UH ⧸ V₁.subgroupOf UH)
    (r.factors.support ⟨1, by have := r.count_eq_two; omega⟩) =
      commutatorAction (r.second.map a.action) (UH ⧸ V₁.subgroupOf UH)
  first_supported : commutatorAction (r.first.map a.action) (UH ⧸ V₁.subgroupOf UH) ≤
    r.factors.support ⟨0, r.factors.count_pos⟩
  second_supported : commutatorAction (r.second.map a.action) (UH ⧸ V₁.subgroupOf UH) ≤
    r.factors.support ⟨1, by have := r.count_eq_two; omega⟩
  first_cross_fixed : r.factors.support ⟨0, r.factors.count_pos⟩ ≤
    FixedPoints.subgroup (r.second.map a.action) (UH ⧸ V₁.subgroupOf UH)
  second_cross_fixed : r.factors.support ⟨1, by have := r.count_eq_two; omega⟩ ≤
    FixedPoints.subgroup (r.first.map a.action) (UH ⧸ V₁.subgroupOf UH)
  complement_fixed : FixedPoints.subgroup (a.actors P) (UH ⧸ V₁.subgroupOf UH) ≤
    FixedPoints.subgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)

variable [Finite G] [IsElementaryAbelian 2 (UH ⧸ V₁.subgroupOf UH)]

private theorem factor_plane (hf : Function.Injective a.action)
    (f : Factorization a P) (i : Fin f.count) (A : Subgroup (Source.Hstar H))
    (hA : Nat.card A = 2)
    (hn : A ≤ normalizer (Source.starImage H (f.factor i) : Set _))
    (hm : ⁅A, Source.starImage H (f.factor i)⁆ ≠ ⊥) :
    Nat.card (commutatorSubgroup (A.map a.action) (UH ⧸ V₁.subgroupOf UH)
      (f.support i)) = 4 ∧
    commutatorSubgroup (A.map a.action) (UH ⧸ V₁.subgroupOf UH)
      (f.support i) ≤ f.support i := by
  apply five_support_plane (A.map a.action) (a.actors (f.factor i))
  · exact (card_map_of_injective hf).trans hA
  · exact (card_map_of_injective hf).trans (f.star_card i)
  · exact f.support_card i
  · exact (map_mono hn).trans (le_normalizer_map a.action)
  · intro he
    apply hm
    apply map_injective hf
    simpa only [map_commutator, Subgroup.map_bot, StarAction.actors] using he

private theorem factor_fixed (hf : Function.Injective a.action)
    (f : Factorization a P) (i : Fin f.count) (A : Subgroup (Source.Hstar H))
    (hA : Nat.card A = 2) (hc : ⁅A, Source.starImage H (f.factor i)⁆ = ⊥) :
    f.support i ≤ FixedPoints.subgroup (A.map a.action) (UH ⧸ V₁.subgroupOf UH) := by
  apply five_support_fixed (A.map a.action) (a.actors (f.factor i))
  · exact (card_map_of_injective hf).trans hA
  · exact (card_map_of_injective hf).trans (f.star_card i)
  · exact f.support_card i
  · rw [StarAction.actors, ← map_commutator, hc, Subgroup.map_bot]

private theorem factor_complement_fixed (hf : Function.Injective a.action)
    (f : Factorization a P) (i : Fin f.count) (A : Subgroup (Source.Hstar H))
    (hn : A ≤ normalizer (Source.starImage H (f.factor i) : Set _))
    (hfull : commutatorAction (A.map a.action) (UH ⧸ V₁.subgroupOf UH) ≤ f.support i) :
    FixedPoints.subgroup (a.actors P) (UH ⧸ V₁.subgroupOf UH) ≤
      FixedPoints.subgroup (A.map a.action) (UH ⧸ V₁.subgroupOf UH) := by
  have hc := fixes_odd_complement (A.map a.action) (a.actors (f.factor i))
    ((card_map_of_injective hf).trans (f.star_card i))
    ((map_mono hn).trans (le_normalizer_map a.action)) hfull
  apply le_trans ?_ hc
  intro w hw b
  have hle : a.actors (f.factor i) ≤ a.actors P :=
    map_mono (map_mono (comap_mono (f.factor_le i)))
  exact hw ⟨b, hle b.property⟩

private theorem rank_one_split (hf : Function.Injective a.action)
    (f : Factorization a P)
    (hcard : Nat.card (Source.starImage H Uγ) = 2)
    (hn : ∀ i, Source.starImage H Uγ ≤ normalizer (Source.starImage H (f.factor i) : Set _))
    (hm : ∃ i, ⁅Source.starImage H Uγ, Source.starImage H (f.factor i)⁆ ≠ ⊥)
    (hbound : (FixedPoints.subgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)).index ≤ 4) :
    ∃ (e : Equiv.Perm (Fin f.count)) (r : RankOneFactors a P Uγ),
      r.factors = f.reindex e ∧ RankOneSplitData r := by
  classical
  obtain ⟨i, hi⟩ := hm
  obtain ⟨hplane, hinside⟩ := factor_plane hf f i _ hcard (hn i) hi
  have hAc : Nat.card (a.actors Uγ) = 2 := (card_map_of_injective hf).trans hcard
  obtain ⟨hfull, hfour⟩ := single_saturation (a.actors Uγ) (f.support i) hAc hplane hbound
  have hsupport : commutatorAction (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH) ≤ f.support i :=
    hfull ▸ hinside
  have hrest (j : Fin f.count) (hji : j ≠ i) :
      ⁅Source.starImage H Uγ, Source.starImage H (f.factor j)⁆ = ⊥ := by
    by_contra hmj
    obtain ⟨hjcard, hjinside⟩ := factor_plane hf f j _ hcard (hn j) hmj
    have hji' : commutatorSubgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)
        (f.support j) ≤ f.support i := (commutatorSubgroup_mono le_top).trans hsupport
    have hbot : commutatorSubgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)
        (f.support j) = ⊥ :=
      bot_unique ((le_inf hjinside hji').trans (f.support_disjoint j i hji).le_bot)
    change Nat.card (commutatorSubgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)
      (f.support j)) = 4 at hjcard
    rw [hbot, card_bot] at hjcard
    omega
  let z : Fin f.count := ⟨0, f.count_pos⟩
  let e : Equiv.Perm (Fin f.count) := Equiv.swap z i
  have hei : e z = i := Equiv.swap_apply_left z i
  have hother (j : Fin f.count) (hj : j.val ≠ 0) : e j ≠ i := by
    intro he
    have hjz : j = z := e.injective (he.trans hei.symm)
    exact hj (congrArg Fin.val hjz)
  let r : RankOneFactors a P Uγ := {
    factors := f.reindex e
    actor_card := hcard
    first_moved := by change ⁅_, Source.starImage H (f.factor (e z))⁆ ≠ ⊥; rw [hei]; exact hi
    remaining_fixed := fun j hj => hrest (e j) (hother j hj)
    moved_card := hfour }
  refine ⟨e, r, rfl, ?_⟩
  have hfirst : r.factors.support ⟨0, r.factors.count_pos⟩ = f.support i := by
    change f.support (e z) = f.support i
    rw [hei]
  constructor
  · rw [hfirst]
    exact hfull
  · rw [hfirst]
    exact hsupport
  · intro j hj
    exact factor_fixed hf f (e j) _ hcard (hrest (e j) (hother j hj))
  · exact factor_complement_fixed hf f i _ (hn i) hsupport

private theorem rank_two_split (hf : Function.Injective a.action)
    (f : Factorization a P) (hs : f.count = 2)
    (hcard : Nat.card (Source.starImage H Uγ) = 4)
    (A B : Subgroup (Source.Hstar H))
    (hAc : Nat.card A = 2) (hBc : Nat.card B = 2)
    (hgen : Source.starImage H Uγ = A ⊔ B)
    (hc : ⁅A, B⁆ = ⊥) (hd : Disjoint A B)
    (hnA : A ≤ normalizer (Source.starImage H (f.factor ⟨0, f.count_pos⟩) : Set _))
    (hnB : B ≤ normalizer (Source.starImage H (f.factor ⟨1, by omega⟩) : Set _))
    (hmA : ⁅A, Source.starImage H (f.factor ⟨0, f.count_pos⟩)⁆ ≠ ⊥)
    (hmB : ⁅B, Source.starImage H (f.factor ⟨1, by omega⟩)⁆ ≠ ⊥)
    (hfA : ⁅A, Source.starImage H (f.factor ⟨1, by omega⟩)⁆ = ⊥)
    (hfB : ⁅B, Source.starImage H (f.factor ⟨0, f.count_pos⟩)⁆ = ⊥)
    (hbound : (FixedPoints.subgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)).index ≤ 16) :
    ∃ r : RankTwoFactors a P Uγ, r.factors = f ∧ RankTwoSplitData r := by
  let z : Fin f.count := ⟨0, f.count_pos⟩
  let o : Fin f.count := ⟨1, by omega⟩
  have hzno : z ≠ o := by intro he; have := congrArg Fin.val he; simp [z, o] at this
  let A' := A.map a.action
  let B' := B.map a.action
  have hAc' : Nat.card A' = 2 := (card_map_of_injective hf).trans hAc
  have hBc' : Nat.card B' = 2 := (card_map_of_injective hf).trans hBc
  have hgen' : a.actors Uγ = A' ⊔ B' := by rw [StarAction.actors, hgen, Subgroup.map_sup]
  obtain ⟨hX, hXin⟩ := factor_plane hf f z A hAc hnA hmA
  obtain ⟨hY, hYin⟩ := factor_plane hf f o B hBc hnB hmB
  have hXB := factor_fixed hf f z B hBc hfB
  have hYA := factor_fixed hf f o A hAc hfA
  have hbound' : (FixedPoints.subgroup (A' ⊔ B' : Subgroup _) (UH ⧸ V₁.subgroupOf UH)).index ≤ 16 :=
    hgen' ▸ hbound
  obtain ⟨hfullA, hfullB, hrelative⟩ := split_saturation A' B' (f.support z) (f.support o)
    hAc' hBc' hXB hYA hX hY hbound'
  have hplaneA : Nat.card (commutatorAction A' (UH ⧸ V₁.subgroupOf UH)) = 4 := hfullA ▸ hX
  have hplaneB : Nat.card (commutatorAction B' (UH ⧸ V₁.subgroupOf UH)) = 4 := hfullB ▸ hY
  have hAX : commutatorAction A' (UH ⧸ V₁.subgroupOf UH) ≤ f.support z := hfullA ▸ hXin
  have hBY : commutatorAction B' (UH ⧸ V₁.subgroupOf UH) ≤ f.support o := hfullB ▸ hYin
  obtain ⟨hmoved, hindex⟩ := split_planes_equality_case A' B' (f.support z) (f.support o)
    hAc' hBc' hXB hfullA hplaneA hplaneB hAX hBY (f.support_disjoint z o hzno)
  let r : RankTwoFactors a P Uγ := {
    factors := f
    count_eq_two := hs
    actor_card := hcard
    first := A
    second := B
    first_card := hAc
    second_card := hBc
    generated := hgen
    commute := hc
    disjoint := hd
    first_moves := hmA
    second_moves := hmB
    first_fixes := hfA
    second_fixes := hfB
    first_plane := hplaneA
    second_plane := hplaneB
    moved_card := hgen'.symm ▸ hmoved
    fixed_index := hgen'.symm ▸ hindex }
  refine ⟨r, rfl, ⟨hgen'.symm ▸ hrelative, hfullA, hfullB, hAX, hBY, hXB, hYA, ?_⟩⟩
  have hCA := factor_complement_fixed hf f z A hnA hAX
  have hCB := factor_complement_fixed hf f o B hnB hBY
  intro w hw b
  have hfix : A' ⊔ B' ≤ MulAction.stabilizer (MulAut (UH ⧸ V₁.subgroupOf UH)) w :=
    sup_le (fun t ht => hCA hw ⟨t, ht⟩) (fun t ht => hCB hw ⟨t, ht⟩)
  exact hfix (hgen' ▸ b.property)

/-- The normalized, jointly faithful five-factor calculation, retaining the
supplied factors and all whole-quotient split-support identities. -/
theorem normalized_split_alternatives (hf : Function.Injective a.action)
    (f : Factorization a P) (hPH : P ≤ H)
    [IsElementaryAbelian 2 (Source.starImage H Uγ)]
    (hne : Source.starImage H Uγ ≠ ⊥)
    (hfaith : Source.starImage H Uγ ⊓ centralizer (Source.starImage H P : Set _) = ⊥)
    (hn : ∀ i, Source.starImage H Uγ ≤ normalizer (Source.starImage H (f.factor i) : Set _))
    (hbound : (FixedPoints.subgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)).index ≤
      (Nat.card (Source.starImage H Uγ)) ^ 2) :
    (∃ (e : Equiv.Perm (Fin f.count)) (r : RankOneFactors a P Uγ),
      r.factors = f.reindex e ∧ RankOneSplitData r) ∨
    (∃ r : RankTwoFactors a P Uγ, r.factors = f ∧ RankTwoSplitData r) := by
  have hfaith' : Source.starImage H Uγ ⊓
      centralizer ((⨆ i, Source.starImage H (f.factor i) : Subgroup _) : Set _) = ⊥ := by
    rw [← f.star_generated hPH]
    exact hfaith
  rcases normalized_actor_alternative f.count_pos f.count_le_two
    (fun i => Source.starImage H (f.factor i)) f.star_card
    (Source.starImage H Uγ) hne hn hfaith' with htwo | hfour
  · obtain ⟨hcard, hm⟩ := htwo
    have hb : (FixedPoints.subgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)).index ≤ 4 := by
      simpa only [hcard, Nat.reducePow] using hbound
    exact Or.inl (rank_one_split hf f hcard hn hm hb)
  · obtain ⟨hs, hcard, i, A, B, hi, hAE, hBE, hAc, hBc, hgen, hd, hc,
      hmA, hfA, hfB, hmB⟩ := hfour
    have hi' : i = (⟨1, by omega⟩ : Fin f.count) :=
      Fin.ext (by change i.val = 1; have := i.isLt; omega)
    subst i
    have hb : (FixedPoints.subgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)).index ≤ 16 := by
      simpa only [hcard, Nat.reducePow] using hbound
    exact Or.inr (rank_two_split hf f hs hcard A B hAc hBc hgen hc hd
      (hAE.trans (hn _)) (hBE.trans (hn _)) hmA hmB hfA hfB hb)

/-- The two source actor alternatives, with normalization and faithfulness
as the explicit algebraic prerequisites of this construction. -/
theorem normalized_rank_alternatives (hf : Function.Injective a.action)
    (f : Factorization a P) (hPH : P ≤ H)
    [IsElementaryAbelian 2 (Source.starImage H Uγ)]
    (hne : Source.starImage H Uγ ≠ ⊥)
    (hfaith : Source.starImage H Uγ ⊓ centralizer (Source.starImage H P : Set _) = ⊥)
    (hn : ∀ i, Source.starImage H Uγ ≤ normalizer (Source.starImage H (f.factor i) : Set _))
    (hbound : (FixedPoints.subgroup (a.actors Uγ) (UH ⧸ V₁.subgroupOf UH)).index ≤
      (Nat.card (Source.starImage H Uγ)) ^ 2) :
    Nonempty (RankOneFactors a P Uγ) ∨ Nonempty (RankTwoFactors a P Uγ) := by
  rcases normalized_split_alternatives hf f hPH hne hfaith hn hbound with
    ⟨_, r, _, _⟩ | ⟨r, _, _⟩
  · exact Or.inl ⟨r⟩
  · exact Or.inr ⟨r⟩

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.ActorAlternatives.SplitAction

end
