module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.BeforeMoved.Source
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourceAssembly
public import CFSG.Quasithin.ChapterD.Section02.RatioDecomposition.NormalOddSeed
public import Theory.GroupTheory.Fitting.NormalSylowFactorization
/-!
# A seed forces the original noncyclic ratio

Restrict to the normal closure of one original noncyclic starred actor and
intersect it with the ambient Fitting subgroup. Its image modulo that
intersection is a two-group, so a supplied Sylow subgroup supplements the
odd kernel. The actual Sylow-fixed generating seed makes the fixed summand
for the kernel coincide with the fixed summand for the normal closure.
Consequently the literal action on the kernel-moved subspace is faithful,
fully Fitting-moved, and retains the original starred actors. D.2.19 then
forces ratio 3/2; rank-one starred actors are excluded by the ratio-one/two
alternative.

Source: Aschbacher--Smith D.2.19, printed pp.187--188, with the original
Sylow-fixed seed from 15.1.2, printed p.1084.
-/
public section
namespace CFSG.Quasithin.ChapterD.BeforeMoved
open Subgroup Representation.BinaryOffender Theory.GroupTheory RatioDecomposition
variable {G V : Type*} [Group G] [Finite G] [Group.IsSolvable G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- An ambient Sylow-fixed generating seed forces the original ratio to be
3/2 as soon as one original starred actor is noncyclic. -/
theorem source_noncyclic_seed_ratio
    {H : Type*} [Group H] [Finite H] {C : GroupClass} (hH : IsSQTK C H)
    (f : H →* G) (honto : Function.Surjective f)
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (S : Sylow 2 G) (Z : Submodule (ZMod 2) V)
    (hZ : Z ≤ fixedSpace ρ (S : Subgroup G))
    (hspan : Submodule.span (ZMod 2) {w | ∃ g v, v ∈ Z ∧ ρ g v = w} = ⊤)
    {A : Subgroup G} (hA : A ∈ QhatStar ρ) (hr : 1 < rank A) :
    cubicRatio ρ = 3 / 2 ∧ ∀ B ∈ QhatStar ρ, 1 < rank B := by
  let N := normalClosure (A : Set G)
  let P := N ⊓ fittingSubgroup G
  let : N.Normal := inferInstanceAs (normalClosure (A : Set G)).Normal
  let : P.Normal := inferInstanceAs (N ⊓ fittingSubgroup G).Normal
  have hAN : A ≤ N := le_normalClosure
  have hPN : P ≤ N := inf_le_left
  have himage := source_normalClosure_image_two ρ hH f honto hf hA hr
    (generalizedFitting_eq_fitting_of_solvable G) hcore
  have hgen : N = P ⊔ (N ⊓ (S : Subgroup G)) :=
    eq_inf_sup_inf_sylow_of_quotient_image_isPGroup N (fittingSubgroup G) S himage
  have hodd : Odd (Nat.card P) :=
    (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot hcore).of_dvd_nat
      (card_dvd_of_le (show P ≤ fittingSubgroup G from inf_le_right))
  let σ := oddMovedAction ρ N P
  have ht := oddMovedAction_transport ρ N P S hodd hgen Z hZ hspan ⟨A,hA,hAN⟩
  have hA' : A.subgroupOf N ∈ QhatStar σ := by
    apply (ht.2 _).mpr
    rwa [map_subgroupOf_eq_of_le hAN]
  have hr' : 1 < rank (A.subgroupOf N) := by rwa [rank_subgroupOf hAN]
  have hfσ : Function.Injective σ :=
    oddMovedAction_faithful ρ hf N P S hodd hgen Z hZ hspan
  have hfull : subspaceCommutator σ ⊤ (fittingSubgroup N) = ⊤ :=
    oddMovedAction_full_of_le ρ N P hPN hodd _ (inf_fitting_subgroupOf_le N)
  have hcoreN : pCore 2 N = ⊥ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_bot]
    apply bot_unique
    exact (show (pCore 2 N).map N.subtype ≤ pCore 2 G from
      le_sSup ⟨inferInstance,pCore_isPGroup.map N.subtype⟩).trans_eq hcore
  have hqσ := (SourceReduction.solvable_source_ratio_and_noncyclic σ
    (hH.subgroup (N.comap f)) (f.subgroupComap N)
    (f.subgroupComap_surjective_of_surjective N honto) hfσ hA' hr' hcoreN hfull).2.1
  have hq : cubicRatio ρ = 3 / 2 := ht.1.symm.trans hqσ
  refine ⟨hq,?_⟩
  intro B hB
  have hp := hB.1.2.1.rank_pos
  by_contra hn
  have he : rank B = 1 := by omega
  rcases QhatStar.ratio_one_or_two_of_rank_one ρ hf hB he with h | h <;>
    rw [hq] at h <;> have hh := congrArg ENNReal.toReal h <;> norm_num at hh
end CFSG.Quasithin.ChapterD.BeforeMoved
