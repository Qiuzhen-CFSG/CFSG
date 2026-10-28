module
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.CyclicPrime
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.SourceReduction
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.InvolutionCentralizers
public import Theory.Representation.BinaryOffender.ComponentSum

/-!
# The common cyclic source reduction in D.2.17

The actual minimum actors of rank one are cyclic involution groups. Their
common minimum is their displacement rank, and they generate the original
actor. At ratio two every small-support involution is again starred.
After excluding the five-core branch, the other odd prime cores are central,
and the SQTK cover makes every involution centralizer in O₃ cyclic.
The Fitting-moved hypothesis is retained exactly as in the source.
Source: Aschbacher–Smith D.2.17–21 and the paragraph after D.2.22, pp.188–189.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal
namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

structure CoreHypotheses : Prop where
  faithful : Function.Injective ρ
  ratio_le : cubicRatio ρ ≤ 2
  generated : Jhat ρ = ⊤
  fitting : generalizedFitting G = fittingSubgroup G
  twoCore : pCore 2 G = ⊥
  rank_one : ∀ A ∈ QhatStar ρ, rank A = 1

structure Hypotheses : Prop extends CoreHypotheses ρ where
  indecomposable : IsRatioIndecomposable ρ
  moved : subspaceCommutator ρ ⊤ (fittingSubgroup G) = ⊤

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The cyclicity assumption in the source is exactly rank one. -/
theorem rank_one_of_cyclic {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hc : IsCyclic A) : rank A = 1 := by
  let := hc
  let := hA.1.2.1.2
  have hd : Nat.card A ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 A
  have he : Nat.card A = 2 := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
    (fun h => hA.1.2.1.1 ((eq_bot_iff_card A).mpr h))
  rw [rank, he]
  exact Nat.log_pow (by decide : 1 < 2) 1

omit [FiniteDimensional (ZMod 2) V] in
/-- The generator is retained in the original ambient group. -/
theorem starred_generator {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : rank A = 1) : ∃ t : G, orderOf t = 2 ∧ zpowers t = A := by
  let : IsElementaryAbelian 2 A := hA.1.2.1.2
  obtain ⟨a,ha⟩ := ne_bot_iff_exists_ne_one.mp hA.1.2.1.1
  have ht : orderOf (a : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (a : G) a.property)
    (fun h => ha (Subtype.ext h))
  refine ⟨a,ht,eq_of_le_of_card_ge (zpowers_le.mpr a.property) ?_⟩
  rw [hA.1.2.1.card_eq_two_pow_rank,hr,Nat.card_zpowers,ht]
  norm_num

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem starred_codimension {A : Subgroup G} (hA : A ∈ QhatStar ρ)
    (hr : rank A = 1) : (fixedCodim ρ A : ℝ≥0∞) = cubicRatio ρ := by
  simpa only [actionRatio,hr,Nat.cast_one,div_one] using hA.1.2.2.2

namespace CoreHypotheses
variable {ρ} (h : CoreHypotheses ρ)
include h

theorem ratio_one_or_two : cubicRatio ρ = 1 ∨ cubicRatio ρ = 2 := by
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr h.ratio_le
  exact QhatStar.ratio_one_or_two_of_rank_one ρ h.faithful hA (h.rank_one A hA)

theorem smallSupport_generated : closure (smallSupportInvolutions ρ) = ⊤ := by
  apply top_unique
  rw [← h.generated]
  apply sSup_le
  intro A hA
  obtain ⟨t,ht,he⟩ := starred_generator ρ hA (h.rank_one A hA)
  rw [← he]
  apply zpowers_le.mpr
  apply Subgroup.subset_closure
  refine ⟨ht,?_⟩
  change Module.finrank (ZMod 2) (ρ t - LinearMap.id).range ≤ 2
  rw [← fixedCodim_zpowers_eq_displacement_rank,he]
  have hd := (starred_codimension ρ hA (h.rank_one A hA)).trans_le h.ratio_le
  exact_mod_cast hd


/-- At ratio two there are no transvections, and every small involution
is itself an inclusion-minimal minimum actor. -/
theorem smallSupport_starred (hq : cubicRatio ρ = 2) {t : G}
    (ht : t ∈ smallSupportInvolutions ρ) :
    zpowers t ∈ QhatStar ρ ∧ fixedCodim ρ (zpowers t) = 2 := by
  obtain ⟨he,hr,hquad,_⟩ := involution_actor_rank_and_fixedCodim ρ t ht.1
  have hc := isCubic_of_isQuadratic hquad
  have hb : fixedCodim ρ (zpowers t) ≤ 2 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact ht.2
  have hl : 2 ≤ (fixedCodim ρ (zpowers t) : ℝ≥0∞) := by
    have hh : cubicRatio ρ ≤ actionRatio ρ (zpowers t) :=
      iInf_le_of_le (zpowers t) (iInf_le_of_le ⟨he,hc⟩ le_rfl)
    simpa only [hq,actionRatio,hr,Nat.cast_one,div_one] using hh
  have hd : fixedCodim ρ (zpowers t) = 2 := by
    have hl' : 2 ≤ fixedCodim ρ (zpowers t) := by exact_mod_cast hl
    omega
  refine ⟨⟨⟨h.ratio_le,he,hc,?_⟩,?_⟩,hd⟩
  · rw [actionRatio,hr,hd,hq]
    norm_num
  · intro B hB hBt
    exact eq_of_le_of_card_ge hBt (by
      rw [Nat.card_zpowers,ht.1]
      have hn : 1 < Nat.card B := (one_lt_card_iff_ne_bot B).mpr hB.2.1.1
      omega)

/-- Once the five-core branch is excluded, every other prime core is central. -/
theorem complement_central
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥) :
    ⊤ ≤ centralizer (SourceReduction.oddComplement G : Set G) := by
  rw [← h.generated]
  apply sSup_le
  intro A hA
  apply le_centralizer_iff.mpr
  refine iSup_le fun p => iSup_le fun hp => ?_
  apply commutator_eq_bot_iff_le_centralizer.mp
  by_cases he : p.1.1 = 2
  · rw [he,h.twoCore,commutator_bot_left]
  · by_contra hm
    have hprime := (source_lemma_D_2_13_cyclic_prime ρ h.faithful hA
      (h.rank_one A hA) ((Fact.out : p.1.1.Prime).odd_of_ne_two he) hm).1
    rcases hprime with h3 | h5
    · exact hp h3
    · exact hm (h5 ▸ hfive A hA)

theorem involution_not_centralizes_three
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (t : G) (ht : orderOf t = 2) : t ∉ centralizer (pCore 3 G : Set G) := by
  have htQ := h.complement_central hfive (mem_top t)
  intro htP
  have htF : t ∈ centralizer (fittingSubgroup G : Set G) := by
    rw [SourceReduction.fitting_eq_three_sup_complement (G := G)]
    intro x hx
    obtain ⟨p,hp,q,hq,rfl⟩ := mem_sup_of_normal_left.mp hx
    rw [mul_assoc,htQ q hq,← mul_assoc,htP p hp,mul_assoc]
  have hle : centralizer (fittingSubgroup G : Set G) ≤ fittingSubgroup G := by
    simpa only [h.fitting] using centralizer_generalizedFitting_le G
  have ho := (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot h.twoCore).of_dvd_nat
    ((fittingSubgroup G).orderOf_dvd_natCard (hle htF))
  rw [ht] at ho
  exact (by decide : ¬ Odd 2) ho

theorem involution_threeCore_centralizer_cyclic
    {H : Type*} [Group H] [Finite H] {K : GroupClass} (hH : IsSQTK K H)
    (f : H →* G) (honto : Function.Surjective f)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (t : G) (ht : orderOf t = 2) :
    IsCyclic (pCore 3 G ⊓ centralizer ({t} : Set G) : Subgroup G) :=
  cyclic_pSubgroup_in_involution_centralizer_of_surjective_rank_two
    (by decide : Odd 3) f honto (hH.stronglyQuasithin 3 (by decide) (by decide))
    (pCore 3 G) pCore_isPGroup t ht (h.involution_not_centralizes_three hfive t ht)
    (pCore 3 G ⊓ centralizer ({t} : Set G))
    (pCore_isPGroup.to_le inf_le_left) inf_le_right

end CoreHypotheses

omit [FiniteDimensional (ZMod 2) V] in
theorem Hypotheses.fixedSpace_eq_bot {ρ : Representation (ZMod 2) G V} (h : Hypotheses ρ) : fixedSpace ρ ⊤ = ⊥ :=
  fixedSpace_top_eq_bot_of_fitting_moved ρ h.twoCore h.moved

end CFSG.Quasithin.ChapterD.CyclicSource
