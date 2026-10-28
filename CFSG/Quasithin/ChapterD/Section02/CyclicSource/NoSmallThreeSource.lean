module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeInverted
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeLocal
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Preparation
public import Theory.Representation.CyclicFixedRank
public import Theory.Representation.GoldschmidtONan.Basic
/-!
# The original no-small-three source action

Transport D.2.26 and the local cyclic-three/extraspecial alternatives to
the given faithful binary representation. Every starred involution fixes
the fixed space of one inverted cubic subgroup. Generation by the starred
family and the original Fitting-moved hypothesis therefore give C_V(O₃)=0
and [V,O₃]=V, without removing a summand or changing the actor.
Source: Aschbacher–Smith D.2.26–29, pp.191–192.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterD.CyclicSource
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

private theorem faithful_fixing_bot
    {G W : Type*} [Group G] [Group W] [MulDistribMulAction G W] [FaithfulSMul G W] :
    fixingSubgroup G (Set.univ : Set W) = ⊥ := by
  apply bot_unique
  intro g hg
  apply eq_of_smul_eq_smul (α := W)
  intro w
  simpa only [one_smul] using ((mem_fixingSubgroup_iff (M := G)).mp hg w trivial)

omit [Finite G] in
private theorem no_small_three_card
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2) :
    let := BinaryGroupAction.action ρ
    ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Nat.card (commutatorAction X (Multiplicative V)) ≠ 4 := by
  let := BinaryGroupAction.action ρ
  dsimp only
  intro X hX hcard hs
  rw [BinaryGroupAction.commutator_card] at hs
  exact hNo X hX hcard (Nat.pow_right_injective (by decide : 1 < 2) hs)

theorem CoreHypotheses.smallSupport_card_four (h : CoreHypotheses ρ)
    (hq : cubicRatio ρ = 2) {t : G} (ht : t ∈ smallSupportInvolutions ρ) :
    let := BinaryGroupAction.action ρ
    Nat.card (commutatorAction (zpowers t) (Multiplicative V)) = 4 := by
  let := BinaryGroupAction.action ρ
  dsimp only
  rw [BinaryGroupAction.commutator_card, CyclicFixedRank.commutator_eq_range,
    ← fixedCodim_zpowers_eq_displacement_rank, (h.smallSupport_starred hq ht).2]
  norm_num

theorem CoreHypotheses.smallSupport_index_four (h : CoreHypotheses ρ)
    (hq : cubicRatio ρ = 2) {t : G} (ht : t ∈ smallSupportInvolutions ρ) :
    let := BinaryGroupAction.action ρ
    Nat.card (Multiplicative V) =
      4 * Nat.card (FixedPoints.subgroup (zpowers t) (Multiplicative V)) := by
  let := BinaryGroupAction.action ρ
  dsimp only
  rw [Nat.card_congr Multiplicative.toAdd, BinaryGroupAction.fixedPoints_eq,
    BinaryGroupAction.card_submoduleEquivSubgroup,
    Module.natCard_eq_pow_finrank (K := ZMod 2),
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    ← fixedCodim_add_finrank ρ (zpowers t), (h.smallSupport_starred hq ht).2, pow_add]
  norm_num [Module.natCard_eq_pow_finrank (K := ZMod 2)]

theorem CoreHypotheses.inverted_threeCore_support (h : CoreHypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    {t x : G} (ht : t ∈ smallSupportInvolutions ρ)
    (hx : x ∈ pCore 3 G) (hne : x ≠ 1) (hinv : t*x*t⁻¹=x⁻¹) :
    orderOf x = 3 ∧ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (zpowers x)) = 4 ∧
      fixedSpace ρ (zpowers x) ≤ fixedSpace ρ (zpowers t) ∧
      ∀ y : G, Commute y x →
        (∀ v ∈ subspaceCommutator ρ ⊤ (zpowers x), ρ y v = v) → Commute y t := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := BinaryGroupAction.faithful ρ h.faithful
  have hti : IsInvolution t := ⟨fun he => by have hh := ht.1; simp [he] at hh, ht.1 ▸ pow_orderOf_eq_one t⟩
  obtain ⟨h3,hs,_,hfix,hcent⟩ := inverted_threeCore_no_small_support
    (V := Multiplicative V) x t hne hx hti hinv (h.smallSupport_card_four hq ht)
    faithful_fixing_bot (no_small_three_card hNo)
  rw [BinaryGroupAction.commutator_card] at hs
  refine ⟨h3,Nat.pow_right_injective (by decide : 1 < 2) hs,?_,?_⟩
  · intro v hv
    rw [mem_fixedSpace_zpowers_iff]
    exact congrArg Multiplicative.toAdd (hfix (Multiplicative.ofAdd v) hv)
  · intro y hy hys
    apply hcent y hy
    intro v hv
    rw [BinaryGroupAction.commutator_eq] at hv
    exact congrArg Multiplicative.ofAdd (hys v.toAdd hv)

private theorem exists_inverted_of_nontrivial_commutator
    {G : Type*} [Group G] (P : Subgroup G) [P.Normal]
    (t : G) (ht : IsInvolution t) (hm : ⁅P, zpowers t⁆ ≠ ⊥) :
    ∃ x ∈ P, x ≠ 1 ∧ t * x * t⁻¹ = x⁻¹ := by
  have hex : ∃ y ∈ P, ⁅y, t⁆ ≠ 1 := by
    by_contra! h
    apply hm
    rw [commutator_eq_bot_iff_le_centralizer]
    intro y hy
    rw [mem_centralizer_iff]
    intro a ha
    obtain ⟨n, rfl⟩ := ha
    exact ((commutatorElement_eq_one_iff_commute.mp (h y hy)).symm.zpow_left n).eq
  obtain ⟨y, hy, hn⟩ := hex
  refine ⟨⁅y,t⁆, commutator_le_left P (zpowers t)
    (commutator_mem_commutator hy (mem_zpowers t)), hn, ?_⟩
  have htt : t * t = 1 := by simpa only [pow_two] using ht.2
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  simp only [commutatorElement_def, mul_inv_rev, inv_inv, hti, mul_assoc, htt, mul_one]

theorem CoreHypotheses.exists_inverted_threeCore (h : CoreHypotheses ρ)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (t : G) (ht : orderOf t = 2) :
    ∃ x ∈ pCore 3 G, x ≠ 1 ∧ t*x*t⁻¹=x⁻¹ := by
  apply exists_inverted_of_nontrivial_commutator (pCore 3 G) t
    ⟨fun he => by simp [he] at ht,ht ▸ pow_orderOf_eq_one t⟩
  intro he
  exact h.involution_not_centralizes_three hfive t ht
    ((commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm (pCore 3 G) (zpowers t)).symm.trans he)) (mem_zpowers t))

theorem CoreHypotheses.local_threeCore_alternatives (h : CoreHypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    {t : G} (ht : t ∈ smallSupportInvolutions ρ) :
    (Nat.card (⁅pCore 3 G, zpowers t⁆ : Subgroup G) = 3 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅pCore 3 G,zpowers t⁆) = 4) ∨
    (IsExtraspecial 3 (⁅pCore 3 G, zpowers t⁆ : Subgroup G) ∧
      Nat.card (⁅pCore 3 G, zpowers t⁆ : Subgroup G) = 27 ∧
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ ⁅pCore 3 G,zpowers t⁆) = 6 ∧
      ⁅(center (⁅pCore 3 G, zpowers t⁆ : Subgroup G)).map
        (⁅pCore 3 G, zpowers t⁆ : Subgroup G).subtype, zpowers t⁆ = ⊥) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := BinaryGroupAction.faithful ρ h.faithful
  have hm : ⁅pCore 3 G,zpowers t⁆ ≠ ⊥ := by
    intro he
    exact h.involution_not_centralizes_three hfive t ht.1
      ((commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm (pCore 3 G) (zpowers t)).symm.trans he)) (mem_zpowers t))
  have hti : IsInvolution t := ⟨fun he => by have hh := ht.1; simp [he] at hh,ht.1 ▸ pow_orderOf_eq_one t⟩
  rcases threeCore_commutator_alternatives t hti hm (h.smallSupport_index_four hq ht).le
    (no_small_three_card hNo) with ⟨hc,hd⟩ | ⟨hex,hc,hd,hcent⟩
  · rw [BinaryGroupAction.commutator_card] at hd
    exact Or.inl ⟨hc,Nat.pow_right_injective (by decide : 1 < 2) hd⟩
  · rw [BinaryGroupAction.commutator_card] at hd
    exact Or.inr ⟨hex,hc,Nat.pow_right_injective (by decide : 1 < 2) hd,hcent⟩

/-- The three-core fixes no vector in the original source module. Every
starred involution fixes the fixed space of one of its inverted cubic lines. -/
theorem Hypotheses.threeCore_fixed_eq_bot (h : Hypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2) :
    fixedSpace ρ (pCore 3 G) = ⊥ := by
  have hfix : fixedSpace ρ (pCore 3 G) ≤ fixedSpace ρ (Jhat ρ) := by
    change fixedSpace ρ (pCore 3 G) ≤ fixedSpace ρ (sSup (QhatStar ρ))
    rw [sSup_eq_iSup',fixedSpace_iSup_family]
    apply le_iInf
    intro A
    obtain ⟨t,ht,he⟩ := starred_generator ρ A.property (h.rank_one A A.property)
    have hsmall : t ∈ smallSupportInvolutions ρ := by
      refine ⟨ht,?_⟩
      change Module.finrank (ZMod 2) (ρ t - LinearMap.id).range ≤ 2
      rw [← fixedCodim_zpowers_eq_displacement_rank,he]
      have hh := (starred_codimension ρ A.property (h.rank_one A A.property)).trans_le h.ratio_le
      exact_mod_cast hh
    obtain ⟨x,hx,hne,hinv⟩ := h.toCoreHypotheses.exists_inverted_threeCore hfive t ht
    have hi := h.toCoreHypotheses.inverted_threeCore_support hq hNo hsmall hx hne hinv
    exact (fixedSpace_antitone ρ (zpowers_le.mpr hx)).trans (he ▸ hi.2.2.1)
  rw [h.generated,h.fixedSpace_eq_bot] at hfix
  exact le_bot_iff.mp hfix

/-- In the no-small-three source branch the three-core itself moves the
whole original module, as asserted after D.2.26. -/
theorem Hypotheses.threeCore_moved_eq_top (h : Hypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2) :
    subspaceCommutator ρ ⊤ (pCore 3 G) = ⊤ := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
  have ho : Odd (Nat.card (pCore 3 G)) := by
    rw [hn]
    exact (by decide : Odd 3).pow
  have hc : IsCompl (fixedSpace ρ (pCore 3 G)) (subspaceCommutator ρ ⊤ (pCore 3 G)) := by
    simpa only [RegularCyclicNormalClosure.displacementSpan, subspaceCommutator, eq_comm] using
      (GoldschmidtONan.isCompl_fixed_moved_of_odd (ρ := ρ) ho)
  simpa only [h.threeCore_fixed_eq_bot hq hfive hNo,bot_sup_eq] using hc.sup_eq_top

end CFSG.Quasithin.ChapterD.CyclicSource
