module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeSource
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.LocalGeneration
public import Theory.GroupAction.ThreeGroupSixteenFaithful
public import Theory.GroupTheory.InvolutionGeneratedAbelianKernel
public import Theory.GroupTheory.CyclicThreeNormalizer
/-!
# The four-dimensional no-small-three endpoint

A faithful three-group on a binary four-space is elementary of order at
most nine. The order-nine case contains a cubic plane, so the source
exclusion makes O₃ have order three. Its conjugation action has order two;
the self-centralizing Fitting subgroup and the central complementary prime
cores give a Fitting-by-involution factorization. Involution generation
then removes the odd central factor, yielding the original kernel and
involution required by the endpoint classification.
Source: Aschbacher–Smith D.2.27, p.191.
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
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

/-- No cubic plane excludes the order-nine three-core in dimension four. -/
theorem Hypotheses.threeCore_card_three_of_finrank_four (h : Hypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (hdim : Module.finrank (ZMod 2) V = 4) : Nat.card (pCore 3 G) = 3 := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := BinaryGroupAction.faithful ρ h.faithful
  have hcard : Nat.card (Multiplicative V) = 16 := by
    rw [Nat.card_congr Multiplicative.toAdd,Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod,hdim]
    norm_num
  obtain ⟨hR,hbound⟩ := three_group_faithful_sixteen_is_elementary
    (pCore_isPGroup (p := 3) (G := G)) hcard
    (faithful_fixing_bot (G := pCore 3 G) (W := Multiplicative V))
  let : IsElementaryAbelian 3 (pCore 3 G) := hR
  have hne : pCore 3 G ≠ ⊥ := by
    intro he
    have hm := h.threeCore_moved_eq_top hq hfive hNo
    rw [he] at hm
    have hz : (⊥ : Submodule (ZMod 2) V) = ⊤ := by
      have hb : subspaceCommutator ρ ⊤ (⊥ : Subgroup G) = ⊥ :=
        (subspaceCommutator_eq_bot_iff _ _ _).mpr (by rw [fixedSpace_bot])
      exact hb.symm.trans hm
    have hh := congrArg (fun W : Submodule (ZMod 2) V => Module.finrank (ZMod 2) W) hz
    simp [hdim] at hh
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
  have hnle : n ≤ 2 := by
    by_contra hh
    have hp : 27 ≤ 3 ^ n := Nat.pow_le_pow_right (by decide : 1 ≤ (3:ℕ)) (by omega : 3 ≤ n)
    omega
  interval_cases n
  · exact (hne ((card_eq_one).mp (by simpa using hn))).elim
  · simpa using hn
  · have hmove : Nat.card (commutatorAction (pCore 3 G) (Multiplicative V)) = 16 := by
      rw [BinaryGroupAction.commutator_card,h.threeCore_moved_eq_top hq hfive hNo,
        finrank_top,hdim]
      norm_num
    obtain ⟨X,hXR,hX,hXs⟩ := exists_small_three_support_of_nine
      (V := Multiplicative V) (pCore 3 G) hn hmove
    rw [BinaryGroupAction.commutator_card] at hXs
    exact (hNo X hXR hX (Nat.pow_right_injective (by decide : 1 < 2) hXs)).elim

/-- A cyclic three-core is the whole odd kernel in this involution-generated
source group: the central complementary Fitting factor disappears in the
abelianization. -/
theorem CoreHypotheses.threeCore_card_three_generation (h : CoreHypotheses ρ)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hRcard : Nat.card (pCore 3 G) = 3)
    (t : G) (ht : orderOf t = 2) :
    pCore 3 G ⊔ zpowers t = ⊤ ∧ ⁅pCore 3 G,zpowers t⁆ = pCore 3 G := by
  let R := pCore 3 G
  let F := fittingSubgroup G
  let C := SourceReduction.oddComplement G
  have hF : F = R ⊔ C := SourceReduction.fitting_eq_three_sup_complement
  have hC : ⊤ ≤ centralizer (C : Set G) := h.complement_central hfive
  have hCF : centralizer (R : Set G) ≤ F := by
    have hf : centralizer (F : Set G) ≤ F := by
      simpa only [h.fitting] using centralizer_generalizedFitting_le G
    apply le_trans ?_ hf
    intro g hg
    rw [hF]
    intro y hy
    obtain ⟨r,hr,c,hc,rfl⟩ := mem_sup_of_normal_left.mp hy
    rw [mul_assoc,hC (mem_top g) c hc,← mul_assoc,hg r hr,mul_assoc]
  have hRne : R ≠ ⊥ := by
    intro he
    have hh : Nat.card R = 1 := card_eq_one.mpr he
    change Nat.card R = 3 at hRcard
    omega
  obtain ⟨x,hxne⟩ := ne_bot_iff_exists_ne_one.mp hRne
  have hxG : (x:G) ≠ 1 := fun he => hxne (Subtype.ext he)
  have hgenx := (cyclicThree_generator R hRcard x x.property hxG).1
  have hfix (g : G) (he : g*(x:G)*g⁻¹=x) : g ∈ centralizer (R : Set G) := by
    intro y hy
    rw [← hgenx] at hy
    obtain ⟨n,rfl⟩ := hy
    exact (Commute.zpow_left (show Commute (x:G) g from
      (mul_inv_eq_iff_eq_mul.mp he).symm) n).eq
  have hinv : t*(x:G)*t⁻¹=(x:G)⁻¹ := by
    rcases cyclicThree_normalizer_conjugates R hRcard x x.property hxG t
      (le_normalizer_of_normal (mem_top t)) with hc | hi
    · exact (h.involution_not_centralizes_three hfive t ht (hfix t hc)).elim
    · exact hi
  have hFG : F ⊔ zpowers t = ⊤ := by
    apply top_unique
    intro g _
    rcases cyclicThree_normalizer_conjugates R hRcard x x.property hxG g
      (le_normalizer_of_normal (mem_top g)) with hc | hi
    · exact mem_sup_left (hCF (hfix g hc))
    · have hgt : g*t ∈ F := by
        apply hCF
        apply hfix
        calc
          (g*t)*(x:G)*(g*t)⁻¹ = g*(t*(x:G)*t⁻¹)*g⁻¹ := by group
          _ = g*(x:G)⁻¹*g⁻¹ := by rw [hinv]
          _ = (g*(x:G)*g⁻¹)⁻¹ := by group
          _ = x := by rw [hi,inv_inv]
      have hh := (F ⊔ zpowers t).mul_mem (mem_sup_left hgt)
        (mem_sup_right ((zpowers t).inv_mem (mem_zpowers t)))
      simpa only [mul_inv_cancel_right] using hh
  have hFcomm (A : Subgroup G) : ⁅F,A⁆ ≤ R := by
    rw [hF]
    apply commutator_sup_le_of_relative_normal ⊤ R C A R
      le_normalizer_of_normal le_top le_top (commutator_le_left _ _)
    have hc : ⁅C,A⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr (le_top.trans hC)
    rw [hc]
    exact bot_le
  have htcomm : ⁅zpowers t,⊤⁆ ≤ R := by
    rw [commutator_comm,← hFG]
    apply commutator_sup_le_of_relative_normal ⊤ F (zpowers t) (zpowers t) R
      le_normalizer_of_normal le_top le_top (hFcomm _)
    rw [commutator_self_eq_bot_iff.mpr inferInstance]
    exact bot_le
  have hder : _root_.commutator G ≤ R := by
    rw [_root_.commutator_def]
    conv_lhs => lhs; rw [← hFG]
    exact commutator_sup_le_of_relative_normal ⊤ F (zpowers t) ⊤ R
      le_normalizer_of_normal le_top le_top (hFcomm _) htcomm
  have hFR : F ≤ R :=
    (le_commutator_of_odd_of_involution_generated h.smallSupport_generated
      (fun s hs => hs.1 ▸ pow_orderOf_eq_one s) F
      (ChapterG.Section08.fitting_odd_of_twoCore_eq_bot h.twoCore)).trans hder
  have hRF : F = R := le_antisymm hFR (pCore_le_fitting G 3)
  have hRG : R ⊔ zpowers t = ⊤ := hRF ▸ hFG
  refine ⟨hRG,?_⟩
  let : IsCyclic R := isCyclic_of_prime_card hRcard
  exact odd_abelian_kernel_eq_commutator_of_involution_generated h.smallSupport_generated
    (fun s hs => hs.1 ▸ pow_orderOf_eq_one s) R (by rw [hRcard]; decide) (zpowers t) hRG

/-- D.2.27's four-dimensional source endpoint, without any added normalizer
model or generation premise. -/
theorem Hypotheses.threeCore_card_three_localGeneration (h : Hypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (hR : Nat.card (pCore 3 G) = 3) : Nonempty (LocalGeneration ρ) := by
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr h.ratio_le
  obtain ⟨t,ht,he⟩ := starred_generator ρ hA (h.rank_one A hA)
  obtain ⟨hgen,hcomm⟩ := h.toCoreHypotheses.threeCore_card_three_generation hfive hR t ht
  refine ⟨{
    kernel := pCore 3 G
    normal := inferInstance
    prime := 3
    prime_prime := by decide
    prime_odd := by decide
    pgroup := pCore_isPGroup
    nontrivial := ?_
    involution := t
    order_two := ht
    generated := hgen
    commutator := hcomm
    moved := h.threeCore_moved_eq_top hq hfive hNo
    codimension := ?_
  }⟩
  · intro hz
    rw [hz,card_bot] at hR
    norm_num at hR
  · rw [he]
    exact_mod_cast (starred_codimension ρ hA (h.rank_one A hA)).trans_le h.ratio_le

/-- The four-dimensional source branch produces the literal local-generation
witness; order nine is excluded by the missing cubic-plane hypothesis. -/
theorem Hypotheses.finrank_four_localGeneration (h : Hypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆ = ⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (hdim : Module.finrank (ZMod 2) V = 4) : Nonempty (LocalGeneration ρ) :=
  h.threeCore_card_three_localGeneration hq hfive hNo
    (h.threeCore_card_three_of_finrank_four hq hfive hNo hdim)

end CFSG.Quasithin.ChapterD.CyclicSource
