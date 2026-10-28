module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeSource
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Separation
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.NoSmallThreeFourSpace
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SaturatedSupport
public import Theory.Representation.NormalizedCThreeInvolution
public import Theory.Representation.BinaryOffender.CommutatorDisplacement
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.CyclicThreeNormalizer
public import Theory.GroupTheory.OddCyclicThreeNormalizer

/-!
# The normal cubic branch of D.2.26–29

A small-support involution centralizing a normal cubic subgroup with a
four-dimensional support fixes that support. Otherwise its displacement
fills the support, and the cyclic three-core commutator produces an
order-nine group on the same four-space, forcing a forbidden cubic plane.
An involution inverting the cubic subgroup fixes its complementary fixed
space by D.2.26. Source indecomposability then makes the support the entire
module, and the proved D.2.27 four-space endpoint supplies local generation.

Source: Aschbacher–Smith, D.2.26–29, pp.191–192. The remaining moving
order-nine branch supplies the normal cubic subgroup used here.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u
variable {G V : Type u} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem normal_support_stable (D : Subgroup G) [D.Normal] :
    ⊤ ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ D) := by
  apply le_subspaceStabilizer
  intro g hg v hv
  exact (subspaceCommutator_invariant_normalizer ρ
    (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
    (show (⊤ : Subgroup G) ≤ normalizer (D : Set G) by rw [normalizer_eq_top]) hg v).2 hv

private theorem small_commutator_idempotent (t : G) (ht : orderOf t = 2) :
    ⁅⁅pCore 3 G,zpowers t⁆,zpowers t⁆ = ⁅pCore 3 G,zpowers t⁆ := by
  apply Stellmacher.SectionOne.commutator_double_eq_self_of_coprime
  · rw [normalizer_eq_top]; exact le_top
  · obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
    rw [Nat.card_zpowers,ht,hn]
    exact (by decide : Nat.Coprime 2 3).pow_right n

/-- A small involution centralizing a normal cubic four-space actor fixes
its support. Otherwise its entire displacement lies in that support, forcing
a faithful elementary nine-group onto a four-space and hence a forbidden
cubic plane. -/
theorem CoreHypotheses.fixes_normal_cubic_support
    (h : CoreHypotheses ρ) (hq : cubicRatio ρ = 2)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (D : Subgroup G) [D.Normal] (hDR : D ≤ pCore 3 G) (hD : Nat.card D = 3)
    (hW : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D) = 4)
    (t : G) (ht : t ∈ smallSupportInvolutions ρ)
    (hF : Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3)
    (hcent : t ∈ centralizer (D : Set G)) :
    subspaceCommutator ρ ⊤ D ≤ fixedSpace ρ (zpowers t) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let := BinaryGroupAction.action ρ
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let : FaithfulSMul G (Multiplicative V) := BinaryGroupAction.faithful ρ h.faithful
  let F := ⁅pCore 3 G,zpowers t⁆
  let W := subspaceCommutator ρ ⊤ D
  let U := commutatorAction D (Multiplicative V)
  let : IsInvariant (zpowers t) (Multiplicative V) U :=
    commutatorAction_isInvariant_of_normalizing_actor (zpowers t) D le_normalizer_of_normal
  by_contra hn
  obtain ⟨v,hv,hvn⟩ := SetLike.not_le_iff_exists.mp hn
  have hne : ∃ v ∈ U, t • v ≠ v := by
    refine ⟨Multiplicative.ofAdd v,?_,?_⟩
    · change Multiplicative.ofAdd v ∈ commutatorAction D (Multiplicative V)
      rw [BinaryGroupAction.commutator_eq]; exact hv
    · intro he
      apply hvn
      rw [mem_fixedSpace_zpowers_iff]
      exact congrArg Multiplicative.toAdd he
  have hti : IsInvolution t :=
    ⟨fun he => by have hh := ht.1; simp [he] at hh,ht.1 ▸ pow_orderOf_eq_one t⟩
  have hUc : Nat.card U = 16 := by rw [BinaryGroupAction.commutator_card,hW]; norm_num
  have hfour := (normalizedCThree_involution_fixed_commutator_card_four
    (V := Multiplicative V) D t hD hti (by rw [normalizer_eq_top]; trivial) hUc hne).2
  have hmap : (commutatorAction (zpowers t) U).map U.subtype ≤
      commutatorAction (zpowers t) (Multiplicative V) := by
    rw [map_le_iff_le_comap,commutatorAction_eq_closure,closure_le]
    rintro _ ⟨a,v,rfl⟩
    change (v : Multiplicative V)⁻¹ * ((a : G) • (v : Multiplicative V)) ∈
      commutatorAction (zpowers t) (Multiplicative V)
    rw [commutatorAction_eq_closure]
    exact subset_closure ⟨a,(v : Multiplicative V),rfl⟩
  have heq : (commutatorAction (zpowers t) U).map U.subtype =
      commutatorAction (zpowers t) (Multiplicative V) := eq_of_le_of_card_ge hmap (by
    rw [card_map_of_injective U.subtype_injective,hfour,h.smallSupport_card_four hq ht])
  have hm : subspaceCommutator ρ ⊤ (zpowers t) ≤ W := by
    intro v hv
    have hh : Multiplicative.ofAdd v ∈ commutatorAction (zpowers t) (Multiplicative V) := by
      rw [BinaryGroupAction.commutator_eq]; exact hv
    have hhU := (map_subtype_le (commutatorAction (zpowers t) U)) (heq.symm ▸ hh)
    change Multiplicative.ofAdd v ∈ commutatorAction D (Multiplicative V) at hhU
    rw [BinaryGroupAction.commutator_eq] at hhU
    exact hhU
  have hfull : ⁅F,zpowers t⁆=F := small_commutator_idempotent t ht.1
  have hFW : subspaceCommutator ρ ⊤ F ≤ W :=
    subspaceCommutator_le_of_commutator_displacement ρ hfull
      (le_top.trans (normal_support_stable D)) (le_top.trans (normal_support_stable D)) hm
  have hFD : F ≤ centralizer (D : Set G) := by
    have hcop : Nat.Coprime 2 (Nat.card (pCore 3 G)) := by
      obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 3) (G := G)).exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 2 3).pow_right n
    have hDC := commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_odd_normalizes_card_three D (pCore 3 G) hD hcop
        le_normalizer_of_normal)
    exact (commutator_le_left _ _).trans (le_centralizer_iff.mp hDC)
  let : IsCyclic D := isCyclic_of_prime_card hD
  let : IsCyclic F := isCyclic_of_prime_card hF
  let : IsElementaryAbelian 3 D := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      rw [←hD]; exact pow_card_eq_one') }
  let : IsElementaryAbelian 3 F := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      rw [←hF]; exact pow_card_eq_one') }
  have hdis : Disjoint D F := by
    by_contra hd
    have hi : D ⊓ F ≠ ⊥ := by simpa only [disjoint_iff] using hd
    have he : D=F := by
      have hc : Nat.card (D ⊓ F : Subgroup G)=3 :=
        ((Nat.dvd_prime Nat.prime_three).mp (hD ▸ card_dvd_of_le (show D ⊓ F ≤ D from inf_le_left))).resolve_left
          (fun hc => hi ((eq_bot_iff_card _).mpr hc))
      exact (eq_of_le_of_card_ge inf_le_left (by rw [hc,hD])).symm.trans
        (eq_of_le_of_card_ge inf_le_right (by rw [hc,hF]))
    have hc : ⁅F,zpowers t⁆=⊥ := by
      rw [←he,commutator_comm,commutator_eq_bot_iff_le_centralizer]
      exact zpowers_le.mpr hcent
    have hb : F=⊥ := hfull.symm.trans hc
    have hh : Nat.card F=3 := hF
    rw [hb,card_bot] at hh; omega
  let : IsElementaryAbelian 3 (D ⊔ F : Subgroup G) := IsElementaryAbelian.sup_of_le_centralizer hFD
  have hEF : D ⊔ F ≤ pCore 3 G := sup_le hDR (commutator_le_left _ _)
  have hEcard : Nat.card (D ⊔ F : Subgroup G)=9 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint D F
      (hFD.trans (Subgroup.centralizer_le_normalizer _)) hdis,hD,hF]
  have hEs : subspaceCommutator ρ ⊤ (D ⊔ F) = W := by
    have he : subspaceCommutator ρ ⊤ (D ⊔ F) =
        subspaceCommutator ρ ⊤ D ⊔ subspaceCommutator ρ ⊤ F := by
      simpa only [iSup_bool_eq,Bool.false_eq_true,↓reduceIte] using
        subspaceCommutator_iSup_family ρ (fun b : Bool => if b then D else F)
    exact he.trans (sup_eq_left.mpr hFW)
  have hEc : Nat.card (commutatorAction (D ⊔ F : Subgroup G) (Multiplicative V))=16 := by
    rw [BinaryGroupAction.commutator_card,hEs]
    change 2 ^ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D)=16
    rw [hW]
    norm_num
  obtain ⟨X,hXE,hX,hXs⟩ := exists_small_three_support_of_nine
    (V := Multiplicative V) (D ⊔ F) hEcard hEc
  rw [BinaryGroupAction.commutator_card] at hXs
  exact hNo X (hXE.trans hEF) hX (Nat.pow_right_injective (by decide : 1<2) hXs)
/-- A normal cubic four-space actor fills the indecomposable source module. -/
theorem Hypotheses.normal_cubic_support_eq_top
    (h : Hypotheses ρ) (hq : cubicRatio ρ = 2)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X = 3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) ≠ 2)
    (hcyc : ∀ t ∈ smallSupportInvolutions ρ,
      Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G) = 3)
    (D : Subgroup G) [D.Normal] (hDR : D ≤ pCore 3 G) (hD : Nat.card D=3)
    (hW : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D)=4) :
    subspaceCommutator ρ ⊤ D=⊤ ∧ Module.finrank (ZMod 2) V=4 := by
  have hdich (A : Subgroup G) (hA : A ∈ QhatStar ρ) :
      subspaceCommutator ρ ⊤ D ≤ fixedSpace ρ A ∨ fixedSpace ρ D ≤ fixedSpace ρ A := by
    obtain ⟨t,ht,he⟩ := starred_generator ρ hA (h.rank_one A hA)
    have hsmall : t ∈ smallSupportInvolutions ρ := by
      refine ⟨ht,?_⟩
      change Module.finrank (ZMod 2) (ρ t-LinearMap.id).range ≤ 2
      rw [←fixedCodim_zpowers_eq_displacement_rank,he]
      exact_mod_cast (starred_codimension ρ hA (h.rank_one A hA)).trans_le h.ratio_le
    have hti : IsInvolution t :=
      ⟨fun he => by simp [he] at ht,ht ▸ pow_orderOf_eq_one t⟩
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one D
      (hD ▸ Nat.prime_three) t hti.2 (by rw [normalizer_eq_top]; trivial) with hc|hi
    · left
      rw [←he]
      exact h.toCoreHypotheses.fixes_normal_cubic_support hq hNo D hDR hD hW
        t hsmall (hcyc t hsmall) (mem_centralizer_iff.mpr (fun x hx => (hc x hx).eq.symm))
    · right
      have hDne : D ≠ ⊥ := fun hz => by rw [hz,card_bot] at hD; omega
      obtain ⟨x,hx⟩ := ne_bot_iff_exists_ne_one.mp hDne
      have hxne : (x:G)≠1 := fun hh => hx (Subtype.ext hh)
      have ho : orderOf (x:G)=3 := by
        apply orderOf_eq_prime
        · exact congrArg Subtype.val (show x^3=1 from hD ▸ pow_card_eq_one' (x := x))
        · exact hxne
      have hxD : zpowers (x:G)=D := eq_of_le_of_card_ge (zpowers_le.mpr x.property)
        (by rw [Nat.card_zpowers,ho,hD])
      have hh := h.toCoreHypotheses.inverted_threeCore_support hq hNo hsmall
        (hDR x.property) hxne (hi x x.property)
      rw [hxD,he] at hh
      exact hh.2.2.1
  have hne : subspaceCommutator ρ ⊤ D ≠ ⊥ := by
    intro hz
    rw [hz,finrank_bot] at hW
    omega
  have hN : (⊤ : Subgroup G) ≤ normalizer (D : Set G) := by rw [normalizer_eq_top]
  have htop := (support_eq_top_of_starred_dichotomy ρ h.generated h.indecomposable
    h.fixedSpace_eq_bot (subspaceCommutator ρ ⊤ D) (fixedSpace ρ D)
    (ElementaryCore.SupportExclusion.moved_split ρ D (by rw [hD]; decide)).symm
    (fun g v hv => (subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hN (mem_top g) v).2 hv)
    (fun g v hv => (fixedSpace_invariant_normalizer ρ hN (mem_top g) v).2 hv)
    hne hdich).1
  refine ⟨htop,?_⟩
  rw [htop,finrank_top] at hW
  exact hW

/-- The normal cubic branch feeds the literal D.2.27 endpoint. -/
theorem Hypotheses.normal_cubic_localGeneration
    (h : Hypotheses ρ) (hq : cubicRatio ρ = 2)
    (hfive : ∀ A ∈ QhatStar ρ, ⁅pCore 5 G,A⁆=⊥)
    (hNo : ∀ X : Subgroup G, X ≤ pCore 3 G → Nat.card X=3 →
      Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X)≠2)
    (hcyc : ∀ t ∈ smallSupportInvolutions ρ,
      Nat.card (⁅pCore 3 G,zpowers t⁆ : Subgroup G)=3)
    (D : Subgroup G) [D.Normal] (hDR : D ≤ pCore 3 G) (hD : Nat.card D=3)
    (hW : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ D)=4) :
    Nonempty (LocalGeneration ρ) :=
  h.finrank_four_localGeneration hq hfive hNo
    (h.normal_cubic_support_eq_top hq hNo hcyc D hDR hD hW).2
end CFSG.Quasithin.ChapterD.CyclicSource
