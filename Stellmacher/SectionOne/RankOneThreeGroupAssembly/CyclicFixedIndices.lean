module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaGeneration
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaActions
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaIndependence
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaCounting
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Support
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.OmegaFixedIndices
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.SupportCentralizers
public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.LocalFixedIndex

/-!
# Cyclic fixed indices and minimal partner support

The fixed index of an arbitrary Sylow involution is the power of two given by its support. A minimal partner in a local order-four coordinate loses a factor, which bounds its offender ratio and identifies its fixed-module centralizer.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

/-- For a nonidentity element of the elementary abelian Sylow group, the
fixed quotient on the complete omega action module is `2` to the number of
omega coordinates moved by that element. -/
public theorem fixedQuotientCard_oddCore_zpowers_eq_pow_support
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    [DecidableEq (Subgroup G)]
    (S : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hnorm : ∀ K : Subgroup G, oneOmega (G := G) (V := V) K →
      S ≤ Subgroup.normalizer K)
    (hcoreEq : oddCore G = oneOmegaGenerated (G := G) (V := V))
    (hdecomp : LemmaOneFourConclusion (G := G) (V := V)
      (oneOmegaGenerated (G := G) (V := V))
      (oneOmegaFinset (G := G) (V := V)))
    (s : S) (hsne : s ≠ 1) :
    fixedQuotientCard (G := G) (V := V)
        (Subgroup.zpowers (s : G))
        (commutatorAction (oddCore G) V) =
      (2 : ℚ) ^
        (omegaSupport (G := G) (V := V) S hnorm s).card := by
  classical
  let B : Subgroup G := Subgroup.zpowers (s : G)
  let Ω := oneOmegaFinset (G := G) (V := V)
  let X := omegaSupport (G := G) (V := V) S hnorm s
  let Y := Ω \ X
  let UX : Subgroup V := X.sup (fun F => commutatorAction F V)
  let UY : Subgroup V := Y.sup (fun F => commutatorAction F V)
  let U : Subgroup V := Ω.sup (fun F => commutatorAction F V)
  have hXsub : X ⊆ Ω := omegaSupport_subset_oneOmegaFinset S hnorm s
  have hXY : Disjoint X Y := by
    exact Finset.disjoint_sdiff
  have hOmegaUnion : X ∪ Y = Ω := Finset.union_sdiff_of_subset hXsub
  have hOmegaCard : Ω.card = X.card + Y.card := by
    rw [← hOmegaUnion, Finset.card_union_of_disjoint hXY]
  have hΩ (F : Subgroup G) (hF : F ∈ Ω) :
      oneOmega (G := G) (V := V) F :=
    (mem_oneOmegaFinset_iff (G := G) (V := V) F).mp hF
  have hX (F : Subgroup G) (hF : F ∈ X) :
      oneOmega (G := G) (V := V) F := hΩ F (hXsub hF)
  have hY (F : Subgroup G) (hF : F ∈ Y) :
      oneOmega (G := G) (V := V) F := hΩ F (Finset.sdiff_subset hF)
  have hBcard : Nat.card B = 2 :=
    natCard_zpowers_eq_two_of_ne_one_of_elementary S hS s hsne
  have hBleS : B ≤ S := (Subgroup.zpowers_le).mpr s.property
  let hBelem : IsElementaryAbelian 2 B := by
    refine {
      toIsMulCommutative := {
        is_comm := ⟨?_⟩ }
      exponent_dvd_p := ?_ }
    · intro a b
      exact Subtype.ext (congrArg (fun z : S => (z : G))
        ((hS.toIsMulCommutative.is_comm.comm
          (⟨a, hBleS a.property⟩ : S) (⟨b, hBleS b.property⟩ : S))))
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
      intro b
      apply Subtype.ext
      have hb := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        hS.exponent_dvd_p (⟨b, hBleS b.property⟩ : S)
      simpa using congrArg Subtype.val hb
  let _ : IsElementaryAbelian 2 B := hBelem
  have hnormB : ∀ F : Subgroup G,
      oneOmega (G := G) (V := V) F → B ≤ Subgroup.normalizer F := by
    intro F hF
    exact hBleS.trans (hnorm F hF)
  have hXfull : ∀ F ∈ X, ⁅F, B⁆ = F := by
    intro F hF
    exact commutator_oneOmega_zpowers_eq_self_of_mem_support
      S hnorm s F (hX F hF) hF
  have hUXcard : Nat.card UX = 4 ^ X.card :=
    natCard_finset_sup_oneOmega_action hdecomp X hX
  have hUXfixed : Nat.card (↥(UX ⊓ FixedPoints.subgroup B V)) =
      2 ^ X.card :=
    natCard_fixed_finset_sup_oneOmega_action_of_full_commutator
      B hBelem hnormB hdecomp X hX hXfull
  have hUYcard : Nat.card UY = 4 ^ Y.card :=
    natCard_finset_sup_oneOmega_action hdecomp Y hY
  have hUYfixed : UY ≤ FixedPoints.subgroup B V := by
    apply Finset.sup_le
    intro F hFY
    have hFnotX : F ∉ X := (Finset.mem_sdiff.mp hFY).2
    have hFcomm : ⁅F, B⁆ = ⊥ :=
      commutator_oneOmega_zpowers_eq_bot_of_not_mem_support
        S hnorm s F (hY F hFY) hFnotX
    have hFfix : B ≤
        fixingSubgroup G (commutatorAction F V : Set V) :=
      Stellmacher.SectionOne.oneOmega_card_two_centralizer_fixes_commutator
        F B (hY F hFY) hBcard hFcomm
    intro u hu
    rw [FixedPoints.mem_subgroup]
    intro b
    exact ((mem_fixingSubgroup_iff (M := G)
      (s := (commutatorAction F V : Set V))).mp
        (hFfix b.property)) u hu
  have hUYfixedCard : Nat.card (↥(UY ⊓ FixedPoints.subgroup B V)) =
      4 ^ Y.card := by
    rw [inf_eq_left.mpr hUYfixed, hUYcard]
  have hdisj : Disjoint UX UY :=
    disjoint_finset_sup_oneOmega_action hdecomp X Y hX hY hXY
  let hUXinv : IsInvariant B V UX :=
    isInvariant_finset_sup X (fun F => commutatorAction F V)
      (fun F hF =>
        commutatorAction_isInvariant_of_normalizing_actor B F
          (hnormB F (hX F hF)))
  let hUYinv : IsInvariant B V UY :=
    isInvariant_finset_sup Y (fun F => commutatorAction F V)
      (fun F hF =>
        commutatorAction_isInvariant_of_normalizing_actor B F
          (hnormB F (hY F hF)))
  let _ : IsInvariant B V UX := hUXinv
  let _ : IsInvariant B V UY := hUYinv
  have hfixedProduct : Nat.card (↥((UX ⊔ UY) ⊓
      FixedPoints.subgroup B V)) = 2 ^ X.card * 4 ^ Y.card := by
    rw [natCard_inf_fixedPoints_sup_eq_mul (A := B) UX UY hdisj,
      hUXfixed, hUYfixedCard]
  have hUeqUnion : U = UX ⊔ UY := by
    dsimp only [U, UX, UY]
    rw [← Finset.sup_union, hOmegaUnion]
  have hUeq : commutatorAction (oddCore G) V = U := by
    calc
      commutatorAction (oddCore G) V =
          commutatorAction (oneOmegaGenerated (G := G) (V := V)) V := by
        rw [hcoreEq]
      _ = ⨆ F : {F : Subgroup G // F ∈ Ω},
          commutatorAction (F : Subgroup G) V := by
        apply commutatorAction_eq_iSup_of_eq_iSup
        exact hdecomp.part_a.1
      _ = U := (finset_sup_apply_eq_iSup_subtype Ω
        (fun F => commutatorAction F V)).symm
  have hUcard : Nat.card U = 4 ^ Ω.card :=
    natCard_finset_sup_oneOmega_action hdecomp Ω hΩ
  unfold fixedQuotientCard
  rw [hUeq, hUcard, hUeqUnion, hfixedProduct, hOmegaCard]
  norm_num [Nat.cast_pow, pow_add]
  change (4 : ℚ) ^ X.card * 4 ^ Y.card /
      (2 ^ X.card * 4 ^ Y.card) = 2 ^ X.card
  have h4X : (4 : ℚ) ^ X.card =
      2 ^ X.card * 2 ^ X.card := by
    rw [show (4 : ℚ) = 2 * 2 by norm_num, mul_pow]
  rw [h4X]
  field_simp

/-- Of the two order-two complements to `A` in an order-four coordinate
`A_i`, choose the one with smaller support.  Multiplication by the generator
of `A` exchanges the two complements, and acts on supports by symmetric
difference. -/
public theorem exists_outside_coordinate_with_minimal_partner_support
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] [DecidableEq (Subgroup G)]
    (S A Aᵢ : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hAS : A ≤ Aᵢ) (hAᵢS : Aᵢ ≤ S)
    (hAcard : Nat.card A = 2) (hAᵢcard : Nat.card Aᵢ = 4)
    (a : S) (hAeq : A = Subgroup.zpowers (a : G))
    (hnorm : ∀ F : Subgroup G, oneOmega (G := G) (V := V) F →
      S ≤ Subgroup.normalizer F) :
    ∃ x : S,
      (x : G) ∈ Aᵢ ∧ (x : G) ∉ A ∧
      (omegaSupport (G := G) (V := V) S hnorm x).card ≤
        ((omegaSupport (G := G) (V := V) S hnorm a) ∆
          omegaSupport (G := G) (V := V) S hnorm x).card := by
  classical
  have hAᵢnotle : Aᵢ ≤ A → False := by
    intro hle
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨xG, hxAᵢ, hxnotA⟩ := Set.not_subset.mp hAᵢnotle
  let x : S := ⟨xG, hAᵢS hxAᵢ⟩
  let y : S := a * x
  have haA : (a : G) ∈ A := by
    rw [hAeq]
    exact Subgroup.mem_zpowers (a : G)
  have hyAᵢ : (y : G) ∈ Aᵢ :=
    Aᵢ.mul_mem (hAS haA) hxAᵢ
  have hynotA : (y : G) ∉ A := by
    intro hyA
    apply hxnotA
    have := A.mul_mem (A.inv_mem haA) hyA
    simpa [y, mul_assoc] using this
  let X := omegaSupport (G := G) (V := V) S hnorm x
  let Y := omegaSupport (G := G) (V := V) S hnorm y
  let Z := omegaSupport (G := G) (V := V) S hnorm a
  by_cases hXY : X.card ≤ Y.card
  · refine ⟨x, hxAᵢ, hxnotA, ?_⟩
    dsimp only [X, Y, Z] at hXY
    have hmul := omegaSupport_mul_eq_symmDiff S hnorm a x
    change X.card ≤ (Z ∆ X).card
    rw [← hmul]
    exact hXY
  · refine ⟨y, hyAᵢ, hynotA, ?_⟩
    dsimp only [X, Y, Z] at hXY
    have haa : a * a = 1 := by
      simpa [pow_two] using
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 S) a)
    have hay : a * y = x := by
      dsimp only [y]
      rw [← mul_assoc, haa, one_mul]
    have hmul := omegaSupport_mul_eq_symmDiff S hnorm a y
    change Y.card ≤ (Z ∆ Y).card
    rw [← hmul, hay]
    change (omegaSupport (G := G) (V := V) S hnorm y).card ≤
      (omegaSupport (G := G) (V := V) S hnorm x).card
    exact (Nat.lt_of_not_ge hXY).le

/-- If the new coordinate contributes exactly one factor and was chosen no
larger than its partner, then every nonempty old support loses at least one
factor. -/
public theorem exists_mem_sdiff_of_card_pos_of_partner
    {ι : Type*} [DecidableEq ι] (A X : Finset ι) (F : ι)
    (hnew : X \ A = {F}) (hpartner : X.card ≤ (A ∆ X).card)
    (hpos : 0 < A.card) : ∃ K, K ∈ A ∧ K ∉ X := by
  by_contra hnone
  have hsubset : A ⊆ X := by
    intro K hKA
    by_contra hKX
    exact hnone ⟨K, hKA, hKX⟩
  have hAdiff : A \ X = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hsubset
  have hsymm : A ∆ X = X \ A := by
    rw [Finset.symmDiff_def, hAdiff, Finset.empty_union]
  have hXle : X.card ≤ 1 := by
    rw [hsymm, hnew] at hpartner
    simpa using hpartner
  have hinter : A ∩ X = A := Finset.inter_eq_left.mpr hsubset
  have hXcard : X.card = 1 + A.card := by
    calc
      X.card = (X \ A).card + (A ∩ X).card := by
        rw [← Finset.card_sdiff_add_card_inter X A, Finset.inter_comm]
      _ = 1 + A.card := by rw [hnew, hinter]; simp
  omega

/-- Adding one new support coordinate while losing at least one old one
cannot increase support cardinality. -/
public theorem card_le_of_sdiff_eq_singleton_of_exists_mem_sdiff
    {ι : Type*} [DecidableEq ι] (A X : Finset ι) (F K : ι)
    (hnew : X \ A = {F}) (hKA : K ∈ A) (hKnotX : K ∉ X) :
    X.card ≤ A.card := by
  have hnewCard : (X \ A).card = 1 := by rw [hnew]; simp
  have hADiffPos : 0 < (A \ X).card :=
    Finset.card_pos.mpr ⟨K, Finset.mem_sdiff.mpr ⟨hKA, hKnotX⟩⟩
  have hXsplit := Finset.card_sdiff_add_card_inter X A
  have hAsplit := Finset.card_sdiff_add_card_inter A X
  rw [Finset.inter_comm] at hAsplit
  omega

/-- A support factor moved by `A` and fixed by an order-two subgroup `B`
provides the extra `B`-fixed points outside `C_V(A)` used on journal p. 18.
Together with the local fixed index two, this proves `m(B) ≤ m(A)`. -/
public theorem m_zpowers_le_of_support_witness
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G)
    (hnorm : ∀ K : Subgroup G, oneOmega (G := G) (V := V) K →
      S ≤ Subgroup.normalizer K)
    (a x : S) (A : Subgroup G)
    (hAeq : A = Subgroup.zpowers (a : G))
    (hAcard : Nat.card A = 2)
    (hBcard : Nat.card (Subgroup.zpowers (x : G)) = 2)
    (K : Subgroup G) (hK : oneOmega (G := G) (V := V) K)
    (hKmemA : K ∈ omegaSupport (G := G) (V := V) S hnorm a)
    (hKnotX : K ∉ omegaSupport (G := G) (V := V) S hnorm x)
    (hratio : (Nat.card (FixedPoints.subgroup A V) : ℚ) /
      Nat.card (↥(FixedPoints.subgroup A V ⊓
        FixedPoints.subgroup (Subgroup.zpowers (x : G)) V)) = 2) :
    m (G := G) (V := V) (Subgroup.zpowers (x : G)) ≤
      m (G := G) (V := V) A := by
  let B : Subgroup G := Subgroup.zpowers (x : G)
  let U : Subgroup V := commutatorAction K V
  have hKcommA : ⁅K, A⁆ = K := by
    rw [hAeq]
    exact commutator_oneOmega_zpowers_eq_self_of_mem_support
      S hnorm a K hK hKmemA
  have hKcommB : ⁅K, B⁆ = ⊥ :=
    commutator_oneOmega_zpowers_eq_bot_of_not_mem_support
      S hnorm x K hK hKnotX
  have hBfix : B ≤ fixingSubgroup G (U : Set V) :=
    Stellmacher.SectionOne.oneOmega_card_two_centralizer_fixes_commutator
      K B hK hBcard hKcommB
  have hAnotfix : ¬ A ≤ fixingSubgroup G (U : Set V) :=
    Stellmacher.SectionOne.oneOmega_full_commutator_nontrivial
      K A hK hKcommA
  have hnotle : ¬ FixedPoints.subgroup B V ≤ FixedPoints.subgroup A V := by
    intro hle
    apply hAnotfix
    intro a0 ha0
    rw [mem_fixingSubgroup_iff]
    intro u hu
    have huB : u ∈ FixedPoints.subgroup B V := by
      rw [FixedPoints.mem_subgroup]
      intro b
      exact ((mem_fixingSubgroup_iff (M := G) (s := (U : Set V))).mp
        (hBfix b.property)) u hu
    have huA := hle huB
    exact (FixedPoints.mem_subgroup (M := A) (a := u)).1 huA ⟨a0, ha0⟩
  exact m_le_of_fixed_intersection_index_two_of_not_le
    A B hAcard hBcard (by simpa only [B] using hratio) hnotle

/-- Under the source's global minimal-`m` hypothesis, an order-two subgroup
whose `m`-value is no larger than `m(S)` automatically has the fixed-module
centralizer condition in `oneAmax`.  Thus the only remaining condition in
the p.18 assertion `B_i ∈ ᶜ₂(S)` is the odd-core commutator centralizer. -/
public theorem fixed_centralizer_eq_of_card_two_of_m_le
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (S B : Subgroup G) (hBS : B ≤ S) (hBcard : Nat.card B = 2)
    (hmin : ∀ Y : Subgroup G, Y ≤ S → Y ≠ ⊥ →
      m (G := G) (V := V) S ≤ m (G := G) (V := V) Y)
    (hmB : m (G := G) (V := V) B ≤ m (G := G) (V := V) S) :
    S ⊓ fixingSubgroup G (FixedPoints.subgroup B V : Set V) = B := by
  let T : Subgroup G :=
    S ⊓ fixingSubgroup G (FixedPoints.subgroup B V : Set V)
  have hBT : B ≤ T := by
    refine le_inf hBS ?_
    intro b hb
    rw [mem_fixingSubgroup_iff]
    intro v hv
    exact (FixedPoints.mem_subgroup (M := B) (a := v)).1 hv ⟨b, hb⟩
  apply le_antisymm
  · change T ≤ B
    by_contra hTnotle
    have hTneB : T ≠ B := fun h => hTnotle h.le
    have hBcardLe : Nat.card B ≤ Nat.card T := Subgroup.card_le_of_le hBT
    have hBcardLt : Nat.card B < Nat.card T := by
      apply lt_of_le_of_ne hBcardLe
      intro hcardEq
      apply hTneB
      exact (Subgroup.eq_of_le_of_card_ge hBT hcardEq.ge).symm
    have hTleS : T ≤ S := inf_le_left
    have hTne : T ≠ ⊥ := by
      intro hTbot
      have hBbot : B = ⊥ := le_antisymm (hTbot ▸ hBT) bot_le
      simp [hBbot] at hBcard
    have hfixEq : FixedPoints.subgroup T V = FixedPoints.subgroup B V := by
      apply le_antisymm
      · intro v hv
        rw [FixedPoints.mem_subgroup]
        intro b
        have hvT := (FixedPoints.mem_subgroup (M := T) (a := v)).1 hv
          ⟨(b : G), hBT b.property⟩
        simpa only [Subgroup.smul_def] using hvT
      · intro v hv
        rw [FixedPoints.mem_subgroup]
        intro t
        have htfix : (t : G) ∈ fixingSubgroup G
            (FixedPoints.subgroup B V : Set V) := t.property.2
        rw [mem_fixingSubgroup_iff] at htfix
        simpa only [Subgroup.smul_def] using htfix v hv
    have hdenLt :
        (Nat.card (FixedPoints.subgroup B V) : ℚ) * Nat.card B <
          (Nat.card (FixedPoints.subgroup T V) : ℚ) * Nat.card T := by
      rw [hfixEq]
      exact mul_lt_mul_of_pos_left (by exact_mod_cast hBcardLt)
        (by exact_mod_cast (Nat.card_pos
          (α := FixedPoints.subgroup B V)))
    have hmTLt : m (G := G) (V := V) T < m (G := G) (V := V) B := by
      unfold m
      have hdenTpos : (0 : ℚ) <
          (Nat.card (FixedPoints.subgroup T V) : ℚ) * Nat.card T :=
        mul_pos (by exact_mod_cast (Nat.card_pos
          (α := FixedPoints.subgroup T V)))
          (by exact_mod_cast (Nat.card_pos (α := T)))
      have hdenBpos : (0 : ℚ) <
          (Nat.card (FixedPoints.subgroup B V) : ℚ) * Nat.card B :=
        mul_pos (by exact_mod_cast (Nat.card_pos
          (α := FixedPoints.subgroup B V)))
          (by exact_mod_cast (Nat.card_pos (α := B)))
      apply (div_lt_div_iff₀ hdenTpos hdenBpos).2
      exact mul_lt_mul_of_pos_left hdenLt
        (by exact_mod_cast (Nat.card_pos (α := V)))
    have hmST := hmin T hTleS hTne
    exact (not_lt_of_ge (hmB.trans hmST)) hmTLt
  · simpa only [T] using hBT

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
