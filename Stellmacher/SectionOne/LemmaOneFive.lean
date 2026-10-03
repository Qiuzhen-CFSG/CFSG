module

public import Stellmacher.SectionsOneToFourDefs
public import Stellmacher.SectionOne.LemmaOneOne
public import Theory.PGroup

/-!
# Stellmacher (1.5)

This module proves the fixed-point quotient formula and the four conclusions
about `oneAmax` subgroups in Stellmacher (1.5), source lines 374--418.  The
source's induction is made explicit by applying coprime-action generation to
each nontrivial elementary abelian subgroup of the chosen Sylow subgroup.
Its index-two `oneAmax` subgroups generate it, and induction inside those
subgroups, followed by `lemma_one_five_oneAmax_transfer`, reduces the generators
to order two.  Parts (b), (d), and (e) then follow from this relative generation
statement and the already established centralizer formula in part (c).  The
index-two `oneAmax`/centralizer dichotomy used by that induction is exported as
`lemma_one_five_oneAmax_or_centralizer_eq` for subsequent coprime-action
arguments.

The Fitting-subgroup centralizer argument is also exported for the reduction
in (1.3): a Sylow 2-subgroup meets the centralizer of the odd core trivially.
-/

@[expose] public section

open scoped BigOperators Pointwise

namespace Stellmacher.SectionOne

universe u v

public structure LemmaOneFiveConclusion
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S U : Subgroup G) : Prop where
  part_a :
    subgroupQuotientCard
        (FixedPoints.subgroup U V)
        (FixedPoints.subgroup S V) =
      m (G := G) (V := V) S * (m (G := G) (V := V) U)⁻¹ *
        (indexWithin S U : ℚ)
  part_b :
    IsElementaryAbelian 2 S →
      S = ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) S A ∧ Nat.card A = 2},
        (A : Subgroup G)
  part_c :
    IsElementaryAbelian 2 S →
      oddCore G =
        ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) S A ∧
          Nat.card S = 2 * Nat.card A},
          oddCore G ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G)
  part_d :
    IsElementaryAbelian 2 S → Nat.card S ≥ 4 →
      oddCore G =
        ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) S A ∧ Nat.card A = 2},
          oddCore G ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G)
  part_e : IsElementaryAbelian 2 S → m (G := G) (V := V) S ≥ 1

theorem lemma_one_five_part_a
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S U : Subgroup G) (hU : U ≤ S) :
    subgroupQuotientCard
        (FixedPoints.subgroup U V)
        (FixedPoints.subgroup S V) =
      m (G := G) (V := V) S * (m (G := G) (V := V) U)⁻¹ *
        (indexWithin S U : ℚ) := by
  classical
  have hcardU : Nat.card (U.subgroupOf S) = Nat.card U :=
    natCard_subgroupOf_eq U S hU
  have hindex : (U.subgroupOf S).index * Nat.card (U.subgroupOf S) = Nat.card S :=
    Subgroup.index_mul_card (H := U.subgroupOf S)
  have hindexQ : (indexWithin S U : ℚ) * (Nat.card U : ℚ) = (Nat.card S : ℚ) := by
    simpa [indexWithin, hcardU] using congrArg (fun n : ℕ => (n : ℚ)) hindex
  have hV : (Nat.card V : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := V)).ne'
  have hFU : (Nat.card (FixedPoints.subgroup U V) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := FixedPoints.subgroup U V)).ne'
  have hFS : (Nat.card (FixedPoints.subgroup S V) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := FixedPoints.subgroup S V)).ne'
  have hSU : (Nat.card U : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := U)).ne'
  simp only [subgroupQuotientCard, m]
  field_simp [hV, hFU, hFS, hSU]
  have hindexQ' : (Nat.card U : ℚ) * (indexWithin S U : ℚ) = (Nat.card S : ℚ) := by
    rw [mul_comm]
    exact hindexQ
  rw [hindexQ']
  simp

theorem lemma_one_five_self_oneAmax
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G) : oneAmax (G := G) (V := V) S S := by
  classical
  unfold oneAmax
  dsimp
  refine ⟨le_rfl, le_rfl, ?_, ?_⟩
  have hSN : (S ⊓ Subgroup.normalizer (S : Set G) : Subgroup G) = S := by
    apply le_antisymm
    · exact inf_le_left
    · exact le_inf le_rfl S.le_normalizer
  have hC : ⁅oddCore G ⊓ Subgroup.centralizer (S : Set G),
      S ⊓ Subgroup.normalizer (S : Set G)⁆ = (⊥ : Subgroup G) := by
    rw [hSN]
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    exact inf_le_right
  rw [hC]
  apply le_antisymm
  · exact inf_le_left
  · refine le_inf le_rfl ?_
    intro s hs z hz
    rw [Set.mem_singleton_iff.mp hz]
    simp
  apply le_antisymm
  · exact inf_le_left
  · refine le_inf le_rfl ?_
    intro s hs
    rw [mem_fixingSubgroup_iff]
    intro v hv
    exact (FixedPoints.mem_subgroup (M := S) (a := v)).1 hv ⟨s, hs⟩

/- The induction step in the source: if `A` is one of the maximal
subgroups for `S`, then every maximal subgroup `A₀` for `A` is also maximal
for `S`.  The only point requiring care is that the centralizer defining
`oneAmax` uses the ambient elementary-abelian group; the subgroup
normalizers therefore collapse to the ambient group. -/
theorem lemma_one_five_oneAmax_transfer
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    {S A A₀ : Subgroup G}
    (hS : IsElementaryAbelian 2 S)
    (hA : oneAmax (G := G) (V := V) S A)
    (hA₀ : oneAmax (G := G) (V := V) A A₀) :
    oneAmax (G := G) (V := V) S A₀ := by
  let : IsElementaryAbelian 2 S := hS
  let : CommGroup S := IsMulCommutative.instCommGroup
  unfold oneAmax at hA hA₀ ⊢
  dsimp at hA hA₀ ⊢
  have hnorm (B : Subgroup G) (hB : B ≤ S) :
      S ≤ Subgroup.normalizer (B : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs b hb
    have hsb : (s : G) * (b : G) = (b : G) * (s : G) := by
      exact congrArg Subtype.val
        ((IsMulCommutative.is_comm (M := S)).comm ⟨s, hs⟩ ⟨b, hB hb⟩)
    rw [hsb]
    simp [mul_assoc, hb]
  have hnormA : S ⊓ Subgroup.normalizer (A : Set G) = S := by
    apply le_antisymm inf_le_left
    exact le_inf le_rfl (hnorm A hA.1)
  have hnormA₀ : S ⊓ Subgroup.normalizer (A₀ : Set G) = S := by
    apply le_antisymm inf_le_left
    exact le_inf le_rfl (hnorm A₀ (hA₀.1.trans hA.1))
  have hA₀S : A₀ ≤ S := hA₀.1.trans hA.1
  have hcommcentral :
      oddCore G ⊓ Subgroup.centralizer (A : Set G) ≤
        oddCore G ⊓ Subgroup.centralizer (A₀ : Set G) := by
    refine le_inf inf_le_left ?_
    exact le_trans inf_le_right (Subgroup.centralizer_le (show
      (A₀ : Set G) ⊆ (A : Set G) from fun x hx => hA₀.1 hx))
  have hYle :
      ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆ ≤
        ⁅oddCore G ⊓ Subgroup.centralizer (A₀ : Set G), S⁆ :=
    Subgroup.commutator_mono hcommcentral le_rfl
  have hnormA₀A : A ⊓ Subgroup.normalizer (A₀ : Set G) = A := by
    apply le_antisymm inf_le_left
    exact le_inf le_rfl (hA.1.trans (hnorm A₀ hA₀S))
  have hYA₀leY0 :
      ⁅oddCore G ⊓ Subgroup.centralizer (A₀ : Set G), A⁆ ≤
        ⁅oddCore G ⊓ Subgroup.centralizer (A₀ : Set G), S⁆ :=
    Subgroup.commutator_mono le_rfl hA.1
  have hAeq : S ⊓ Subgroup.centralizer
      ((⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), (S : Subgroup G)⁆ : Subgroup G) : Set G) = A := by
    simpa [hnormA] using hA.2.2.1
  have hA₀eq : A ⊓ Subgroup.centralizer
      ((⁅oddCore G ⊓ Subgroup.centralizer (A₀ : Set G), (A : Subgroup G)⁆ : Subgroup G) : Set G) = A₀ := by
    simpa [hnormA₀A] using hA₀.2.2.1
  let Y₀ : Subgroup G :=
    ⁅oddCore G ⊓ Subgroup.centralizer (A₀ : Set G), S⁆
  have hA₀centY0 : A₀ ≤ Subgroup.centralizer (Y₀ : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hYcent : Y₀ ≤ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.commutator_le]
      intro w hw s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hwA : (w : G) * (a : G) = (a : G) * (w : G) :=
        (Subgroup.mem_centralizer_iff.mp hw.2 (a : G) ha).symm
      have hwa : Commute (a : G) (w : G) := hwA.symm
      have hsa : Commute (a : G) (s : G) := by
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := S)).comm ⟨s, hs⟩ ⟨a, hA₀S ha⟩) |>.symm
      have hprod : Commute (a : G)
          ((w : G) * (s : G) * (w : G)⁻¹ * (s : G)⁻¹) := by
        exact (((hwa.mul_right hsa).mul_right hwa.inv_right).mul_right hsa.inv_right)
      exact hprod.symm.eq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYcent hy)
  refine ⟨hA₀S, le_trans hA₀.2.1 hA.2.1, ?_, ?_⟩
  · rw [hnormA₀]
    change S ⊓ Subgroup.centralizer (Y₀ : Set G) = A₀
    apply le_antisymm
    · intro x hx
      have hxY : x ∈ Subgroup.centralizer
          ((⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), (S : Subgroup G)⁆ : Subgroup G) : Set G) := by
        exact (Subgroup.centralizer_le (show
          ((⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), (S : Subgroup G)⁆ : Subgroup G) : Set G) ⊆
            ((⁅oddCore G ⊓ Subgroup.centralizer (A₀ : Set G), (S : Subgroup G)⁆ : Subgroup G) : Set G) from
          fun y hy => hYle hy)) hx.2
      have hxA : x ∈ A := by
        have hx' : x ∈ S ⊓ Subgroup.centralizer
            ((⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), (S : Subgroup G)⁆ : Subgroup G) : Set G) :=
          ⟨hx.1, hxY⟩
        rw [hAeq] at hx'
        exact hx'
      have hxY₀A : x ∈ Subgroup.centralizer
          ((⁅oddCore G ⊓ Subgroup.centralizer (A₀ : Set G), (A : Subgroup G)⁆ : Subgroup G) : Set G) := by
        exact (Subgroup.centralizer_le (show
          ((⁅oddCore G ⊓ Subgroup.centralizer (A₀ : Set G), (A : Subgroup G)⁆ : Subgroup G) : Set G) ⊆
            ((⁅oddCore G ⊓ Subgroup.centralizer (A₀ : Set G), (S : Subgroup G)⁆ : Subgroup G) : Set G) from
          fun y hy => hYA₀leY0 hy)) hx.2
      have hx' : x ∈ A ⊓ Subgroup.centralizer
          ((⁅oddCore G ⊓ Subgroup.centralizer (A₀ : Set G), (A : Subgroup G)⁆ : Subgroup G) : Set G) :=
        ⟨hxA, hxY₀A⟩
      rw [hA₀eq] at hx'
      exact hx'
    · intro x hx
      exact ⟨hA₀S hx, hA₀centY0 hx⟩
  · have hfixset :
        (FixedPoints.subgroup (↥A) V : Set V) ⊆
          FixedPoints.subgroup (↥A₀) V := by
      intro v hv
      change (∀ a : A, a • v = v) at hv
      change ∀ a : A₀, a • v = v
      intro a
      have hv' := hv ⟨(a : G), hA₀.1 a.property⟩
      simpa only [Subgroup.smul_def] using hv'
    have hfixle :
        fixingSubgroup G (FixedPoints.subgroup A₀ V : Set V) ≤
          fixingSubgroup G (FixedPoints.subgroup A V : Set V) := by
      apply fixingSubgroup_antitone
      exact hfixset
    apply le_antisymm
    · intro x hx
      have hxA : x ∈ A := by
        have hx' : x ∈ S ⊓ fixingSubgroup G
            (FixedPoints.subgroup A V : Set V) := ⟨hx.1, hfixle hx.2⟩
        rw [hA.2.2.2] at hx'
        exact hx'
      have hx' : x ∈ A ⊓ fixingSubgroup G
          (FixedPoints.subgroup A₀ V : Set V) := ⟨hxA, hx.2⟩
      rw [hA₀.2.2.2] at hx'
      exact hx'
    · intro x hx
      refine ⟨hA₀S hx, ?_⟩
      change x ∈ fixingSubgroup G (FixedPoints.subgroup (↥A₀) V : Set V)
      rw [mem_fixingSubgroup_iff]
      intro v hv
      exact (FixedPoints.mem_subgroup (M := A₀) (a := v)).1 hv ⟨x, hx⟩

/- A second source step used in the index-two dichotomy.  An automorphism of
order two of an odd-order group cannot have a nontrivial displacement that it
also fixes: the displacement then has both order dividing two and order
coprime to two. -/
private theorem lemma_one_five_centralizer_of_central_commutator
    {G : Type u} [Group G] [Finite G]
    {S W₀ : Subgroup G} [IsElementaryAbelian 2 S]
    (hW₀ : W₀ ≤ oddCore G)
    (hcent : S ≤ Subgroup.centralizer
      ((⁅W₀, S⁆ : Subgroup G) : Set G)) :
    W₀ ≤ Subgroup.centralizer (S : Set G) := by
  let : (oddCore G).Normal := pPrimeCore_normal
  have hcommW : ⁅W₀, S⁆ ≤ oddCore G := by
    exact (Subgroup.commutator_mono hW₀ le_rfl).trans
      (Subgroup.commutator_le_left (oddCore G) S)
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  let y : G := (w : G)⁻¹ * (s : G) * (w : G) * (s : G)⁻¹
  have hy : y ∈ ⁅W₀, S⁆ := by
    dsimp [y]
    simpa [commutatorElement_def] using
      (Subgroup.commutator_mem_commutator (W₀.inv_mem hw) hs)
  have hyW : y ∈ oddCore G := hcommW hy
  have hsy : (s : G) * y * (s : G)⁻¹ = y := by
    have hcomm : y * (s : G) = (s : G) * y :=
      Subgroup.mem_centralizer_iff.mp (hcent hs) y hy
    calc
      (s : G) * y * (s : G)⁻¹ = y * (s : G) * (s : G)⁻¹ := by rw [hcomm.symm]
      _ = y := by simp
  have hs2 : (s : G) ^ 2 = 1 := by
    have h := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 S) (⟨s, hs⟩ : S)
    simpa using h
  have hsinv : (s : G)⁻¹ = (s : G) := by
    apply inv_eq_of_mul_eq_one_left
    simpa [pow_two] using hs2
  have hconj : (s : G) * (w : G) * (s : G)⁻¹ = (w : G) * y := by
    dsimp [y]
    simp [mul_assoc]
  have htwice : (s : G) * ((s : G) * (w : G) * (s : G)⁻¹) * (s : G)⁻¹ = (w : G) := by
    calc
      (s : G) * ((s : G) * (w : G) * (s : G)⁻¹) * (s : G)⁻¹ =
          ((s : G) ^ 2) * (w : G) * ((s : G)⁻¹ * (s : G)⁻¹) := by
            simp only [hsinv]
            simp [pow_two, mul_assoc]
      _ = (w : G) := by
        have hss : (s : G) * (s : G) = 1 := by simpa [pow_two] using hs2
        rw [hs2, hsinv]
        rw [hss]
        simp
  have hy2 : y ^ 2 = 1 := by
    have htwice' : (w : G) * y * y = (w : G) := by
      calc
        (w : G) * y * y = ((s : G) * (w : G) * (s : G)⁻¹) *
            ((s : G) * y * (s : G)⁻¹) := by rw [hconj, hsy]
        _ = (s : G) * ((w : G) * y) * (s : G)⁻¹ := by simp [mul_assoc]
        _ = (s : G) * ((s : G) * (w : G) * (s : G)⁻¹) * (s : G)⁻¹ := by rw [← hconj]
        _ = (w : G) := htwice
    apply mul_left_cancel (a := (w : G))
    simpa [pow_two, mul_assoc] using htwice'
  let yw : oddCore G := ⟨y, hyW⟩
  have hordW' : orderOf yw ∣ Nat.card (oddCore G) := orderOf_dvd_natCard yw
  have hordW : orderOf y ∣ Nat.card (oddCore G) := by
    have heq : orderOf y = orderOf (yw : G) := by rfl
    rw [heq, Subgroup.orderOf_coe]
    exact hordW'
  have hord2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
  have hord1 : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes
    pPrimeCore_coprime_card hord2 hordW
  have hyone : y = 1 := (orderOf_eq_one_iff).mp hord1
  dsimp [y] at hyone
  have hm := congrArg (fun z : G => (w : G) * z * (s : G)) hyone
  simpa [mul_assoc] using hm

private theorem lemma_one_five_centralizer_eq_of_central_commutator
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    {S A : Subgroup G} (hS : IsElementaryAbelian 2 S) (hA : A ≤ S)
    (hcent : S ≤ Subgroup.centralizer
      ((⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆ : Subgroup G) : Set G)) :
    oddCore G ⊓ Subgroup.centralizer (A : Set G) =
      oddCore G ⊓ Subgroup.centralizer (S : Set G) := by
  let : IsElementaryAbelian 2 S := hS
  have hle : oddCore G ⊓ Subgroup.centralizer (A : Set G) ≤
      Subgroup.centralizer (S : Set G) := by
    apply lemma_one_five_centralizer_of_central_commutator
      (W₀ := oddCore G ⊓ Subgroup.centralizer (A : Set G)) inf_le_left
    exact hcent
  apply le_antisymm
  · exact le_inf inf_le_left hle
  · refine le_inf inf_le_left ?_
    exact le_trans inf_le_right
      (Subgroup.centralizer_le (show (A : Set G) ⊆ (S : Set G) from hA))

private theorem lemma_one_five_index_two_intermediate
    {G : Type u} [Group G] [Finite G] {S A T : Subgroup G}
    (hAS : A ≤ S) (hAT : A ≤ T) (hTS : T ≤ S)
    (hcard : Nat.card S = 2 * Nat.card A) : T = A ∨ T = S := by
  have hcardA : Nat.card (A.subgroupOf S) = Nat.card A := natCard_subgroupOf_eq A S hAS
  have hprod : (A.subgroupOf S).index * Nat.card (A.subgroupOf S) = Nat.card S :=
    Subgroup.index_mul_card (H := A.subgroupOf S)
  have hidx : A.relIndex S = 2 := by
    dsimp [Subgroup.relIndex]
    rw [hcardA, hcard] at hprod
    apply Nat.mul_right_cancel (m := Nat.card A)
    · exact Nat.card_pos
    · exact hprod
  have hmul : A.relIndex T * T.relIndex S = A.relIndex S :=
    Subgroup.relIndex_mul_relIndex A T S hAT hTS
  have hiTSdvd : T.relIndex S ∣ 2 := by
    rw [← hidx]
    exact Subgroup.relIndex_dvd_of_le_left S hAT
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hiTSdvd with hi1 | hi2
  · right
    exact le_antisymm hTS (Subgroup.relIndex_eq_one.mp hi1)
  · left
    have hiAT : A.relIndex T = 1 := by
      rw [hi2] at hmul
      omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hiAT) hAT

/- The centralizer half of the index-two dichotomy in the source. -/
private theorem lemma_one_five_centralizer_condition_or_eq
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    {S A : Subgroup G} (hS : IsElementaryAbelian 2 S) (hA : A ≤ S)
    (hcard : Nat.card S = 2 * Nat.card A) :
    (S ⊓ Subgroup.centralizer
      ((⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆ : Subgroup G) : Set G) = A) ∨
      oddCore G ⊓ Subgroup.centralizer (A : Set G) =
        oddCore G ⊓ Subgroup.centralizer (S : Set G) := by
  let : IsElementaryAbelian 2 S := hS
  let : CommGroup S := IsMulCommutative.instCommGroup
  have hAle : A ≤ Subgroup.centralizer
      ((⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆ : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hYcent : ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆ ≤
        Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.commutator_le]
      intro w hw s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hwA : (w : G) * (a : G) = (a : G) * (w : G) :=
        (Subgroup.mem_centralizer_iff.mp hw.2 (a : G) ha).symm
      have hwa : Commute (a : G) (w : G) := hwA.symm
      have hsa : Commute (a : G) (s : G) := by
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := S)).comm ⟨s, hs⟩ ⟨a, hA ha⟩) |>.symm
      exact (((hwa.mul_right hsa).mul_right hwa.inv_right).mul_right hsa.inv_right).symm.eq
    exact Subgroup.mem_centralizer_singleton_iff.mp (hYcent hy)
  let T : Subgroup G := S ⊓ Subgroup.centralizer
      ((⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆ : Subgroup G) : Set G)
  have hAT : A ≤ T := le_inf hA hAle
  have hTS : T ≤ S := inf_le_left
  rcases lemma_one_five_index_two_intermediate hA hAT hTS hcard with hTA | hTS'
  · exact Or.inl hTA
  · right
    apply lemma_one_five_centralizer_eq_of_central_commutator (V := V) hS hA
    intro s hs
    have hsT : s ∈ T := by rw [hTS']; exact hs
    exact hsT.2

private theorem lemma_one_five_fixed_condition_or_eq
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    {S A : Subgroup G} (hS : IsElementaryAbelian 2 S) (hA : A ≤ S)
    (hcard : Nat.card S = 2 * Nat.card A) :
    (S ⊓ fixingSubgroup G (FixedPoints.subgroup (↥A) V : Set V) = A) ∨
      FixedPoints.subgroup (↥A) V = FixedPoints.subgroup (↥S) V := by
  let : IsElementaryAbelian 2 S := hS
  let : CommGroup S := IsMulCommutative.instCommGroup
  have hAle : A ≤ fixingSubgroup G
      (FixedPoints.subgroup (↥A) V : Set V) := by
    intro a ha
    rw [mem_fixingSubgroup_iff]
    intro v hv
    exact (FixedPoints.mem_subgroup (M := A) (a := v)).1 hv ⟨a, ha⟩
  let T : Subgroup G := S ⊓ fixingSubgroup G
      (FixedPoints.subgroup (↥A) V : Set V)
  have hAT : A ≤ T := le_inf hA hAle
  have hTS : T ≤ S := inf_le_left
  rcases lemma_one_five_index_two_intermediate hA hAT hTS hcard with hTA | hTS'
  · exact Or.inl hTA
  · right
    apply le_antisymm
    · intro v hv
      change ∀ s : S, s • v = v
      intro s
      have hsT : (s : G) ∈ T := by rw [hTS']; exact s.property
      have hsFix := hsT.2
      change (s : G) ∈ fixingSubgroup G
        (FixedPoints.subgroup (↥A) V : Set V) at hsFix
      rw [mem_fixingSubgroup_iff] at hsFix
      exact hsFix v hv
    · intro v hv
      change ∀ a : A, a • v = v
      intro a
      have hs : (a : G) ∈ S := hA a.property
      have hv' := (FixedPoints.mem_subgroup (M := S) (a := v)).1 hv ⟨(a : G), hs⟩
      simpa only [Subgroup.smul_def] using hv'

private theorem lemma_one_five_isInvariant_commutatorAction
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    {S Y : Subgroup G}
    (hYnorm : ∀ s : S, ∀ y : G, y ∈ Y → (s : G) * y * (s : G)⁻¹ ∈ Y) :
    IsInvariant S V (commutatorAction (A := Y) (G := V)) := by
  have hforward : ∀ s : S, ∀ v : V,
      v ∈ commutatorAction (A := Y) (G := V) →
        s • v ∈ commutatorAction (A := Y) (G := V) := by
    intro s v hv
    rw [commutatorAction_eq_closure] at hv ⊢
    refine Subgroup.closure_induction (k := {x : V | ∃ y : Y, ∃ g : V, x = g⁻¹ * (y • g)})
      (p := fun x _ => s • x ∈ Subgroup.closure {x : V | ∃ y : Y, ∃ g : V, x = g⁻¹ * (y • g)})
      (x := v) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨y, g, rfl⟩
      refine Subgroup.subset_closure ⟨⟨(s : G) * (y : G) * (s : G)⁻¹,
        hYnorm s y y.property⟩, s • g, ?_⟩
      change s • (g⁻¹ * ((y : G) • g)) = _
      have hconj : s • ((y : G) • g) =
          ((s : G) * (y : G) * (s : G)⁻¹) • (s • g) := by
        change (s : G) • ((y : G) • g) =
          ((s : G) * (y : G) * (s : G)⁻¹) • ((s : G) • g)
        simp [smul_smul, mul_assoc]
      rw [smul_mul', smul_inv', hconj]
      rfl
    · simp
    · intro x z _ _ hx hz
      simpa [smul_mul'] using Subgroup.mul_mem _ hx hz
    · intro x _ hx
      simpa [smul_inv'] using Subgroup.inv_mem _ hx
  refine ⟨?_⟩
  intro s v
  constructor
  · exact hforward s v
  · intro hv
    have hback := hforward (s⁻¹) (s • v) hv
    simpa [smul_smul] using hback

private theorem lemma_one_five_fixedpoint_transfer
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) {S A : Subgroup G}
    (hS : IsElementaryAbelian 2 S) (hA : A ≤ S)
    (hfix : FixedPoints.subgroup (↥A) V = FixedPoints.subgroup (↥S) V) :
    oddCore G ⊓ Subgroup.centralizer (A : Set G) =
      oddCore G ⊓ Subgroup.centralizer (S : Set G) := by
  classical
  let : Group.IsSolvable G := h.G_solvable
  let : IsElementaryAbelian 2 S := hS
  let : CommGroup S := IsMulCommutative.instCommGroup
  let W : Subgroup G := oddCore G
  let W₀ : Subgroup G := W ⊓ Subgroup.centralizer (A : Set G)
  let Y : Subgroup G := ⁅W₀, S⁆
  have hWnormal : W.Normal := by
    dsimp [W]
    exact pPrimeCore_normal
  let : W.Normal := hWnormal
  have hW₀leW : W₀ ≤ W := inf_le_left
  have hYleW : Y ≤ W := by
    exact (Subgroup.commutator_mono hW₀leW le_rfl).trans
      (Subgroup.commutator_le_left W S)
  have hYnorm : ∀ s : S, ∀ y : G, y ∈ Y →
      (s : G) * y * (s : G)⁻¹ ∈ Y := by
    intro s y hy
    exact (Subgroup.mem_normalizer_iff.mp
      (Subgroup.normalizer_commutator_ge_right W₀ S s.property) y).1 hy
  have hYfix : Y ≤ fixingSubgroup G
      (FixedPoints.subgroup (↥S) V : Set V) := by
    rw [show Y = ⁅W₀, S⁆ from rfl, Subgroup.commutator_le]
    intro w hw s hs
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have hvS : ∀ t : S, t • v = v := by
      exact (FixedPoints.mem_subgroup (M := S) (a := v)).1 hv
    have hvA : v ∈ FixedPoints.subgroup (↥A) V := by
      rw [hfix]
      exact hv
    have hwinvA : ∀ a : A, (a : G) • ((w : G)⁻¹ • v) =
        (w : G)⁻¹ • v := by
      intro a
      have hwa : (a : G) * (w : G)⁻¹ = (w : G)⁻¹ * (a : G) := by
        have hcomm : (w : G) * (a : G) = (a : G) * (w : G) :=
          (Subgroup.mem_centralizer_iff.mp hw.2 (a : G) a.property).symm
        have := congrArg (fun z : G => (w : G)⁻¹ * z * (w : G)⁻¹) hcomm
        simpa [mul_assoc] using this
      have hva := (FixedPoints.mem_subgroup (M := A) (a := v)).1 hvA a
      calc
        (a : G) • ((w : G)⁻¹ • v) = ((a : G) * (w : G)⁻¹) • v := by rw [smul_smul]
        _ = ((w : G)⁻¹ * (a : G)) • v := by rw [hwa]
        _ = (w : G)⁻¹ • ((a : G) • v) := by rw [smul_smul]
        _ = (w : G)⁻¹ • v := by simpa [Subgroup.smul_def] using congrArg (fun z : V => (w : G)⁻¹ • z) hva
    have hwvS : (w : G)⁻¹ • v ∈ FixedPoints.subgroup (↥S) V := by
      rw [FixedPoints.mem_subgroup]
      intro t
      have hwvA : (w : G)⁻¹ • v ∈ FixedPoints.subgroup (↥A) V := by
        rw [FixedPoints.mem_subgroup]
        exact hwinvA
      have hwvS' : (w : G)⁻¹ • v ∈ FixedPoints.subgroup (↥S) V := by
        rw [← hfix]
        exact hwvA
      exact (FixedPoints.mem_subgroup (M := S) (a := (w : G)⁻¹ • v)).1 hwvS' t
    have hs_inv_v : (s : G)⁻¹ • v = v := by
      have := hvS (⟨s, hs⟩⁻¹)
      simpa [Subgroup.smul_def] using this
    have hs_wv : (s : G) • ((w : G)⁻¹ • v) = (w : G)⁻¹ • v := by
      exact (FixedPoints.mem_subgroup (M := S) (a := (w : G)⁻¹ • v)).1 hwvS ⟨s, hs⟩
    rw [commutatorElement_def]
    simp only [mul_smul]
    rw [hs_inv_v, hs_wv]
    simp
  have hYcop : Nat.Coprime (Nat.card Y) (Nat.card V) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [hn]
    exact (Nat.Coprime.of_dvd_right (Subgroup.card_dvd_of_le hYleW)
      pPrimeCore_coprime_card).symm.pow_right n
  have hcompl : IsCompl (FixedPoints.subgroup (↥Y) V)
      (commutatorAction (A := Y) (G := V)) :=
    let : Group.IsSolvable V := Group.isSolvable_of_comm
      (fun a b => (IsMulCommutative.is_comm (M := V)).comm a b)
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := Y) inferInstance hYcop inferInstance
  let H : Subgroup V := commutatorAction (A := Y) (G := V)
  have hHinv : IsInvariant S V H := by
    dsimp [H]
    exact lemma_one_five_isInvariant_commutatorAction hYnorm
  let : IsInvariant S V H := hHinv
  have hfixH : FixedPoints.subgroup (↥S) H = ⊥ := by
    apply le_antisymm
    · intro x hx
      have hxS : ∀ s : S, s • (x : V) = (x : V) := by
        intro s
        exact congrArg Subtype.val
          ((FixedPoints.mem_subgroup (M := S) (a := x)).1 hx s)
      have hxV : (x : V) ∈ FixedPoints.subgroup (↥S) V :=
        (FixedPoints.mem_subgroup (M := S) (a := (x : V))).2 hxS
      have hxY : (x : V) ∈ FixedPoints.subgroup (↥Y) V := by
        rw [FixedPoints.mem_subgroup]
        intro y
        have hyfix := hYfix y.property
        change (y : G) ∈ fixingSubgroup G
          (FixedPoints.subgroup (↥S) V : Set V) at hyfix
        rw [mem_fixingSubgroup_iff] at hyfix
        have hy := hyfix (x : V) hxV
        simpa [Subgroup.smul_def] using hy
      have hxinf : (x : V) ∈ FixedPoints.subgroup (↥Y) V ⊓ H :=
        ⟨hxY, x.property⟩
      have hxbot : (x : V) ∈ (⊥ : Subgroup V) := by
        rw [hcompl.inf_eq_bot] at hxinf
        exact hxinf
      apply Subtype.ext
      simpa using hxbot
    · exact bot_le
  have hHbot : H = ⊥ := by
    by_contra hHne
    let : Fact (Nat.Prime 2) := ⟨by decide⟩
    have hHp : IsPGroup 2 H := (IsElementaryAbelian.isPGroup 2 V).to_subgroup H
    obtain ⟨n, hn⟩ := hHp.exists_card_eq
    have hnpos : 0 < n := by
      by_contra hn0
      have : n = 0 := Nat.eq_zero_of_not_pos hn0
      apply hHne
      apply (Subgroup.eq_bot_iff_card H).2
      simp [hn, this]
    have hdiv : 2 ∣ Nat.card H := by
      rw [hn]
      exact dvd_pow_self 2 (Nat.ne_of_gt hnpos)
    have hSp : IsPGroup 2 S := hS.isPGroup 2 S
    obtain ⟨x, hxfix, hxne⟩ := hSp.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := H) hdiv (a := (1 : H)) (by simp)
    have hxsub : x ∈ FixedPoints.subgroup (↥S) H := by
      rw [FixedPoints.mem_subgroup]
      intro s
      exact (MulAction.mem_fixedPoints.mp hxfix) s
    have hxsub' := hxsub
    rw [hfixH] at hxsub'
    have hxone : x = (1 : H) := by simpa using hxsub'
    exact hxne hxone.symm
  have htriv : ActsTrivially (A := Y) (G := V) :=
    actsTrivially_of_commutatorAction_eq_bot (G := V) (A := Y) (by simpa [H] using hHbot)
  have hYbot : Y = ⊥ := by
    apply le_antisymm
    · intro y hy
      have hyfix : y ∈ fixingSubgroup G (Set.univ : Set V) := by
        rw [mem_fixingSubgroup_iff]
        intro v _
        exact htriv ⟨y, hy⟩ v
      have : y ∈ (⊥ : Subgroup G) := by
        rw [← h.action_faithful]
        exact hyfix
      simpa using this
    · exact bot_le
  have hW₀centS : W₀ ≤ Subgroup.centralizer (S : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hYbot
  apply le_antisymm
  · exact le_inf inf_le_left hW₀centS
  · refine le_inf inf_le_left ?_
    exact le_trans inf_le_right
      (Subgroup.centralizer_le (show (A : Set G) ⊆ (S : Set G) from hA))

private theorem lemma_one_five_m_le_of_fixedpoint_ne
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    {S A : Subgroup G} (hA : A ≤ S)
    (hcard : Nat.card S = 2 * Nat.card A)
    (hne : FixedPoints.subgroup (↥A) V ≠ FixedPoints.subgroup (↥S) V) :
    m (G := G) (V := V) A ≤ m (G := G) (V := V) S := by
  have hfixle : FixedPoints.subgroup (↥S) V ≤ FixedPoints.subgroup (↥A) V := by
    intro v hv
    change (∀ s : S, s • v = v) at hv
    change ∀ a : A, a • v = v
    intro a
    have hv' := hv ⟨(a : G), hA a.property⟩
    simpa only [Subgroup.smul_def] using hv'
  let CS : Subgroup V := FixedPoints.subgroup (↥S) V
  let CA : Subgroup V := FixedPoints.subgroup (↥A) V
  have hindex : 1 < (CS.subgroupOf CA).index :=
    Subgroup.one_lt_index_of_ne_top (by
      intro htop
      apply hne
      have hCA_le_CS : CA ≤ CS := (Subgroup.subgroupOf_eq_top.mp htop)
      apply le_antisymm
      · exact hCA_le_CS
      · exact hfixle)
  have hcard_index : Nat.card CS * (CS.subgroupOf CA).index = Nat.card CA := by
    have hcard_sub : Nat.card (CS.subgroupOf CA) = Nat.card CS :=
      natCard_subgroupOf_eq _ _ hfixle
    have hprod := Subgroup.index_mul_card (H := CS.subgroupOf CA)
    simpa [hcard_sub, mul_comm] using hprod
  have hcard_fixed : 2 * Nat.card CS ≤ Nat.card CA := by
    have hi : 2 ≤ (CS.subgroupOf CA).index := by omega
    nlinarith [hcard_index]
  unfold m
  have hVpos : (0 : ℚ) < Nat.card V := by exact_mod_cast Nat.card_pos
  have hCSpos : (0 : ℚ) < Nat.card CS := by exact_mod_cast Nat.card_pos
  have hCApos : (0 : ℚ) < Nat.card CA := by exact_mod_cast Nat.card_pos
  have hApos : (0 : ℚ) < Nat.card A := by exact_mod_cast Nat.card_pos
  have hSpos : (0 : ℚ) < Nat.card S := by exact_mod_cast Nat.card_pos
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have hcard_fixedQ : (2 : ℚ) * Nat.card CS ≤ Nat.card CA := by exact_mod_cast hcard_fixed
  have hcardQ : (Nat.card S : ℚ) = 2 * Nat.card A := by exact_mod_cast hcard
  have hbaseQ : (Nat.card CS : ℚ) * Nat.card S ≤ Nat.card CA * Nat.card A := by
    calc
      (Nat.card CS : ℚ) * Nat.card S =
          (2 * Nat.card CS) * Nat.card A := by rw [hcardQ]; ring
      _ ≤ (Nat.card CA : ℚ) * Nat.card A := by gcongr
  exact mul_le_mul_of_nonneg_left hbaseQ (by positivity)

/-- The index-two dichotomy implicit in the proof of Stellmacher (1.5): an
index-two subgroup of an elementary abelian actor is either in `oneAmax`, or
its fixed points on the odd core already equal those of the whole actor. -/
public theorem lemma_one_five_oneAmax_or_centralizer_eq
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) {S A : Subgroup G}
    (hS : IsElementaryAbelian 2 S) (hA : A ≤ S)
    (hcard : Nat.card S = 2 * Nat.card A) :
    oneAmax (G := G) (V := V) S A ∨
      oddCore G ⊓ Subgroup.centralizer (A : Set G) =
        oddCore G ⊓ Subgroup.centralizer (S : Set G) := by
  let : IsElementaryAbelian 2 S := hS
  let : CommGroup S := IsMulCommutative.instCommGroup
  by_cases hfixeq :
      FixedPoints.subgroup (↥A) V = FixedPoints.subgroup (↥S) V
  · exact Or.inr (lemma_one_five_fixedpoint_transfer h hS hA hfixeq)
  have hfixcond :
      S ⊓ fixingSubgroup G (FixedPoints.subgroup (↥A) V : Set V) = A := by
    rcases lemma_one_five_fixed_condition_or_eq (G := G) (V := V) hS hA hcard with
      hcond | heq
    · exact hcond
    · exact (hfixeq heq).elim
  rcases lemma_one_five_centralizer_condition_or_eq (V := V) hS hA hcard with
    hcentcond | hcentEq
  · left
    unfold oneAmax
    dsimp
    refine ⟨hA, lemma_one_five_m_le_of_fixedpoint_ne hA hcard hfixeq, ?_, hfixcond⟩
    have hnorm : S ≤ Subgroup.normalizer (A : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro s hs a ha
      have hsa : (s : G) * (a : G) = (a : G) * (s : G) := by
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := S)).comm ⟨s, hs⟩ ⟨a, hA ha⟩)
      rw [hsa]
      simpa [mul_assoc] using ha
    have hnormEq : S ⊓ Subgroup.normalizer (A : Set G) = S :=
      le_antisymm inf_le_left (le_inf le_rfl hnorm)
    simpa [hnormEq] using hcentcond
  · exact Or.inr hcentEq

private theorem lemma_one_five_sup_index_two_subgroups
    {G : Type u} [Group G] [Finite G]
    {S : Subgroup G} [IsElementaryAbelian 2 S]
    (hcard : 4 ≤ Nat.card S) :
    (⨆ (A : Subgroup S) (_ : Nat.card S = 2 * Nat.card A), A) = ⊤ := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (IsPGroup 2 S) := ⟨IsElementaryAbelian.isPGroup 2 S⟩
  let : Nontrivial S := by
    apply (Subgroup.nontrivial_iff_ne_bot S).2
    intro hbot
    simp [hbot] at hcard
  let J : Subgroup S :=
    ⨆ (A : Subgroup S) (_ : Nat.card S = 2 * Nat.card A), A
  apply le_antisymm le_top
  by_contra hJ
  have hJne : J ≠ ⊤ := by
    intro htop
    apply hJ
    change ⊤ ≤ J
    rw [← htop]
  rcases (eq_top_or_exists_le_coatom J).resolve_left hJne with ⟨M, hMcoat, hJM⟩
  have hMcardQ : Nat.card (S ⧸ M) = 2 :=
    _root_.card_quotient_coatom_eq_prime hMcoat
  have hMcard : Nat.card S = 2 * Nat.card M := by
    simpa [hMcardQ, Nat.mul_comm] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup M)
  have hMJ : M ≤ J := by
    exact le_iSup_of_le M (le_iSup_of_le hMcard le_rfl)
  have hMtop : M ≠ ⊤ := hMcoat.ne_top
  have hnot_subset : ¬ (Set.univ : Set S) ⊆ (M : Set S) := by
    intro hsub
    apply hMtop
    apply le_antisymm
    · intro x hx
      exact Set.mem_univ x
    · exact fun x hx => hsub (Set.mem_univ x)
  obtain ⟨x, _hx, hxM⟩ := Set.not_subset.mp hnot_subset
  have hxne : x ≠ (1 : S) := by
    intro hxone
    apply hxM
    simp [hxone]
  have horder : orderOf x = 2 := by
    exact (orderOf_eq_two_iff IsElementaryAbelian.exponent_eq_prime).2 hxne
  have hzp_card : Nat.card (Subgroup.zpowers x) = 2 := by
    rw [Nat.card_zpowers, horder]
  have hzp_top : Subgroup.zpowers x ≠ (⊤ : Subgroup S) := by
    intro htop
    have : Nat.card S = 2 := by
      calc
        Nat.card S = Nat.card (⊤ : Subgroup S) := by simp
        _ = Nat.card (Subgroup.zpowers x) := by rw [htop]
        _ = 2 := hzp_card
    omega
  rcases (eq_top_or_exists_le_coatom (Subgroup.zpowers x)).resolve_left hzp_top with
    ⟨N, hNcoat, hzpN⟩
  have hNcardQ : Nat.card (S ⧸ N) = 2 :=
    _root_.card_quotient_coatom_eq_prime hNcoat
  have hNcard : Nat.card S = 2 * Nat.card N := by
    simpa [hNcardQ, Nat.mul_comm] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup N)
  have hNJ : N ≤ J := le_iSup_of_le N (le_iSup_of_le hNcard le_rfl)
  have hxN : x ∈ N := hzpN (Subgroup.mem_zpowers x)
  exact hxM (hJM (hNJ hxN))

theorem lemma_one_five_m_ge_one_of_card_two
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (T : Subgroup G)
    (hcard : Nat.card T = 2) :
    m (G := G) (V := V) T ≥ 1 := by
  classical
  have hTtop : T ≠ ⊥ := by
    intro hbot
    have hcard_bot : Nat.card T = 1 := by
      simp [hbot]
    omega
  have hfix_ne_top : FixedPoints.subgroup T V ≠ ⊤ := by
    intro htop
    have hTker : T ≤ fixingSubgroup G (Set.univ : Set V) := by
      intro t ht
      rw [mem_fixingSubgroup_iff]
      intro v _hv
      have htv : (⟨t, ht⟩ : T) • v = v := by
        have hm : v ∈ FixedPoints.subgroup T V := by simp [htop]
        exact (FixedPoints.mem_subgroup (M := T) (a := v)).1 hm ⟨t, ht⟩
      exact htv
    have hTbot : T = ⊥ := by
      apply le_antisymm
      · exact h.action_faithful ▸ hTker
      · exact bot_le
    exact hTtop hTbot
  have hindex : 1 < (FixedPoints.subgroup T V).index :=
    Subgroup.one_lt_index_of_ne_top hfix_ne_top
  have hcard_index : Nat.card (FixedPoints.subgroup T V) *
      (FixedPoints.subgroup T V).index = Nat.card V := by
    simpa [Nat.mul_comm] using
      (Subgroup.index_mul_card (H := FixedPoints.subgroup T V))
  have hcard_fixed : 2 * Nat.card (FixedPoints.subgroup T V) ≤ Nat.card V := by
    have hi : 2 ≤ (FixedPoints.subgroup T V).index := by omega
    nlinarith [hcard_index]
  unfold m
  have hfixpos : (0 : ℚ) < Nat.card (FixedPoints.subgroup T V) := by
    exact_mod_cast (Nat.card_pos (α := FixedPoints.subgroup T V))
  rw [hcard]
  have hcardQ : (2 : ℚ) * Nat.card (FixedPoints.subgroup T V) ≤ Nat.card V := by
    exact_mod_cast hcard_fixed
  apply (le_div_iff₀ (by positivity :
    (0 : ℚ) < (Nat.card (FixedPoints.subgroup T V) : ℚ) * 2)).2
  nlinarith

theorem lemma_one_five_oddCore_ne_bot
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) : oddCore G ≠ ⊥ := by
  classical
  let : Group.IsSolvable G := h.G_solvable
  have hGsub : ¬ Subsingleton G := by
    intro hsub
    let : Subsingleton G := hsub
    have hcard1 : Nat.card G = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨1⟩⟩
    rcases h.G_even with ⟨k, hk⟩
    rw [hcard1] at hk
    omega
  let : Nontrivial G := not_subsingleton_iff_nontrivial.mp hGsub
  obtain ⟨M, hMnorm, hMne, hMmin⟩ :=
    exists_minimal_normal h.G_solvable (inferInstance : Nontrivial G)
  let : M.Normal := hMnorm
  let : IsMinimalNormal M := {
    minimal := by
      intro K hKnorm hKle
      by_cases hKbot : K = ⊥
      · exact Or.inl hKbot
      · exact Or.inr (hMmin K hKnorm hKle hKbot)
  }
  let : Group.IsSolvable (↥M) := inferInstance
  obtain ⟨q, hqprime, hMelem⟩ :=
    minimalNormal_solvable_exists_isElementaryAbelian M
  by_contra hWbot
  have hqne2 : q ≠ 2 := by
    intro hq2
    subst q
    have hMp : IsPGroup 2 M := hMelem.isPGroup 2 M
    have hM_le_pcore : M ≤ pCore 2 G := le_sSup ⟨hMnorm, hMp⟩
    have hMbot : M = ⊥ := by
      rw [h.twoCore_eq_bot] at hM_le_pcore
      exact le_bot_iff.mp hM_le_pcore
    exact hMne hMbot
  have hqodd : Odd q := by
    rcases hqprime.eq_two_or_odd with hq2 | hqodd
    · exact (hqne2 hq2).elim
    · exact Nat.odd_iff.mpr hqodd
  let : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨n, hn⟩ := (hMelem.isPGroup q M).exists_card_eq
  have hMcard_cop : Nat.Coprime 2 (Nat.card M) := by
    rw [hn]
    exact (hqodd.pow).coprime_two_left
  have hMbot : M = ⊥ :=
    (pPrimeCore_eq_bot_iff (p := 2) (G := G)).1 hWbot M hMnorm hMcard_cop
  exact hMne hMbot

/- The standard Fitting-subgroup argument used implicitly in the source's
   sentence "From (c) we get ...".  Since `O₂(G) = 1`, the Fitting subgroup
   has odd order and is contained in `O_{2'}(G)`; self-centralization of the
   Fitting subgroup then forces a Sylow 2-subgroup to centralize no nontrivial
   part of the odd core. -/
public theorem lemma_one_five_sylow_oddCore_centralizer_bot
    {G : Type u} {V : Type v} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) :
    (S : Subgroup G) ⊓ Subgroup.centralizer (oddCore G : Set G) = ⊥ := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let F : Subgroup G := fittingSubgroup G
  let W : Subgroup G := oddCore G
  have hF_normal : F.Normal := by
    simpa [F] using fittingSubgroup_normal
  have hF_nil : Group.IsNilpotent (↥F) := by
    simpa [F] using fittingSubgroup_nilpotent
  have hF_cop : Nat.Coprime 2 (Nat.card F) := by
    apply (Nat.prime_two.coprime_iff_not_dvd).2
    intro h2
    let P : Sylow 2 (↥F) := Classical.choice Sylow.nonempty
    have hPne : (P : Subgroup F) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P h2
    have hP_normal_sub : (P : Subgroup F).Normal :=
      Group.IsNilpotent.sylow_normal hF_nil 2 P
    let : P.Characteristic := Sylow.characteristic_of_normal P hP_normal_sub
    let : ((P : Subgroup F).map F.subtype).Normal := by infer_instance
    have hP_p : IsPGroup 2 ((P : Subgroup F).map F.subtype) :=
      IsPGroup.map (p := 2) (H := (P : Subgroup F)) P.isPGroup' F.subtype
    have hPmap_le : (P : Subgroup F).map F.subtype ≤ pCore 2 G :=
      le_sSup ⟨inferInstance, hP_p⟩
    have hPmap_core : (P : Subgroup F).map F.subtype = pCore 2 G := by
      apply le_antisymm hPmap_le
      rw [h.twoCore_eq_bot]
      exact bot_le
    have hPmap_bot : (P : Subgroup F).map F.subtype = ⊥ := hPmap_core.trans h.twoCore_eq_bot
    apply hPne
    apply Subgroup.map_injective F.subtype_injective
    simp [hPmap_bot]
  have hFleW : F ≤ W := by
    exact le_sSup ⟨hF_normal, hF_cop⟩
  have hcentF : Subgroup.centralizer (F : Set G) ≤ F :=
    centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable h.G_solvable
  have hSWcop : Nat.Coprime (Nat.card (S : Subgroup G)) (Nat.card W) := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (G := G) (p := 2)).pow_left n
  have hSWbot : (S : Subgroup G) ⊓ W = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard hSWcop).eq_bot
  apply le_antisymm
  · intro x hx
    have hxS : x ∈ (S : Subgroup G) := hx.1
    have hxWcent : x ∈ Subgroup.centralizer (W : Set G) := hx.2
    have hxFcent : x ∈ Subgroup.centralizer (F : Set G) := by
      exact (Subgroup.centralizer_le (show (F : Set G) ⊆ (W : Set G) from
        fun y hy => hFleW hy)) hxWcent
    have hxF : x ∈ F := hcentF hxFcent
    have hxW : x ∈ W := hFleW hxF
    have hxSW : x ∈ (S : Subgroup G) ⊓ W := ⟨hxS, hxW⟩
    rw [hSWbot] at hxSW
    exact hxSW
  · exact bot_le

/- If the odd core centralized a Sylow 2-subgroup, the pullback of the
nontrivial 2-core of the quotient by the odd core would give a nontrivial
normal 2-subgroup of `G`.  This is the source's missing exclusion of the
centralizer branch in part (c). -/
private theorem lemma_one_five_centralizer_sylow_ne
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS : IsElementaryAbelian 2 (S : Subgroup G))
    (hWcent : oddCore G ≤
      Subgroup.centralizer ((S : Subgroup G) : Set G)) : False := by
  classical
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : IsElementaryAbelian 2 (S : Subgroup G) := hS
  let : Group.IsSolvable G := h.G_solvable
  let W : Subgroup G := oddCore G
  let : W.Normal := by
    dsimp [W]
    exact pPrimeCore_normal
  let Q := G ⧸ W
  let q : G →* Q := QuotientGroup.mk' W
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective W
  have hQcore : pPrimeCore 2 Q = ⊥ := by
    dsimp [Q, W]
    exact pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hSbot : (S : Subgroup G) ≠ ⊥ :=
    Sylow.ne_bot_of_dvd_card S h.G_even.two_dvd
  have hScopW : Nat.Coprime (Nat.card (S : Subgroup G)) (Nat.card W) := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn]
    exact (pPrimeCore_coprime_card (G := G) (p := 2)).pow_left n
  have hQnontriv : Nontrivial Q := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    let : Subsingleton Q := hsub
    have hSleW : (S : Subgroup G) ≤ W := by
      intro s hs
      have hqone : q s = 1 := Subsingleton.elim _ _
      have hsKer : s ∈ q.ker := (MonoidHom.mem_ker).2 hqone
      have hsKer' : s ∈ W := by
        change s ∈ (QuotientGroup.mk' W).ker at hsKer
        rw [QuotientGroup.ker_mk'] at hsKer
        exact hsKer
      exact hsKer'
    have hinf : (S : Subgroup G) ⊓ W = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard hScopW).eq_bot
    apply hSbot
    apply le_antisymm
    · simpa [inf_eq_left.mpr hSleW] using hinf
    · exact bot_le
  have hQsolv : Group.IsSolvable Q := Group.isSolvable_of_surjective hqsurj
  let : Group.IsSolvable Q := hQsolv
  obtain ⟨M, hMnorm, hMne, hMmin⟩ :=
    exists_minimal_normal (G := Q) hQsolv hQnontriv
  let : M.Normal := hMnorm
  let : IsMinimalNormal M := {
    minimal := by
      intro K hKnorm hKle
      by_cases hKbot : K = ⊥
      · exact Or.inl hKbot
      · exact Or.inr (hMmin K hKnorm hKle hKbot)
  }
  let : Group.IsSolvable (↥M) := inferInstance
  obtain ⟨r, hrprime, hMelem⟩ :=
    minimalNormal_solvable_exists_isElementaryAbelian M
  have hPne : pCore 2 Q ≠ ⊥ := by
    rcases hrprime.eq_two_or_odd with hr2 | hrodd
    · subst r
      have hMp : IsPGroup 2 M := hMelem.isPGroup 2 M
      intro hPbot
      have hMle : M ≤ pCore 2 Q := le_sSup ⟨hMnorm, hMp⟩
      exact hMne (le_bot_iff.mp (hPbot ▸ hMle))
    · have hrodd' : Odd r := Nat.odd_iff.mpr hrodd
      let : Fact r.Prime := ⟨hrprime⟩
      obtain ⟨n, hn⟩ := (hMelem.isPGroup r M).exists_card_eq
      have hMcardcop : Nat.Coprime 2 (Nat.card M) := by
        rw [hn]
        exact (hrodd'.pow).coprime_two_left
      have hMleodd : M ≤ pPrimeCore 2 Q := le_sSup ⟨hMnorm, hMcardcop⟩
      have hMbot : M = ⊥ := by
        rw [hQcore] at hMleodd
        exact le_bot_iff.mp hMleodd
      exact (hMne hMbot).elim
  let Sbar : Sylow 2 Q := S.mapSurjective hqsurj
  have hPbar_le : pCore 2 Q ≤ (Sbar : Subgroup Q) :=
    IsPGroup.le_sylow_of_normal (pCore_isPGroup (G := Q) (p := 2)) Sbar
  let K : Subgroup G := (pCore 2 Q).comap q
  have hKnormal : K.Normal := by
    dsimp [K]
    exact (inferInstance : (pCore 2 Q).Normal).comap q
  let R : Subgroup G := (S : Subgroup G) ⊓ K
  have hRleS : R ≤ (S : Subgroup G) := inf_le_left
  have hRleK : R ≤ K := inf_le_right
  have hRne : R ≠ ⊥ := by
    intro hRbot
    let : Nontrivial (pCore 2 Q) :=
      (Subgroup.nontrivial_iff_ne_bot (pCore 2 Q)).2 hPne
    obtain ⟨x, hxne⟩ :=
      (nontrivial_iff_exists_ne (1 : pCore 2 Q)).mp inferInstance
    have hxSbar : (x : Q) ∈ (Sbar : Subgroup Q) := hPbar_le x.property
    rcases Subgroup.mem_map.mp hxSbar with ⟨s, hsS, hsx⟩
    have hsK : s ∈ K := by
      change q s ∈ pCore 2 Q
      rw [hsx]
      exact x.property
    have hsR : s ∈ R := ⟨hsS, hsK⟩
    have hsne : s ≠ (1 : G) := by
      intro hsone
      apply hxne
      simpa [hsone] using hsx.symm
    apply hsne
    have hsbot : s ∈ (⊥ : Subgroup G) := by simpa [hRbot] using hsR
    simpa using hsbot
  have hWleK : W ≤ K := by
    intro w hw
    change q w ∈ pCore 2 Q
    have hqw : q w = 1 := by
      apply (QuotientGroup.eq_one_iff (N := W) (w : G)).2
      exact hw
    rw [hqw]
    exact (pCore 2 Q).one_mem
  have hKWsup : K = W ⊔ R := by
    apply le_antisymm
    · intro x hx
      have hxSbar : q x ∈ (Sbar : Subgroup Q) := hPbar_le hx
      rcases Subgroup.mem_map.mp hxSbar with ⟨s, hsS, hsx⟩
      have hsK : s ∈ K := by
        change q s ∈ pCore 2 Q
        rw [hsx]
        exact hx
      have hsR : s ∈ R := ⟨hsS, hsK⟩
      let w : G := s⁻¹ * x
      have hwW : w ∈ W := by
        have hwker : w ∈ q.ker := by
          apply (MonoidHom.mem_ker).2
          change q w = 1
          dsimp [w]
          rw [map_mul, map_inv, hsx]
          simp
        change w ∈ (QuotientGroup.mk' W).ker at hwker
        rw [QuotientGroup.ker_mk'] at hwker
        exact hwker
      have hwcomm : (w : G) * (s : G) = (s : G) * (w : G) :=
        (Subgroup.mem_centralizer_iff.mp (hWcent hwW) (s : G) hsS).symm
      have hxws : x = (w : G) * (s : G) := by
        have hxsw : x = (s : G) * (w : G) := by
          dsimp [w]
          simp
        exact hxsw.trans hwcomm.symm
      rw [hxws]
      apply (Subgroup.mem_sup_of_normal_left).2
      exact ⟨w, hwW, s, hsR, rfl⟩
    · refine sup_le hWleK hRleK
  have hRnormal : R.Normal := by
    constructor
    intro x hx g
    have hxK : x ∈ K := hRleK hx
    have hxKg : g * x * g⁻¹ ∈ K := hKnormal.conj_mem x hxK g
    rw [hKWsup] at hxKg
    rcases (Subgroup.mem_sup_of_normal_left).1 hxKg with
      ⟨w, hwW, r, hrR, hwr⟩
    have hx2 : x ^ 2 = 1 := by
      have hxS : (x : G) ∈ (S : Subgroup G) := hRleS hx
      have hx2' := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (S : Subgroup G)) ⟨x, hxS⟩
      simpa using hx2'
    have hxg2 : (g * x * g⁻¹) ^ 2 = 1 := by
      simpa [pow_two, mul_assoc] using congrArg (fun z : G => g * z * g⁻¹) hx2
    have hr2 : r ^ 2 = 1 := by
      have hrS : (r : G) ∈ (S : Subgroup G) := hRleS hrR
      have hr2' := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (S : Subgroup G)) ⟨r, hrS⟩
      simpa using hr2'
    have hcommwr : (w : G) * (r : G) = (r : G) * (w : G) :=
      (Subgroup.mem_centralizer_iff.mp (hWcent hwW) (r : G) (hRleS hrR)).symm
    have hw2 : (w : G) ^ 2 = 1 := by
      rw [← hwr] at hxg2
      have hwr2 : ((w : G) * (r : G)) ^ 2 = (w : G) ^ 2 := by
        calc
          ((w : G) * (r : G)) ^ 2 =
              (w : G) * ((r : G) * (w : G)) * (r : G) := by
            simp [pow_two, mul_assoc]
          _ = (w : G) * ((w : G) * (r : G)) * (r : G) := by
            rw [← hcommwr]
          _ = (w : G) * (w : G) * ((r : G) * (r : G)) := by
            simp [mul_assoc]
          _ = (w : G) * (w : G) * (r : G) ^ 2 := by
            rw [pow_two]
          _ = (w : G) ^ 2 := by
            rw [hr2]
            simp [pow_two]
      exact hwr2 ▸ hxg2
    let yw : W := ⟨w, hwW⟩
    have hordW' : orderOf yw ∣ Nat.card W :=
      orderOf_dvd_natCard yw
    have hordW : orderOf (w : G) ∣ Nat.card W := by
      have heq : orderOf (w : G) = orderOf (yw : G) := by rfl
      rw [heq, Subgroup.orderOf_coe]
      exact hordW'
    have hord2 : orderOf (w : G) ∣ 2 := orderOf_dvd_of_pow_eq_one hw2
    have hord1 : orderOf (w : G) = 1 := Nat.eq_one_of_dvd_coprimes
      (pPrimeCore_coprime_card (G := G) (p := 2)) hord2 hordW
    have hwone : (w : G) = 1 := (orderOf_eq_one_iff).mp hord1
    have hyEq : g * x * g⁻¹ = r := by
      rw [← hwr, hwone]
      simp
    rw [hyEq]
    exact hrR
  have hRp : IsPGroup 2 R := by
    intro x
    have hxS : (x : G) ∈ (S : Subgroup G) := hRleS x.property
    obtain ⟨n, hn⟩ := (hS.isPGroup 2 (S : Subgroup G)) ⟨x, hxS⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    simpa using hn
  have hRlecore : R ≤ pCore 2 G := le_sSup ⟨hRnormal, hRp⟩
  have hRbot : R = ⊥ := by
    rw [h.twoCore_eq_bot] at hRlecore
    exact le_bot_iff.mp hRlecore
  exact hRne hRbot

private theorem lemma_one_five_isElementaryAbelian_of_le
    {G : Type u} [Group G] {S A : Subgroup G}
    (hS : IsElementaryAbelian 2 S) (hA : A ≤ S) :
    IsElementaryAbelian 2 A := by
  let : IsElementaryAbelian 2 S := hS
  refine {
    toIsMulCommutative := {
      is_comm := ⟨?_⟩ }
    exponent_dvd_p := ?_ }
  · intro a b
    apply Subtype.ext
    change (a : G) * (b : G) = (b : G) * (a : G)
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := S)).comm
        ⟨a, hA a.property⟩ ⟨b, hA b.property⟩)
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro a
    apply Subtype.ext
    have ha := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 S)
      (⟨a, hA a.property⟩ : S)
    simpa using congrArg Subtype.val ha

private theorem lemma_one_five_exists_oneAmax_index_two
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS : IsElementaryAbelian 2 (S : Subgroup G)) :
    ∃ A : Subgroup G,
      oneAmax (G := G) (V := V) (S : Subgroup G) A ∧
        Nat.card (S : Subgroup G) = 2 * Nat.card A := by
  classical
  let : IsElementaryAbelian 2 (S : Subgroup G) := hS
  let : CommGroup (S : Subgroup G) := IsMulCommutative.instCommGroup
  have hWneq : oddCore G ≠
      oddCore G ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
    intro hEq
    apply lemma_one_five_centralizer_sylow_ne h S hS
    exact hEq ▸ inf_le_right
  have hgen : oddCore G =
      ⨆ (A : Subgroup (S : Subgroup G))
        (_ : Nat.card (S : Subgroup G) = 2 * Nat.card A),
        oddCore G ⊓ Subgroup.centralizer
          ((A.map (S : Subgroup G).subtype : Subgroup G) : Set G) := by
    simpa using (lemma_one_one h S).part_c hS
  by_contra hnone
  push Not at hnone
  apply hWneq
  apply le_antisymm
  · conv_lhs => rw [hgen]
    refine iSup₂_le ?_
    intro A hAcard
    let AG : Subgroup G := A.map (S : Subgroup G).subtype
    have hAGle : AG ≤ (S : Subgroup G) := by
      dsimp [AG]
      exact Subgroup.map_subtype_le A
    have hAGcard : Nat.card (S : Subgroup G) = 2 * Nat.card AG := by
      dsimp [AG]
      simpa only [Subgroup.card_subtype] using hAcard
    rcases lemma_one_five_oneAmax_or_centralizer_eq h hS hAGle hAGcard with
      hA | hEq
    · exact (hnone AG hA hAGcard).elim
    · rw [hEq]
  · exact inf_le_left

theorem lemma_one_five_part_b_of_card_two
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G) (hcard : Nat.card S = 2) :
    S = ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) S A ∧ Nat.card A = 2},
      (A : Subgroup G) := by
  classical
  let AS : {A : Subgroup G // oneAmax (G := G) (V := V) S A ∧ Nat.card A = 2} :=
    ⟨S, ⟨lemma_one_five_self_oneAmax S, hcard⟩⟩
  apply le_antisymm
  · exact le_iSup (fun A : {A : Subgroup G //
      oneAmax (G := G) (V := V) S A ∧ Nat.card A = 2} => (A : Subgroup G)) AS
  · refine iSup_le ?_
    intro A
    exact A.property.1.1

/- The coprime-action generation used in (1.5)(c), generalized from the
chosen Sylow subgroup to any nontrivial elementary abelian subgroup below it.
This is the induction interface implicit in the source proof. -/
private theorem lemma_one_five_oddCore_eq_iSup_index_two
    {G : Type u} [Group G] [Finite G]
    (T : Subgroup G) (hT : IsElementaryAbelian 2 T) (hTne : T ≠ ⊥) :
    oddCore G =
      ⨆ (A : Subgroup T) (_ : Nat.card T = 2 * Nat.card A),
        oddCore G ⊓ Subgroup.centralizer
          ((A.map T.subtype : Subgroup G) : Set G) := by
  classical
  let : IsElementaryAbelian 2 T := hT
  let : CommGroup T := IsMulCommutative.instCommGroup
  let : Fact (IsPGroup 2 T) := ⟨IsElementaryAbelian.isPGroup 2 T⟩
  let W : Subgroup G := oddCore G
  let hWnormal : W.Normal := by
    dsimp [W]
    exact pPrimeCore_normal
  let hTnormW : T ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.le_normalizer_of_normal
  let : MulDistribMulAction T W :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer T W hTnormW
  let : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hTne
  have hindex_top :
      (⨆ (A : Subgroup T) (_ : Nat.card T = 2 * Nat.card A),
        fixedPointSubgroup A W) = ⊤ := by
    by_cases hTcyc : IsCyclic T
    · let : IsCyclic T := hTcyc
      have hTcard : Nat.card T = 2 := by
        rw [← hTcyc.exponent_eq_card]
        exact IsElementaryAbelian.exponent_eq_prime
      have hbotcard : Nat.card T = 2 * Nat.card (⊥ : Subgroup T) := by
        simp [hTcard]
      have hfixbot : fixedPointSubgroup (⊥ : Subgroup T) W = ⊤ := by
        ext w
        simp [FixedPoints.mem_subgroup]
      apply top_unique
      rw [← hfixbot]
      exact le_iSup_of_le (⊥ : Subgroup T)
        (le_iSup_of_le hbotcard le_rfl)
    · have hcop : Nat.Coprime 2 (Nat.card W) := by
        dsimp [W]
        exact pPrimeCore_coprime_card
      have hcyclic_top :
          (⨆ (Y : Subgroup T) (_ : IsCyclic (T ⧸ Y)),
            fixedPointSubgroup Y W) = ⊤ :=
        iSup_fixedPointSubgroup_cyclicQuot_eq_top_of_noncyclic_abelian_pGroup_action
          (G := W) (A := T) (p := 2) hcop (hncyc := hTcyc)
      have hcyclic_le :
          (⨆ (Y : Subgroup T) (_ : IsCyclic (T ⧸ Y)),
            fixedPointSubgroup Y W) ≤
              ⨆ (A : Subgroup T) (_ : Nat.card T = 2 * Nat.card A),
                fixedPointSubgroup A W := by
        refine iSup₂_le ?_
        intro Y hYcyc
        by_cases hYtop : Y = ⊤
        · obtain ⟨M, hM⟩ := IsCoatomic.exists_coatom (Subgroup T)
          have hMquot : Nat.card (T ⧸ M) = 2 :=
            card_quotient_coatom_eq_prime (p := 2) hM
          have hMcard : Nat.card T = 2 * Nat.card M := by
            simpa [hMquot] using
              (Subgroup.card_eq_card_quotient_mul_card_subgroup M)
          refine le_iSup_of_le M (le_iSup_of_le hMcard ?_)
          subst Y
          exact fixedPoints_subgroup_antitone T W le_top
        · let : Y.Normal := inferInstance
          have hYelem : IsElementaryAbelian 2 (T ⧸ Y) := by
            refine
              { toIsMulCommutative := inferInstance
                exponent_dvd_p := ?_ }
            refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
            intro q
            obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective Y q
            have ht2 : t ^ 2 = 1 :=
              Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
                (IsElementaryAbelian.exponent_dvd_p 2 T) t
            simpa only [map_pow, map_one] using
              congrArg (QuotientGroup.mk' Y) ht2
          let : IsElementaryAbelian 2 (T ⧸ Y) := hYelem
          let : Nontrivial (T ⧸ Y) := QuotientGroup.nontrivial_iff.mpr hYtop
          have hYcardQ : Nat.card (T ⧸ Y) = 2 := by
            rw [← hYcyc.exponent_eq_card]
            exact IsElementaryAbelian.exponent_eq_prime
          have hYcard : Nat.card T = 2 * Nat.card Y := by
            simpa [hYcardQ] using
              (Subgroup.card_eq_card_quotient_mul_card_subgroup Y)
          exact le_iSup_of_le Y (le_iSup_of_le hYcard le_rfl)
      apply top_unique
      rw [← hcyclic_top]
      exact hcyclic_le
  have htopmap : (⊤ : Subgroup W).map W.subtype = W := by
    ext x
    simp
  have hterm (A : Subgroup T) :
      (fixedPointSubgroup A W).map W.subtype =
        W ⊓ Subgroup.centralizer
          ((A.map T.subtype : Subgroup G) : Set G) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.property, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨t, htA, rfl⟩
      have htfix : (⟨t, htA⟩ : A) • w = w := hw ⟨t, htA⟩
      have hTfix : (t : T) • w = w := by
        simpa only [Subgroup.smul_def] using htfix
      have hconj : (t : G) * (w : G) * (t : G)⁻¹ = (w : G) :=
        (Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
          T W hTnormW t w).symm.trans (congrArg Subtype.val hTfix)
      have hmul := congrArg (fun z : G => z * (t : G)) hconj
      simpa [mul_assoc] using hmul
    · rintro ⟨hxW, hxcent⟩
      refine ⟨⟨x, hxW⟩, ?_, rfl⟩
      change ∀ y : A, y • (⟨x, hxW⟩ : W) = ⟨x, hxW⟩
      intro y
      apply Subtype.ext
      have hymem : (y : G) ∈ A.map T.subtype :=
        Subgroup.mem_map.mpr ⟨(y : T), y.property, rfl⟩
      have hycomm : (y : G) * x = x * (y : G) :=
        Subgroup.mem_centralizer_iff.mp hxcent (y : G) hymem
      calc
        ((y : T) • (⟨x, hxW⟩ : W) : W) =
            (y : G) * x * (y : G)⁻¹ :=
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe_explicit
            T W hTnormW (y : T) ⟨x, hxW⟩
        _ = x := by rw [hycomm]; simp [mul_assoc]
  have hmap := congrArg (fun K : Subgroup W => K.map W.subtype) hindex_top
  simp only [Subgroup.map_iSup] at hmap
  simp_rw [hterm] at hmap
  rw [htopmap] at hmap
  simpa [W] using hmap.symm

private theorem lemma_one_five_oddCore_centralizer_ne_of_nontrivial_le_sylow
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) {T : Subgroup G}
    (hTS : T ≤ (S : Subgroup G)) (hTne : T ≠ ⊥) :
    oddCore G ≠ oddCore G ⊓ Subgroup.centralizer (T : Set G) := by
  intro hEq
  have hWcentT : oddCore G ≤ Subgroup.centralizer (T : Set G) := by
    rw [hEq]
    exact inf_le_right
  have hTcentW : T ≤ Subgroup.centralizer (oddCore G : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hWcentT hw) t ht).symm
  have hTbot : T ≤ ⊥ := by
    intro t ht
    have ht' : t ∈ (S : Subgroup G) ⊓
        Subgroup.centralizer (oddCore G : Set G) := ⟨hTS ht, hTcentW ht⟩
    rw [lemma_one_five_sylow_oddCore_centralizer_bot h S] at ht'
    exact ht'
  exact hTne (le_bot_iff.mp hTbot)

/- Part (c), in the relative form needed by the induction in parts (b) and
(d). -/
private theorem lemma_one_five_part_c_relative
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (T : Subgroup G)
    (hTS : T ≤ (S : Subgroup G)) (hT : IsElementaryAbelian 2 T)
    (hTne : T ≠ ⊥) :
    oddCore G =
      ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) T A ∧
          Nat.card T = 2 * Nat.card A},
        oddCore G ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G) := by
  classical
  let : IsElementaryAbelian 2 T := hT
  let : CommGroup T := IsMulCommutative.instCommGroup
  let W : Subgroup G := oddCore G
  let K : Subgroup G :=
    ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) T A ∧
        Nat.card T = 2 * Nat.card A},
      W ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G)
  have hWneq : W ≠ W ⊓ Subgroup.centralizer (T : Set G) := by
    simpa [W] using
      lemma_one_five_oddCore_centralizer_ne_of_nontrivial_le_sylow h S hTS hTne
  have hgen : W =
      ⨆ (A : Subgroup T) (_ : Nat.card T = 2 * Nat.card A),
        W ⊓ Subgroup.centralizer
          ((A.map T.subtype : Subgroup G) : Set G) := by
    simpa [W] using lemma_one_five_oddCore_eq_iSup_index_two T hT hTne
  have hgood : ∃ A : Subgroup T,
      Nat.card T = 2 * Nat.card A ∧
        W ⊓ Subgroup.centralizer
            ((A.map T.subtype : Subgroup G) : Set G) ≠
          W ⊓ Subgroup.centralizer (T : Set G) := by
    by_contra hn
    push Not at hn
    apply hWneq
    apply le_antisymm
    · conv_lhs => rw [hgen]
      refine iSup₂_le ?_
      intro A hAcard
      exact (hn A hAcard).le
    · exact inf_le_left
  obtain ⟨B, hBcard, hBneq⟩ := hgood
  have hBmap_le : B.map T.subtype ≤ T := Subgroup.map_subtype_le B
  have hBcard_map : Nat.card T =
      2 * Nat.card (B.map T.subtype) := by
    simpa only [Subgroup.card_subtype] using hBcard
  have hBcandidate : oneAmax (G := G) (V := V) T (B.map T.subtype) := by
    rcases lemma_one_five_oneAmax_or_centralizer_eq h hT hBmap_le hBcard_map with
      hA | hEq
    · exact hA
    · exact (hBneq hEq).elim
  have hWTc_le_B : W ⊓ Subgroup.centralizer (T : Set G) ≤
      W ⊓ Subgroup.centralizer
        ((B.map T.subtype : Subgroup G) : Set G) := by
    refine le_inf inf_le_left ?_
    intro x hx
    exact (Subgroup.centralizer_le (show
      ((B.map T.subtype : Subgroup G) : Set G) ⊆ (T : Set G) from
        fun x hx => hBmap_le hx)) hx.2
  have hWTc_le_K : W ⊓ Subgroup.centralizer (T : Set G) ≤ K := by
    exact hWTc_le_B.trans (le_iSup (fun A :
      {A : Subgroup G // oneAmax (G := G) (V := V) T A ∧
        Nat.card T = 2 * Nat.card A} =>
      W ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G))
      ⟨B.map T.subtype, hBcandidate, hBcard_map⟩)
  apply le_antisymm
  · change W ≤ ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) T A ∧
        Nat.card T = 2 * Nat.card A},
      W ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G)
    conv_lhs => rw [hgen]
    refine iSup₂_le ?_
    intro A hAcard
    let AG : Subgroup G := A.map T.subtype
    have hAGle : AG ≤ T := by
      dsimp [AG]
      exact Subgroup.map_subtype_le A
    have hAGcard : Nat.card T = 2 * Nat.card AG := by
      dsimp [AG]
      simpa only [Subgroup.card_subtype] using hAcard
    rcases lemma_one_five_oneAmax_or_centralizer_eq h hT hAGle hAGcard with
      hA | hEq
    · exact le_iSup (fun A :
        {A : Subgroup G // oneAmax (G := G) (V := V) T A ∧
          Nat.card T = 2 * Nat.card A} =>
          W ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G))
        ⟨AG, hA, hAGcard⟩
    · rw [hEq]
      exact hWTc_le_K
  · exact iSup_le fun A => inf_le_left

private theorem lemma_one_five_exists_oneAmax_index_two_relative
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (T : Subgroup G)
    (hTS : T ≤ (S : Subgroup G)) (hT : IsElementaryAbelian 2 T)
    (hTne : T ≠ ⊥) :
    ∃ A : Subgroup G,
      oneAmax (G := G) (V := V) T A ∧ Nat.card T = 2 * Nat.card A := by
  classical
  let : IsElementaryAbelian 2 T := hT
  let : CommGroup T := IsMulCommutative.instCommGroup
  have hWneq : oddCore G ≠
      oddCore G ⊓ Subgroup.centralizer (T : Set G) :=
    lemma_one_five_oddCore_centralizer_ne_of_nontrivial_le_sylow h S hTS hTne
  have hgen : oddCore G =
      ⨆ (A : Subgroup T) (_ : Nat.card T = 2 * Nat.card A),
        oddCore G ⊓ Subgroup.centralizer
          ((A.map T.subtype : Subgroup G) : Set G) :=
    lemma_one_five_oddCore_eq_iSup_index_two T hT hTne
  by_contra hnone
  push Not at hnone
  apply hWneq
  apply le_antisymm
  · conv_lhs => rw [hgen]
    refine iSup₂_le ?_
    intro A hAcard
    let AG : Subgroup G := A.map T.subtype
    have hAGle : AG ≤ T := by
      dsimp [AG]
      exact Subgroup.map_subtype_le A
    have hAGcard : Nat.card T = 2 * Nat.card AG := by
      dsimp [AG]
      simpa only [Subgroup.card_subtype] using hAcard
    rcases lemma_one_five_oneAmax_or_centralizer_eq h hT hAGle hAGcard with
      hA | hEq
    · exact (hnone AG hA hAGcard).elim
    · rw [hEq]
  · exact inf_le_left

private theorem lemma_one_five_index_two_candidates_generate_relative
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (T : Subgroup G)
    (hTS : T ≤ (S : Subgroup G)) (hT : IsElementaryAbelian 2 T)
    (hcard4 : 4 ≤ Nat.card T) :
    T =
      ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) T A ∧
          Nat.card T = 2 * Nat.card A},
        (A : Subgroup G) := by
  classical
  let : IsElementaryAbelian 2 T := hT
  let : CommGroup T := IsMulCommutative.instCommGroup
  let W : Subgroup G := oddCore G
  let J : Subgroup G :=
    ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) T A ∧
      Nat.card T = 2 * Nat.card A},
      (A : Subgroup G)
  have hTne : T ≠ ⊥ := by
    intro hbot
    simp [hbot] at hcard4
  have hpartc : W =
      ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) T A ∧
          Nat.card T = 2 * Nat.card A},
        W ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G) := by
    simpa [W] using lemma_one_five_part_c_relative h S T hTS hT hTne
  obtain ⟨B, hBgood, hBcard⟩ :=
    lemma_one_five_exists_oneAmax_index_two_relative h S T hTS hT hTne
  have hBcard2 : 2 ≤ Nat.card B := by omega
  have hBne : B ≠ ⊥ := by
    intro hbot
    simp [hbot] at hBcard2
  by_contra hJ
  push Not at hJ
  have hJle : J ≤ T := by
    dsimp [J]
    refine iSup_le ?_
    intro A
    exact A.property.1.1
  have hBleJ : B ≤ J :=
    le_iSup (fun A : {A : Subgroup G //
      oneAmax (G := G) (V := V) T A ∧
      Nat.card T = 2 * Nat.card A} => (A : Subgroup G))
      ⟨B, hBgood, hBcard⟩
  have hJcard_lt : Nat.card J < Nat.card T := by
    have hJcardT : Nat.card J ≤ Nat.card T :=
      Nat.card_le_card_of_injective
        (fun x => (⟨x.1, hJle x.2⟩ : T))
        (by
          intro x y hxy
          apply Subtype.ext
          simpa using congrArg Subtype.val hxy)
    have hJneq : J ≠ T := by
      intro hEq
      exact hJ hEq.symm
    apply Nat.lt_of_le_of_ne hJcardT
    intro hcard
    apply hJneq
    exact Subgroup.eq_of_le_of_card_ge hJle hcard.symm.le
  have hJeqB : J = B := by
    rcases lemma_one_five_index_two_intermediate hBgood.1 hBleJ hJle hBcard with
      hJB | hJT
    · exact hJB
    · exact (hJ (by simpa [J] using hJT.symm)).elim
  have hAeqB (A : {A : Subgroup G //
      oneAmax (G := G) (V := V) T A ∧
      Nat.card T = 2 * Nat.card A}) :
      (A : Subgroup G) = B := by
    apply Subgroup.eq_of_le_of_card_ge
    · have hAJ : (A : Subgroup G) ≤ J :=
        le_iSup (fun C : {C : Subgroup G //
          oneAmax (G := G) (V := V) T C ∧
          Nat.card T = 2 * Nat.card C} => (C : Subgroup G)) A
      simpa [hJeqB] using hAJ
    · omega
  have hWleB : W ≤ W ⊓ Subgroup.centralizer (B : Set G) := by
    conv_lhs => rw [hpartc]
    refine iSup_le ?_
    intro A
    rw [hAeqB A]
  have hBcent : B ≤ Subgroup.centralizer (W : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hWleB hw).2 b hb).symm
  have hBbot : B ≤ ⊥ := by
    intro b hb
    have hSb : b ∈ (S : Subgroup G) := hTS (hBgood.1 hb)
    have hWb : b ∈ Subgroup.centralizer (W : Set G) := hBcent hb
    have hSW : b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) :=
      ⟨hSb, hWb⟩
    rw [show (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) = ⊥ by
      simpa [W] using lemma_one_five_sylow_oddCore_centralizer_bot h S] at hSW
    exact hSW
  exact hBne (le_bot_iff.mp hBbot)

private theorem lemma_one_five_elementary_card_cases
    {G : Type u} [Group G] [Finite G] (T : Subgroup G)
    (hT : IsElementaryAbelian 2 T) :
    Nat.card T = 1 ∨ Nat.card T = 2 ∨ 4 ≤ Nat.card T := by
  obtain ⟨n, hn⟩ := (hT.isPGroup 2 T).exists_card_eq
  rcases n with _ | n
  · left
    simpa using hn
  rcases n with _ | n
  · right
    left
    simpa using hn
  · right
    right
    rw [hn]
    calc
      4 = 4 * 1 := by omega
      _ ≤ 4 * 2 ^ n := Nat.mul_le_mul_left 4 (Nat.one_le_pow n 2 (by omega))
      _ = 2 ^ (n + 2) := by ring

/- The simultaneous induction behind source parts (b) and (d).  Every
nontrivial step first spans `T` by its index-two `oneAmax` subgroups, applies
the induction hypothesis inside each one, and transports the resulting
order-two candidates back to `T`. -/
private theorem lemma_one_five_order_two_candidates_generate_relative
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (T : Subgroup G)
    (hTS : T ≤ (S : Subgroup G)) (hT : IsElementaryAbelian 2 T) :
    T =
      ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) T A ∧
          Nat.card A = 2},
        (A : Subgroup G) := by
  classical
  have hmain : ∀ n : ℕ, ∀ T : Subgroup G,
      T ≤ (S : Subgroup G) → IsElementaryAbelian 2 T → Nat.card T = n →
      T =
        ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) T A ∧
            Nat.card A = 2},
          (A : Subgroup G) := by
    intro n
    refine Nat.strongRecOn n ?_
    intro n ih T hTS hT hcard
    rcases lemma_one_five_elementary_card_cases T hT with hcard1 | hcard2 | hcard4
    · have hTbot : T = ⊥ := (Subgroup.eq_bot_iff_card T).2 hcard1
      rw [hTbot]
      apply le_antisymm
      · exact bot_le
      · refine iSup_le ?_
        intro A
        simpa using A.property.1.1
    · exact lemma_one_five_part_b_of_card_two T hcard2
    · have hindex :=
        lemma_one_five_index_two_candidates_generate_relative h S T hTS hT hcard4
      apply le_antisymm
      · refine hindex.le.trans ?_
        refine iSup_le ?_
        intro A
        have hAelem : IsElementaryAbelian 2 (A : Subgroup G) :=
          lemma_one_five_isElementaryAbelian_of_le hT A.property.1.1
        have hAcard_lt : Nat.card (A : Subgroup G) < n := by
          have hApos : 0 < Nat.card (A : Subgroup G) := Nat.card_pos
          omega
        have hAgen := ih (Nat.card (A : Subgroup G)) hAcard_lt
          (A : Subgroup G) (A.property.1.1.trans hTS) hAelem rfl
        rw [hAgen]
        refine iSup_le ?_
        intro B
        have hBmax : oneAmax (G := G) (V := V) T (B : Subgroup G) :=
          lemma_one_five_oneAmax_transfer hT A.property.1 B.property.1
        exact le_iSup (fun C : {C : Subgroup G //
          oneAmax (G := G) (V := V) T C ∧ Nat.card C = 2} =>
            (C : Subgroup G)) ⟨B, hBmax, B.property.2⟩
      · refine iSup_le ?_
        intro A
        exact A.property.1.1
  exact hmain (Nat.card T) T hTS hT rfl

theorem lemma_one_five_exists_oneAmax_card_two_relative
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G) (T : Subgroup G)
    (hTS : T ≤ (S : Subgroup G)) (hT : IsElementaryAbelian 2 T)
    (hTne : T ≠ ⊥) :
    ∃ A : Subgroup G,
      oneAmax (G := G) (V := V) T A ∧ Nat.card A = 2 := by
  classical
  let I := {A : Subgroup G // oneAmax (G := G) (V := V) T A ∧
    Nat.card A = 2}
  have hgen : T = ⨆ A : I, (A : Subgroup G) := by
    simpa [I] using
      lemma_one_five_order_two_candidates_generate_relative h S T hTS hT
  rcases isEmpty_or_nonempty I with hI | hI
  · let _ : IsEmpty I := hI
    have hsup : (⨆ A : I, (A : Subgroup G)) = ⊥ :=
      iSup_of_empty (fun A : I => (A : Subgroup G))
    exact (hTne (hgen.trans hsup)).elim
  · obtain ⟨A⟩ := hI
    exact ⟨A, A.property⟩

private theorem lemma_one_five_part_c_of_centralizer_ne
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS : IsElementaryAbelian 2 (S : Subgroup G))
    (hWneq : oddCore G ≠
      oddCore G ⊓ Subgroup.centralizer (S : Set G)) :
    oddCore G =
      ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) (S : Subgroup G) A ∧
          Nat.card (S : Subgroup G) = 2 * Nat.card A},
        oddCore G ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G) := by
  classical
  let : IsElementaryAbelian 2 (S : Subgroup G) := hS
  let : CommGroup (S : Subgroup G) := IsMulCommutative.instCommGroup
  let W : Subgroup G := oddCore G
  let K : Subgroup G :=
    ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) (S : Subgroup G) A ∧
        Nat.card (S : Subgroup G) = 2 * Nat.card A},
      W ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G)
  have hgen : W =
      ⨆ (A : Subgroup (S : Subgroup G)) (_ : Nat.card (S : Subgroup G) =
        2 * Nat.card A),
        W ⊓ Subgroup.centralizer
          ((A.map (S : Subgroup G).subtype : Subgroup G) : Set G) := by
    simpa [W] using (lemma_one_one h S).part_c hS
  have hgood : ∃ A : Subgroup (S : Subgroup G),
      Nat.card (S : Subgroup G) = 2 * Nat.card A ∧
        W ⊓ Subgroup.centralizer
            ((A.map (S : Subgroup G).subtype : Subgroup G) : Set G) ≠
          W ⊓ Subgroup.centralizer (S : Set G) := by
    by_contra hn
    push Not at hn
    apply hWneq
    apply le_antisymm
    · change W ≤ W ⊓ Subgroup.centralizer (S : Set G)
      conv_lhs => rw [hgen]
      refine iSup₂_le ?_
      intro A hAcard
      exact (hn A hAcard).le
    · exact inf_le_left
  obtain ⟨B, hBcard, hBneq⟩ := hgood
  have hBmap_le : B.map (S : Subgroup G).subtype ≤ (S : Subgroup G) :=
    Subgroup.map_subtype_le B
  have hBcard_map : Nat.card (S : Subgroup G) =
      2 * Nat.card (B.map (S : Subgroup G).subtype) := by
    simpa only [Subgroup.card_subtype] using hBcard
  have hBcandidate : oneAmax (G := G) (V := V) (S : Subgroup G)
      (B.map (S : Subgroup G).subtype) := by
    rcases lemma_one_five_oneAmax_or_centralizer_eq h hS hBmap_le hBcard_map with
      hA | hEq
    · exact hA
    · exact (hBneq hEq).elim
  have hWSc_le_B : W ⊓ Subgroup.centralizer (S : Set G) ≤
      W ⊓ Subgroup.centralizer
        ((B.map (S : Subgroup G).subtype : Subgroup G) : Set G) := by
    refine le_inf inf_le_left ?_
    intro x hx
    exact (Subgroup.centralizer_le (show
      ((B.map (S : Subgroup G).subtype : Subgroup G) : Set G) ⊆ (S : Set G) from
        fun x hx => hBmap_le hx)) hx.2
  have hWSc_le_K : W ⊓ Subgroup.centralizer (S : Set G) ≤ K := by
    exact hWSc_le_B.trans (le_iSup (fun A :
      {A : Subgroup G // oneAmax (G := G) (V := V) (S : Subgroup G) A ∧
        Nat.card (S : Subgroup G) = 2 * Nat.card A} =>
      W ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G))
      ⟨B.map (S : Subgroup G).subtype, hBcandidate, hBcard_map⟩)
  apply le_antisymm
  · change W ≤ ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) (S : Subgroup G) A ∧
        Nat.card (S : Subgroup G) = 2 * Nat.card A},
      W ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G)
    conv_lhs => rw [hgen]
    refine iSup₂_le ?_
    intro A hAcard
    let AG : Subgroup G := A.map (S : Subgroup G).subtype
    have hAGle : AG ≤ (S : Subgroup G) := by
      dsimp [AG]
      exact Subgroup.map_subtype_le A
    have hAGcard : Nat.card (S : Subgroup G) = 2 * Nat.card AG := by
      dsimp [AG]
      simpa only [Subgroup.card_subtype] using hAcard
    rcases lemma_one_five_oneAmax_or_centralizer_eq h hS hAGle hAGcard with hA | hEq
    · exact le_iSup (fun A :
        {A : Subgroup G // oneAmax (G := G) (V := V) (S : Subgroup G) A ∧
          Nat.card (S : Subgroup G) = 2 * Nat.card A} =>
          W ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G))
        ⟨AG, hA, hAGcard⟩
    · rw [hEq]
      exact hWSc_le_K
  · exact iSup_le fun A => inf_le_left

/- The omitted subgroup-generation bridge following (1.5)(c).  The rank-one
   case is handled separately in the main theorem; for rank at least two,
   the centralizer equation forces at least two distinct candidate
   hyperplanes, and hence their span is all of `S`. -/
private theorem lemma_one_five_index_two_candidates_generate
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (hS : IsElementaryAbelian 2 (S : Subgroup G))
    (hcard4 : 4 ≤ Nat.card (S : Subgroup G)) :
    (S : Subgroup G) =
      ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) (S : Subgroup G) A ∧
        Nat.card (S : Subgroup G) = 2 * Nat.card A},
        (A : Subgroup G) := by
  classical
  let : IsElementaryAbelian 2 (S : Subgroup G) := hS
  let : CommGroup (S : Subgroup G) := IsMulCommutative.instCommGroup
  let W : Subgroup G := oddCore G
  let J : Subgroup G :=
    ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) (S : Subgroup G) A ∧
      Nat.card (S : Subgroup G) = 2 * Nat.card A},
      (A : Subgroup G)
  have hWneq : W ≠ W ⊓ Subgroup.centralizer (S : Set G) := by
    intro hEq
    apply lemma_one_five_centralizer_sylow_ne h S hS
    rw [show oddCore G = W from rfl, hEq]
    exact inf_le_right
  have hpartc : W =
      ⨆ A : {A : Subgroup G // oneAmax (G := G) (V := V) (S : Subgroup G) A ∧
        Nat.card (S : Subgroup G) = 2 * Nat.card A},
      W ⊓ Subgroup.centralizer ((A : Subgroup G) : Set G) := by
    simpa [W] using lemma_one_five_part_c_of_centralizer_ne h S hS hWneq
  obtain ⟨B, hBgood, hBcard⟩ :=
    lemma_one_five_exists_oneAmax_index_two h S hS
  have hBcard2 : 2 ≤ Nat.card B := by omega
  have hBne : B ≠ ⊥ := by
    intro hbot
    simp [hbot] at hBcard2
  by_contra hJ
  push Not at hJ
  have hJle : J ≤ (S : Subgroup G) := by
    dsimp [J]
    refine iSup_le ?_
    intro A
    exact A.property.1.1
  have hBleJ : B ≤ J := by
    exact le_iSup (fun A : {A : Subgroup G //
      oneAmax (G := G) (V := V) (S : Subgroup G) A ∧
      Nat.card (S : Subgroup G) = 2 * Nat.card A} => (A : Subgroup G))
      ⟨B, hBgood, hBcard⟩
  have hJcard_lt : Nat.card J < Nat.card (S : Subgroup G) := by
    have hJcardS : Nat.card J ≤ Nat.card (S : Subgroup G) :=
      Nat.card_le_card_of_injective
        (fun x => (⟨x.1, hJle x.2⟩ : (S : Subgroup G)))
        (by
          intro x y hxy
          apply Subtype.ext
          simpa using congrArg Subtype.val hxy)
    have hJneq : J ≠ (S : Subgroup G) := by
      intro hEq
      exact hJ hEq.symm
    apply Nat.lt_of_le_of_ne hJcardS
    intro hcard
    apply hJneq
    exact Subgroup.eq_of_le_of_card_ge hJle hcard.symm.le
  have hJeqB : J = B := by
    rcases lemma_one_five_index_two_intermediate hBgood.1 hBleJ hJle hBcard with
      hJB | hJS
    · exact hJB
    · exact (hJ (by simpa [J] using hJS.symm)).elim
  have hAeqB (A : {A : Subgroup G //
      oneAmax (G := G) (V := V) (S : Subgroup G) A ∧
      Nat.card (S : Subgroup G) = 2 * Nat.card A}) :
      (A : Subgroup G) = B := by
    apply Subgroup.eq_of_le_of_card_ge
    · have hAJ : (A : Subgroup G) ≤ J := le_iSup (fun C : {C : Subgroup G //
          oneAmax (G := G) (V := V) (S : Subgroup G) C ∧
          Nat.card (S : Subgroup G) = 2 * Nat.card C} => (C : Subgroup G)) A
      simpa [hJeqB] using hAJ
    · omega
  have hWleB : W ≤ W ⊓ Subgroup.centralizer (B : Set G) := by
    conv_lhs => rw [hpartc]
    refine iSup_le ?_
    intro A
    rw [hAeqB A]
  have hBcent : B ≤ Subgroup.centralizer (W : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hWleB hw).2 b hb).symm
  have hBbot : B ≤ ⊥ := by
    intro b hb
    have hSb : b ∈ (S : Subgroup G) := hBgood.1 hb
    have hWb : b ∈ Subgroup.centralizer (W : Set G) := hBcent hb
    have hSW : b ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) := ⟨hSb, hWb⟩
    rw [show (S : Subgroup G) ⊓ Subgroup.centralizer (W : Set G) = ⊥ by
      simpa [W] using lemma_one_five_sylow_oddCore_centralizer_bot h S] at hSW
    exact hSW
  exact hBne (le_bot_iff.mp hBbot)

/-- **Stellmacher (1.5).**  The fixed-point quotient formula and, for
elementary abelian `S`, the four generation and lower-bound assertions. -/
public theorem lemma_one_five
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (h : Hypotheses G V) (S : Sylow 2 G)
    (U : Subgroup G) (hU : U ≤ (S : Subgroup G)) :
    LemmaOneFiveConclusion (G := G) (V := V) (S : Subgroup G) U := by
  refine
    { part_a := lemma_one_five_part_a (S : Subgroup G) U hU
      part_b := by
        intro hS
        by_cases hSbot : (S : Subgroup G) = ⊥
        · rw [hSbot]
          apply le_antisymm
          · exact bot_le
          · refine iSup_le ?_
            intro A
            simpa using A.property.1.1
        · by_cases hcard : Nat.card (S : Subgroup G) = 2
          · exact lemma_one_five_part_b_of_card_two (S : Subgroup G) hcard
          · exact lemma_one_five_order_two_candidates_generate_relative
              h S (S : Subgroup G) le_rfl hS
      part_c := by
        intro hS
        by_cases hC : oddCore G ≠
            oddCore G ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G)
        · exact lemma_one_five_part_c_of_centralizer_ne h S hS hC
        · exfalso
          apply lemma_one_five_centralizer_sylow_ne h S hS
          have hWeq : oddCore G =
              oddCore G ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
            not_ne_iff.mp hC
          rw [hWeq]
          exact inf_le_right
      part_d := by
        intro hS hS4
        by_cases hcard4 : Nat.card (S : Subgroup G) = 4
        · have hC : oddCore G ≠
              oddCore G ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
            intro hEq
            apply lemma_one_five_centralizer_sylow_ne h S hS
            exact hEq ▸ inf_le_right
          have hpartc := lemma_one_five_part_c_of_centralizer_ne h S hS hC
          apply hpartc.trans
          apply le_antisymm
          · refine iSup_le ?_
            intro A
            have hAcard : Nat.card (A : Subgroup G) = 2 := by
              omega
            exact le_iSup (fun B :
                {B : Subgroup G // oneAmax (G := G) (V := V)
                  (S : Subgroup G) B ∧ Nat.card B = 2} =>
                oddCore G ⊓ Subgroup.centralizer ((B : Subgroup G) : Set G))
              ⟨A, A.property.1, hAcard⟩
          · refine iSup_le ?_
            intro A
            have hAcard : Nat.card (S : Subgroup G) =
                2 * Nat.card (A : Subgroup G) := by
              omega
            exact le_iSup (fun B :
                {B : Subgroup G // oneAmax (G := G) (V := V)
                  (S : Subgroup G) B ∧
                  Nat.card (S : Subgroup G) = 2 * Nat.card B} =>
                oddCore G ⊓ Subgroup.centralizer ((B : Subgroup G) : Set G))
              ⟨A, A.property.1, hAcard⟩
        · have hC : oddCore G ≠
              oddCore G ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
            intro hEq
            apply lemma_one_five_centralizer_sylow_ne h S hS
            exact hEq ▸ inf_le_right
          have hpartc := lemma_one_five_part_c_of_centralizer_ne h S hS hC
          apply hpartc.trans
          apply le_antisymm
          · refine iSup_le ?_
            intro A
            have hAelem : IsElementaryAbelian 2 (A : Subgroup G) :=
              lemma_one_five_isElementaryAbelian_of_le hS A.property.1.1
            have hAcard2 : 2 ≤ Nat.card (A : Subgroup G) := by
              have hApos : 0 < Nat.card (A : Subgroup G) := Nat.card_pos
              omega
            have hAne : (A : Subgroup G) ≠ ⊥ := by
              intro hAbot
              simp [hAbot] at hAcard2
            obtain ⟨B, hBmax, hBcard⟩ :=
              lemma_one_five_exists_oneAmax_card_two_relative h S
                (A : Subgroup G) A.property.1.1 hAelem hAne
            have hBmaxS : oneAmax (G := G) (V := V)
                (S : Subgroup G) B :=
              lemma_one_five_oneAmax_transfer hS A.property.1 hBmax
            have hcent : Subgroup.centralizer ((A : Subgroup G) : Set G) ≤
                Subgroup.centralizer (B : Set G) :=
              Subgroup.centralizer_le hBmax.1
            have hterm : oddCore G ⊓
                Subgroup.centralizer ((A : Subgroup G) : Set G) ≤
                oddCore G ⊓ Subgroup.centralizer (B : Set G) :=
              inf_le_inf le_rfl hcent
            exact hterm.trans (le_iSup (fun C :
              {C : Subgroup G // oneAmax (G := G) (V := V)
                (S : Subgroup G) C ∧ Nat.card C = 2} =>
                  oddCore G ⊓ Subgroup.centralizer ((C : Subgroup G) : Set G))
              ⟨B, hBmaxS, hBcard⟩)
          · exact iSup_le fun A => inf_le_left.trans hpartc.le
      part_e := by
        intro hS
        by_cases hcard : Nat.card (S : Subgroup G) = 1
        · have hSbot : (S : Subgroup G) = ⊥ :=
            (Subgroup.eq_bot_iff_card (S : Subgroup G)).2 hcard
          rw [hSbot]
          unfold m
          simp
        · by_cases hcard : Nat.card (S : Subgroup G) = 2
          · exact lemma_one_five_m_ge_one_of_card_two h (S : Subgroup G) hcard
          · by_cases hcard4 : Nat.card (S : Subgroup G) = 4
            · obtain ⟨A, hA, hAcard⟩ :=
                lemma_one_five_exists_oneAmax_index_two h S hS
              have hAcard2 : Nat.card A = 2 := by
                omega
              have hmA : m (G := G) (V := V) A ≥ 1 :=
                lemma_one_five_m_ge_one_of_card_two h A hAcard2
              have hmAle : m (G := G) (V := V) A ≤
                  m (G := G) (V := V) (S : Subgroup G) := hA.2.1
              linarith
            · have hSne : (S : Subgroup G) ≠ ⊥ :=
                Sylow.ne_bot_of_dvd_card S h.G_even.two_dvd
              obtain ⟨A, hAmax, hAcard⟩ :=
                lemma_one_five_exists_oneAmax_card_two_relative h S
                  (S : Subgroup G) le_rfl hS hSne
              have hmA : m (G := G) (V := V) A ≥ 1 :=
                lemma_one_five_m_ge_one_of_card_two h A hAcard
              have hmAle : m (G := G) (V := V) A ≤
                  m (G := G) (V := V) (S : Subgroup G) := hAmax.2.1
              linarith }

end Stellmacher.SectionOne
