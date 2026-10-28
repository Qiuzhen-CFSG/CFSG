module
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.Restriction
public import Theory.GroupTheory.CComponent.CubicCenterRankNormal
public import Theory.GroupTheory.CComponent.OddRankNormal
public import Theory.SpecificGroups.Classical.PairedOddRank
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.AtlasPort.LinearGroups.G2.OrderChecks
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Intrinsic group reductions for nonbinary linear-three MS-pairs

The join-based input implies the literal product in C.1.31. An odd prime
in the split torus gives rank two in the full SL₃ quotient. The SQTK rank
bound then forces the relative C-component to be normal, including when
its scalar center has order three. No ambient normality is used.

The component quotient embeds in the join's two-core quotient. Its order
is at least 60480, so that quotient cannot be G₂(2), of order 12096.
Consequently the original MS2 disjunction supplies a proper odd-index
witness. Restricting this witness and MS3 to the literal join preserves
the original core quotient map.

These are initial reductions, not the module alternatives of C.1.34.
Source: Aschbacher--Smith C.1.31--34, printed pp.135--137, and the
MS93 Main Theorem hypotheses, printed pp.828--829. The matrix order and
simplicity results use the attributed ATLAS port; see LICENSES/ATLAS.txt.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open RankTwo.NonbinarySymplectic
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F)

/-- Restriction to the literal join retains the supplied SL₃ marking. -/
@[expose] noncomputable def joinQuotientEquiv
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    ((K.subgroupOf (K ⊔ R)) ⧸ pCore 2 (K.subgroupOf (K ⊔ R))) ≃* SL(3,F) :=
  (subgroupOfCoreQuotientEquiv le_sup_left).trans e

omit [Finite G] [Finite F] in
/-- Compatibility with both original quotient maps on representatives. -/
theorem joinQuotientEquiv_mk (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (k : K.subgroupOf (K ⊔ R)) :
    joinQuotientEquiv (R := R) e (QuotientGroup.mk' _ k) =
      e (QuotientGroup.mk' _ ⟨k,k.property⟩) := rfl

include h

omit [Finite G] in
/-- The full core quotient is quasisimple; its scalar center is retained. -/
theorem quotient_quasisimple : IsQuasisimple (K ⧸ pCore 2 K) := by
  obtain ⟨e⟩ := h.model
  let : IsQuasisimple SL(3,F) := {
    toIsPerfect := Atlas.sl_perfect 3 (by decide)
    simple := Atlas.psl_simple_high_rank 3 (by decide) }
  exact IsQuasisimple.of_mulEquiv e.symm

/-- Odd rank forces normality relative to the join, including at field four. -/
theorem component_normal (hn : 1 < n) : (K.subgroupOf (K ⊔ R)).Normal := by
  obtain ⟨e⟩ := h.model
  let f := joinQuotientEquiv (R := R) e
  let : IsQuasisimple SL(3,F) := {
    toIsPerfect := Atlas.sl_perfect 3 (by decide)
    simple := Atlas.psl_simple_high_rank 3 (by decide) }
  let : IsQuasisimple ((K.subgroupOf (K ⊔ R)) ⧸
      pCore 2 (K.subgroupOf (K ⊔ R))) := IsQuasisimple.of_mulEquiv f.symm
  have hq : 4 ≤ Nat.card F := by
    rw [h.field_card]
    exact Nat.pow_le_pow_right (n := 2) (by decide) hn
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd (by omega : Nat.card F - 1 ≠ 1)
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := by
    apply Odd.of_dvd_nat _ hd
    rw [h.field_card]
    have he := (even_two : Even (2 : ℕ)).pow_of_ne_zero (by omega : n ≠ 0)
    have he' := Nat.even_iff.mp he
    have hpos : 0 < 2^n := pow_pos (by decide) _
    exact Nat.odd_iff.mpr (by omega)
  have hr : 2 ≤ primeRank p ((K.subgroupOf (K ⊔ R)) ⧸
      pCore 2 (K.subgroupOf (K ⊔ R))) := by
    rw [primeRank_congr p f]
    exact Theory.SpecificGroups.Classical.PairedOddRank.linear_special_of_dvd hp hd
  have hz : Nat.card (center ((K.subgroupOf (K ⊔ R)) ⧸
      pCore 2 (K.subgroupOf (K ⊔ R)))) ∣ 3 := by
    rw [Nat.card_congr (centerCongr f).toEquiv]
    exact Matrix.SL3.card_center_dvd_three F
  by_cases he : p = 3
  · subst p
    exact h.component.2.normal_of_cubic_core_center_threeRank
      (Nat.le_of_dvd (by decide) hz) hr (h.sqtk.stronglyQuasithin 3 hp ho)
  · have hc : Nat.Coprime p (Nat.card (center ((K.subgroupOf (K ⊔ R)) ⧸
        pCore 2 (K.subgroupOf (K ⊔ R))))) :=
      (hp.coprime_iff_not_dvd.mpr (fun hd =>
        he ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd))).of_dvd_right hz
    exact h.component.2.normal_of_coprime_core_center_primeRank ho hc hr
      (h.sqtk.stronglyQuasithin p hp ho)

/-- The original radical normalizes the original component. -/
theorem radical_normalizes (hn : 1 < n) : R ≤ normalizer (K : Set G) :=
  le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer le_sup_left).mp
    (component_normal h hn))

/-- The generated join is the actual product required in MS1. -/
theorem product (hn : 1 < n) :
    ∀ g ∈ K ⊔ R, ∃ k ∈ K, ∃ r ∈ R, k*r=g := by
  intro g hg
  exact Set.mem_mul.mp ((coe_mul_of_right_le_normalizer_left K R
    (radical_normalizes h hn)).symm ▸ hg)

omit [Finite G] in
private theorem card_sl_ge (hn : 1 < n) : 60480 ≤ Nat.card SL(3,F) := by
  have hq : 4 ≤ Nat.card F := by
    rw [h.field_card]
    exact Nat.pow_le_pow_right (n := 2) (by decide) hn
  have h2 : 16 ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hq 2
  have h3 : 64 ≤ Nat.card F ^ 3 := Nat.pow_le_pow_left hq 3
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
  have hb := Nat.mul_le_mul (Nat.mul_le_mul h3 (Nat.sub_le_sub_right h3 1))
    (Nat.sub_le_sub_right h2 1)
  exact hb

/-- The nonbinary component is too large for the exceptional MS2(b) quotient. -/
theorem not_exceptional (hn : 1 < n) : ¬ MSExceptional K R := by
  rintro ⟨_,f,_⟩
  obtain ⟨e⟩ := h.model
  let J := K ⊔ R
  let L := K.subgroupOf J
  let B := L.map (QuotientGroup.mk' (pCore 2 J))
  let q : (L ⧸ pCore 2 L) ≃* B := cComponentTwoCoreQuotientEquiv h.component.2
  have hc : Nat.card SL(3,F) = Nat.card B :=
    Nat.card_congr ((joinQuotientEquiv (R := R) e).symm.trans q).toEquiv
  have hb := B.card_le_card_group
  rw [←hc,Nat.card_congr f.toEquiv,Atlas.G2.OrderChecks.binary_order] at hb
  have hh := card_sl_ge h hn
  omega

/-- MS2(a) follows from the original disjunction. -/
theorem oddIndex (hn : 1 < n) : MSOddIndex K R :=
  h.radical.resolve_right (not_exceptional h hn)

/-- The proper odd-index witness, inside the actual join. -/
theorem join_oddIndex (hn : 1 < n) : MSOddIndexRadical (R.subgroupOf (K ⊔ R)) :=
  msOddIndexRadical_subgroupOf (oddIndex h hn)

omit [Finite G] in
/-- MS3 after restriction, with characteristicity inside R and relative normality. -/
theorem join_characteristic : MSCharacteristicCondition (R.subgroupOf (K ⊔ R)) :=
  msCharacteristic_subgroupOf le_sup_right h.characteristic

/-- The literal product on the join carrier used by the MS93 reductions. -/
theorem join_product (hn : 1 < n) : ∀ g : (K ⊔ R : Subgroup G),
    ∃ k ∈ K.subgroupOf (K ⊔ R), ∃ r ∈ R.subgroupOf (K ⊔ R), k*r=g := by
  intro g
  obtain ⟨k,hk,r,hr,he⟩ := product h hn g g.property
  exact ⟨⟨k,mem_sup_left hk⟩,hk,⟨r,mem_sup_right hr⟩,hr,Subtype.ext he⟩

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource
