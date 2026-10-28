module

public import BenderSuzuki.External.Huppert.XI.SubgroupSolvable
public import Theory.SpecificGroups.Suzuki.ElementaryNormalizer
public import Theory.ElementaryAbelian.CyclicKernel

/-!
# Normal elementary Sylow subgroups and odd complements in Suzuki groups

An elementary Sylow two-subgroup of order greater than two in a solvable
Suzuki subgroup is normal. Standard solvable containment reduces this to the
Borel: a two-subgroup in the split normalizer has order at most two, and an
elementary two-subgroup in a nonsplit normalizer injects into its cyclic
quotient and therefore also has order at most two.

A nontrivial normal two-subgroup can be conjugated into a root group. Its
normalizer is then contained in the Borel. Every odd subgroup injects into
the cyclic root quotient, of order q-1. Root-element centralizers are
two-groups, which gives the literal fixed-point-free commutation conclusion.
The embedding versions retain the actual homomorphism and relative normality.

Source: GLS4, Chapter 4, Lemma 3.8, and its applications in Chapter 2,
Lemmas 14.7–14.8; Huppert--Blackburn III, XI.3.3 and XI.3.12(e).
-/

open Subgroup
open scoped Pointwise
namespace BenderSuzuki.MatrixGroups

private theorem quotient_comp_injective_of_coprime
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Injective f) (N : Subgroup B) [N.Normal]
    (hcop : Nat.Coprime (Nat.card A) (Nat.card N)) :
    Function.Injective ((QuotientGroup.mk' N).comp f) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hxN : f x ∈ N := (QuotientGroup.eq_one_iff _).mp hx
  have hd : orderOf x ∣ Nat.card N := by
    rw [← orderOf_injective f hf x]
    exact N.orderOf_dvd_natCard hxN
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_natCard x) hd)

private theorem q_minus_one_odd (m : ℕ) : Odd (2 ^ (2 * m + 1) - 1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow
    (Even.pow_of_ne_zero even_two (by omega)) odd_one

/-- The quotient of the concrete Borel by its root subgroup is cyclic of
order q-1. -/
public theorem suzukiBorel_root_quotient_structure (m : ℕ) (hm : 0 < m) :
    let _ := suzukiRootSubgroup_normal_in_borel m
    IsCyclic (SuzukiBorelSubgroup m ⧸
      (SuzukiRootSubgroup m).subgroupOf (SuzukiBorelSubgroup m)) ∧
    Nat.card (SuzukiBorelSubgroup m ⧸
      (SuzukiRootSubgroup m).subgroupOf (SuzukiBorelSubgroup m)) =
        2 ^ (2 * m + 1) - 1 := by
  let B := SuzukiBorelSubgroup m
  let R := (SuzukiRootSubgroup m).subgroupOf B
  let : R.Normal := suzukiRootSubgroup_normal_in_borel m
  have hRB : SuzukiRootSubgroup m ≤ B := by
    change SuzukiRootSubgroup m ≤ SuzukiBorelSubgroup m
    rw [suzukiBorelSubgroup_eq_sup]; exact le_sup_left
  have hTB : SuzukiSplitTorus m ≤ B := by
    change SuzukiSplitTorus m ≤ SuzukiBorelSubgroup m
    rw [suzukiBorelSubgroup_eq_sup]; exact le_sup_right
  let t := (QuotientGroup.mk' R).comp (Subgroup.inclusion hTB)
  have ht : Function.Surjective t := by
    intro q
    induction q using QuotientGroup.induction_on with | H b =>
      have hb : (b : SuzukiMatrixGroup m) ∈
          (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) *
            (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m)) := by
        rw [← coe_mul_of_right_le_normalizer_left _ _
          (suzukiSplitTorus_le_normalizer_root m), ← suzukiBorelSubgroup_eq_sup]
        exact b.property
      obtain ⟨r, hr, s, hs, hrs⟩ := hb
      refine ⟨⟨s, hs⟩, ?_⟩
      have he : b = (⟨r, hRB hr⟩ : B) * ⟨s, hTB hs⟩ := Subtype.ext hrs.symm
      change QuotientGroup.mk' R ⟨s, hTB hs⟩ = QuotientGroup.mk' R b
      have hrq : QuotientGroup.mk' R (⟨r, hRB hr⟩ : B) = 1 :=
        (QuotientGroup.eq_one_iff (N := R) (⟨r, hRB hr⟩ : B)).mpr hr
      rw [he, map_mul, hrq, one_mul]
  let : IsCyclic (SuzukiSplitTorus m) := suzukiSplitTorus_isCyclic m hm
  refine ⟨isCyclic_of_surjective t ht, ?_⟩
  have hc := R.card_mul_index
  have hr : Nat.card R = (2 ^ (2 * m + 1)) ^ 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hRB).toEquiv).trans
      (suzukiRootSubgroup_card m hm)
  rw [hr, suzukiBorelSubgroup_card m hm] at hc
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hc

private theorem normal_sylow_of_borel_embedding
    {A : Type*} [Group A] [Finite A] {m : ℕ} (hm : 0 < m)
    (f : A →* SuzukiMatrixGroup m) (hf : Function.Injective f)
    (hB : ∀ a, f a ∈ SuzukiBorelSubgroup m) (V : Sylow 2 A) :
    (V : Subgroup A).Normal := by
  let fb := f.codRestrict (SuzukiBorelSubgroup m) hB
  have hfb : Function.Injective fb := fun a b h => hf (congrArg Subtype.val h)
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  have hPB : (P : Subgroup (SuzukiMatrixGroup m)) ≤ SuzukiBorelSubgroup m := by
    rw [hP, suzukiBorelSubgroup_eq_sup]; exact le_sup_left
  let PB := P.subtype hPB
  have hn : (PB : Subgroup (SuzukiBorelSubgroup m)).Normal := by
    change ((P : Subgroup (SuzukiMatrixGroup m)).subgroupOf _).Normal
    rw [hP]
    exact suzukiRootSubgroup_normal_in_borel m
  let : Unique (Sylow 2 (SuzukiBorelSubgroup m)) := Sylow.unique_of_normal PB hn
  obtain ⟨Q, hQ⟩ := V.exists_comap_eq_of_injective hfb
  have he : Q = PB := Subsingleton.elim _ _
  rw [← hQ, he]
  exact hn.comap fb

private theorem elementary_card_le_two_in_nonsplit
    {A : Type*} [Group A] [Finite A] [IsElementaryAbelian 2 A]
    {m : ℕ} (hm : 0 < m) {T : Subgroup (SuzukiMatrixGroup m)}
    (hT : IsSuzukiMaximalNonsplit m T)
    (f : A →* normalizer (T : Set (SuzukiMatrixGroup m)))
    (hf : Function.Injective f) : Nat.card A ≤ 2 := by
  let N := normalizer (T : Set (SuzukiMatrixGroup m))
  let T' := T.subgroupOf N
  have hcT : Odd (Nat.card T') := by
    rw [Nat.card_congr (subgroupOfEquivOfLe T.le_normalizer).toEquiv]
    apply Odd.of_dvd_nat _ hT.card_dvd
    exact Even.add_odd ((even_two.pow_of_ne_zero (by omega : 2 * m + 1 ≠ 0)).pow_of_ne_zero (by decide : 2 ≠ 0)) odd_one
  obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hinj := quotient_comp_injective_of_coprime f hf T' (by
    rw [hk]; exact hcT.coprime_two_left.pow_left k)
  let : IsCyclic (N ⧸ T') := (hT.normalizer_quotient hm).1
  let : IsCyclic A := isCyclic_of_injective _ hinj
  apply Nat.le_of_dvd (by decide : 0 < 2)
  rw [← IsCyclic.exponent_eq_card]
  exact IsElementaryAbelian.exponent_dvd_p 2 A

/-- A solvable group embedded in the actual Suzuki group has a normal
elementary Sylow two-subgroup whenever that Sylow subgroup has order > 2. -/
public theorem suzuki_normal_elementary_sylow_of_embedding
    {A : Type*} [Group A] [Finite A] [Group.IsSolvable A]
    {m : ℕ} (hm : 0 < m) (f : A →* SuzukiMatrixGroup m)
    (hf : Function.Injective f) (V : Sylow 2 A) [IsElementaryAbelian 2 V]
    (hcard : 2 < Nat.card V) : (V : Subgroup A).Normal := by
  let : Group.IsSolvable f.range :=
    Group.isSolvable_of_surjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  obtain ⟨T⟩ := exists_suzukiNonsplitTorusPair m hm
  obtain ⟨c, hc⟩ := suzukiStandardContainment_of_isSolvable hm T f.range
  let F := (MulAut.conj c).toMonoidHom.comp f
  have hF : Function.Injective F := (MulAut.conj c).injective.comp hf
  have hmem (a : A) : F a ∈ f.range.map (MulAut.conj c).toMonoidHom :=
    ⟨f a, ⟨a, rfl⟩, rfl⟩
  rcases hc with hB | hT | hT | hT
  · exact normal_sylow_of_borel_embedding hm F hF (fun a => hB (hmem a)) V
  · exfalso
    let j := (F.comp (V : Subgroup A).subtype).codRestrict
      (normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m)))
      (fun v => hT (hmem v))
    have hj : Function.Injective j := fun a b h =>
      Subtype.ext (hF (congrArg Subtype.val h))
    have hd := Subgroup.card_dvd_of_injective j hj
    rw [suzukiSplitTorus_normalizer_card m hm] at hd
    obtain ⟨k, hk⟩ := V.isPGroup'.exists_card_eq
    have hcop : Nat.Coprime (Nat.card V) (2 ^ (2 * m + 1) - 1) := by
      rw [hk]; exact (q_minus_one_odd m).coprime_two_left.pow_left k
    exact (not_le_of_gt hcard) (Nat.le_of_dvd (by decide)
      (hcop.dvd_of_dvd_mul_right hd))
  · exact False.elim ((not_le_of_gt hcard)
      (elementary_card_le_two_in_nonsplit hm T.plus_maximal
        ((F.comp (V : Subgroup A).subtype).codRestrict _ (fun v => hT (hmem v)))
        (fun a b h => Subtype.ext (hF (congrArg Subtype.val h)))))
  · exact False.elim ((not_le_of_gt hcard)
      (elementary_card_le_two_in_nonsplit hm T.minus_maximal
        ((F.comp (V : Subgroup A).subtype).codRestrict _ (fun v => hT (hmem v)))
        (fun a b h => Subtype.ext (hF (congrArg Subtype.val h)))))

private theorem normal_two_subgroup_borel_embedding
    {A : Type*} [Group A] [Finite A] {m : ℕ} (hm : 0 < m)
    (f : A →* SuzukiMatrixGroup m) (hf : Function.Injective f)
    (V : Subgroup A) (hp : IsPGroup 2 V) (hn : V.Normal) (hne : V ≠ ⊥) :
    ∃ c : SuzukiMatrixGroup m,
      (∀ a, (MulAut.conj c) (f a) ∈ SuzukiBorelSubgroup m) ∧
      ∀ v ∈ V, (MulAut.conj c) (f v) ∈ SuzukiRootSubgroup m := by
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨Q, hQ⟩ := (hp.map f).exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) Q P
  let F := (MulAut.conj c).toMonoidHom.comp f
  have hF : Function.Injective F := (MulAut.conj c).injective.comp hf
  have hVR : V.map F ≤ SuzukiRootSubgroup m := by
    rw [← hP, ← hc]
    rintro x ⟨v, hv, rfl⟩
    exact ⟨f v, hQ (mem_map_of_mem f hv), rfl⟩
  have hVne : V.map F ≠ ⊥ := by
    intro h
    apply hne
    exact (Subgroup.map_eq_bot_iff_of_injective V hF).mp h
  have hFN : F.range ≤ normalizer (V.map F : Set (SuzukiMatrixGroup m)) := by
    rw [le_normalizer_iff]
    rintro a ⟨a, rfl⟩ v ⟨v, hv, rfl⟩
    exact ⟨a * v * a⁻¹, hn.conj_mem v hv a, by simp⟩
  refine ⟨c, fun a => ?_, fun v hv => hVR (mem_map_of_mem F hv)⟩
  exact suzuki_normalizer_le_borel_of_le_root m hm (V.map F) hVne hVR
    (hFN ⟨a, rfl⟩)

/-- A nontrivial normal two-subgroup in an embedded Suzuki subgroup forces
every odd subgroup to be cyclic of order dividing q-1, with no nonidentity
fixed points on that normal two-subgroup. No complement factorization is needed. -/
public theorem suzuki_odd_subgroup_of_normal_two_embedding
    {A : Type*} [Group A] [Finite A] {m : ℕ} (hm : 0 < m)
    (f : A →* SuzukiMatrixGroup m) (hf : Function.Injective f)
    (V : Subgroup A) (hp : IsPGroup 2 V) (hn : V.Normal) (hne : V ≠ ⊥)
    (Y : Subgroup A) (hodd : Odd (Nat.card Y)) :
    IsCyclic Y ∧ Nat.card Y ∣ 2 ^ (2 * m + 1) - 1 ∧
      ∀ y ∈ Y, y ≠ 1 → ∀ u ∈ V, Commute u y → u = 1 := by
  obtain ⟨c, hB, hR⟩ := normal_two_subgroup_borel_embedding hm f hf V hp hn hne
  let F := (MulAut.conj c).toMonoidHom.comp f
  have hF : Function.Injective F := (MulAut.conj c).injective.comp hf
  let B := SuzukiBorelSubgroup m
  let R := (SuzukiRootSubgroup m).subgroupOf B
  let : R.Normal := suzukiRootSubgroup_normal_in_borel m
  have hRB : SuzukiRootSubgroup m ≤ B := by
    change SuzukiRootSubgroup m ≤ SuzukiBorelSubgroup m
    rw [suzukiBorelSubgroup_eq_sup]; exact le_sup_left
  have hr : Nat.card R = (2 ^ (2 * m + 1)) ^ 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hRB).toEquiv).trans
      (suzukiRootSubgroup_card m hm)
  let FY : Y →* B := (F.comp Y.subtype).codRestrict B (fun y => hB y)
  have hFY : Function.Injective FY := fun a b h =>
    Subtype.ext (hF (congrArg Subtype.val h))
  let qY := (QuotientGroup.mk' R).comp FY
  have hqY : Function.Injective qY := quotient_comp_injective_of_coprime FY hFY R
    (by rw [hr]; exact (hodd.coprime_two_right.pow_right (2 * m + 1)).pow_right 2)
  have hquot := suzukiBorel_root_quotient_structure m hm
  let : IsCyclic (B ⧸ R) := hquot.1
  refine ⟨isCyclic_of_injective qY hqY, ?_, ?_⟩
  · rw [← hquot.2]
    exact Subgroup.card_dvd_of_injective qY hqY
  · intro y hy hy1 u hu hcomm
    by_contra hu1
    have hFu1 : F u ≠ 1 := fun h => hu1 (hF (h.trans (map_one F).symm))
    have hFyR : F y ∈ SuzukiRootSubgroup m :=
      suzukiRootSubgroup_centralizer_le m hm (hR u hu) hFu1
        (mem_centralizer_singleton_iff.mpr ((hcomm.map F).symm.eq))
    have hqy : qY ⟨y, hy⟩ = 1 :=
      (QuotientGroup.eq_one_iff (FY ⟨y, hy⟩)).mpr hFyR
    exact hy1 (congrArg Subtype.val (hqY (hqy.trans (map_one qY).symm)))

/-- Intrinsic subgroup form of the normal elementary Sylow consequence of
GLS4, Chapter 4, Lemma 3.8. -/
public theorem suzuki_elementary_sylow_normal {m : ℕ} (hm : 0 < m)
    (H : Subgroup (SuzukiMatrixGroup m)) [Group.IsSolvable H]
    (V : Sylow 2 H) [IsElementaryAbelian 2 V] (hcard : 2 < Nat.card V) :
    (V : Subgroup H).Normal :=
  suzuki_normal_elementary_sylow_of_embedding hm H.subtype H.subtype_injective V hcard

end BenderSuzuki.MatrixGroups
