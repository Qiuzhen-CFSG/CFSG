module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Excluding a transposition row with an inherited A₆ section

In C.2.7(3)(b), the actual intersection image centralizes the marked
transposition. Its solvable star kernel preserves the simple A₆ section,
so its order is divisible by nine. The transposition centralizers in
degrees five through seven have no such divisor. In degree eight, the
original Sylow subgroup normalizes the radical and hence centralizes its
order-two star image. Its intersection with K maps onto a Sylow of A₈,
whose order cannot divide the transposition centralizer order 1440.

All maps are the original maps into KR/C_KR(Ω₁Z(O₂(KR))). Normality of K
in G is not required: the actual Sylow only needs to normalize K and R.
Source: Aschbacher--Smith C.2.7(3)(b), pp.145--147, and the comparison in
3.3.22, p.597. The fixed-coset application is in
SourceAlternatingSeven/LocalAnalysisSylowResidualsComponentsExclusions.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.C27Source
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

private theorem core_quotient_card_dvd {B D : Type*} [Group B] [Finite B]
    [Group D] [Finite D] [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (f : B →* D) [Group.IsSolvable f.ker] : Nat.card (B ⧸ pCore 2 B) ∣ Nat.card D := by
  have hk : f.ker ≤ pCore 2 B := by
    rw [← PerfectCoreTwoExtension.radical_eq_core]
    exact le_solvableRadical _ inferInstance inferInstance
  let q := QuotientGroup.mk' (pCore 2 B)
  let q' : (B ⧸ f.ker) →* (B ⧸ pCore 2 B) := QuotientGroup.lift f.ker q (by
    simpa only [q, QuotientGroup.ker_mk'] using hk)
  have hq' : Function.Surjective q' := by
    intro x
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 B) x
    exact ⟨QuotientGroup.mk' f.ker b,rfl⟩
  have hd := card_dvd_of_surjective q' hq'
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hd
  exact hd.trans f.range.card_subgroup_dvd_card

variable {G : Type*} [Group G] [Finite G] {H K R M B : Subgroup G}

/-- The actual intersection star image retains the factor nine from an A6 section. -/
theorem starM_nine_dvd_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) :
    9 ∣ Nat.card (starM K R M) := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := e.isSimpleGroup
  let q := QuotientGroup.mk' (starKernel K R)
  let f : B →* starM K R M :=
    (q.comp (inclusion (hB.trans inf_le_right |>.trans le_sup_left))).codRestrict _
      (fun b => mem_map_of_mem q (show (b : G) ∈ M ⊓ K from hB b.property))
  let j : f.ker →* (toStarImage K R).ker :=
    { toFun := fun b => ⟨inclusion (hB.trans inf_le_right) b.val, by
        apply Subtype.ext
        exact congrArg (fun a : starM K R M => (a : StarQuotient K R))
          (show f b.val = 1 from b.property)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hh
    exact Subtype.ext (Subtype.ext (congrArg (fun a => (a.val : G)) hh))
  let : Group.IsSolvable (toStarImage K R).ker := toStarImage_ker_solvable_from_source h
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hj
  have hd := core_quotient_card_dvd f
  have hc : Nat.card (B ⧸ pCore 2 B) = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [hc] at hd
  exact (by decide : 9 ∣ 360).trans hd

private theorem swap_centralizer_card {n : ℕ} (s : Equiv.Perm (Fin n)) (hs : s.IsSwap) :
    Nat.card (centralizer ({s} : Set (Equiv.Perm (Fin n)))) = 2 * (n - 2).factorial := by
  rw [Equiv.Perm.nat_card_centralizer, Equiv.Perm.isSwap_iff_cycleType.mp hs]
  simp [mul_comm]

private theorem no_sylow_eight_centralizes_swap
    (P : Sylow 2 (alternatingGroup (Fin 8))) (s : Equiv.Perm (Fin 8)) (hs : s.IsSwap)
    (hc : ∀ x ∈ (P : Subgroup (alternatingGroup (Fin 8))),
      Commute (x : Equiv.Perm (Fin 8)) s) : False := by
  have h64 : 64 ∣ Nat.card P := P.pow_dvd_card_of_pow_dvd_card (n := 6) (by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial])
  let f : P →* centralizer ({s} : Set (Equiv.Perm (Fin 8))) :=
    ((alternatingGroup (Fin 8)).subtype.comp (P : Subgroup _).subtype).codRestrict _
      (fun x => mem_centralizer_singleton_iff.mpr (hc x x.property).eq)
  have hf : Function.Injective f := by
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : centralizer ({s} : Set (Equiv.Perm (Fin 8))) => z.val) hh
  have hd := h64.trans (card_dvd_of_injective f hf)
  rw [swap_centralizer_card s hs] at hd
  norm_num [Nat.factorial] at hd

omit [Finite G] in
private theorem transposition_fixed
    {n : ℕ} (e : AlternatingComponentModel K R n)
    {r : StarQuotient K R} {s : Equiv.Perm (Fin n)}
    (ha : ∀ k k' : starImage K R K,
      (k' : StarQuotient K R) = r * (k : StarQuotient K R) * r⁻¹ ↔
        (e.groupIso k' : Equiv.Perm (Fin n)) =
          s * (e.groupIso k : Equiv.Perm (Fin n)) * s⁻¹)
    {k : starImage K R K} (hk : Commute (k : StarQuotient K R) r) :
    Commute (e.groupIso k : Equiv.Perm (Fin n)) s := by
  have he := (ha k k).mp (by rw [← hk.eq, mul_inv_cancel_right])
  exact Commute.symm (mul_inv_eq_iff_eq_mul.mp he.symm)

/-- A Sylow-normalized radical rules out the degree-eight transposition row. -/
theorem no_transposition_eight_of_sylow_normalizes
    (T : Sylow 2 G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (ha : TranspositionAction K R 8) : False := by
  obtain ⟨e,r,s,hr,hR,hs,ha⟩ := ha
  obtain ⟨U,hU⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow T K hTK
  let f := toStarImage K R
  let P : Sylow 2 (alternatingGroup (Fin 8)) :=
    (U.mapSurjective (toStarImage_surjective K R)).mapSurjective
      (f := e.groupIso.toMonoidHom) e.groupIso.surjective
  apply no_sylow_eight_centralizes_swap P s hs
  rintro x ⟨k,⟨u,hu,rfl⟩,rfl⟩
  apply transposition_fixed e ha
  have huT : (u : G) ∈ (T : Subgroup G) := by
    change u ∈ (U : Subgroup K) at hu
    rw [hU] at hu
    exact hu
  have hn : (f u : StarQuotient K R) ∈ normalizer (starImage K R R : Set _) := by
    apply (R.subgroupOf (K ⊔ R)).le_normalizer_map (QuotientGroup.mk' (starKernel K R))
    apply mem_map_of_mem
    rw [← subgroupOf_normalizer_eq (show R ≤ K ⊔ R from le_sup_right)]
    exact hTR huT
  rw [hR, ← zpowers_eq_closure, normalizer_zpowers_eq_centralizer_of_order_two r hr] at hn
  exact mem_centralizer_singleton_iff.mp hn

/-- Entire C.2.7(3)(b) exclusion, retaining the source Sylow and A6 section. -/
theorem no_transposition_alternative_of_six
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (T : Sylow 2 G) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hB : B ≤ M ⊓ K) [Group.IsPerfect B]
    (e6 : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))
    {n : ℕ} (hn : 5 ≤ n) (hn' : n ≤ 8) (ha : TranspositionAction K R n)
    (hM : starM K R M = starImage K R K ⊓
      centralizer (starImage K R R : Set (StarQuotient K R))) : False := by
  by_cases he : n = 8
  · subst n
    exact no_transposition_eight_of_sylow_normalizes T hTK hTR ha
  obtain ⟨e,r,s,hr,hR,hs,ha⟩ := ha
  have hMK : starM K R M ≤ starImage K R K := by rw [hM]; exact inf_le_left
  let f : starM K R M →* centralizer ({s} : Set (Equiv.Perm (Fin n))) :=
    ((alternatingGroup (Fin n)).subtype.comp
      (e.groupIso.toMonoidHom.comp (inclusion hMK))).codRestrict _ (by
        intro x
        apply mem_centralizer_singleton_iff.mpr
        apply transposition_fixed e ha
        have hx := x.property
        simp only [hM, mem_inf] at hx
        exact (mem_centralizer_iff.mp hx.2 r (hR ▸ subset_closure (Set.mem_singleton r))).symm)
  have hf : Function.Injective f := by
    intro x y hh
    have hh' : (e.groupIso (inclusion hMK x) : Equiv.Perm (Fin n)) =
        (e.groupIso (inclusion hMK y) : Equiv.Perm (Fin n)) :=
      congrArg (fun z : centralizer ({s} : Set (Equiv.Perm (Fin n))) => z.val) hh
    exact inclusion_injective hMK (e.groupIso.injective (Subtype.ext hh'))
  have hd := (starM_nine_dvd_of_six h hB e6).trans (card_dvd_of_injective f hf)
  rw [swap_centralizer_card s hs] at hd
  have hsmall : n ≤ 7 := by omega
  interval_cases n <;> norm_num [Nat.factorial] at hd

end CFSG.Quasithin.ChapterC.C27Source
