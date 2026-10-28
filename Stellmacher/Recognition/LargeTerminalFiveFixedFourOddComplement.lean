module

public import Stellmacher.Recognition.LargeTerminalFiveFixedFourSylow
public import Theory.GroupTheory.NormalOddKleinFourCentralization

/-!
# The odd complement centralizes the actual fixed four-group

Write Q for the second core, R for the first residual, V = C_Q(A), and
W = C_Q(R′). For an involution y in V outside R, its centralizer in Q
is W. The normalizer condition in O₂(C_G(y))W, together with confinement
of N_G(W), forces O₂(C_G(y)) ≤ W. Since V centralizes W, characteristic
two gives V ≤ O₂(C_G(y)). Thus V lies in the two-core of the centralizer
of each of its involutions, including the distinguished central involution.
The normal-odd-subgroup coprime-action lemma now shows that every normal
odd complement in C_G(A) centralizes V.

Source: Thompson VI, printed p.630, the noncyclic four-fixed alternative.
No odd-local solvability or global five-normalizer confinement is used.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix Subgroup
open scoped Pointwise

universe u

private theorem core_le_of_normalizer_condition
    {G : Type u} [Group G] [Finite G]
    (H W U : Subgroup G) (hW : IsPGroup 2 W) (hU : IsPGroup 2 U)
    (hWH : W ≤ H) (hUH : U ≤ H) (hHU : H ≤ normalizer (U : Set G))
    (hNW : normalizer (W : Set G) ⊓ H ≤ W) : U ≤ W := by
  let T := U ⊔ W
  have hWT : W ≤ T := le_sup_right
  have hT : IsPGroup 2 T := hU.to_sup_of_normal_left' hW (hWH.trans hHU)
  have hTH : T ≤ H := sup_le hUH hWH
  by_contra hn
  have hproper : W.subgroupOf T < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    exact fun hh => hn (le_sup_left.trans hh)
  let _ : Group.IsNilpotent T := hT.isNilpotent
  obtain ⟨t, htN, htW⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (W.subgroupOf T) hproper)
  have htN' : (t : G) ∈ normalizer (W : Set G) := by
    rw [← subgroupOf_normalizer_eq hWT] at htN
    exact htN
  exact htW (hNW ⟨htN', hTH t.property⟩)

/-- Each involution of the actual fixed four has that four in its full
centralizer's two-core. This is the local input for the odd-complement action. -/
public theorem LargeTerminalContext.five_fixed_four_le_involution_centralizer_core
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (y : G) (hy : y ∈ twoCoreIn ctx.second ⊓ centralizer (A : Set G))
    (hy1 : y ≠ 1) :
    twoCoreIn ctx.second ⊓ centralizer (A : Set G) ≤
      twoCoreIn (centralizer ({y} : Set G)) := by
  classical
  let Q := twoCoreIn ctx.second
  let V := Q ⊓ centralizer (A : Set G)
  let W := Q ⊓ centralizer (DerivedAmbient ctx.firstResidual : Set G)
  let H := centralizer ({y} : Set G)
  let U := twoCoreIn H
  obtain ⟨hVfour, _, hVR, _⟩ := ctx.five_fixed_four_ambient_data A hAN hcard hncyc hfixed
  let _ := hVfour
  let _ : IsMulCommutative V := IsKleinFour.isMulCommutative
  have hy2 : orderOf y = 2 := by
    apply orderOf_eq_prime _ hy1
    have hh := Monoid.pow_exponent_eq_one (⟨y, hy⟩ : V)
    rw [IsKleinFour.exponent_two] at hh
    exact congrArg V.subtype hh
  by_cases hyR : y ∈ ctx.firstResidual
  · obtain ⟨z, hz, hgen, _⟩ := ctx.involution_centralizer_core
    have hyZ : y ∈ zpowers z := hgen.symm ▸ hVR ▸ (show y ∈ V ⊓ ctx.firstResidual from ⟨hy, hyR⟩)
    have heq : y = z := by
      rw [mem_zpowers_iff_mem_range_orderOf, hz] at hyZ
      obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hyZ
      have hn2 := Finset.mem_range.mp hn
      interval_cases n
      · exact (hy1 (by simpa using he.symm)).elim
      · simpa using he.symm
    rw [heq, ctx.involution_centralizer_eq_second hS z hz hgen]
    exact inf_le_left
  have hWdef : Q ⊓ centralizer (V : Set G) = W :=
    ctx.five_fixed_four_core_centralizer_eq hS A hA hAN hcard hncyc hfixed
  have hVW : V ≤ W := by
    rw [← hWdef]
    exact le_inf inf_le_left (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hWH : W ≤ H := by
    rw [← hWdef]
    exact inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.mpr hy))
  have hQH : Q ⊓ H = W := by
    apply (eq_of_le_of_card_ge (le_inf inf_le_left hWH) ?_).symm
    exact (ctx.fixed_core_centralizer_card_le_sixtyfour hS A hA hAN hfixed y
      hy.1 hy.2 hyR).trans_eq (ctx.derived_centralizer_card_and_index hS).1.symm
  have hNW : normalizer (W : Set G) ≤ ctx.second :=
    ctx.derived_centralizer_normalizer_le_second hS
  have hUt : IsPGroup 2 U := pCore_isPGroup.map H.subtype
  have hWt : IsPGroup 2 W := (pCore_isPGroup.map ctx.second.subtype).to_le inf_le_left
  have hHU : H ≤ normalizer (U : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (twoCoreIn_le H)).mp (twoCoreIn_normal H)
  have hUH : U ≤ H := twoCoreIn_le H
  have hUN : U ⊓ normalizer (W : Set G) ≤ W := by
    let B := U ⊓ normalizer (W : Set G)
    have hBA : A ≤ normalizer (B : Set G) := by
      have hAH : A ≤ H := by
        intro a ha
        exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hy.2 a ha)
      have hAW : A ≤ normalizer (W : Set G) :=
        hAP.trans (ctx.derived_centralizer_normalizer_local_data hS).2.1
      exact (le_inf (hAH.trans hHU) (hAW.trans le_normalizer)).trans
        inf_normalizer_le_normalizer_inf
    have hBQ : B ≤ Q := ctx.five_normalized_two_subgroup_le_second_core A B hA hAP
      (inf_le_right.trans hNW) (hUt.to_le inf_le_left) hBA
    exact (le_inf hBQ (inf_le_left.trans hUH)).trans_eq hQH
  have hUW : U ≤ W := by
    let T := U ⊔ W
    have hTH : T ≤ H := sup_le hUH hWH
    have hN : normalizer (W : Set G) ⊓ T ≤ W := by
      intro t ht
      have hprod : t ∈ (U : Set G) * (W : Set G) := by
        rw [← coe_mul_of_right_le_normalizer_left U W (hWH.trans hHU)]
        exact ht.2
      obtain ⟨u, hu, w, hw, heq⟩ := hprod
      rw [← heq] at ht ⊢
      have huN : u ∈ normalizer (W : Set G) := by
        have hh := (normalizer (W : Set G)).mul_mem ht.1
          ((normalizer (W : Set G)).inv_mem (W.le_normalizer hw))
        simpa only [mul_inv_cancel_right] using hh
      exact W.mul_mem (hUN ⟨hu, huN⟩) hw
    exact core_le_of_normalizer_condition T W U hWt hUt le_sup_right le_sup_left
      (hTH.trans hHU) hN
  have hVCW : V ≤ centralizer (W : Set G) := by
    apply le_centralizer_iff.mpr
    rw [← hWdef]
    exact inf_le_right
  have hchar := (ctx.localStructure H
    (Theory.GroupTheory.isTwoLocal_involution_centralizer hy2)).2
  intro v hv
  have hvH : v ∈ H := hWH (hVW hv)
  have hc : (⟨v, hvH⟩ : H) ∈ centralizer (pCore 2 H : Set H) := by
    intro u hu
    apply Subtype.ext
    exact mem_centralizer_iff.mp (hVCW hv) u (hUW (mem_map_of_mem H.subtype hu))
  exact mem_map_of_mem H.subtype (hchar hc)

/-- Every normal odd subgroup of the five-centralizer centralizes its actual
fixed four-group. In particular this applies to a normal odd complement. -/
public theorem LargeTerminalContext.five_fixed_four_normal_odd_subgroup_le_centralizer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (K : Subgroup (centralizer (A : Set G))) (hKnormal : K.Normal)
    (hKodd : Odd (Nat.card K)) :
    K ≤ centralizer (((twoCoreIn ctx.second ⊓ centralizer (A : Set G)).subgroupOf
      (centralizer (A : Set G))) : Set (centralizer (A : Set G))) := by
  let C := centralizer (A : Set G)
  let V := twoCoreIn ctx.second ⊓ C
  let L := K.map C.subtype
  let _ := hKnormal
  let _ : IsKleinFour V := (ctx.five_fixed_four_ambient_data A hAN hcard hncyc hfixed).1
  have hCN : C ≤ normalizer (L : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      K.le_normalizer_map C.subtype
  have hLodd : Odd (Nat.card L) := by
    rwa [card_map_of_injective C.subtype_injective]
  have hLC : L ≤ centralizer (V : Set G) :=
    normal_odd_centralizes_four_of_le_involution_cores C L V hCN hLodd inf_le_right
      (ctx.five_fixed_four_le_involution_centralizer_core hS A hA hAP hAN hcard hncyc hfixed)
  intro k hk
  rw [mem_centralizer_iff]
  intro v hv
  apply Subtype.ext
  exact mem_centralizer_iff.mp (hLC (mem_map_of_mem C.subtype hk)) v hv

/-- The normal odd complement supplied by transfer acts trivially on the
fixed four-group. Complementarity is not needed for this centralization step. -/
public theorem LargeTerminalContext.five_fixed_four_odd_complement_le_centralizer
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hncyc : ¬ IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (K : Subgroup (centralizer (A : Set G))) (hKnormal : K.Normal)
    (hKodd : Odd (Nat.card K))
    (_hKcomp : K.IsComplement' ((twoCoreIn ctx.second ⊓ centralizer (A : Set G)).subgroupOf
      (centralizer (A : Set G)))) :
    K ≤ centralizer (((twoCoreIn ctx.second ⊓ centralizer (A : Set G)).subgroupOf
      (centralizer (A : Set G))) : Set (centralizer (A : Set G))) :=
  ctx.five_fixed_four_normal_odd_subgroup_le_centralizer hS A hA hAP hAN hcard hncyc hfixed
    K hKnormal hKodd

end Stellmacher.Recognition
