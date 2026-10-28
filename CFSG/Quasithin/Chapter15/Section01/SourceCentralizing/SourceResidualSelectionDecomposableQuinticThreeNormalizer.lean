module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticNormalizer
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.GroupTheory.PGroup.SupercriticalAutomorphisms
public import Theory.GroupTheory.PGroup.ExponentPrimeRankTwoOrder
public import Theory.GroupTheory.PGroup.ThreeGroupSmallAutomorphisms
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# Five-subgroups preserve residuals with arbitrary three-group sections

A finite three-group of three-rank at most two has no automorphism of
order five. A supercritical subgroup has order at most twenty-seven,
so the small three-group automorphism theorem excludes five in its
automorphism group. The supercritical restriction kernel is a three-group,
which detects every possible order-five automorphism of the whole group.

Consequently a five-group acts trivially on the three-core of a group of
three-rank at most two. Applying this after quotienting the two-core, then
lifting two-perfect containment, proves normalization for every two-perfect
normal subgroup with a three-group two-core quotient. The final theorem
retains the actual surjective action map and its unrestricted kernel.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15
namespace DecomposableQuinticControl

private theorem not_five_dvd_aut_of_three_rank_two
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 3 P)
    (hr : primeRank 3 P ≤ 2) : ¬ 5 ∣ Nat.card (MulAut P) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨X,hX⟩ := hP.exists_supercriticalPSubgroup (by decide)
  let : X.Characteristic := hX.characteristic
  have hpX : IsPGroup 3 X := hP.to_subgroup X
  have hrX : primeRank 3 X ≤ 2 := (primeRank_subgroup_le 3 X).trans hr
  have hcard : Nat.card X ≤ 27 := by
    by_cases hab : IsMulCommutative X
    · let : IsMulCommutative X := hab
      let : IsElementaryAbelian 3 X := { exponent_dvd_p := hX.exponent_dvd_p }
      have hh := (primeRank_le_iff_elementary_card_le P).mp hr X inferInstance
      exact hh.trans (by decide)
    have hr2 : primeRank 3 X=2 := by
      by_contra hne
      have hr1 : primeRank 3 X≤1 := by omega
      let : IsCyclic X := hpX.isCyclic_of_odd_of_elementary_card_le (by decide)
        (fun E hE => by
          let := hE
          exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hr1 E)
      exact hab inferInstance
    have hnt : Nontrivial X := by
      rcases subsingleton_or_nontrivial X with h | h
      · let := h
        exact (hab inferInstance).elim
      · exact h
    let := hnt
    have hexp : Monoid.exponent X=3 :=
      (Monoid.exponent_eq_prime_iff (by decide : Nat.Prime 3)).mpr
        (fun x hx => orderOf_eq_prime (hX.pow_eq_one x) hx)
    exact hpX.card_le_prime_cube_of_exponent_prime_rank_two (by decide)
      hexp hr2 hX.derived_le_center
  have hnotX : ¬ 5 ∣ Nat.card (MulAut X) := by
    intro hfive
    have hh := (elementary_three_of_card_le_eightyone_of_five_dvd_card_mulAut
      hpX (hcard.trans (by decide)) hfive).1
    omega
  intro hfive
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' 5 hfive
  have ho := (MulAut.characteristic X).orderOf_map_eq_of_coprime_of_isPGroup_ker
    (hX.isPGroup_restriction_kernel hP (by decide)) a
    (show Nat.Coprime 3 (orderOf a) by rw [ha]; decide)
  apply hnotX
  rw [←ha,←ho]
  exact orderOf_dvd_natCard (MulAut.characteristic X a)

private theorem normal_three_fixed_by_five_action
    {K P : Type*} [Group K] [Finite K] [Group P] [Finite P]
    (Y : Subgroup K) [Y.Normal] (hY : IsPGroup 3 Y)
    (hr : primeRank 3 K ≤ 2) (hP : IsPGroup 5 P) (a : P →* MulAut K) :
    ∀ p : P, ∀ y : K, y ∈ Y → a p y = y := by
  let R := pCore 3 K
  have hYR : Y ≤ R := le_sSup ⟨inferInstance,hY⟩
  have hcop : Nat.Coprime 5 (Nat.card (MulAut R)) :=
    (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 5)).mpr
      (not_five_dvd_aut_of_three_rank_two pCore_isPGroup
        ((primeRank_subgroup_le 3 R).trans hr))
  let b := (MulAut.characteristic R).comp a
  have hb : b=1 := by
    apply MonoidHom.ext
    intro p
    obtain ⟨n,hn⟩ := hP p
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (hcop.pow_left n)
    · exact orderOf_dvd_of_pow_eq_one (by rw [←map_pow,hn,map_one])
    · exact orderOf_dvd_natCard (b p)
  intro p y hy
  have he := DFunLike.congr_fun (DFunLike.congr_fun hb p) (⟨y,hYR hy⟩ : R)
  exact congrArg Subtype.val he

private theorem normal_three_residual_stable_by_five_action
    {K P : Type*} [Group K] [Finite K] [Group P] [Finite P]
    (Y : Subgroup K) [Y.Normal] (hpY : IsPPerfect 2 Y)
    (hY : IsPGroup 3 (Y ⧸ pCore 2 Y)) (hr : primeRank 3 K ≤ 2)
    (hP : IsPGroup 5 P) (a : P →* MulAut K) (p : P) :
    Y.map (a p).toMonoidHom ≤ Y := by
  let q := QuotientGroup.mk' (pCore 2 K)
  let B := Y.map q
  let : B.Normal := (inferInstance : Y.Normal).map q (QuotientGroup.mk'_surjective _)
  have hB : IsPGroup 3 B :=
    hY.of_equiv ((inferInstance : Y.Normal).isSubnormal.quotientCoreImageEquiv 2)
  let b := (quotientAut (pCore 2 K)).comp a
  have hfix := normal_three_fixed_by_five_action B hB
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup).trans hr)
    hP b
  apply isPPerfect_le_of_map_le_of_kernel_normalizes q _ Y
    (hpY.of_surjective ((a p).toMonoidHom.subgroupMap Y)
      ((a p).toMonoidHom.subgroupMap_surjective Y))
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) le_normalizer_of_normal
  rintro _ ⟨_,⟨y,hy,rfl⟩,rfl⟩
  have he := hfix p (q y) (mem_map_of_mem q hy)
  change quotientAut (pCore 2 K) (a p) (q y)=q y at he
  rw [quotientAut_apply_mk] at he
  exact he ▸ mem_map_of_mem q hy

/-- A five-subgroup normalizing a group of three-rank at most two normalizes
its normal two-perfect subgroup with arbitrary three-group two-core quotient. -/
theorem five_normalizes_three_residual
    {G : Type*} [Group G] [Finite G] (P K Y : Subgroup G)
    (hYK : Y≤K) (hn : K≤normalizer (Y : Set G))
    (hpY : IsPPerfect 2 Y) (hY : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hr : primeRank 3 K≤2) (hP : IsPGroup 5 P)
    (hPK : P≤normalizer (K : Set G)) : P≤normalizer (Y : Set G) := by
  let YK := Y.subgroupOf K
  let : YK.Normal := (normal_subgroupOf_iff_le_normalizer hYK).mpr hn
  let e := subgroupOfEquivOfLe hYK
  have hpYK : IsPPerfect 2 YK := hpY.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hYKthree : IsPGroup 3 (YK ⧸ pCore 2 YK) := by
    let eQ := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    exact hY.of_equiv eQ.symm
  let a : P →* MulAut K := K.normalizerMonoidHom.comp (inclusion hPK)
  apply le_normalizer_iff.mpr
  intro p hp y hy
  have hh := normal_three_residual_stable_by_five_action YK hpYK hYKthree hr hP a ⟨p,hp⟩
  exact hh (mem_map_of_mem (a ⟨p,hp⟩).toMonoidHom (show (⟨y,hYK hy⟩ : K)∈YK from hy))

/-- A five-subgroup of an action image which centralizes a residual with a three-group two-core quotient is
already contained in the image of the residual normalizer. -/
theorem five_image_le_normalizer_map_of_three_residual
    {L D : Type*} [Group L] [Finite L] [Group D] [Finite D]
    (f : L →* D) (hf : Function.Surjective f) (Y : Subgroup L)
    (hpY : IsPPerfect 2 Y) (hY : IsPGroup 3 (Y ⧸ pCore 2 Y))
    (hrL : primeRank 3 L ≤ 2)
    (A : Subgroup D) (hA5 : IsPGroup 5 A)
    (hAY : A ≤ centralizer (Y.map f : Set D))
    (hker : f.ker ≤ normalizer (Y : Set L)) :
    A ≤ (normalizer (Y : Set L)).map f := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let B := A.comap f
  let q : B →* A := f.subgroupComap A
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective A hf
  let P : Sylow 5 B := Sylow.nonempty.some
  have hPmap : (P : Subgroup B).map q = ⊤ :=
    ((P.mapSurjective hq).is_maximal' (hA5.to_subgroup ⊤) le_top).symm
  let P0 : Subgroup L := (P : Subgroup B).map B.subtype
  have hP0 : IsPGroup 5 P0 := P.isPGroup'.map B.subtype
  have hPmapA : P0.map f = A := by
    change ((P : Subgroup B).map B.subtype).map f = A
    rw [map_map]
    change (P : Subgroup B).map (A.subtype.comp q) = A
    rw [← map_map, hPmap, ← MonoidHom.range_eq_map, range_subtype]
  let K : Subgroup L := Y ⊔ f.ker
  have hYK : Y ≤ K := le_sup_left
  have hKnY : K ≤ normalizer (Y : Set L) :=
    sup_le Y.le_normalizer hker
  have hPK : P0 ≤ normalizer (K : Set L) := by
    have hm : P0.map f ≤ normalizer (Y.map f : Set D) :=
      hPmapA ▸ hAY.trans (Subgroup.centralizer_le_normalizer _)
    have hh := ((map_le_iff_le_comap).mp hm).trans ((Y.map f).le_normalizer_comap f)
    simpa only [Subgroup.comap_map_eq] using hh
  have hrK : primeRank 3 K ≤ 2 := (primeRank_subgroup_le 3 K).trans hrL
  have hPNY := five_normalizes_three_residual P0 K Y hYK hKnY hpY hY hrK hP0 hPK
  rw [← hPmapA]
  exact map_mono hPNY

end DecomposableQuinticControl
end CFSG.Quasithin.Chapter15
