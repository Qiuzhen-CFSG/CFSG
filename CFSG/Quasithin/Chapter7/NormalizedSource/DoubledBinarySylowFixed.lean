module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryIntersection
public import Theory.GroupTheory.IndexTwoCentralizerFixedCard
public import Theory.GroupTheory.InnerImageGeometry
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.ElementaryAbelian.Injective
/-!
# The small Sylow action on the paired-plane moving subgroup

The literal paired-plane centralizer induces S₃ on the original doubled
orbit. A two-subgroup therefore has image of order at most two, with its
whole-orbit centralizer as kernel. The original local Sylow centralizer
preserves [W,L₀]. The involution fixed-point count then gives at least four
fixed elements in this elementary subgroup of order sixteen.

NonFFSourceDoubledBinarySylowFixed supplies the actual chosen-module action,
Sylow placement and moving-subgroup order. A faithful inner action sends
the fixed subgroup into the center of a Sylow subgroup of K/Z(K); its
elementary subgroup of order at least four makes that center noncyclic.
Component exclusion and ambient containment remain with
qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, proof of 7.7.6, printed p.706, refs/quasithin.pdf.
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySylowFixed
open ChapterE DoubledBinaryLocalCore

private theorem two_image_card_le_two {X : Type*} [Group X] [Finite X]
    (hp : IsPGroup 2 X) (f : X →* Equiv.Perm (Fin 3)) : Nat.card f.range ≤ 2 := by
  obtain ⟨k,hk⟩ := (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_card_eq
  have hd : Nat.card f.range ∣ 6 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin, show Nat.factorial 3 = 6 by decide] using f.range.card_subgroup_dvd_card
  have hb := Nat.le_of_dvd (by decide : 0 < 6) hd
  have hk3 : k < 3 := by
    by_contra h
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show 3 ≤ k by omega)
    norm_num at hh
    omega
  interval_cases k <;> rw [hk] at hd ⊢ <;> norm_num at *

/-- The whole-orbit kernel has index at most two in each two-subgroup of
an actual paired-plane centralizer. -/
theorem centralizer_index_le_two
    {G : Type*} [Group G] [Finite G] (W U S : Subgroup G)
    (hSN : S ≤ normalizer (W : Set G)) (hSC : S ≤ centralizer (U : Set G))
    (hp : IsPGroup 2 S)
    (he : Nonempty (inducedAutomizer W (centralizer (U : Set G)) ≃* Equiv.Perm (Fin 3))) :
    ((centralizer (W : Set G)).subgroupOf S).index ≤ 2 := by
  obtain ⟨π,hπ,hker⟩ := DoubledBinaryPlaneQuotient.centralizer_quotient W U he
  let hle : S ≤ normalizer (W : Set G) ⊓ centralizer (U : Set G) := le_inf hSN hSC
  let r := π.comp (inclusion hle)
  have hk : r.ker = (centralizer (W : Set G)).subgroupOf S := by
    ext s
    change inclusion hle s ∈ π.ker ↔ _
    rw [hker]
    rfl
  rw [← hk,index_ker]
  exact two_image_card_le_two hp r

/-- A normalized elementary sixteen has at least four common fixed elements
when the ambient action has a kernel of index at most two. -/
theorem four_le_fixed_card
    {G : Type*} [Group G] [Finite G] (W A S : Subgroup G)
    [IsElementaryAbelian 2 A] (hAW : A ≤ W)
    (hSA : S ≤ normalizer (A : Set G)) (hcard : Nat.card A = 16)
    (hi : ((centralizer (W : Set G)).subgroupOf S).index ≤ 2) :
    4 ≤ Nat.card ((centralizer (S : Set G)).subgroupOf A) := by
  let N := (centralizer (W : Set G)).subgroupOf S
  let : MulDistribMulAction S A := conjMulDistribMulActionOfLeNormalizer S A hSA
  have hfix : ∀ n ∈ N, ∀ a : A, n • a = a := by
    intro n hn a
    apply Subtype.ext
    change (n : G) * (a : G) * (n : G)⁻¹ = (a : G)
    exact mul_inv_eq_iff_eq_mul.mpr (hn _ (hAW a.property)).symm
  have he : FixedPoints.subgroup S A = (centralizer (S : Set G)).subgroupOf A := by
    ext a
    constructor
    · intro ha s hs
      have hh := congrArg A.subtype (ha ⟨s,hs⟩)
      exact mul_inv_eq_iff_eq_mul.mp hh
    · intro ha s
      apply Subtype.ext
      change (s : G) * (a : G) * (s : G)⁻¹ = (a : G)
      exact mul_inv_eq_iff_eq_mul.mpr (ha s s.property)
  have hnpos : 0 < N.index := Nat.pos_of_ne_zero N.index_ne_zero_of_finite
  have hsq : Nat.card A ≤ Nat.card (FixedPoints.subgroup S A) ^ 2 := by
    rcases (show N.index = 1 ∨ N.index = 2 by change N.index ≤ 2 at hi; omega) with hn | hn
    · have htop : FixedPoints.subgroup S A = ⊤ := by
        apply top_unique
        intro a _ s
        exact hfix s (index_eq_one.mp hn ▸ mem_top s) a
      rw [htop,card_top,hcard]
      norm_num
    · exact card_le_fixed_card_sq_of_index_two_kernel N hn hfix
  rw [he,hcard] at hsq
  nlinarith

/-- The actual local Sylow centralizer preserves the residual moving subgroup. -/
theorem localSylow_normalizes_movement
    {G : Type*} [Group G] (W L T U : Subgroup G)
    (hTL : T ≤ normalizer (L : Set G)) (hTW : T ≤ normalizer (W : Set G)) :
    T ⊓ centralizer (U : Set G) ≤ normalizer ((⁅W,localResidual L U⁆ : Subgroup G) : Set G) := by
  have hTR : T ⊓ centralizer (U : Set G) ≤ normalizer (localResidual L U : Set G) :=
    ((le_inf (inf_le_left.trans hTL)
      (inf_le_right.trans (centralizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image _ (pResidual 2 _))
  intro s hs
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hTW hs.1),
    mem_normalizer_iff_map_conj_eq.mp (hTR hs)]

/-- A faithful inner elementary action with at least four Sylow-fixed elements
forces a noncyclic center in a Sylow subgroup of the literal central quotient. -/
theorem centralQuotient_sylow_center_not_cyclic
    {G : Type*} [Group G] [Finite G] (K A S : Subgroup G)
    [IsElementaryAbelian 2 A] (hAN : A ≤ normalizer (K : Set G))
    (P : Sylow 2 K) (hPS : (P : Subgroup K).map K.subtype ≤ S)
    (hfixed : 4 ≤ Nat.card ((centralizer (S : Set G)).subgroupOf A))
    (j : A →* K ⧸ center K) (hj : Function.Injective j)
    (hact : ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
      K.normalizerMonoidHom (inclusion hAN a)) :
    ∃ Q : Sylow 2 (K ⧸ center K), ¬ IsCyclic (center Q) := by
  let I := MulAut.innerSubgroup K
  let u : K →* I := MulAut.conj.rangeRestrict
  have hu : Function.Surjective u := MulAut.conj.rangeRestrict_surjective
  let Pᵢ : Sylow 2 I := P.mapSurjective hu
  let F := (centralizer (S : Set G)).subgroupOf A
  change 4 ≤ Nat.card F at hfixed
  let i : A →* I := innerEquivCentralQuotient.symm.toMonoidHom.comp j
  let r : F →* I := i.comp F.subtype
  have hr : Function.Injective r :=
    (innerEquivCentralQuotient.symm.injective.comp hj).comp F.subtype_injective
  let E := r.range
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_injective
    F.subtype F.subtype_injective
  have hpE : IsPGroup 2 E := (IsElementaryAbelian.isPGroup 2 F).of_surjective
    r.rangeRestrict r.rangeRestrict_surjective
  have hEC : E ≤ centralizer (Pᵢ : Set I) := by
    rintro _ ⟨a,rfl⟩ b hb
    obtain ⟨k,hk,rfl⟩ := hb
    have hfix : (i a.val : MulAut K) k = k := by
      rw [show (i a.val : MulAut K) = _ from hact a.val]
      apply Subtype.ext
      change (a.val : G) * (k : G) * (a.val : G)⁻¹ = (k : G)
      exact mul_inv_eq_iff_eq_mul.mpr
        (a.property (k : G) (hPS (mem_map_of_mem K.subtype hk))).symm
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    change k * ((i a.val : MulAut K) x) * k⁻¹ =
      (i a.val : MulAut K) (k*x*k⁻¹)
    rw [map_mul,map_mul,map_inv,hfix]
  have hEP : E ≤ (Pᵢ : Subgroup I) := by
    apply sup_eq_right.mp
    exact Pᵢ.is_maximal' (hpE.to_sup_of_normal_left' Pᵢ.isPGroup'
      ((le_centralizer_iff.mp hEC).trans (Subgroup.centralizer_le_normalizer _))) le_sup_right
  let rP : F →* Pᵢ := r.codRestrict _ (fun a => hEP ⟨a,rfl⟩)
  have hc : ∀ a, rP a ∈ center Pᵢ := by
    intro a
    apply mem_center_iff.mpr
    intro b
    exact Subtype.ext (hEC ⟨a,rfl⟩ b b.property)
  let rZ : F →* center Pᵢ := rP.codRestrict _ hc
  have hrZ : Function.Injective rZ := by
    intro a b hab
    exact hr (congrArg (fun z : center Pᵢ => (z.val : I)) hab)
  have hn : ¬ IsCyclic (center Pᵢ) := by
    intro hcyc
    let := hcyc
    let : IsCyclic F := isCyclic_of_injective rZ hrZ
    have hd := IsElementaryAbelian.exponent_dvd_p 2 F
    rw [IsCyclic.exponent_eq_card] at hd
    have hh := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  let Q := Pᵢ.mapSurjective (f := (innerEquivCentralQuotient (H := K)).toMonoidHom)
    (innerEquivCentralQuotient (H := K)).surjective
  let e : Pᵢ ≃* Q := (innerEquivCentralQuotient (H := K)).subgroupMap (Pᵢ : Subgroup I)
  exact ⟨Q, fun h => hn ((centerCongr e).isCyclic.mpr h)⟩


end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySylowFixed
