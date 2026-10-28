module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySylowFixed

/-!
# Sylow placement of the projected moving subgroup

Let A and a component Sylow P lie in the original two-subgroup S, with
A acting by inner automorphisms on K. Their images lie in the two-group
image of S intersect N_G(K); Sylow maximality puts the image of A in the
image of P. Centralizer indices decrease under restriction and surjection,
so an index-at-most-two centralizer in S supplies the same bound in P's
inner image.

The inner-group equivalence agrees with the canonical quotient K → K/Z(K).
Thus the result retains the literal image of the original P, as required
when lifting the later centralization conclusion. The chosen-module
application is NonFFSourceDoubledBinaryComponentSylow.
Source: Aschbacher–Smith, proof of 7.7.6, printed p.706,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryComponentSylow

private theorem inner_sylow
    {G : Type*} [Group G] [Finite G] (K A S : Subgroup G)
    (hAS : A ≤ S) (hpS : IsPGroup 2 S)
    (hAN : A ≤ normalizer (K : Set G))
    (P : Sylow 2 K) (hPS : (P : Subgroup K).map K.subtype ≤ S)
    (hi : ((centralizer (A : Set G)).subgroupOf S).index ≤ 2)
    (i : A →* MulAut.innerSubgroup K)
    (hact : ∀ a : A, (i a : MulAut K) = K.normalizerMonoidHom (inclusion hAN a)) :
    let PI := P.mapSurjective (f := (MulAut.conj : K →* MulAut K).rangeRestrict)
      MulAut.conj.rangeRestrict_surjective
    i.range ≤ (PI : Subgroup _) ∧
      ((centralizer (i.range : Set (MulAut.innerSubgroup K))).subgroupOf (PI : Subgroup _)).index ≤ 2 := by
  let I := MulAut.innerSubgroup K
  let u : K →* I := MulAut.conj.rangeRestrict
  have hu : Function.Surjective u := MulAut.conj.rangeRestrict_surjective
  let PI := P.mapSurjective hu
  let E := i.range
  let N := normalizer (K : Set G)
  let f := K.normalizerMonoidHom
  let J := ((S.subgroupOf N).map f).subgroupOf I
  have hpJ : IsPGroup 2 J := (hpS.comap_subtype.map f).comap_subtype
  have hPJ : (PI : Subgroup I) ≤ J := by
    rintro _ ⟨k,hk,rfl⟩
    refine ⟨⟨k,K.le_normalizer k.property⟩,hPS (mem_map_of_mem K.subtype hk),?_⟩
    ext x
    rfl
  have hEJ : E ≤ J := by
    rintro _ ⟨a,rfl⟩
    exact ⟨inclusion hAN a,hAS a.property,(hact a).symm⟩
  have hEP : E ≤ (PI : Subgroup I) := hEJ.trans (PI.is_maximal' hpJ hPJ).le
  let C := (centralizer (E : Set I)).subgroupOf (PI : Subgroup I)
  let r : P →* PI := u.subgroupMap (P : Subgroup K)
  have hr : Function.Surjective r := u.subgroupMap_surjective _
  let s : P →* S := ((K.subtype.comp (P : Subgroup K).subtype).codRestrict S
    (fun k => hPS (mem_map_of_mem K.subtype k.property)))
  let F := (centralizer (A : Set G)).subgroupOf S
  have hFC : F.comap s ≤ C.comap r := by
    intro k hk
    change (u k.val) ∈ centralizer (E : Set I)
    rintro _ ⟨a,rfl⟩
    have hfix : (i a : MulAut K) k.val = k.val := by
      rw [show (i a : MulAut K) = _ from hact a]
      apply Subtype.ext
      change (a : G) * (k.val : G) * (a : G)⁻¹ = (k.val : G)
      exact mul_inv_eq_iff_eq_mul.mpr (hk (a : G) a.property)
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    change (i a : MulAut K) (k.val*x*k.val⁻¹) =
      k.val * ((i a : MulAut K) x) * k.val⁻¹
    rw [map_mul,map_mul,map_inv,hfix]
  have hindex : C.index ≤ 2 := by
    rw [←C.index_comap_of_surjective hr]
    apply (Nat.le_of_dvd (Nat.pos_of_ne_zero (F.comap s).index_ne_zero_of_finite)
      (index_dvd_of_le hFC)).trans
    apply le_trans _ hi
    rw [F.index_comap]
    exact (relIndex_le_of_le_right (H := F) (le_top : s.range ≤ ⊤)
      (by simpa using F.index_ne_zero_of_finite)).trans_eq F.relIndex_top_right
  exact ⟨hEP,hindex⟩

private theorem transport_sylow {I X : Type*} [Group I] [Group X] [Finite I]
    (e : I ≃* X) (PI : Sylow 2 I) (E : Subgroup I)
    (hEP : E ≤ (PI : Subgroup I))
    (hindex : ((centralizer (E : Set I)).subgroupOf (PI : Subgroup I)).index ≤ 2) :
    ∃ Q : Sylow 2 X, (Q : Subgroup X) = (PI : Subgroup I).map e.toMonoidHom ∧
      E.map e.toMonoidHom ≤ (Q : Subgroup X) ∧
      ((centralizer (E.map e.toMonoidHom : Set X)).subgroupOf (Q : Subgroup X)).index ≤ 2 := by
  let : Finite X := Finite.of_equiv I e.toEquiv
  let Q := PI.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcentral : (centralizer (E : Set I)).map e.toMonoidHom ≤
      centralizer (E.map e.toMonoidHom : Set X) :=
    map_centralizer_le_centralizer_image (E : Set I) e.toMonoidHom
  have hsmall : ((centralizer (E : Set I)).map e.toMonoidHom).relIndex (Q : Subgroup X) ≤ 2 := by
    change ((centralizer (E : Set I)).map e.toMonoidHom).relIndex
      ((PI : Subgroup I).map e.toMonoidHom) ≤ 2
    rw [relIndex_map_map_of_injective _ _ e.injective]
    exact hindex
  refine ⟨Q,rfl,map_mono hEP,?_⟩
  exact (relIndex_le_of_le_left (L := (Q : Subgroup X)) hcentral
    (by exact index_ne_zero_of_finite)).trans hsmall

private theorem inner_conj {K : Type*} [Group K] (k : K) :
    innerEquivCentralQuotient ((MulAut.conj : K →* MulAut K).rangeRestrict k) =
      (QuotientGroup.mk' (center K)) k := by
  change QuotientGroup.quotientMulEquivOfEq DoubleCoverCentralizer.conj_kernel
    ((QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).symm
      (MulAut.conj.rangeRestrict k)) = _
  have he : (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).symm
      (MulAut.conj.rangeRestrict k) = QuotientGroup.mk k := by
    apply (QuotientGroup.quotientKerEquivRange (MulAut.conj : K →* MulAut K)).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [he]
  rfl

/-- The inner image lies in the canonical image of the original component
Sylow, with centralizer index at most two. -/
theorem projected_sylow
    {G : Type*} [Group G] [Finite G] (K A S : Subgroup G)
    (hAS : A ≤ S) (hpS : IsPGroup 2 S)
    (hAN : A ≤ normalizer (K : Set G))
    (P : Sylow 2 K) (hPS : (P : Subgroup K).map K.subtype ≤ S)
    (hi : ((centralizer (A : Set G)).subgroupOf S).index ≤ 2)
    (j : A →* K ⧸ center K)
    (hact : ∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
      K.normalizerMonoidHom (inclusion hAN a)) :
    let Q := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
    j.range ≤ (Q : Subgroup _) ∧
      ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf (Q : Subgroup _)).index ≤ 2 := by
  let e := innerEquivCentralQuotient (H := K)
  let i : A →* MulAut.innerSubgroup K := e.symm.toMonoidHom.comp j
  have hinner := inner_sylow K A S hAS hpS hAN P hPS hi i hact
  obtain ⟨Q,hQI,hQ,hC⟩ := transport_sylow e _ i.range hinner.1 hinner.2
  have hj : i.range.map e.toMonoidHom = j.range := by
    rw [←MonoidHom.range_comp]
    congr 1
    ext a
    exact e.apply_symm_apply (j a)
  have hmap : e.toMonoidHom.comp (MulAut.conj : K →* MulAut K).rangeRestrict =
      QuotientGroup.mk' (center K) := by
    ext k
    exact inner_conj k
  have hQQ : (Q : Subgroup (K ⧸ center K)) =
      (P : Subgroup K).map (QuotientGroup.mk' (center K)) := by
    rw [hQI]
    change ((P : Subgroup K).map (MulAut.conj : K →* MulAut K).rangeRestrict).map
      e.toMonoidHom = _
    rw [map_map,hmap]
  rw [hj,hQQ] at hQ hC
  exact ⟨hQ,hC⟩

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryComponentSylow
