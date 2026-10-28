module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.PSL3.Geometry
public import Mathlib.GroupTheory.Schreier
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Quotient-rank trapping for the PSL₃ two-plane members

The two-plane geometry supplies the normalizer dichotomy.  This module proves
the remaining conditional calculation for an actual E-member: its literal
quotient rank forces a large intersection of the plane with the normal
two-core cut down to the normal model `L`, and the active odd-prime or
component clause excludes the plane-normalizer alternative.

The index of the core intersection in the plane is at most `2^(f-1)`, while
the plane has order `2^(2*f)`. Thus its core intersection has order greater
than `2^f`. The geometric dichotomy remains an explicit input, to be proved
by the PSL₃ source assembly owner.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.1--6 and E.1.14(1), printed pp.209--211 and 214. The latter cites
Aschbacher, *GF(2)-representations of finite groups* (1982), Lemma 4.7.
-/

public section

open Subgroup
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.PSL3Obstruction

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

private theorem two_subgroup_le_core {N P : Subgroup G} [N.Normal]
    (hN : IsTwoClosed N) (hP : IsPGroup 2 P) (hPN : P ≤ N) : P ≤ pCore 2 G := by
  obtain ⟨S, hS⟩ := hN
  let : (S : Subgroup N).Characteristic := S.characteristic_of_normal hS
  have hsn : ((S : Subgroup N).map N.subtype).Normal := inferInstance
  have hle : P.subgroupOf N ≤ (S : Subgroup N) := by
    let _ := hS
    have hpg := hP.comap_of_injective N.subtype N.subtype_injective
    obtain ⟨U, hU⟩ := hpg.exists_le_sylow
    have hSU : S = U := by
      apply Sylow.ext
      exact (S.is_maximal' U.isPGroup' (S.isPGroup'.le_sylow_of_normal U)).symm
    simpa only [hSU, subgroupOf] using hU
  calc
    P = (P.subgroupOf N).map N.subtype := (map_subgroupOf_eq_of_le hPN).symm
    _ ≤ (S : Subgroup N).map N.subtype := map_mono hle
    _ ≤ pCore 2 G := le_sSup ⟨hsn, S.isPGroup'.map N.subtype⟩

private theorem core_le_radical (H : Type*) [Group H] [Finite H] :
    pCore 2 H ≤ solvableRadical H := by
  let _ := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  exact le_solvableRadical _ inferInstance inferInstance

private theorem member_not_le_core {T A K : Subgroup G} (h : IsEMember T A K) :
    ¬ A.subgroupOf K ≤ pCore 2 K := by
  intro hA
  have hz : (A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) = ⊥ := by
    apply bot_unique
    rintro x ⟨a, ha, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr (hA ha)
  rcases h.2.2.2.2.2 with ho | hc
  · obtain ⟨p, _, _, _, hne, hcomm, _⟩ := ho
    exact hne (hcomm.trans (by rw [hz, commutator_bot_right]))
  · have hzR : (A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K)) = ⊥ := by
      apply bot_unique
      rintro x ⟨a, ha, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mpr (core_le_radical K (hA ha))
    obtain ⟨_, _, _, D, hD, _, hc | hn⟩ := hc
    · rw [hzR, commutator_bot_right] at hc
      have hs := hD.2.simple
      rw [hc] at hs
      let _ := hs
      exact not_nontrivial_iff_subsingleton.mpr
        (inferInstance : Subsingleton ((⊥ : Subgroup (K ⧸ solvableRadical K)) ⧸
          center (⊥ : Subgroup (K ⧸ solvableRadical K)))) hs.toNontrivial
    · exact hn.1 (hzR ▸ bot_le)

private theorem quotient_card_le_of_rank_le {A K : Subgroup G}
    {i : ℕ} (hAK : A ≤ K) (hA : IsElementaryAbelian 2 A)
    {N : Subgroup K} [N.Normal]
    (hr : Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' N)) ≤ i) :
    Nat.card ((A.subgroupOf K).map (QuotientGroup.mk' N)) ≤ 2 ^ i := by
  let _ := hA
  let a := (A.subgroupOf K).map (QuotientGroup.mk' N)
  let _ : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf hAK
  let _ : IsElementaryAbelian 2 a := IsElementaryAbelian.map _
  let _ : CommGroup a := IsMulCommutative.instCommGroup
  have hdvd : Nat.card a ∣ 2 ^ Group.rank a := card_dvd_exponent_pow_rank' a
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 a))
  exact (Nat.le_of_dvd (by positivity) hdvd).trans
    (Nat.pow_le_pow_right (by decide) hr)

private theorem member_core_image_card_le {T A K : Subgroup G} {i : ℕ}
    (hK : IsEMemberAt i T A K) :
    Nat.card ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≤ 2 ^ i := by
  rcases hK.2 with ho | hc
  · exact quotient_card_le_of_rank_le hK.1.2.2.1 hK.1.1 ho.2
  · let a := A.subgroupOf K
    let R := solvableRadical K
    let _ := hK.1.1
    let _ : IsElementaryAbelian 2 a := IsElementaryAbelian.subgroupOf hK.1.2.2.1
    have hRQ : R ⊓ a ≤ pCore 2 K :=
      two_subgroup_le_core hc.1.1
        (IsElementaryAbelian.isPGroup 2 a).to_inf_right inf_le_left
    have hindex : (pCore 2 K).relIndex a ≤ R.relIndex a := by
      have hd := relIndex_dvd_of_le_left a hRQ
      rw [inf_relIndex_right] at hd
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero (R.subgroupOf a).index_ne_zero_of_finite) hd
    have hCindex : (pCore 2 K).relIndex a =
        Nat.card (a.map (QuotientGroup.mk' (pCore 2 K))) := by
      simpa only [QuotientGroup.ker_mk'] using relIndex_ker a (QuotientGroup.mk' (pCore 2 K))
    have hRindex : R.relIndex a = Nat.card (a.map (QuotientGroup.mk' R)) := by
      simpa only [QuotientGroup.ker_mk'] using relIndex_ker a (QuotientGroup.mk' R)
    rw [hCindex, hRindex] at hindex
    exact hindex.trans (quotient_card_le_of_rank_le hK.1.2.2.1 hK.1.1 hc.2)

omit [Finite G] in
private theorem core_intersection_card_gt {A K L : Subgroup G}
    {f : ℕ} (hf : 1 < f) (hAL : A ≤ L) (hAK : A ≤ K)
    (hcard : Nat.card A = 2 ^ (2 * f))
    (hsmall : Nat.card ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≤
      2 ^ (f - 1)) :
    2 ^ f < Nat.card ((((pCore 2 K).map K.subtype) ⊓ L) ⊓ A : Subgroup G) := by
  let AK := A.subgroupOf K
  let N := pCore 2 K
  let H := N.subgroupOf AK
  have hindex : H.index = Nat.card (AK.map (QuotientGroup.mk' N)) := by
    simpa only [QuotientGroup.ker_mk', relIndex, H] using
      relIndex_ker AK (QuotientGroup.mk' N)
  have hprod : Nat.card H * Nat.card (AK.map (QuotientGroup.mk' N)) = Nat.card A := by
    rw [← hindex, H.card_mul_index]
    exact Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv
  have hmap : Nat.card H = Nat.card (((N.map K.subtype) ⊓ L) ⊓ A : Subgroup G) := by
    have heq : H.map (K.subtype.comp AK.subtype) =
        ((N.map K.subtype) ⊓ L) ⊓ A := by
      rw [← Subgroup.map_map]
      change ((N.subgroupOf AK).map AK.subtype).map K.subtype = _
      rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_inf N AK K.subtype K.subtype_injective]
      rw [show AK.map K.subtype = A from map_subgroupOf_eq_of_le hAK]
      rw [inf_assoc, inf_eq_right.mpr hAL]
    have hinj : Function.Injective (K.subtype.comp AK.subtype) :=
      fun x y h => Subtype.ext (Subtype.ext h)
    rw [← heq, Subgroup.card_map_of_injective hinj]
  rw [← hmap]
  rw [hcard] at hprod
  by_contra hnot
  have hle : Nat.card H ≤ 2 ^ f := Nat.le_of_not_gt hnot
  have hbound : Nat.card H * Nat.card (AK.map (QuotientGroup.mk' N)) ≤
      2 ^ f * 2 ^ (f - 1) := Nat.mul_le_mul hle hsmall
  have hpowlt : 2 ^ f * 2 ^ (f - 1) < 2 ^ (2 * f) := by
    rw [← Nat.pow_add]
    apply Nat.pow_lt_pow_right (by decide : 1 < 2)
    omega
  omega

/-- The literal quotient ranks in E.1.5 trap every marked plane member in the
matrix Sylow normalizer, conditional only on the stated geometric dichotomy. -/
theorem members_le_normalizer_sylowImage (L : Subgroup G) [L.Normal]
    (e : L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (hgeo : LargeIntersectionNormalizer L e f)
    (T : Sylow 2 G) (hST : sylowImage L e ≤ (T : Subgroup G))
    (b : Bool) (K : Subgroup G)
    (hK : IsEMemberAt (f - 1) (T : Subgroup G) (planeImage L e b) K) :
    K ≤ normalizer (sylowImage L e : Set G) := by
  let _ := Fintype.ofFinite F
  let _ : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let A := planeImage L e b
  let C := (pCore 2 K).map K.subtype
  let Q := C ⊓ L
  let hA : IsElementaryAbelian 2 A := hK.1.1
  have hAL : A ≤ L := (planeImage_le L e b).trans (sylowImage_le L e)
  have hAK : A ≤ K := hK.1.2.2.1
  obtain ⟨S, hS⟩ := hK.1.2.2.2.2.1
  have hcoreS : pCore 2 K ≤ (S : Subgroup K) :=
    pCore_isPGroup.le_sylow_of_normal S
  have hCT : C ≤ (T : Subgroup G) :=
    (map_mono hcoreS).trans (by rw [hS, subgroupOf_map_subtype]; exact inf_le_left)
  have hQS : Q ≤ sylowImage L e := by
    rw [← inf_eq_sylowImage L e (by omega) hF T hST]
    exact le_inf inf_le_right (inf_le_left.trans hCT)
  have hCnorm : K ≤ normalizer (C : Set G) := by
    change K ≤ normalizer (((pCore 2 K).map K.subtype : Subgroup G) : Set G)
    have h := Subgroup.le_normalizer_map (H := pCore 2 K) K.subtype
    simpa only [normalizer_eq_top_iff.mpr inferInstance, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] using h
  have hQnorm : K ≤ normalizer (Q : Set G) :=
    (le_inf hCnorm le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  have hlarge : 2 ^ f < Nat.card (Q ⊓ A : Subgroup G) :=
    core_intersection_card_gt hf hAL hAK (planeImage_mem L e hF b).2.2
      (member_core_image_card_le hK)
  rcases hgeo Q hQS b hlarge with hQA | hQSyl
  · exfalso
    apply member_not_le_core hK.1
    let _ : (A.subgroupOf K).Normal :=
      normal_subgroupOf_of_le_normalizer (hQnorm.trans hQA)
    exact le_sSup ⟨inferInstance, (IsElementaryAbelian.isPGroup 2 A).comap_subtype⟩
  · exact hQnorm.trans hQSyl

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.PSL3Obstruction
