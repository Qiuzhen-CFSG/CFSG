module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.NormalizedQuotient
public import Theory.SpecificGroups.Janko4.Model.ElementarySylowFixers
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# Excluding J₄ with the two original summands

The kernel on the moved subgroup U is exactly the original point line,
which lies in the natural summand and is disjoint from the dual hyperplane.
Thus their images in K/O₂(K) are disjoint and nontrivial. The actual marked
point Sylow preserves both images, as does its intersection with K and its
image in that quotient.

Each nontrivial normal subgroup of a finite two-group meets its center.
The proved center order two for Sylow subgroups of the actual J₄ carrier
therefore rules out this disjoint pair. No multiplier calculation or extra
module-recognition premise is required. Core.Complete supplies all source
containment and Sylow premises.
Source: Aschbacher--Smith 12.1.6, printed p.791, and 1.1.5(3)(f), p.502.
The imported native J₄ centralizer calculations retain their attribution.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel

private theorem no_disjoint_normal_pair_of_sylow_center_two
    {Q : Type*} [Group Q] [Finite Q] (P : Sylow 2 Q)
    (hc : Nat.card (center P) = 2) (A D : Subgroup Q)
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 D]
    (hPA : (P : Subgroup Q) ≤ normalizer (A : Set Q))
    (hPD : (P : Subgroup Q) ≤ normalizer (D : Set Q))
    (hA : A ≠ ⊥) (hD : D ≠ ⊥) (hAD : Disjoint A D) : False := by
  have hcsub (E : Subgroup Q) [IsElementaryAbelian 2 E]
      (hPE : (P : Subgroup Q) ≤ normalizer (E : Set Q)) (hE : E ≠ ⊥) :
      center P ≤ E.subgroupOf P := by
    have hEP : E ≤ (P : Subgroup Q) := sup_eq_left.mp
      (P.is_maximal' (P.isPGroup'.to_sup_of_normal_right'
        (IsElementaryAbelian.isPGroup 2 E) hPE) le_sup_left)
    let D := E.subgroupOf P
    let : D.Normal := normal_subgroupOf_of_le_normalizer hPE
    have hd : D ≠ ⊥ := by
      intro hd
      have he := congrArg (map (P : Subgroup Q).subtype) hd
      rw [map_subgroupOf_eq_of_le hEP,Subgroup.map_bot] at he
      exact hE he
    have hi := center_inf_ne_bot_of_normal P.isPGroup' D hd
    have hsize := (one_lt_card_iff_ne_bot _).mpr hi
    have he : center P ⊓ D = center P := eq_of_le_of_card_ge inf_le_left (by omega)
    exact he.symm.le.trans inf_le_right
  have hCA := hcsub A hPA hA
  have hCD := hcsub D hPD hD
  have hcb : center P = ⊥ := le_bot_iff.mp (by
    intro x hx
    have hh : (x : Q) ∈ A ⊓ D := ⟨hCA hx,hCD hx⟩
    rw [hAD.eq_bot,mem_bot] at hh
    exact Subtype.ext hh)
  simp [hcb] at hc

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

private theorem pure_summand_cards
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    Nat.card B.naturalSummand = 2^n ∧ Nat.card (S.pureDualHyperplane w hp) = 2^(n-1) := by
  open Representation.BinaryOffender in
    have hn : (binarySubgroup S.setup.natural).map
        (componentOrbit V (T : Subgroup G)).subtype = B.naturalSummand := by
      ext x
      constructor
      · rintro ⟨v,hv,rfl⟩
        exact (B.mem_naturalSummand v).mpr ((S.natural_marking v).mp hv)
      · intro hx
        let v : componentOrbit V (T : Subgroup G) := ⟨x,B.naturalSummand_le hx⟩
        exact ⟨v,(S.natural_marking v).mpr ((B.mem_naturalSummand v).mp hx),rfl⟩
    constructor
    · rw [←hn,card_map_of_injective (componentOrbit V (T : Subgroup G)).subtype_injective,
        binarySubgroup_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
        S.setup.naturalCoordinates.finrank_eq]
      simp only [BinaryLinear.OuterCyclic.Space,Module.finrank_pi,Fintype.card_fin]
    · change Nat.card ((binarySubgroup (S.setup.dualHyperplane
        ⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩)).map
        (componentOrbit V (T : Subgroup G)).subtype) = _
      rw [card_map_of_injective (componentOrbit V (T : Subgroup G)).subtype_injective,
        binarySubgroup_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
        S.setup.dualHyperplane_finrank _ hw]

/-- Two disjoint nontrivial marked images in the component quotient exclude
J₄, whose Sylow two-subgroups have center of order two. -/
theorem pure_component_not_janko_four
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hs : S.MarkedAmbientSylow hTM)
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (hfix : (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
      S.setup.naturalFixed (S.setup.naturalSylowNormalizer
        ((T.subtype hTM).mapSurjective B.actionProjection_surjective)))
    (K : Subgroup (B.pointCentralizer w)) [K.Normal]
    (hX : (B.pointResidual w).subgroupOf (B.pointCentralizer w) ≤ K)
    (hU : B.naturalSummand ⊔ S.pureDualHyperplane w hp ≤ K.map (B.pointCentralizer w).subtype)
    (hc : center K = pCore 2 K) (e : (K ⧸ pCore 2 K) ≃* Janko4.Model) : False := by
  let H := B.pointCentralizer w
  let N := B.naturalSummand
  let D := S.pureDualHyperplane w hp
  let U := N ⊔ D
  let j : K →* G := H.subtype.comp K.subtype
  have hj : Function.Injective j := H.subtype_injective.comp K.subtype_injective
  let A := N.comap j
  let C := D.comap j
  let R := U.comap j
  let q := QuotientGroup.mk' (pCore 2 K)
  have hrange : U ≤ j.range := by
    simpa only [j,MonoidHom.range_comp,range_subtype] using hU
  have hAm : A.map j = N := map_comap_eq_self (le_sup_left.trans hrange)
  have hCm : C.map j = D := map_comap_eq_self (le_sup_right.trans hrange)
  have hRm : R.map j = U := map_comap_eq_self hrange
  have hUW : U ≤ componentOrbit V (T : Subgroup G) := sup_le B.naturalSummand_le
    ((S.pureDualHyperplane_le_dualSummand w hp).trans B.dualSummand_le)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (inclusion hUW) (inclusion_injective hUW)
  let : IsElementaryAbelian 2 R := IsElementaryAbelian.comap_of_injective j hj U
  have hAR : A ≤ R := comap_mono le_sup_left
  have hCR : C ≤ R := comap_mono le_sup_right
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
    (inclusion hAR) (inclusion_injective hAR)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_injective
    (inclusion hCR) (inclusion_injective hCR)
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  let : IsElementaryAbelian 2 (C.map q) := IsElementaryAbelian.map q
  have hker : (R ⊓ q.ker).map j = zpowers (w : G) := by
    rw [map_inf _ _ _ hj,hRm,QuotientGroup.ker_mk',←hc]
    change U ⊓ (center K).map (H.subtype.comp K.subtype) = _
    rw [←map_map]
    exact S.pure_moving_center_intersection w hw hp K hX hU
  have hkcard : Nat.card (R ⊓ q.ker : Subgroup K) = 2 := by
    rw [←card_map_of_injective hj,hker,Nat.card_zpowers]
    exact orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : G) w.property)
      (fun he => hw (Subtype.ext he))
  have hkerA : R ⊓ q.ker ≤ A := by
    intro x hx
    have hh := hker ▸ mem_map_of_mem j hx
    exact (zpowers_le.mpr ((B.mem_naturalSummand w).mpr hp)) hh
  have hAC : A ⊓ C = ⊥ := by
    apply map_injective hj
    rw [map_inf _ _ _ hj,hAm,hCm,Subgroup.map_bot]
    exact le_bot_iff.mp ((inf_le_inf_left _ (S.pureDualHyperplane_le_dualSummand w hp)).trans
      B.naturalSummand_inf_dualSummand.le)
  have himages : Disjoint (A.map q) (C.map q) := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    rintro y ⟨⟨a,ha,hay⟩,⟨c,hc',hcy⟩⟩
    have hak : a*c⁻¹ ∈ q.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv,hay,hcy,mul_inv_cancel]
    have haA : a*c⁻¹ ∈ A := hkerA ⟨R.mul_mem (hAR ha) (R.inv_mem (hCR hc')),hak⟩
    have hcA : c ∈ A := by
      have hh := A.mul_mem (A.inv_mem haA) ha
      simpa only [mul_inv_rev,inv_inv,inv_mul_cancel_right] using hh
    have hc1 : c = 1 := mem_bot.mp (hAC ▸ (show c ∈ A ⊓ C from ⟨hcA,hc'⟩))
    simpa only [mem_bot,hc1,map_one] using hcy.symm
  obtain ⟨hncard,hdcard⟩ := S.pure_summand_cards w hw hp
  have hnon (E : Subgroup K) [IsElementaryAbelian 2 E]
      (hER : E ≤ R) (hsize : 2 < Nat.card E) : E.map q ≠ ⊥ := by
    intro he
    have hec := IsElementaryAbelian.card_inf_ker_mul_card_map E q
    rw [he] at hec
    rw [show Nat.card (⊥ : Subgroup (K ⧸ pCore 2 K)) = 1 from by simp, mul_one] at hec
    have hbound := card_le_of_le (inf_le_inf_right q.ker hER)
    rw [hkcard] at hbound
    omega
  have hAn : A.map q ≠ ⊥ := hnon A hAR (by
    rw [←card_map_of_injective hj,hAm,hncard]
    rcases B.degree with rfl | rfl <;> decide)
  have hCn : C.map q ≠ ⊥ := hnon C hCR (by
    rw [←card_map_of_injective hj,hCm,hdcard]
    rcases B.degree with rfl | rfl <;> decide)
  obtain ⟨P₁,hP₀⟩ := hs w hw hp hfix
  let P₀ : Sylow 2 H := P₁
  have hPm : (P₀ : Subgroup H).map H.subtype = B.pointSylow w :=
    hP₀.trans (S.marked_centralizer_eq hTM w hw hp hfix).symm
  obtain ⟨P,hP⟩ := P₀.exists_subgroupOf_eq_of_normal K
  have hloc (x : K) (hx : x ∈ (P : Subgroup K)) : j x ∈ B.localPointCentralizer w := by
    have hxP : (x : H) ∈ (P₀ : Subgroup H) := by rw [hP] at hx; exact hx
    have ht := hPm ▸ mem_map_of_mem H.subtype hxP
    exact ⟨hTM ht.1,ht.2⟩
  have hPN : (P : Subgroup K) ≤ normalizer (A : Set K) := by
    apply le_trans _ (N.le_normalizer_comap j)
    intro x hx
    have hxP : (x : H) ∈ (P₀ : Subgroup H) := by rw [hP] at hx; exact hx
    have ht := hPm ▸ mem_map_of_mem H.subtype hxP
    change j x ∈ normalizer (B.naturalSummand : Set G)
    change j x ∈ (T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G) at ht
    rw [S.marked_centralizer_eq hTM w hw hp hfix] at ht
    exact ht.2
  have hPD : (P : Subgroup K) ≤ normalizer (C : Set K) := by
    apply le_trans _ (D.le_normalizer_comap j)
    intro x hx
    have hm := hloc x hx
    have hd := S.pure_centralizer_le_dualNormalizer w hw hp hm
    have hr := B.localPointCentralizer_normalizes_residual w hm
    change j x ∈ normalizer (S.pureDualHyperplane w hp : Set G)
    rw [←(S.pure_residual_commutators hNM w hw hp).2,
      mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp hd,mem_normalizer_iff_map_conj_eq.mp hr]
  let Pq := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 K))
  have hPqA : (Pq : Subgroup (K ⧸ pCore 2 K)) ≤ normalizer (A.map q : Set (K ⧸ pCore 2 K)) :=
    (map_mono hPN).trans (le_normalizer_map q)
  have hPqC : (Pq : Subgroup (K ⧸ pCore 2 K)) ≤ normalizer (C.map q : Set (K ⧸ pCore 2 K)) :=
    (map_mono hPD).trans (le_normalizer_map q)
  let Pj : Sylow 2 Janko4.Model := Pq.mapSurjective (f := e.toMonoidHom) e.surjective
  let : IsElementaryAbelian 2 ((A.map q).map e.toMonoidHom) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 ((C.map q).map e.toMonoidHom) := IsElementaryAbelian.map _
  exact no_disjoint_normal_pair_of_sylow_center_two Pj (Janko4.sylow_center_card_two Pj)
    ((A.map q).map e.toMonoidHom) ((C.map q).map e.toMonoidHom)
    ((map_mono hPqA).trans (le_normalizer_map e.toMonoidHom))
    ((map_mono hPqC).trans (le_normalizer_map e.toMonoidHom))
    (fun he => hAn ((map_eq_bot_iff_of_injective _ e.injective).mp he))
    (fun he => hCn ((map_eq_bot_iff_of_injective _ e.injective).mp he))
    (disjoint_map e.injective himages)
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
