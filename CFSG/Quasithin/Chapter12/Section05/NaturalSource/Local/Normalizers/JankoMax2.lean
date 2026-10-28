module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Normalizers.JankoNativeParabolic
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First.ScalarKernel

/-!
# The original cubic survives the first-centralizer projection

The original Y = O²(P) is two-perfect and is normalized by M1*. If its
image through the first centralizer's M22 projection were a two-group,
the native scalar-kernel theorem would put the original point parabolic
in that centralizer. The previously proved parabolic exclusion rules this
out. The original index-three Sylow in P then makes three divide this
same image, retaining the whole cubic covering kernel.

The actual solvable Y-closure and original full Sylow now apply the native
M22 actor bound: the same projected actor has order dividing 2^21 times 9.
No parabolic or actor placement is assumed beyond the specified max2
actor branch. JankoMax2Actor compares this bound with the original
two-parabolic intersection and proves the ambient normalizer containment.
Final native-cover discharge remains with qt-d-1251-local, and final
exterior discharge is qt-d-1251-source.

Source: Aschbacher–Smith, 12.5.4, printed p.819/PDF p.836.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}
namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)
open Janko4.InvolutionCentralizers.First.QuotientExtension
local notation "C₂" => Janko4.InvolutionCentralizers.First.centralizer

/-- The same original residual has a cubic image through the full native M22 map. -/
theorem point_projection_janko_max2_cubic_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (i : ℕ) (hi : i = 3 ∨ i = 6)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤ C₂) :
    let U := ((s.pointCoreImage s.Y).subgroupOf (s.pointCoreImage K)).map e.toMonoidHom
    U.subgroupOf C₂ ≤ H ∧
      3 ∣ Nat.card (((U.subgroupOf C₂).subgroupOf H).map mathieuProjection) := by
  have hYK := s.Y_le_point_component_of_large_model h hK hN
    (.inr (.inr ⟨(s.pointComponentCoreEquivImage hK.1 hN).trans e⟩))
  let C := s.pointCoreImage K
  let Y₀ := s.pointCoreImage s.Y
  let Y := Y₀.subgroupOf C
  let U := Y.map e.toMonoidHom
  let A := (s.localPointProjection K i).subgroupOf C
  let P := s.pointComponentParabolic K
  let Uc := U.subgroupOf C₂
  let Uh := Uc.subgroupOf H
  have hYC : Y₀ ≤ C := s.pointCoreImage_mono hYK
  have hYA : Y ≤ A := by
    apply comap_mono
    exact le_inf hYC ((s.pointCoreImage_mono (le_inf
      ((s.Y_le_local_residual i hi).trans (s.marking.Li_le_Gi i))
      ((map_subtype_le _).trans (s.P_le_M₁.trans inf_le_right)))).trans le_sup_left)
  have hUC : U ≤ C₂ := (map_mono hYA).trans hactor
  have hp₀ : IsPPerfect 2 Y₀ := (isPPerfect_embedded_pResidual 2 s.P).of_surjective
    (s.pointCoreImageHom s.Y ((map_subtype_le _).trans (s.P_le_M₁.trans inf_le_right)))
    (s.pointCoreImageHom_surjective _ _)
  have hpY : IsPPerfect 2 Y := hp₀.of_surjective
    (subgroupOfEquivOfLe hYC).symm.toMonoidHom (subgroupOfEquivOfLe hYC).symm.surjective
  have hpU : IsPPerfect 2 U := hpY.of_surjective
    (e.subgroupMap Y).toMonoidHom (e.subgroupMap Y).surjective
  have hpUc : IsPPerfect 2 Uc := hpU.of_surjective
    (subgroupOfEquivOfLe hUC).symm.toMonoidHom (subgroupOfEquivOfLe hUC).symm.surjective
  have hUH : Uc ≤ H := by
    have ht : IsPGroup 2 (Multiplicative (ZMod 2)) := IsPGroup.of_card (n := 1) (by simp)
    have he := hpUc.hom_eq_one_of_isPGroup ht (centralizerOuterCharacter.comp Uc.subtype)
    intro x hx
    rw [←centralizerOuterCharacter_ker]
    exact DFunLike.congr_fun he ⟨x,hx⟩
  have hpUh : IsPPerfect 2 Uh := hpUc.of_surjective
    (subgroupOfEquivOfLe hUH).symm.toMonoidHom (subgroupOfEquivOfLe hUH).symm.surjective
  let d : Uh ≃* Y₀ := (subgroupOfEquivOfLe hUH).trans
    ((subgroupOfEquivOfLe hUC).trans ((e.subgroupMap Y).symm.trans (subgroupOfEquivOfLe hYC)))
  have hUnot : ¬ IsPGroup 2 Uh := fun ht => s.pointCoreImage_Y_not_two (ht.of_equiv d)
  have hPN : P ≤ normalizer (Y : Set C) := by
    intro p hp y
    exact s.pointCoreImage_M₁_normalizes_Y hp
      (y : s.marking.Gi 1 ⧸ pCore 2 (s.marking.Gi 1))
  have hPU : P.map e.toMonoidHom ≤ normalizer (U : Set Janko4.Model) :=
    (map_mono hPN).trans (Y.le_normalizer_map e.toMonoidHom)
  have hmap : Uh.map (((C₂).subtype).comp H.subtype) = U := by
    rw [←map_map, map_subgroupOf_eq_of_le hUH, map_subgroupOf_eq_of_le hUC]
  obtain ⟨S,hS,hSA⟩ := s.point_projection_contains_original_sylow hN i hi
  have hSP : (S : Subgroup C) ≤ P := by
    rw [hS]
    exact comap_mono (s.pointCoreImage_mono (le_inf le_sup_right s.sylow_le_G₁))
  let Se := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hnon := non_two_mathieu_image_of_external_normalizer Se
    ((map_mono hSA).trans hactor) (P.map e.toMonoidHom) (map_mono hSP)
    (s.pointComponentParabolic_not_janko_firstCentralizer h hK hLK hN e)
    Uh hpUh hUnot (hmap.symm ▸ hPU)
  refine ⟨hUH, ?_⟩
  by_contra hthree
  apply hnon
  have hdiv : Nat.card (Uh.map mathieuProjection) ∣ Nat.card s.P := by
    have hd := Uh.card_map_dvd mathieuProjection
    rw [Nat.card_congr d.toEquiv] at hd
    apply hd.trans
    apply (card_dvd_of_surjective
      (s.pointCoreImageHom s.Y ((map_subtype_le _).trans (s.P_le_M₁.trans inf_le_right)))
      (s.pointCoreImageHom_surjective _ _)).trans
    exact card_dvd_of_le (map_subtype_le (pResidual 2 s.P))
  obtain ⟨n,hn⟩ := T.isPGroup'.exists_card_eq
  have hc := ((T : Subgroup G).subgroupOf s.P).card_mul_index
  change Nat.card ((T : Subgroup G).subgroupOf s.P) *
    (T : Subgroup G).relIndex s.P = Nat.card s.P at hc
  rw [Nat.card_congr (subgroupOfEquivOfLe s.sylow_le_P).toEquiv,
    hn, s.sylow_relIndex_P] at hc
  rw [←hc] at hdiv
  exact IsPGroup.of_card_dvd_pow
    ((Nat.prime_three.coprime_iff_not_dvd.mpr hthree).symm.dvd_of_dvd_mul_right hdiv)

private theorem solvable_of_injective_map {B F : Type*} [Group B] [Group F]
    (f : B →* F) (hf : Function.Injective f) (A : Subgroup B)
    (hs : Group.IsSolvable (A.map f)) : Group.IsSolvable A := by
  let := hs
  exact Group.isSolvable_of_isSolvable_injective
    (f := (A.equivMapOfInjective f hf).toMonoidHom) (A.equivMapOfInjective f hf).injective

/-- The source solvable closure bounds the original max2 actor, with its full Sylow retained. -/
theorem point_projection_janko_max2_card_dvd
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) {K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn (s.marking.Gi 1))
    (hLK : s.marking.Li 1 ≤ K) (hN : (K.subgroupOf (s.marking.Gi 1)).Normal)
    (e : s.pointCoreImage K ≃* Janko4.Model)
    (i : ℕ) (hi : i = 3 ∨ i = 6)
    (hactor : ((s.localPointProjection K i).subgroupOf (s.pointCoreImage K)).map
      e.toMonoidHom ≤ C₂) :
    Nat.card (s.localPointProjection K i) ∣ 2^21 * 9 := by
  have hYK := s.Y_le_point_component_of_large_model h hK hN
    (.inr (.inr ⟨(s.pointComponentCoreEquivImage hK.1 hN).trans e⟩))
  let C := s.pointCoreImage K
  let Y := (s.pointCoreImage s.Y).subgroupOf C
  let A := (s.localPointProjection K i).subgroupOf C
  let U := Y.map e.toMonoidHom
  let Ae := A.map e.toMonoidHom
  let Uc := U.subgroupOf C₂
  let Ac := Ae.subgroupOf C₂
  let N := conjugateSpanBy Uc Ac
  have hYC : s.pointCoreImage s.Y ≤ C := s.pointCoreImage_mono hYK
  have hYA : Y ≤ A := by
    apply comap_mono
    exact le_inf hYC ((s.pointCoreImage_mono (le_inf
      ((s.Y_le_local_residual i hi).trans (s.marking.Li_le_Gi i))
      ((map_subtype_le _).trans (s.P_le_M₁.trans inf_le_right)))).trans le_sup_left)
  have hUC : U ≤ C₂ := (map_mono hYA).trans hactor
  have hNA : N ≤ Ac := conjugateSpanBy_le (comap_mono (map_mono hYA)) Ac.le_normalizer
  have hsource : (conjugateSpanBy Y A).map C.subtype =
      conjugateSpanBy (s.pointCoreImage s.Y) (s.localPointProjection K i) := by
    rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le hYC,
      map_subgroupOf_eq_of_le (show s.localPointProjection K i ≤ C from inf_le_left)]
  have hsol : Group.IsSolvable (conjugateSpanBy Y A) :=
    solvable_of_injective_map C.subtype C.subtype_injective _
      (hsource.symm ▸ s.projected_Y_span_solvable h hN hYK i hi)
  have heSol : Group.IsSolvable (conjugateSpanBy U Ae) := by
    change Group.IsSolvable (conjugateSpanBy (Y.map e.toMonoidHom) (A.map e.toMonoidHom))
    rw [←map_conjugateSpanBy]
    let := hsol
    exact Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective _)
  have hNmap : N.map (C₂).subtype = conjugateSpanBy U Ae := by
    rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le hUC,
      map_subgroupOf_eq_of_le hactor]
  have hNs : Group.IsSolvable N := solvable_of_injective_map (C₂).subtype
    (C₂).subtype_injective _ (hNmap.symm ▸ heSol)
  have h3 : 3 ∣ Nat.card ((N.subgroupOf H).map mathieuProjection) :=
    (s.point_projection_janko_max2_cubic_image h hK hLK hN e i hi hactor).2.trans
      (card_dvd_of_le (map_mono (comap_mono (le_conjugateSpanBy Uc Ac))))
  obtain ⟨S, _, hSA⟩ := s.point_projection_contains_original_sylow hN i hi
  let Se := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hSe : (Se : Subgroup Janko4.Model) ≤ C₂ := (map_mono hSA).trans hactor
  have hc := actor_card_dvd_of_solvable_normal_three (Se.subtype hSe) Ac N
    (comap_mono (map_mono hSA)) hNA (le_normalizer_conjugateSpanBy Uc Ac) hNs h3
  let d : Ac ≃* s.localPointProjection K i := (subgroupOfEquivOfLe hactor).trans
    ((e.subgroupMap A).symm.trans (subgroupOfEquivOfLe inf_le_left))
  rwa [Nat.card_congr d.toEquiv] at hc

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
