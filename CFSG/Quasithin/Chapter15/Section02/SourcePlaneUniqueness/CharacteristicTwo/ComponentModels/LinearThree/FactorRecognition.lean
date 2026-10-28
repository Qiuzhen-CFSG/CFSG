module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.PairApplications

public import Theory.GroupTheory.PResidual.CoreNormalized
public import Theory.GroupTheory.CubicAutomorphismLines.FourActors

/-!
# Recognition of the two cubic residual factors

The literal wreath quotient of H identifies its action on K/O₂(K) with
D₈. A Sylow subgroup maps onto this action, so the index-two subgroup S
has action image of order at least four. Restriction to the two cubic
lines of the constructed residual pair then gives independent inversions.
Consequently those two lines exhaust the S-invariant cubic lines.

For an S-invariant two-perfect candidate E, reducibility puts O₂(K) in S.
Thus E is normalized by O₂(K) and is the two-residual of its quotient-line
preimage. This gives relative normality in K and recovers E from the
recognized line. No assertion is made about arbitrary subgroups in an
extension, or about a lone diagonal inverter.

Source: Aschbacher--Smith, original 15.2.21 and the calculation (*) in
15.2.23, printed pp.1114 and 1116; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
open Chapter13.Section08.Components.Swapped.LinearThree
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem local_normalizes (H : Subgroup G) :
    H ≤ normalizer (smallActionK H : Set G) :=
  H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))

private def localActor (H : Subgroup G) :
    H →* MulAut ((smallActionK H) ⧸ pCore 2 (smallActionK H)) :=
  (normalCubicQuotientAction (smallActionK H)).comp (inclusion (local_normalizes H))

private theorem localActor_card (H : Subgroup G)
    (hw : (H ⧸ pCore 2 H) ≃* ChosenGeometry.Wreath) :
    Nat.card (localActor H).range = 8 := by
  let a : pResidual 2 H ≃* smallActionK H :=
    (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let q := QuotientGroup.congr (pCore 2 (pResidual 2 H))
    (pCore 2 (smallActionK H)) a (pCore_map_iso 2 a)
  let c := MulAut.congr q
  have he : localActor H = c.toMonoidHom.comp (ResidualAction.action (X := H)) := by
    ext x z
    obtain ⟨z,rfl⟩ := q.surjective z
    induction z using Quotient.inductionOn with
    | h z =>
      change quotientAut (pCore 2 (smallActionK H))
        ((smallActionK H).normalizerMonoidHom (inclusion (local_normalizes H) x))
          (q (QuotientGroup.mk' _ z)) =
        q (ResidualAction.action x (q.symm (q (QuotientGroup.mk' _ z))))
      rw [q.symm_apply_apply]
      have hq (y : pResidual 2 H) : q (QuotientGroup.mk' _ y) =
          QuotientGroup.mk' (pCore 2 (smallActionK H)) (a y) :=
        QuotientGroup.congr_mk' _ _ _ _ y
      change _ = q (quotientAut _ (MulAut.conjNormal x) (QuotientGroup.mk' _ z))
      rw [hq,quotientAut_apply_mk,quotientAut_apply_mk,hq]
      rfl
  rw [he,MonoidHom.range_comp,card_map_of_injective c.injective]
  exact (Nat.card_congr
    (ResidualAction.actionEquivDihedral (hw.trans ChosenGeometry.matrixWreathEquiv)).toEquiv).trans
      (by rw [DihedralGroup.nat_card])

private theorem sylow_image_full {A D : Type*} [Group A] [Finite A] [Group D]
    (f : A →* D) (P : Sylow 2 A) (hp : IsPGroup 2 f.range) :
    (P : Subgroup A).map f = f.range := by
  let q := f.rangeRestrict
  have hq := f.rangeRestrict_surjective
  let R := P.mapSurjective hq
  have hR : (R : Subgroup f.range) = ⊤ := (R.is_maximal' (hp.to_subgroup ⊤) le_top).symm
  have hh := congrArg (map f.range.subtype) hR
  change ((P : Subgroup A).map q).map f.range.subtype = _ at hh
  rw [map_map,← MonoidHom.range_eq_map,range_subtype] at hh
  exact hh

private theorem half_image_card {A D : Type*} [Group A] [Finite A] [Group D]
    (f : A →* D) (hcard : Nat.card f.range = 8) (S : Subgroup A) (hi : S.index = 2) :
    4 ≤ Nat.card (S.map f) := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let q := f.rangeRestrict
  let B := S.map q
  let : Finite (Quotient (QuotientGroup.leftRel B)) := Quotient.finite _
  have hd : B.index ∣ 2 := hi ▸ S.index_map_dvd f.rangeRestrict_surjective
  have hb := B.card_mul_index
  have hi0 : 0 < B.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have hile : B.index ≤ 2 := Nat.le_of_dvd (by decide) hd
  rw [hcard] at hb
  have he : Nat.card (S.map f) = Nat.card B := by
    have hh := card_subtype f.range B
    rw [show B.map f.range.subtype = S.map f from by rw [map_map]; rfl] at hh
    exact hh
  rw [he]
  nlinarith

variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include d in
theorem source_plane_actor_card_ge_four (hI : PlaneEscapes Mc ZS I) :
    4 ≤ Nat.card (((planeSylow T ZS).subgroupOf (normalizer (smallActionK H : Set G))).map
      (normalCubicQuotientAction (smallActionK H))) := by
  let f := localActor H
  have hcard : Nat.card f.range = 8 := localActor_card H d.geometry.quotient.some
  have hp : IsPGroup 2 f.range := IsPGroup.of_card (n := 3) hcard
  have hTH : (T : Subgroup G) ≤ H := by
    have hout : H ∈ Chapter1.HOver G (T : Set G) ∧ ¬ H ≤ M := d.geometry.outside.1
    exact hout.1.2
  let P := T.subtype hTH
  have hfull := sylow_image_full f P hp
  let g := f.comp (inclusion hTH)
  have hP : (P : Subgroup H) = (T : Subgroup G).subgroupOf H := by
    ext x
    rfl
  have hg : g.range = f.range := by
    simpa [g, MonoidHom.range_comp, inclusion_range, hP] using hfull
  have hS := half_image_card g (hg ▸ hcard)
    ((planeSylow T ZS).subgroupOf (T : Subgroup G)) (d.escape_index hI).2
  have hmap : ((planeSylow T ZS).subgroupOf (T : Subgroup G)).map g =
      ((planeSylow T ZS).subgroupOf (normalizer (smallActionK H : Set G))).map
        (normalCubicQuotientAction (smallActionK H)) := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨⟨t,(local_normalizes H) (hTH t.property)⟩,ht,rfl⟩
    · rintro ⟨s,hs,rfl⟩
      exact ⟨⟨s,hs.1⟩,hs,rfl⟩
  rwa [hmap] at hS


include d in
/-- The actual Sylow action recognizes every invariant two-perfect cubic
candidate as one of the two constructed normal residual factors. -/
theorem classify_residualPair (hI : PlaneEscapes Mc ZS I)
    (hnot : ¬ IsSmallActionIrreducible (planeSylow T ZS) (smallActionK H))
    {t : G}
    (p : SmallActionsSource.ResidualPair (T : Subgroup G) (planeSylow T ZS)
      (smallActionK H) t)
    (E : Subgroup G) (hEK : E ≤ smallActionK H) (hp : IsPPerfect 2 E)
    (hc : Nat.card (E ⧸ pCore 2 E) = 3)
    (hSE : planeSylow T ZS ≤ normalizer (E : Set G)) :
    E = p.K₁ ∨ E = p.K₂ := by
  let K := smallActionK H
  let Q := K ⧸ pCore 2 K
  let S := planeSylow T ZS
  let e := ChosenGeometry.residualQuotientEquiv H d.geometry.quotient.some
  let : IsElementaryAbelian 3 Q :=
    IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  have hKS : K.pCoreIn 2 ≤ S :=
    (pCoreIn_mono_of_normalizes (map_subtype_le _) (local_normalizes H)).trans
      (SmallActionsSource.core_le_planeSylow_of_reducible d hI hnot)
  have hn : (E.subgroupOf K).Normal := by
    apply normal_of_isPPerfect_of_core_normalizes (p := 2)
    · exact hp.of_surjective (subgroupOfEquivOfLe hEK).symm.toMonoidHom
        (subgroupOfEquivOfLe hEK).symm.surjective
    · rw [← subgroupOf_normalizer_eq hEK]
      intro k hk
      exact hSE (hKS (mem_map_of_mem K.subtype hk))
  have hE : E ∈ normalCubicResiduals K := ⟨hEK,hn,hp,hc⟩
  let D := (S.subgroupOf (normalizer (K : Set G))).map (normalCubicQuotientAction K)
  have hD : 4 ≤ Nat.card D := source_plane_actor_card_ge_four d hI
  let A := normalCubicResidualImage K p.K₁
  let B := normalCubicResidualImage K p.K₂
  let C := normalCubicResidualImage K E
  have stable (L : Subgroup G) (hLK : L ≤ K) (hSL : S ≤ normalizer (L : Set G)) :
      ∀ a : D, ∀ z ∈ normalCubicResidualImage K L, (a : MulAut Q) z ∈
        normalCubicResidualImage K L := by
    intro a z hz
    obtain ⟨s,hs,he⟩ := a.property
    have hh := normalCubicResidualImage_conjugate K L hLK s
    have hconj : L.map (MulAut.conj (s : G)).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp (hSL hs)
    have hh' : normalCubicResidualImage K L =
        (normalCubicResidualImage K L).map (normalCubicQuotientAction K s).toMonoidHom := by
      simpa only [hconj] using hh
    have hm := mem_map_of_mem (normalCubicQuotientAction K s).toMonoidHom hz
    rw [← hh'] at hm
    change normalCubicQuotientAction K s z ∈ normalCubicResidualImage K L at hm
    rw [he] at hm
    exact hm
  have hgen : A ⊔ B = ⊤ := by
    change (p.K₁.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) ⊔
      (p.K₂.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) = ⊤
    rw [← Subgroup.map_sup,← subgroupOf_sup p.first.1 p.second.1,p.span,
      subgroupOf_self,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hh := CubicAutomorphismLines.invariant_eq_of_four_actors
    D.subtype D.subtype_injective hD A B C
    (normalCubicResidualImage_card p.first) (normalCubicResidualImage_card p.second)
    (normalCubicResidualImage_card hE) hgen
    (stable _ p.first.1 p.normalized)
    (stable _ p.second.1 (p.second_normalized inf_le_left (d.escape_index hI).2))
    (stable _ hEK hSE)
  exact hh.imp (normalCubicResidualImage_injective hE p.first)
    (normalCubicResidualImage_injective hE p.second)

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
