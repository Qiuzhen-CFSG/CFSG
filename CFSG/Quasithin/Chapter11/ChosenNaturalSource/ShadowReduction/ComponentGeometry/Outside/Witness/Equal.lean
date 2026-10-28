module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Models.Source
public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The equal-component R₁-Sylow construction

When K=L₁, the actual quotient action identifies T intersect C_G(K/O₂(K))
with R₁. The kernel is normal inside Gz, so Sylow restriction proves that
R₁ is Sylow there. The selected two-residual lies in that same kernel:
the alternative O²(H) ≤ K would force H ≤ M. Thus the literal subgroup
R₁ O²(H) lies in H, escapes M, and has an actual Sylow with image R₁.
It is normal relative to H and has the same embedded two-residual.

The original flag supplies the quotient identification and centerlessness;
neither Sylow status nor a subgroup witness is assumed. Generation one
remains with qt-d-1222-shadow-component-witness. The earlier geometry and
11.3.2 inputs retain their producers qt-d-1222-natural-local-geometry,
qt-d-1222-shadow-linear-geometry, qt-d-1222-shadow-component-triangle and
qt-d-1222-shadow-component-comparison, with final discharge by
qt-d-1222-shadow-components.

Source: Aschbacher--Smith, 11.4.3 and 11.5.1, printed pp.778--779.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

omit [Finite G] in
/-- A normalizing subgroup with trivial quotient commutators lies in the literal action kernel. -/
theorem coreCentralizer_of_commutator {A B : Subgroup G}
    (hn : B ≤ normalizer (A : Set G)) (hc : ⁅B,A⁆ ≤ A.pCoreIn 2) :
    B ≤ Closure.coreQuotientCentralizer A := by
  intro b hb
  refine ⟨⟨b,hn hb⟩,?_,rfl⟩
  apply MulEquiv.ext
  intro x
  induction x using Quotient.inductionOn with | h a =>
    rw [show (⟦a⟧ : A ⧸ pCore 2 A) = QuotientGroup.mk' (pCore 2 A) a from rfl,
      Closure.coreQuotientAction_apply_mk]
    have hh := hc (commutator_mem_commutator hb a.property)
    change b * (a : G) * b⁻¹ * (a : G)⁻¹ ∈ A.pCoreIn 2 at hh
    obtain ⟨k,hk,he⟩ := hh
    have he' : k = A.normalizerMonoidHom ⟨b,hn hb⟩ a * a⁻¹ := Subtype.ext he
    rw [he'] at hk
    have hq := (QuotientGroup.eq_one_iff (N := pCore 2 A) _).mpr hk
    change QuotientGroup.mk' (pCore 2 A) (_ * a⁻¹) = 1 at hq
    rw [map_mul, map_inv] at hq
    exact mul_inv_eq_one.mp hq

/-- The Sylow radical is the actual kernel on the first component quotient. -/
theorem radical_eq_sylow_inf_coreCentralizer
    (hT : (T : Subgroup G) ≤ E.G₁) (hK : E.K = E.L₁)
    (hc : center (E.K ⧸ pCore 2 E.K) = ⊥) :
    E.R₁ = (T : Subgroup G) ⊓ Closure.coreQuotientCentralizer E.K := by
  have hn := hT.trans E.G₁_normalizes_K
  have hk := pCoreJoinAction_kernel 2 hn T.isPGroup' hc
  have hR : E.R₁ = (E.K ⊔ (T : Subgroup G)).pCoreIn 2 := by rw [hK]; rfl
  have hRT : E.R₁ ≤ (T : Subgroup G) := LocalGeometry.localRadical_le_sylow _
  apply le_antisymm
  · refine le_inf hRT ?_
    rw [hR]
    rintro _ ⟨r,hr,rfl⟩
    exact ⟨inclusion (sup_le E.K.le_normalizer hn) r,hk.ge hr,rfl⟩
  · rintro t ⟨ht,c,hc,hct⟩
    rw [hR]
    let t' : (E.K ⊔ (T : Subgroup G) : Subgroup G) := ⟨t,mem_sup_right ht⟩
    refine ⟨t',hk.le ?_,rfl⟩
    change Closure.coreQuotientAction E.K (inclusion (sup_le E.K.le_normalizer hn) t') = 1
    have he : inclusion (sup_le E.K.le_normalizer hn) t' = c := Subtype.ext hct.symm
    rw [he]
    exact hc

/-- Normality is inside Gz; restriction of its original Sylow gives R₁. -/
theorem radical_sylow_in_point_kernel (h : Comparison.EarlierGeometry E)
    (he : E.Kz = E.K) (hT : (T : Subgroup G) ≤ E.G₁) (hK : E.K = E.L₁)
    (hc : center (E.K ⧸ pCore 2 E.K) = ⊥) : Chapter1.IsSylowIn 2 E.R₁ (Yz E) := by
  let N := (Yz E).subgroupOf (Gz E)
  let : N.Normal := normal_subgroupOf_of_le_normalizer (point_normalizes_kernel E he)
  obtain ⟨P,hP⟩ := (T.subtype h.sylow_le_pointCentralizer).exists_subgroupOf_eq_of_normal N
  let e := subgroupOfEquivOfLe (show Yz E ≤ Gz E from inf_le_left)
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    obtain ⟨n,hn,rfl⟩ := hy
    rw [radical_eq_sylow_inf_coreCentralizer E hT hK hc]
    exact ⟨hP.le hn,n.property.2⟩
  · intro x hx
    have hx' := (radical_eq_sylow_inf_coreCentralizer E hT hK hc).le hx
    let n : N := ⟨⟨x,h.sylow_le_pointCentralizer hx'.1⟩,
      h.sylow_le_pointCentralizer hx'.1,hx'.2⟩
    refine ⟨e n,⟨n,?_,rfl⟩,rfl⟩
    exact hP.ge hx'.1

private theorem residual_sup_sylow {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H) :
    (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
  have he := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
  simpa only [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using he

/-- Passing from T to its characteristic local radical preserves relative normality. -/
theorem radical_carrier_normal (hTH : (T : Subgroup G) ≤ E.H) :
    ((E.R₁ ⊔ (pResidual 2 E.H).map E.H.subtype).subgroupOf E.H).Normal := by
  let N := (pResidual 2 E.H).map E.H.subtype
  let J := E.R₁ ⊔ N
  have hHN : E.H ≤ normalizer (N : Set G) := E.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image E.H (pResidual 2 E.H))
  have hTR : (T : Subgroup G) ≤ normalizer (E.R₁ : Set G) :=
    (le_sup_right : (T : Subgroup G) ≤ E.L₁ ⊔ (T : Subgroup G)).trans
      ((E.L₁ ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hTJ : (T : Subgroup G) ≤ normalizer (J : Set G) :=
    (le_inf hTR (hTH.trans hHN)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply normal_subgroupOf_of_le_normalizer
  change E.H ≤ normalizer (J : Set G)
  calc
    E.H = N ⊔ (T : Subgroup G) := (residual_sup_sylow hTH).symm
    _ ≤ normalizer (J : Set G) :=
      sup_le ((le_sup_right : N ≤ J).trans J.le_normalizer) hTJ

/-- The smaller carrier has exactly the same embedded two-residual as H. -/
theorem radical_carrier_residual (hTH : (T : Subgroup G) ≤ E.H) :
    (pResidual 2 (E.R₁ ⊔ (pResidual 2 E.H).map E.H.subtype : Subgroup G)).map
      (E.R₁ ⊔ (pResidual 2 E.H).map E.H.subtype).subtype =
        (pResidual 2 E.H).map E.H.subtype := by
  let N := (pResidual 2 E.H).map E.H.subtype
  have hHN : E.H ≤ normalizer (N : Set G) := E.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image E.H (pResidual 2 E.H))
  have hn : E.R₁ ≤ normalizer (N : Set G) :=
    (LocalGeometry.localRadical_le_sylow _).trans (hTH.trans hHN)
  have hp : IsPPerfect 2 N := (isPPerfect_pResidual 2).of_surjective
    ((pResidual 2 E.H).equivMapOfInjective E.H.subtype E.H.subtype_injective).toMonoidHom
    ((pResidual 2 E.H).equivMapOfInjective E.H.subtype E.H.subtype_injective).surjective
  change (pResidual 2 (E.R₁ ⊔ N : Subgroup G)).map (E.R₁ ⊔ N).subtype = N
  rw [sup_comm E.R₁ N]
  exact embedded_pResidual_join_pGroup N E.R₁ hp (isPGroup_pCoreIn _ _) hn

/-- The selected residual lies in the literal quotient centralizer in the equality row. -/
theorem selected_residual_le_point_kernel (he : E.Kz = E.K) (hK : E.K = E.L₁)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M) (hHz : E.H ≤ Gz E)
    (hs : SelectedResidualAlternative E) : (pResidual 2 E.H).map E.H.subtype ≤ Yz E := by
  have hN : (pResidual 2 E.H).map E.H.subtype ≤ E.H := map_subtype_le _
  have hc : ⁅E.K,(pResidual 2 E.H).map E.H.subtype⁆ ≤ E.K.pCoreIn 2 := by
    apply hs.resolve_right
    intro hNK
    have hNM : (pResidual 2 E.H).map E.H.subtype ≤ E.M :=
      hNK.trans (hK ▸ E.L₁_le.trans L.le_normalizer)
    exact hH.1.2 ((residual_sup_sylow hH.1.1.2).symm ▸
      sup_le hNM D.sylow_normalizes_component)
  refine le_inf (hN.trans hHz) (coreCentralizer_of_commutator
    (hN.trans (hHz.trans (point_normalizes_component E he))) ?_)
  simpa only [commutator_comm] using hc

/-- The explicit R₁ O²(H) carrier, including escape and an actual Sylow witness.
Generation one is a separate remaining source obligation. -/
theorem equal_selected_radical_carrier (h : Comparison.EarlierGeometry E)
    (he : E.Kz = E.K) (hT : (T : Subgroup G) ≤ E.G₁) (hK : E.K = E.L₁)
    (hc : center (E.K ⧸ pCore 2 E.K) = ⊥)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M) (hHz : E.H ≤ Gz E)
    (hs : SelectedResidualAlternative E) :
    let J := E.R₁ ⊔ (pResidual 2 E.H).map E.H.subtype
    J ≤ E.H ∧ ¬ J ≤ E.M ∧ Chapter1.IsSylowIn 2 E.R₁ J ∧ J ≤ Yz E := by
  have hN : (pResidual 2 E.H).map E.H.subtype ≤ E.H := map_subtype_le _
  have hRT : E.R₁ ≤ (T : Subgroup G) := LocalGeometry.localRadical_le_sylow _
  have hSyl := radical_sylow_in_point_kernel E h he hT hK hc
  have hRY := (Chapter1.isSylowIn_iff.mp hSyl).2.1
  have hJY := sup_le hRY (selected_residual_le_point_kernel E he hK hH hHz hs)
  refine ⟨sup_le (hRT.trans hH.1.1.2) hN,?_,hSyl.restrict le_sup_left hJY,hJY⟩
  intro hJM
  apply hH.1.2
  rw [← residual_sup_sylow hH.1.1.2]
  exact sup_le (le_sup_right.trans hJM) D.sylow_normalizes_component

variable (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H₀ : Subgroup G)

private theorem flag_quotient :
    Nonempty ((f.Li 0 ⧸ pCore 2 (f.Li 0)) ≃* Theory.PSL2.Group S.field.Carrier) := by
  obtain ⟨f₀, hu, _, hm, _⟩ := LocalGeometry.exists_unique_marked_flag D S c
  have he : f.Li 0 = f₀.Li 0 := congrArg
    (fun U => LocalGeometry.localResidual L (c.preimage U))
    (hu 0 _ (f.dimension 0) (f.invariant 0))
  rw [he]
  exact hm 0

/-- The original first flag residual has centerless two-core quotient. -/
theorem ofFlag_first_quotient_center :
    center (f.Li 0 ⧸ pCore 2 (f.Li 0)) = ⊥ := by
  let e := (flag_quotient S f).some
  apply bot_unique
  intro a ha
  apply e.injective
  have he : e a ∈ center (Theory.PSL2.Group S.field.Carrier) :=
    MulEquivClass.apply_mem_center e ha
  rw [GorensteinWalter.psl2_center_eq_bot S.field.Carrier,mem_bot] at he
  exact he.trans e.map_one.symm

/-- Centerlessness is proved from the actual original flag quotient. -/
theorem ofFlag_equal_quotient_center
    (hK : (ofFlag S f X z H₀).K = (ofFlag S f X z H₀).L₁) :
    center ((ofFlag S f X z H₀).K ⧸ pCore 2 (ofFlag S f X z H₀).K) = ⊥ := by
  rw [hK]
  exact ofFlag_first_quotient_center S f

/-- Selection and the R₁-Sylow carrier on the unchanged chosen flag. -/
theorem ofFlag_equal_selected_radical_carrier
    (h : Comparison.EarlierGeometry (ofFlag S f X z H₀))
    (he : (ofFlag S f X z H₀).Kz = (ofFlag S f X z H₀).K)
    (hK : (ofFlag S f X z H₀).K = (ofFlag S f X z H₀).L₁)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H₀).point J →
      Proposition1132At D S (ofFlag S f X z H₀).point J) :
    ∃ H, H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      H ≤ Gz (ofFlag S f X z H₀) ∧ SelectedResidualAlternative (ofFlag S f X z H) ∧
      let J := (ofFlag S f X z H).R₁ ⊔ (pResidual 2 H).map H.subtype
      J ≤ H ∧ ¬ J ≤ normalizer (L : Set G) ∧
        Chapter1.IsSylowIn 2 (ofFlag S f X z H).R₁ J ∧ J ≤ Yz (ofFlag S f X z H) := by
  obtain ⟨H,hH,hHz,hs⟩ := Models.ofFlag_equal_selected_H S f X z H₀ h he hK
    (flag_quotient S f) hNT h1132
  refine ⟨H,hH,hHz,hs,?_⟩
  have h' : Comparison.EarlierGeometry (ofFlag S f X z H) :=
    ⟨h.point_mem,h.point_fixed,h.point_ne_one,h.seed_centralizes,
      h.line_component,h.point_component,h.normalizer_split⟩
  exact equal_selected_radical_carrier (ofFlag S f X z H) h' he (f.invariant 0) hK
    (ofFlag_equal_quotient_center S f X z H₀ hK) hH hHz hs

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside
