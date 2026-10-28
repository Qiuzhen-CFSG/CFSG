module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFive
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFiveCore
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceSixSelection

/-!
# Original source-(6) regular element and moving conjugator

Reuse the generic symmetric-matrix selection internally, and lift it through
both full original endpoint quotients. The original plane cover and paired
midpoint indices discharge the selection premises. No minimal replacement
or new saturation premise is introduced.

Source: MS93 (3.7)(6), printed p.876, initial element and conjugator selection.
-/

public noncomputable section
open scoped Pointwise commutatorElement IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource SaturatedDistanceTwo
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
variable (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include h hshort hinner hnsyl

/-- Source (6)'s regular element and moving conjugator, selected on the
same full endpoint quotient. No non-normalization premise is assumed. -/
theorem original_source_six_exists_moving_regular_element
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (2^n)^2 ≤ (Q R z).relIndex (Z R a)) :
    ∃ x ∈ Z R z, x ∉ Q R a ∧
      Z R a ⊓ centralizer ({x} : Set (FreeAmalgam R))=Z R t ∧
      ∃ y ∈ stabilizer R a, y ∈ normalizer (Q R t : Set (FreeAmalgam R)) ∧
        y ∈ normalizer (x • (Q R a : Set (FreeAmalgam R))) ∧
        x⁻¹*(y*x*y⁻¹) ∈ Q R a ∧
        y ∉ normalizer (((Z R z ⊔ Q R a) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  let := h.component_normal
  obtain ⟨⟨cv⟩,_,hai,hzi,_⟩ := original_source_four_large_paired_geometry h hshort hinner hnsyl g hb path hat hzt hcritical
  rcases cv with ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩,
    hTS,β,hβmark,hact,hαker,⟨k,hk⟩⟩
  change Q R t →* L (K := E.Carrier) at β
  change Sp E.Carrier at k
  change ∀ u : Q R t, (e.groupEquiv.symm (β u) : _) = κ (inclusion hTS u) at hβmark
  change ∀ (u : Q R t) (w : (originalMovedSection h).space.toSubmodule),
    j (Multiplicative.ofAdd (MovedSection.coverAction (originalMovedSection h) e (β u) w)) =
      u.val*j (Multiplicative.ofAdd w)*u.val⁻¹ at hact
  change ((commutator (Sp E.Carrier)).subtype.comp β).range.map
    (MulAut.conj k).toMonoidHom=planeRadicalAmbient at hk
  have hq : 1<2^n := one_lt_pow₀ (by decide : 1<(2:ℕ)) (by have := h.nonbinary; omega)
  have hFc : Nat.card E.Carrier=2^n := by rw [E.card_eq,hE]
  have hCtop : (K.map (QuotientGroup.mk' (pCore 2 H)))=⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q=⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let S := stabilizer R a
  let κC := κ.codRestrict ((K.map (QuotientGroup.mk' (pCore 2 H)))) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  let ψ := (MulAut.conj k).toMonoidHom.comp ((commutator (Sp E.Carrier)).subtype.comp γ)
  have hγ (u : Q R t) : γ (inclusion hTS u)=β u := by
    apply e.groupEquiv.symm.injective
    apply Subtype.ext
    exact (congrArg Subtype.val (e.groupEquiv.symm_apply_apply
      (κC (inclusion hTS u)))).trans (hβmark u).symm
  have hψt (u : Q R t) : ψ (inclusion hTS u)=k*α u*k⁻¹ := by
    change k*(γ (inclusion hTS u)).val*k⁻¹=_
    rw [hγ]
    rfl
  have hκC_onto : Function.Surjective κC := by
    intro x
    obtain ⟨u,hu⟩ := hκ x.val
    exact ⟨u,Subtype.ext hu⟩
  have hγonto : Function.Surjective γ := e.groupEquiv.surjective.comp hκC_onto
  have hSponto : Function.Surjective (commutator (Sp E.Carrier)).subtype := by
    intro x
    refine ⟨⟨x,?_⟩,rfl⟩
    rw [LargeField.commutator_eq_top (by rw [hFc]; exact Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) h.nonbinary)]
    trivial
  have hψonto : Function.Surjective ψ :=
    (MulAut.conj k).surjective.comp (hSponto.comp hγonto)
  have hψker : ψ.ker=(Q R a).subgroupOf S := by
    dsimp only [ψ,γ]
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj k).injective,
      MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective,
      MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective,
      MonoidHom.ker_codRestrict,←hκQ,subgroupOf_map_subtype_eq]
  let T := (Q R t).subgroupOf S
  let A := (Z R z).subgroupOf S
  have hZzQ : Z R z ≤ Q R z :=
    (g.omega_bound z path.end_color (by
      rw [g.distance_constant z path.end_color]; change 0<g.b R; omega)).trans (omegaCenter_le _)
  have hZzT := hZzQ.trans (original_core_le_edge R path.end_color hzt)
  have hZzS := hZzT.trans hTS
  have hTmap : T.map ψ=planeRadicalAmbient := by
    rw [←hk,←MonoidHom.range_comp]
    apply le_antisymm
    · rintro _ ⟨u,hu,rfl⟩
      exact ⟨⟨u.val,hu⟩,(hψt ⟨u.val,hu⟩).symm⟩
    · rintro _ ⟨u,rfl⟩
      exact ⟨inclusion hTS u,u.property,hψt u⟩
  have hreverse : (2^n)^2 ≤ (Q R a).relIndex (Z R z) := by
    by_contra hn
    have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer
    let rev : CriticalPath R g z a :=
      { start_color := path.end_color
        walk := path.walk.reverse
        shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
        critical := critical_reverse R g hedge a path.start_color
          (by rw [g.distance_constant a path.start_color]; change 0<g.b R; omega)
          z path.end_color path.critical }
    have hh' := (h.original_small_critical_indices_eq_field rev (by omega)
      (by simpa only [h.field_card] using lt_of_not_ge hn)).2
    rw [hh',h.field_card] at hcritical
    nlinarith
  have hZtQa : Z R t ≤ Q R a :=
    (Sp4Four.edge_Z_le_endpoint R path.start_color hat).trans
      ((g.omega_bound a path.start_color (by rw [g.distance_constant a path.start_color]; change 0<g.b R; omega)).trans (omegaCenter_le _))
  have hAc : Nat.card (A.map ψ)=Nat.card E.Carrier^2 := by
    rw [←relIndex_ker,hψker,relIndex_subgroupOf hZzS,hFc]
    apply le_antisymm ?_ hreverse
    exact (relIndex_le_of_le_left hZtQa (by rw [hzi]; positivity)).trans_eq hzi
  obtain ⟨x,hx,hreg,y,hyT,hcoset,hmove⟩ := lifted_plane_selection hFc h.nonbinary ψ hψonto T A
    (by rw [hψker]; exact subgroupOf_mono _ (original_core_le_edge R path.start_color hat))
    (subgroupOf_mono _ hZzT) hTmap hAc
  have hyT' : y.val ∈ normalizer (Q R t : Set (FreeAmalgam R)) := by
    have hh := T.le_normalizer_map S.subtype (mem_map_of_mem S.subtype hyT)
    rwa [map_subgroupOf_eq_of_le hTS] at hh
  have hmove' : y.val ∉ normalizer (((Z R z ⊔ Q R a) : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
    intro hh
    apply hmove
    have hh' := (Z R z ⊔ Q R a).le_normalizer_comap S.subtype hh
    change y ∈ normalizer (((Z R z ⊔ Q R a).subgroupOf S) : Set S) at hh'
    rwa [subgroupOf_sup hZzS (show Q R a ≤ S from fun _ hx => hx.1),←hψker] at hh'
  have hxT : x.val ∈ Q R t := hZzT hx
  have hreg' (v : Vector E.Carrier) (hv : (β ⟨x.val,hxT⟩).val • v=v)
      (u : Q R t) : (β u).val • v=v := by
    have hxψ : ψ x • (k • v)=k • v := by
      change ψ (inclusion hTS ⟨x.val,hxT⟩) • (k • v)=k • v
      rw [hψt ⟨x.val,hxT⟩]
      change (k*(β ⟨x.val,hxT⟩).val*k⁻¹) • (k • v)=_
      rw [mul_smul,mul_smul,inv_smul_smul,hv]
    have hh := hreg (k • v) hxψ (inclusion hTS u) u.property
    rw [hψt] at hh
    change (k*(β u).val*k⁻¹) • (k • v)=k • v at hh
    apply (toLinear k).injective
    simpa only [mul_smul,inv_smul_smul,toLinear_apply] using hh
  have hC := regular_fixed_lift
    (MovedSection.coverAction (originalMovedSection h) e)
    (MovedSection.coverProjection (originalMovedSection h) e) he
    (U R a) (Q R t) ⟨x.val,hxT⟩ j hj hjr
    β hact hreg'
  have hZaX := g.omega_bound a path.start_color
    (by rw [g.distance_constant a path.start_color]; change 0<g.b R; omega)
  have hZaT := hZaX.trans ((omegaCenter_le _).trans (original_core_le_edge R path.start_color hat))
  have ht : color R t=true := by
    apply Bool.eq_true_of_not_eq_false
    intro he
    exact adjacent_color_ne R hat (path.start_color.trans he.symm)
  have hZt : Z R t=omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
  have hcent : Z R t ≤ centralizer (Q R t : Set (FreeAmalgam R)) := by
    rw [hZt]
    exact fun v hv => (mem_omegaCenter_iff.mp hv).2.2
  let := g.Z_elementary (by omega) a path.start_color
  have hnorm : Z R t ≤ normalizer (U R a : Set (FreeAmalgam R)) :=
    ((Sp4Four.edge_Z_le_endpoint R path.start_color hat).trans
      ((Z R a).le_centralizer.trans (centralizer_le (U_le_Z a)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have heq : Z R a ⊓ centralizer ({x.val} : Set (FreeAmalgam R))=Z R t := by
    apply le_antisymm
    · rintro y ⟨hy,hyx⟩
      have hy' : y ∈ Z R a := hy
      rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat,
        ←SetLike.mem_coe,coe_mul_of_right_le_normalizer_left _ _ hnorm] at hy'
      obtain ⟨u,hu,v,hv,rfl⟩ := hy'
      have hux : u ∈ centralizer ({x.val} : Set (FreeAmalgam R)) := by
        apply mem_centralizer_singleton_iff.mpr
        have hvx := hcent hv x.val hxT
        have hh := mem_centralizer_singleton_iff.mp hyx
        apply mul_right_cancel (b := v)
        calc
          u*x*v = u*(x*v) := mul_assoc _ _ _
          _ = u*(v*x) := by rw [hvx]
          _ = (u*v)*x := (mul_assoc _ _ _).symm
          _ = x*(u*v) := hh
          _ = x*u*v := (mul_assoc _ _ _).symm
      have huT := (hC.le ⟨hu,hux⟩).2
      rw [hZt]
      exact mem_omegaCenter_iff.mpr ⟨hZaT hy,(mem_omegaCenter_iff.mp (hZaX hy)).2.1,
        (centralizer (Q R t : Set (FreeAmalgam R))).mul_mem huT (hcent hv)⟩
    · exact le_inf (Sp4Four.edge_Z_le_endpoint R path.start_color hat)
        (fun y hy => mem_centralizer_singleton_iff.mpr (hcent hy x.val hxT).symm)
  have hcoset' : x.val⁻¹*(y.val*x.val*y.val⁻¹) ∈ Q R a := by
    have hh : x⁻¹*(y*x*y⁻¹) ∈ (Q R a).subgroupOf S := hψker ▸ hcoset
    exact hh
  refine ⟨x.val,hx,?_,heq,y.val,y.property,hyT',
    coset_normalizer_of_conjugate (Q R a) x.val y.val
      (Q_normalized R a y.property) hcoset',hcoset',hmove'⟩
  · intro hxQ
    have hZa : Z R a ≤ Z R t := by
      rw [←heq]
      refine le_inf le_rfl ?_
      intro u hu
      exact mem_centralizer_singleton_iff.mpr
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a path.start_color)
          hu x.val hxQ).symm
    rw [relIndex_eq_one.mpr hZa] at hai
    nlinarith


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
