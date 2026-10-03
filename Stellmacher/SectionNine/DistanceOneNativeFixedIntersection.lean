module
public import Stellmacher.SectionTwo.NativeBaumannOddFixedIntersection
public import Stellmacher.SectionNine.NineTwoAmbientSetup
public import Stellmacher.SectionFiveToSeven.VertexLocalModule
public import Stellmacher.BaumannMap

/-!
# A native Baumann fixed vector in the actual odd fixed complement

In the original ambient Section Nine context, suppose the native elementary
Thompson subgroup acts nontrivially on the initial center. For any supplied
faithful quotient-module witness on that center, a nontrivial fixed subgroup
of a subgroup F of the quotient odd core contains a nonidentity ambient
vector centralized by the actual Baumann subgroup. Neither critical length
one nor extracted distance-one action data is needed.

Choose the actual local Sylow mapping onto the distinguished ambient Sylow.
The vertex module theorem identifies its native module with the initial
center. This identifies the witness kernel with the native centralizer and
gives an equivariant multiplicative equivalence for the exact two named
actions. Native Thompson nontriviality descends through the projection, and
the native odd fixed-intersection theorem supplies a common fixed vector.
Its image is nonidentity and centralizes the ambient Baumann subgroup by
the witness conjugation equation and injective Baumann transport.

This is the nontrivial native Thompson branch of Stellmacher (9.1), Journal
of Algebra 190 (1997), p.47, using (2.2). It provides the actual fixed vector
for the separate (6.4) generation argument, without assuming that conclusion.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem distance_one_odd_fixed_inf_baumann_ne_bot
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hJnative : ¬ elementaryAbelianMaxJ T ≤
      Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer
        (ZAt ctx.Γ ctx.criticalPath.a : Set G)) (ZAt ctx.Γ ctx.criticalPath.a))
    (F : let _ := w.groupX; Subgroup w.X) :
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    F ≤ SectionOne.oddCore w.X →
    FixedPoints.subgroup F (ZAt ctx.Γ ctx.criticalPath.a) ≠ ⊥ →
    (FixedPoints.subgroup F (ZAt ctx.Γ ctx.criticalPath.a)).map
      (ZAt ctx.Γ ctx.criticalPath.a).subtype ⊓
      Subgroup.centralizer (baumannIn T : Set G) ≠ ⊥ := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  change F ≤ SectionOne.oddCore w.X → FixedPoints.subgroup F Za ≠ ⊥ →
    (FixedPoints.subgroup F Za).map Za.subtype ⊓
      Subgroup.centralizer (baumannIn T : Set G) ≠ ⊥
  intro hF hfix
  obtain ⟨hTP,U,hU⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).1
  have hUne : (U : Subgroup P) ≠ ⊥ := by
    intro hh
    apply ctx.sectionSeven.S_nontrivial
    rw [← hU,hh,Subgroup.map_bot]
  have heven : Even (Nat.card P) := by
    have hd : 2 ∣ Nat.card U := U.isPGroup'.card_eq_or_dvd.resolve_left
      (fun hc => hUne (Subgroup.card_eq_one.mp hc))
    exact even_iff_two_dvd.mpr (hd.trans (Subgroup.card_subgroup_dvd_card (U : Subgroup P)))
  have hsec : SectionTwo.Hypotheses P :=
    ⟨(edge_local_data ctx.sectionSeven Γ cp).1.2,heven,
      (edge_characteristic_data ctx.sectionSeven Γ cp).1⟩
  let V := SectionTwo.vSubgroup U
  have hVmap : V.map P.subtype = Za := vertexZ_eq_local_vSubgroup Γ cp.a U
  have hker : w.projection.ker = SectionTwo.cSubgroup U := by
    rw [w.kernel_eq]
    ext a
    change ((a:G)∈P ∧ (a:G)∈Subgroup.centralizer (Za:Set G)) ↔
      a∈Subgroup.centralizer (V:Set P)
    constructor
    · rintro ⟨_,ha⟩
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      apply P.subtype_injective
      exact Subgroup.mem_centralizer_iff.mp ha v
        (hVmap ▸ Subgroup.mem_map_of_mem P.subtype hv)
    · intro ha
      refine ⟨a.property,Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro v hv
      rw [← hVmap] at hv
      obtain ⟨v,hv,rfl⟩ := hv
      exact congrArg P.subtype (Subgroup.mem_centralizer_iff.mp ha v hv)
  let _ := SectionTwo.quotientConjugationAction U w.projection w.surjective hker
  let e : V ≃* Za := (V.equivMapOfInjective P.subtype P.subtype_injective).trans
    (MulEquiv.subgroupCongr hVmap)
  have he (v : V) : ((e v : Za) : G) = ((v : P) : G) := by
    simp only [e,MulEquiv.trans_apply,MulEquiv.subgroupCongr_apply]
    exact Subgroup.coe_equivMapOfInjective_apply V P.subtype P.subtype_injective v
  have heq (g : w.X) (v : V) : e (g • v) = g • e v := by
    obtain ⟨a,rfl⟩ := w.surjective g
    apply Subtype.ext
    rw [he]
    change (((w.projection a • v : V) : P) : G) = ((w.action (w.projection a)) (e v) : G)
    rw [SectionTwo.quotientConjugationAction_smul_coe U w.projection w.surjective hker,
      w.action_compatible]
    change (a:G) * ((v:P):G) * (a:G)⁻¹ = (a:G) * (e v:G) * (a:G)⁻¹
    rw [he]
  have hefix (K : Subgroup w.X) (v : V) :
      v ∈ FixedPoints.subgroup K V ↔ e v ∈ FixedPoints.subgroup K Za := by
    constructor
    · intro hv k
      change (k:w.X) • e v = e v
      rw [← heq]
      exact congrArg e (hv k)
    · intro hv k
      apply e.injective
      change e ((k:w.X) • v) = e v
      rw [heq]
      exact hv k
  have hfixV : FixedPoints.subgroup F V ≠ ⊥ := by
    intro hh
    apply hfix
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro z hz
    have hhmem := (hefix F (e.symm z)).mpr (by simpa only [e.apply_symm_apply] using hz)
    rw [hh,Subgroup.mem_bot] at hhmem
    simpa only [e.apply_symm_apply,map_one] using congrArg e hhmem
  let J := elementaryAbelianMaxJ (U : Subgroup P)
  let BU := (U : Subgroup P) ⊓ Subgroup.centralizer
    (omegaOneCenterAmbient J : Set P)
  have hJmap : J.map P.subtype = elementaryAbelianMaxJ T := by
    rw [← hU]
    exact (elementaryAbelianMaxJ_map_injective P.subtype P.subtype_injective _).symm
  have hBmap : BU.map P.subtype = baumannIn T := by
    dsimp [BU,J]
    rw [baumann_map_injective P.subtype P.subtype_injective,hU]
    rfl
  have hJne : J.map w.projection ≠ ⊥ := by
    intro hh
    have hJK : J ≤ SectionTwo.cSubgroup U := by
      rw [← hker]
      exact (Subgroup.map_eq_bot_iff J).mp hh
    apply hJnative
    rw [← hJmap]
    rintro j ⟨j,hj,rfl⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro z hz
    change z ∈ Za at hz
    rw [← hVmap] at hz
    obtain ⟨v,hv,rfl⟩ := hz
    exact congrArg P.subtype (Subgroup.mem_centralizer_iff.mp (hJK hj) v hv)
  have hint := SectionTwo.native_baumann_odd_fixed_inf_ne_bot hsec U w.projection
    w.surjective hker BU rfl hJne F hF hfixV
  obtain ⟨v,hv,hvne⟩ : ∃ v ∈ FixedPoints.subgroup F V ⊓
      FixedPoints.subgroup (BU.map w.projection) V, v ≠ 1 := by
    by_contra! hh
    exact hint ((Subgroup.eq_bot_iff_forall _).mpr hh)
  have hzF := (hefix F v).mp hv.1
  have hzB := (hefix (BU.map w.projection) v).mp hv.2
  have hcentral : (e v:G) ∈ Subgroup.centralizer (baumannIn T : Set G) := by
    apply Subgroup.mem_centralizer_iff.mpr
    intro b hb
    rw [← hBmap] at hb
    obtain ⟨b,hb,rfl⟩ := hb
    have hh := congrArg Subtype.val (hzB ⟨w.projection b,Subgroup.mem_map_of_mem w.projection hb⟩)
    change ((w.action (w.projection b)) (e v) : G) = (e v:G) at hh
    rw [w.action_compatible] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  intro hbot
  have hh : (e v:G) ∈ (FixedPoints.subgroup F Za).map Za.subtype ⊓
      Subgroup.centralizer (baumannIn T : Set G) :=
    ⟨Subgroup.mem_map_of_mem Za.subtype hzF,hcentral⟩
  rw [hbot,Subgroup.mem_bot] at hh
  apply hvne
  apply e.injective
  rw [map_one]
  exact Subtype.ext hh

end Stellmacher.SectionNine
