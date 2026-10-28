module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.AlternatingConstrained
-- Continue the original residual-action argument within this source family.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFDoubledShortRoute.AlternatingConstrained
public import Theory.SpecificGroups.BinaryLinear.QuinticNormalizer
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.MaximalLevi
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Excluding the SL₅(2) star in the alternating doubled rows

The original normalized intersection residual acts on the constrained
component's core-central quotient with solvable kernel. Its perfect image
is inner. The genuine C.2.7 large-component argument places the normalizer
of the nontrivial radical intersection inside the literal star intersection;
normality of the original residual makes that normalizer preserve its image.

A factor five forces this radical normalizer to be an endpoint parabolic
of SL₅(2). Its two-core quotient is A₈. The normal residual image must
surject onto that quotient, but the original residual has simple section
A₆ or A₇ and solvable kernel, so it cannot also have A₈ as a quotient.
The proof retains the full star kernel, both two-core quotient maps, the
covering center and the actual original normality and intersection maps.
No placement of an ambient Sylow subgroup in the intersection is assumed.

The original-witness applications eliminate all constrained A₇ components
and leave only the A₈ star for A₆. The final application places the entire
A₇ source orbit and intersection residual in an ordinary component of the
same reciprocal overgroup. The ordinary-component exclusion, the A₆/A₈
fixed-module argument and the final odd-normalizer bounds remain open.

Source: Aschbacher--Smith B.5.1, C.2.7(3)(h), C.4.5--8 and 4.4.6,
printed pp.99,145--147,152--154,620, refs/quasithin.pdf. The endpoint quotient
calculation uses the same basis transport as
Theory.SpecificGroups.BinaryLinear.SixSectionSmallIndex.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource
open Chapter4.Section04.NormalizedRankOneOddControl
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open BinaryLinear.OuterCyclic

private theorem end_quotient (H : Subgroup (LinearGroup 5))
    (hH : BinaryLinear.FiveParabolicStabilizer.IsEndParabolic H) :
    Nonempty ((H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 8)) := by
  open BinaryLinear.FiveFlagGeometry BinaryLinear.FiveFlagGeometry.MaximalOvergroups in
    rcases hH with ⟨v,hv,rfl⟩ | ⟨f,hf,rfl⟩
    · obtain ⟨b,hb⟩ := GeometricFlags.exists_flagSpace
        (Submodule.span (ZMod 2) {v}) 0 (by simpa using finrank_span_singleton hv)
      let e := MulEquiv.subgroupCongr ((flagStabilizer_singleton b 0).trans (congrArg BinaryLinear.parabolic hb))
      exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans
        ((lineQuotientEquiv b).trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm)⟩
    · have hd : Module.finrank (ZMod 2) f.ker = 4 := by
        have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hf
        norm_num [Space] at hh
        omega
      obtain ⟨b,hb⟩ := GeometricFlags.exists_flagSpace f.ker 3 (by simpa using hd)
      let e := MulEquiv.subgroupCongr ((flagStabilizer_singleton b 3).trans (congrArg BinaryLinear.parabolic hb))
      exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans
        ((hyperplaneQuotientEquiv b).trans Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.symm)⟩

private theorem no_small_normal_image
    {A S P : Type*} [Group A] [Finite A] [Group S] [Finite S] [IsSimpleGroup S]
    [Group P] [Finite P]
    (hS : ¬ Group.IsSolvable S) (hsmall : Nat.card S < 20160)
    (π : A →* S) (hπ : Function.Surjective π) [Group.IsSolvable π.ker]
    (f : A →* P) [Group.IsSolvable f.ker] [f.range.Normal]
    (e : (P ⧸ pCore 2 P) ≃* alternatingGroup (Fin 8)) : False := by
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 P))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 P := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent (pCore 2 P) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := hk.symm ▸ inferInstanceAs (Group.IsSolvable (pCore 2 P))
  let g := q.comp f
  let : Group.IsSolvable g.ker := isSolvable_comap_of_solvable_ker f q.ker
  let : g.range.Normal := by
    dsimp only [g]
    rw [MonoidHom.range_comp]
    exact Subgroup.Normal.map inferInstance q hq
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : g.range.Normal).eq_bot_or_eq_top with hz | ht
  · have hg : g.ker = ⊤ := MonoidHom.ker_eq_top_iff.mpr (g.range_eq_bot_iff.mp hz)
    let : Group.IsSolvable (⊤ : Subgroup A) := hg ▸ inferInstanceAs (Group.IsSolvable g.ker)
    let : Group.IsSolvable A := Group.isSolvable_of_surjective (f := (topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom)
      topEquiv.surjective
    exact hS (Group.isSolvable_of_surjective hπ)
  · have hn : ¬ Group.IsSolvable (alternatingGroup (Fin 8)) :=
      Group.IsPerfect.not_isSolvable _
    have hd := SimpleSection.card_dvd_of_solvable_representation hn g
      (MonoidHom.range_eq_top.mp ht) π
    rw [nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd
    exact (not_le_of_gt hsmall) (Nat.le_of_dvd Nat.card_pos hd)

private theorem no_small_inner_actor
    {A S Q : Type*} [Group A] [Finite A] [Group S] [Finite S] [IsSimpleGroup S]
    [Group Q] [Finite Q]
    (hS : ¬ Group.IsSolvable S) (hsmall : Nat.card S < 20160) (h5 : 5 ∣ Nat.card S)
    (π : A →* S) (hπ : Function.Surjective π) [Group.IsSolvable π.ker]
    (e : Q ≃* SL(5,ZMod 2))
    (U : Subgroup Q) (hU : IsPGroup 2 U) (hne : U ≠ ⊥)
    (B : Subgroup (MulAut Q)) [Group.IsPerfect B]
    (b : A →* B) (hb : Function.Surjective b) [Group.IsSolvable b.ker]
    (hi : B ≤ MulAut.innerSubgroup Q)
    (hfix : ∀ a ∈ B, U.map a.toMonoidHom = U)
    (hn : (normalizer (U : Set Q)).map MulAut.conj ≤ normalizer (B : Set (MulAut Q))) : False := by
  have hz : center Q = ⊥ :=
    (Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv e
      (Theory.SpecificGroups.BinaryComponentResidual.linear (Or.inr rfl))).1
  have hc : Function.Injective (MulAut.conj : Q →* MulAut Q) :=
    Theory.GroupTheory.conj_injective_of_center_eq_bot hz
  let C := B.comap (MulAut.conj : Q →* MulAut Q)
  let f : C →* B := (MulAut.conj.comp C.subtype).codRestrict _ (fun c => c.property)
  have hf : Function.Injective f := fun x y he => Subtype.ext (hc (congrArg Subtype.val he))
  have hs : Function.Surjective f := by
    intro a
    obtain ⟨x,hx⟩ := hi a.property
    exact ⟨⟨x,show MulAut.conj x ∈ B from hx.symm ▸ a.property⟩,Subtype.ext hx⟩
  let t := MulEquiv.ofBijective f ⟨hf,hs⟩
  have hCN : C ≤ normalizer (U : Set Q) := by
    intro c hc
    exact mem_normalizer_iff_map_conj_eq.mpr (hfix (MulAut.conj c) hc)
  have hNC : normalizer (U : Set Q) ≤ normalizer (C : Set Q) := by
    intro x hx y
    have hh := (hn (mem_map_of_mem MulAut.conj hx)) (MulAut.conj y)
    change MulAut.conj y ∈ B ↔ MulAut.conj (x * y * x⁻¹) ∈ B
    simp only [SetLike.mem_coe] at hh
    simpa only [map_mul,map_inv] using hh
  let a := e.trans (slEquivLinear 5)
  let P := normalizer (U.map a.toMonoidHom : Set (LinearGroup 5))
  let r : A →* P := ((a.toMonoidHom.comp (C.subtype.comp (t.symm.toMonoidHom.comp b))).codRestrict P
    (fun x => by
      change a (t.symm (b x)) ∈ normalizer (U.map a.toMonoidHom : Set (LinearGroup 5))
      rw [←map_equiv_normalizer_eq]
      exact mem_map_of_mem a.toMonoidHom (hCN (t.symm (b x)).property)))
  have hrk : r.ker = b.ker := by
    ext x
    change (r x = 1) ↔ b x = 1
    rw [Subtype.ext_iff]
    change a (t.symm (b x)) = 1 ↔ _
    rw [a.map_eq_one_iff]
    change ((t.symm (b x) : C) : Q) = ((1 : C) : Q) ↔ _
    rw [Subtype.val_inj,t.symm.map_eq_one_iff]
  let : Group.IsSolvable r.ker := hrk.symm ▸ inferInstanceAs (Group.IsSolvable b.ker)
  have hrange : r.range = (C.map a.toMonoidHom).subgroupOf P := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact mem_map_of_mem a.toMonoidHom (t.symm (b x)).property
    · rintro ⟨c,hc,he⟩
      obtain ⟨x,hx⟩ := hb (t ⟨c,hc⟩)
      refine ⟨x,Subtype.ext ?_⟩
      change a (t.symm (b x)) = y
      rw [hx,t.symm_apply_apply]
      exact he
  have hn' : P ≤ normalizer (C.map a.toMonoidHom : Set (LinearGroup 5)) := by
    change normalizer (U.map a.toMonoidHom : Set (LinearGroup 5)) ≤ _
    rw [←map_equiv_normalizer_eq,←map_equiv_normalizer_eq]
    exact map_mono hNC
  let : r.range.Normal := hrange.symm ▸ normal_subgroupOf_of_le_normalizer hn'
  have hd := h5.trans (SimpleSection.card_dvd_of_solvable_representation hS π hπ r)
  obtain ⟨ep⟩ := end_quotient P
    (BinaryLinear.QuinticNormalizer.normalizer_isEndParabolic _ (hU.map _)
      (fun he => hne ((U.map_eq_bot_iff_of_injective a.injective).mp he)) hd)
  exact no_small_normal_image hS hsmall π hπ r ep

private theorem no_constrained_linearFive_of_small_section
    {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S) (hsmall : Nat.card S < 20160) (h5 : 5 ∣ Nat.card S)
    (π : F →* S) (hπ : Function.Surjective π) [Group.IsSolvable π.ker]
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e5 : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)) : False := by
  let K₀ := K.map H.subtype
  let C := starImage K₀ R K₀
  let eK := K.equivMapOfInjective H.subtype H.subtype_injective
  let hi := h.constrained_source_input K hK hq hout hfK
  have hz : center C = ⊥ :=
    (Theory.SpecificGroups.BinaryComponentResidual.Facts.of_equiv e5
      (Theory.SpecificGroups.BinaryComponentResidual.linear (Or.inr rfl))).1
  let a : coreCentralQuotient K ≃* C :=
    (coreCentralQuotientCongr eK).trans
      (ChapterC.Section04Constrained.source_simple_equiv hi (MulEquiv.refl C) hz)
  have ha (k : K) : a (coreCentralProjection K k) = toStarImage K₀ R (eK k) := by
    rw [MulEquiv.trans_apply,coreCentralQuotientCongr_apply,
      ChapterC.Section04Constrained.source_simple_equiv_mk]
    rfl
  let U := coreCentralIntersectionImage K (R.subgroupOf H)
  have hu : U.map a.toMonoidHom = (starImage K₀ R R).subgroupOf C := by
    let : (K₀.subgroupOf (K₀ ⊔ R)).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le K₀.le_normalizer hi.normalizes)
    rw [←ChapterC.C27Source.component_intersection_star_eq_of_normal_input
      (ChapterC.C27Source.source_join_input hi)]
    ext z
    constructor
    · rintro ⟨y,⟨k,hk,rfl⟩,rfl⟩
      exact ⟨eK k,hk,(ha k).symm⟩
    · rintro ⟨k,hk,rfl⟩
      refine ⟨coreCentralProjection K (eK.symm k),⟨eK.symm k,?_,rfl⟩,?_⟩
      · change ((eK.symm k : K) : H).val ∈ R
        have he := congrArg (fun k : K₀ => (k : G)) (eK.apply_symm_apply k)
        change ((eK.symm k : K) : H).val = (k : G) at he
        rwa [he]
      · change a (coreCentralProjection K (eK.symm k)) = _
        rw [ha,eK.apply_symm_apply]
  have hlarge : 40320 < Nat.card C := by
    rw [Nat.card_congr (e5.trans ((slEquivLinear 5).trans (matrixEquivLinear 5).symm)).toEquiv,
      Matrix.card_GL_field]
    decide
  obtain ⟨hrad,hcontrol⟩ := ChapterC.C27Source.star_intersection_placement_from_source_of_large_order hi hlarge
  have hU : IsPGroup 2 U := coreCentralIntersectionImage_isPGroup K _ h.isRadical.isPGroup
  have hUne : U ≠ ⊥ := by
    intro he
    exact hrad.1 (by rw [←hu,he,Subgroup.map_bot])
  let B := coreCentralActorImage K (F.subgroupOf H)
  obtain ⟨b,hb,hbk⟩ := constrained_actor_map h hn K hK hq hout
  let := hbk
  let : Group.IsPerfect F := (h.normalized_span_eq hn) ▸ h.span_perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective hb
  let : Group.IsSolvable (MulAut.Outer (coreCentralQuotient K)) :=
    h.constrained_core_central_outer_solvable K hq
  have hAR : F.subgroupOf H ≤ normalizer (R.subgroupOf H : Set H) := by
    intro x hx r
    exact h.span_normalizes_radical ((h.normalized_span_eq hn).symm ▸ hx) (r : G)
  apply no_small_inner_actor hS hsmall h5 π hπ (a.trans e5) U hU hUne B b hb
    (MulAut.perfect_subgroup_le_inner B)
    (fun z hz => coreCentralActorImage_stabilizes K _ _ hAR hz)
  have hMF : M.subgroupOf H ≤ normalizer (F.subgroupOf H : Set H) := by
    intro m hm f
    exact hn hm (f : G)
  have hMB := coreCentralActorImage_normalizes K (M.subgroupOf H) (F.subgroupOf H) hMF
  rintro _ ⟨z,hz,rfl⟩
  apply hMB
  have hz' : a z ∈ normalizer ((starImage K₀ R R).subgroupOf C : Set C) := by
    rw [←hu,←map_equiv_normalizer_eq]
    exact mem_map_of_mem a.toMonoidHom hz
  obtain ⟨k,hk,he⟩ := hcontrol hz'
  let k₀ : K₀ := ⟨k,hk.2⟩
  let k' : K := eK.symm k₀
  have hkaz : a (coreCentralProjection K k') = a z := by
    rw [ha]
    change toStarImage K₀ R (eK (eK.symm k₀)) = _
    rw [eK.apply_symm_apply]
    exact Subtype.ext he
  have hkz : coreCentralProjection K k' = z := a.injective hkaz
  have hkM : ((k' : K) : H) ∈ M.subgroupOf H := by
    have hh := congrArg (fun k : K₀ => (k : G)) (eK.apply_symm_apply k₀)
    change ((k' : K) : H).val ∈ M
    change ((k' : K) : H).val = (k : G) at hh
    rw [hh]
    exact hk.1
  refine ⟨⟨k'.val,K.le_normalizer k'.property⟩,hkM,?_⟩
  rw [←hkz]
  apply MulEquiv.ext
  intro x
  obtain ⟨y,rfl⟩ := ((QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K))).comp
    (QuotientGroup.mk'_surjective (pCore 2 K))) x
  change normalizerCoreCentralAction K _ (coreCentralProjection K y) = _
  rw [normalizerCoreCentralAction_apply]
  change coreCentralProjection K (k' * y * k'⁻¹) = _
  rw [map_mul,map_mul,map_inv]
  rfl

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape

/-- The original alternating reciprocal witness excludes the actual SL5(2)
star marking. The normalizer of the nontrivial radical image is forced to be
an endpoint parabolic, whose simple A8 Levi quotient cannot contain the normal
image of the original A6 or A7 residual. No Sylow-placement premise is added. -/
theorem sourceOrbit_alternating_witness_no_linearFive
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {n : ℕ} (hn : n = 6 ∨ n = 7)
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin n)) Y)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (e5 : starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2)) :
    False := by
  obtain ⟨m⟩ := hmodel
  let e := (D.componentCentralQuotientEquiv h.quasisimple).trans
    ((centerQuotientCongr m.groupEquiv).trans
      ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot
        (by simp only [Nat.card_eq_fintype_card,Fintype.card_fin]; omega :
          4 ≤ Nat.card (Fin n)))).trans QuotientGroup.quotientBot))
  let := h.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (alternatingGroup (Fin n)) := e.symm.isSimpleGroup
  let : Group.IsPerfect (alternatingGroup (Fin n)) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  rcases hw with ⟨_,_,_,_,_,_,hc,_,hNF,_,_,⟨c,_⟩,_⟩
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let r : F →* (L ⧸ pCore 2 L) := c.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  have hrk : r.ker = pCore 2 F := by
    rw [MonoidHom.ker_comp_of_injective _ _ c.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent (pCore 2 F) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable r.ker := hrk.symm ▸ inferInstanceAs (Group.IsSolvable (pCore 2 F))
  let π : F →* alternatingGroup (Fin n) := e.toMonoidHom.comp
    ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp r)
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (c.surjective.comp (QuotientGroup.mk'_surjective _)))
  let : Group.IsSolvable π.ker := by
    have he : π.ker = (center (L ⧸ pCore 2 L)).comap r := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,
        ← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    rw [he]
    exact isSolvable_comap_of_solvable_ker r _
  apply no_constrained_linearFive_of_small_section hc
    ((normal_subgroupOf_iff_le_normalizer hc.component_le).mp hNF)
    (Group.IsPerfect.not_isSolvable _) _ _ π hπ K hK hq hout hfK e5
  · rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]
  · rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num [Nat.factorial]

/-- The constrained A7 reciprocal branch is impossible on the literal star
quotient. Together with the finite sieve this discharges every constrained row. -/
theorem sourceOrbit_seven_witness_not_constrained
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) : False := by
  obtain ⟨_,⟨e5⟩⟩ := D.sourceOrbit_seven_witness_constrained_linearFive h σ hmodel hw K hK hq hout hfK
  exact D.sourceOrbit_alternating_witness_no_linearFive h (Or.inr rfl) σ hmodel hw K hK hq hout hfK e5

/-- The only remaining constrained row for the actual A6 reciprocal witness
is the A8 star marking. The fixed-module exclusion remains to be proved. -/
theorem sourceOrbit_six_witness_constrained_eight
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (ChapterB.QuasisimpleSource.alternatingNatural 6)))
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    K.Normal ∧ Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
      alternatingGroup (Fin 8)) := by
  obtain ⟨hKn,hcases⟩ := D.sourceOrbit_alternating_witness_constrained_binary h
    (Or.inl rfl) _ hmodel hw K hK hq hout hfK
  rcases hcases with he | he
  · exact ⟨hKn,he⟩
  · obtain ⟨e5⟩ := he
    exact (D.sourceOrbit_alternating_witness_no_linearFive h (Or.inl rfl) _ hmodel
      hw K hK hq hout hfK e5).elim

/-- The original A7 reciprocal obstruction now supplies an ordinary component
containing the entire source orbit and the original intersection residual. -/
theorem sourceOrbit_seven_reciprocal_ordinary_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ Representation.BinaryOffender.IsFFModule D.sourceOrbitNormalizerRepresentation)
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 7)) (Fin 4 → ZMod 2))
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) σ))
    (A : Subgroup G)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (ho : Odd (Nat.card A))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ J H W : Subgroup G, Witness L V A J H W ∧
      let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      D.sourceOrbit ≤ J.pCoreIn 2 ∧ D.sourceOrbit ≤ F.pCoreIn 2 ∧
      D.sourceOrbit = ⁅D.sourceOrbit,F⁆ ∧
      D.sourceOrbit ⊓ centralizer (F : Set G) = ⊥ ∧
      ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        F.subgroupOf H ≤ K ∧ D.sourceOrbit.subgroupOf H ≤ K := by
  obtain ⟨J,H,W,hw,_,hWJ,hWF,hcomm,hfix,K,hK,hq,hout,hKn,hcases⟩ :=
    D.sourceOrbit_seven_reciprocal_normal_component h hmany hnon σ hmodel A hA ho hnot
  rcases hcases with hordinary | hfK
  · have hc := hw.2.2.2.2.2.2.1
    have hFK := hc.ordinary_component_contains_original K hordinary
    exact ⟨J,H,W,hw,hWJ,hWF,hcomm,hfix,K,hordinary,hKn,hout,hFK,
      (subgroupOf_mono H (hWF.trans (pCoreIn_le 2 _))).trans hFK⟩
  · exact (D.sourceOrbit_seven_witness_not_constrained h σ hmodel hw K hK hq hout hfK).elim

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
