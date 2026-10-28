module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Multiplicity.SupportObstruction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Intersection.Classification
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Intersection.Movement

/-!
# Cubic containment in the Thompson-moving SL₃ branch

On the original D,S, B.2.7 puts the literal Thompson image in the full
normalizer orbit's offender subgroup. Thus L=[L,J(T)] puts the marked
SL₃ component there. The genuine B.5 classification on that offender
subgroup gives either an irreducible component action or a quadratic ratio
at most one on the component itself. The existing exact natural-copy ratio
s/2 then gives s≤2; the original quotient marking and full scalar center
are retained throughout. A.3.19's checked one/two-copy argument now places
every order-three element of N_G(L) in L in this branch.

A moving H-star intersection supplies the Thompson identity, so it also
implies cubic containment. Conversely an escaping cubic forces J(T) to
centralize the original seed, every H-star intersection to normalize that
seed, and Ω₁Z(T) to lie in the center of every H-star subgroup. These are
necessary consequences on the original ambient input, not assumptions
added to 11.0.4. Exclusion of this remaining configuration stays with
qt-d-1222-natural-preliminary-source; qt-d-1222-natural-local-geometry
retains the final source assembly.

Source: Aschbacher--Smith, B.2.7 and B.5.1/B.5.6, printed pp.77,99--110;
3.1.8(3), p.575; 3.2.2(6), p.579; A.3.19, pp.54--55; and 11.0.3--4,
p.760, combined manuscript of 1 March 2004.
-/

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups ENNReal IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter3.Section02.ChosenSource325
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
public noncomputable section
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

namespace ThompsonCubic
open CFSG.Quasithin.ChapterB.SourceInduction
variable {H W : Type*} [Group H] [Finite H]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W)

private theorem irrPlus_or_component_ratio
    (h : FFHypothesis CFSG.KnownSimple.IsKnownSimple ρ) {K : Subgroup H}
    (hK : IsComponent H K) (hr : 1 < primeRank 3 K)
    (hm : moved ρ K = ⊤) (F : BinaryField) (e : K ≃* SL(3,F.Carrier)) :
    IsIrrPlus ρ K ⊤ ∨ quadraticRatio (ρ.comp K.subtype) ≤ 1 := by
  obtain ⟨hq,⟨c⟩⟩ := quasisimple_fitting_of_full_high_rank ρ h hK hr hm
  have he : K = generalizedFitting H := hK.eq_of_le
    ⟨(inferInstance : (generalizedFitting H).Normal).isSubnormal,hq⟩
    (component_le_generalizedFitting H K hK)
  subst K
  have hs : c.sectionData.space.toSubmodule = ⊤ := c.sectionData.space_eq.trans hm
  cases c.clause_one with
  | irreducible hi _ _ _ _ => exact Or.inl (hs ▸ hi)
  | doubleThree _ whole _ _ hq =>
    right
    let a : H ≃* generalizedFitting H := (MulEquiv.subgroupCongr whole).trans topEquiv |>.symm
    have hh := quadraticRatio_le_of_injective_equivariant ρ
      (ρ.comp (generalizedFitting H).subtype) a.toMonoidHom a.injective
      (LinearEquiv.refl (ZMod 2) W) (fun _ _ => rfl)
    exact hh.trans_eq hq
  | naturalDual d hd _ hn =>
    obtain ⟨a⟩ := hn
    exact (SourceCompletion.no_linearThree_binary_equiv F hd (e.symm.trans a.groupEquiv)).elim
  | repeatedNatural d s hd _ _ _ hn =>
    obtain ⟨a⟩ := hn
    exact (SourceCompletion.no_linearThree_binary_equiv F hd (e.symm.trans a.groupEquiv)).elim

end ThompsonCubic

private theorem fullAction_thompson_image_le :
    letI := fullModule_elementary D S
    (Stellmacher.elementaryAbelianMaxJ
      ((T : Subgroup G).subgroupOf (normalizer (L : Set G)))).map
      (actionHom (fullModuleConjugation D S)) ≤
      offenderSubgroup (imageRepresentation (fullModuleConjugation D S)) := by
  let := fullModule_elementary D S
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  have hUM : U ≤ M := iSup_conjugates_le_of_le_normalizer V M M
    (D.le_sylow.trans D.sylow_normalizes_component) M.le_normalizer
  let U₀ := U.subgroupOf M
  let : U₀.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_componentOrbit V M)
  let a : U₀ ≃* U := subgroupOfEquivOfLe hUM
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.of_injective a.toMonoidHom a.injective
  let E : Additive U₀ ≃ₗ[ZMod 2] Additive U :=
    LinearEquiv.ofBijective (a.toMonoidHom.toAdditive.toZModLinearMap 2)
      ⟨a.injective,a.surjective⟩
  let ρ := fullModuleConjugation D S
  let f := actionHom ρ
  have hf : Function.Surjective f := ρ.asGroupHom.rangeRestrict_surjective
  have hk : f.ker = centralizer (U₀ : Set M) := by
    ext g
    rw [MonoidHom.mem_ker,actionHom_eq_one_iff]
    constructor
    · intro h u hu
      have hh := congrArg (fun v : Additive U => (v.toMul : G)) (h (Additive.ofMul (a ⟨u,hu⟩)))
      apply Subtype.ext
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro h v
      apply Additive.toMul.injective
      apply Subtype.ext
      have hh := congrArg (fun x : M => (x : G)) (h (a.symm v.toMul).val (a.symm v.toMul).property)
      change (g : G) * (v.toMul : G) * (g : G)⁻¹ = (v.toMul : G)
      exact mul_inv_eq_iff_eq_mul.mpr hh.symm
  let σ := NormalElementaryQuotient.representation U₀ f hf hk
  have he (g : actionImage ρ) (v : Additive U₀) :
      E (σ g v) = imageRepresentation ρ g (E v) := by
    obtain ⟨g,rfl⟩ := hf g
    apply Additive.toMul.injective
    apply Subtype.ext
    exact congrArg (fun x : M => (x : G))
      (NormalElementaryQuotient.representation_apply U₀ f hf hk g v)
  let P : Sylow 2 M := T.subtype D.sylow_normalizes_component
  change (Stellmacher.elementaryAbelianMaxJ (P : Subgroup M)).map f ≤ _
  rw [map_le_iff_le_comap]
  apply sSup_le
  intro A hA
  apply map_le_iff_le_comap.mp
  by_cases hn : A.map f = ⊥
  · rw [hn]
    exact bot_le
  · have hb := NormalElementaryQuotient.maxElementary_isBestOffender U₀ f hf hk
      (P : Subgroup M) A ((IsElementaryAbelian.isPGroup 2 U₀).le_sylow_of_normal P) hA hn
    have hb' := hb.map_equivariant σ (imageRepresentation ρ) (MulEquiv.refl _) E he
    have hh := hb'.le_offenderSubgroup (imageRepresentation ρ)
    change (A.map f).map (MonoidHom.id _) ≤ _ at hh
    rwa [Subgroup.map_id] at hh

/-- B.2.7 places the actual marked component in the full offender subgroup
when the original Thompson commutator identity holds. -/
theorem fullAction_component_le_offender_of_thompson
    (hcomm : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ) ≤
      offenderSubgroup (imageRepresentation ρ) := by
  let := fullModule_elementary D S
  let M := normalizer (L : Set G)
  let K := L.subgroupOf M
  let J := Stellmacher.elementaryAbelianMaxJ ((T : Subgroup G).subgroupOf M)
  let f := actionHom (fullModuleConjugation D S)
  have hK : K = ⁅K,J⁆ := by
    apply map_injective M.subtype_injective
    rw [map_commutator,←Stellmacher.elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective]
    rw [map_subgroupOf_eq_of_le L.le_normalizer,
      map_subgroupOf_eq_of_le D.sylow_normalizes_component]
    exact hcomm
  let O := offenderSubgroup (imageRepresentation (fullModuleConjugation D S))
  let : O.Normal := offenderSubgroup_normal _
  change K.map f ≤ O
  rw [hK,map_commutator]
  exact (commutator_mono le_rfl (fullAction_thompson_image_le D S)).trans
    (commutator_le_right _ _)

private theorem fullAction_component_moved :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    moved (imageRepresentation ρ)
      ((L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)) = ⊤ := by
  let := fullModule_elementary D S
  let U := componentOrbit V (normalizer (L : Set G))
  let ρ := fullModuleConjugation D S
  let f := actionHom ρ
  let K := (L.subgroupOf (normalizer (L : Set G))).map f
  let W := moved (imageRepresentation ρ) K
  let C := W.toAddSubgroup.toSubgroup'.map U.subtype
  have hc : ⁅U,L⁆ ≤ C := by
    apply commutator_le.mpr
    intro u hu l hl
    let w : Additive U := Additive.ofMul ⟨u,hu⟩
    let a := f (inclusion L.le_normalizer ⟨l,hl⟩)
    have ha : a ∈ K := mem_map_of_mem f hl
    have hw : w - imageRepresentation ρ a w ∈ W := by
      apply W.neg_mem_iff.mp
      rw [neg_sub]
      exact Submodule.subset_span ⟨a,ha,w,Submodule.mem_top,rfl⟩
    refine ⟨(w - imageRepresentation ρ a w).toMul,hw,?_⟩
    change u / (l * u * l⁻¹) = ⁅u,l⁆
    rw [commutatorElement_def]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc]
  have hUC : U ≤ C := (fullModule_eq_commutator D S).le.trans hc
  apply top_unique
  intro v _
  obtain ⟨w,hw,he⟩ := hUC v.toMul.property
  have he' : w = v.toMul := Subtype.ext he
  change Additive.ofMul w ∈ W at hw
  rw [he'] at hw
  exact hw

private theorem sl3_irrPlus_or_component_ratio_of_component_le_offender
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree)
    (hKO : letI := fullModule_elementary D S
      let ρ := fullModuleConjugation D S
      (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ) ≤
        offenderSubgroup (imageRepresentation ρ)) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let τ := imageRepresentation ρ
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    IsIrrPlus τ K ⊤ ∨ quadraticRatio (τ.comp K.subtype) ≤ 1 := by
  let := fullModule_elementary D S
  let ρ := fullModuleConjugation D S
  let τ := imageRepresentation ρ
  let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
  let O := offenderSubgroup τ
  let σ := τ.comp O.subtype
  let K₀ := K.subgroupOf O
  let a : K₀ ≃* K := subgroupOfEquivOfLe hKO
  have hf : ChapterB.SourceInduction.FFHypothesis CFSG.KnownSimple.IsKnownSimple σ :=
    ChapterB.InternalThompsonAction.offender_hypothesis τ (actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective (normalizer_sqtk D S)
      (imageRepresentation_injective ρ) (fullAction_twoCore_eq_bot D S)
  have hm : moved σ K₀ = ⊤ := by
    rw [moved,subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hKO]
    exact fullAction_component_moved D S
  have hr : 1 < primeRank 3 K₀ := by
    rw [primeRank_equiv 3 a]
    exact (by omega : 1 < 2).trans_le (sl3_fullAction_rank_pair D S m heven).1
  obtain ⟨e,_⟩ := sl3_fullAction_component_marking D S m
  rcases ThompsonCubic.irrPlus_or_component_ratio σ hf
      ((sl3_fullAction_component_isComponent D S m).subgroupOf hKO) hr hm S.field
      (a.trans e) with hi | hq
  · exact Or.inl ((IsIrrPlus.subgroupOf_iff τ K O hKO ⊤).mp hi)
  · right
    exact (quadraticRatio_le_of_injective_equivariant (σ.comp K₀.subtype)
      (τ.comp K.subtype) a.toMonoidHom a.injective
      (LinearEquiv.refl _ _) (fun _ _ => rfl)).trans hq

private theorem fullModule_component_copies
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {s : ℕ} (h : FullModuleNaturalCopies D S m s) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    Nonempty (ActionEquiv ((imageRepresentation ρ).comp K.subtype)
      (repeated (linearNatural S.field 3) s)) := by
  let := fullModule_elementary D S
  obtain ⟨e,he⟩ := sl3_fullAction_component_marking D S m
  obtain ⟨b,hb⟩ := h
  refine ⟨⟨e,b,?_⟩⟩
  rintro ⟨k,l,hl,rfl⟩ v
  change (l : G) ∈ L at hl
  have hh := he ⟨l,hl⟩
  exact (hb ⟨l,hl⟩ v).trans (congrArg (fun g => repeated (linearNatural S.field 3) s g (b v)) hh.symm)

private theorem fullModule_copies_le_one_of_irrPlus
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {s : ℕ} (hs : 0 < s) (h : FullModuleNaturalCopies D S m s)
    (hi : letI := fullModule_elementary D S
      let ρ := fullModuleConjugation D S
      IsIrrPlus (imageRepresentation ρ)
        ((L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)) ⊤) : s ≤ 1 := by
  let := fullModule_elementary D S
  let ρ := fullModuleConjugation D S
  let τ := imageRepresentation ρ
  let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
  obtain ⟨e⟩ := fullModule_component_copies D S m h
  let j : (Fin 3 → S.field.Carrier) →ₗ[ZMod 2]
      Additive (componentOrbit V (normalizer (L : Set G))) :=
    e.linearEquiv.symm.toLinearMap.comp (LinearMap.single (R := ZMod 2) (φ := fun _ : Fin s => Fin 3 → S.field.Carrier) ⟨0,hs⟩)
  have hj : Function.Injective j := by
    intro v w hh
    have hh' := congrFun (e.linearEquiv.symm.injective hh) ⟨0,hs⟩
    simpa using hh'
  have hjs : K ≤ subspaceStabilizer τ j.range := by
    apply le_subspaceStabilizer
    rintro k hk w ⟨v,rfl⟩
    refine ⟨(linearNatural S.field 3) (e.groupEquiv ⟨k,hk⟩) v,?_⟩
    apply e.linearEquiv.injective
    have hh := e.intertwines ⟨k,hk⟩ (j v)
    change e.linearEquiv (τ k (j v)) = _ at hh
    rw [hh]
    change e.linearEquiv (e.linearEquiv.symm _) = _
    simp only [LinearEquiv.apply_symm_apply]
    funext i
    by_cases hi : i = ⟨0,hs⟩
    · subst i; simp [repeated,j]
    · simp [repeated,hi,j]
  have hn : j.range ≠ ⊥ := by
    intro hz
    have hj0 := LinearMap.range_eq_bot.mp hz
    obtain ⟨v,hv⟩ := exists_ne (0 : Fin 3 → S.field.Carrier)
    exact hv (hj (by rw [hj0]; rfl))
  have ht : j.range = ⊤ := (hi.eq_or_le_fixedSpace τ hjs le_top).resolve_right (fun hh =>
    hn (bot_unique (hh.trans_eq (sl3_fullAction_component_fixedSpace_eq_bot D S m))))
  have hd := LinearMap.finrank_le_finrank_of_surjective (LinearMap.range_eq_top.mp ht)
  have hF := NaturalMultiplicity.natural_finrank S.field 1
  have hF' : Module.finrank (ZMod 2) (Fin 3 → S.field.Carrier) = 3 * S.field.degree := by
    simpa only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,one_mul] using hF
  rw [h.finrank,hF'] at hd
  nlinarith [S.field.degree_pos]

/-- B.5 bounds the original full natural multiplicity by two once its
marked component lies in the actual offender subgroup. -/
theorem fullModule_sl3_copies_le_two_of_component_le_offender
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree)
    (hKO : letI := fullModule_elementary D S
      let ρ := fullModuleConjugation D S
      (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ) ≤
        offenderSubgroup (imageRepresentation ρ))
    {s : ℕ} (hs : 0 < s) (h : FullModuleNaturalCopies D S m s) : s ≤ 2 := by
  let := fullModule_elementary D S
  rcases sl3_irrPlus_or_component_ratio_of_component_le_offender D S m heven hKO with hi | hq
  · exact (fullModule_copies_le_one_of_irrPlus D S m hs h hi).trans (by decide)
  · obtain ⟨e⟩ := fullModule_component_copies D S m h
    have hh := quadraticRatio_le_of_injective_equivariant _ _ e.groupEquiv.toMonoidHom
      e.groupEquiv.injective e.linearEquiv e.intertwines
    rw [NaturalMultiplicity.natural_quadraticRatio S.field hs] at hh
    have hb : (s : ℝ≥0∞) / 2 ≤ 1 := hh.trans hq
    have hb' : (s : ℝ≥0∞) ≤ 2 := by
      simpa using (ENNReal.div_le_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mp hb
    exact_mod_cast hb'

/-- The genuine Thompson identity, via B.2.7 and B.5, bounds the natural
multiplicity of the original full orbit by two. -/
theorem fullModule_sl3_copies_le_two_of_thompson
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree)
    (hcomm : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    {s : ℕ} (hs : 0 < s) (h : FullModuleNaturalCopies D S m s) : s ≤ 2 :=
  fullModule_sl3_copies_le_two_of_component_le_offender D S m heven
    (fullAction_component_le_offender_of_thompson D S hcomm) hs h

/-- Source 11.0.4 on the original D,S when the Thompson subgroup moves L.
All multiplicity, coordinate and invariant-constituent premises are discharged. -/
theorem sl3_orderThree_mem_of_thompson
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree)
    (hcomm : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    {x : G} (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3) : x ∈ L := by
  obtain ⟨s,hs,h⟩ := fullModule_sl3_natural_copies D S m
  have hb := fullModule_sl3_copies_le_two_of_thompson D S m heven hcomm hs h
  apply sl3_orderThree_mem_of_fullModule_finrank_lt D S m heven ?_ hxM hx
  rw [h.finrank]
  nlinarith [S.field.degree_pos]

/-- A moving H-star intersection supplies the Thompson identity, hence the
unconditional cubic conclusion in that genuine ambient branch. -/
theorem sl3_orderThree_mem_of_intersection_moves
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hmove : ¬ H ⊓ normalizer (L : Set G) ≤ normalizer (V : Set G))
    {x : G} (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3) : x ∈ L :=
  sl3_orderThree_mem_of_thompson D S m heven
    (thompson_commutator_of_intersection_moves D S hH hmove) hxM hx

/-- An escaping cubic forces every original H-star intersection to normalize
the actual seed. This retains the remaining nonmoving branch for assembly. -/
theorem sl3_intersection_normalizes_of_cubic_outside
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) {x : G}
    (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3) (hxL : x ∉ L)
    (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    H ⊓ normalizer (L : Set G) ≤ normalizer (L : Set G) ⊓ normalizer (V : Set G) := by
  apply le_inf inf_le_right
  by_contra hn
  exact hxL (sl3_orderThree_mem_of_intersection_moves D S m heven hH hn hxM hx)

/-- A cubic outside L can occur only in the Thompson-central seed branch.
This is an obstruction derived on the original input, not an added premise. -/
theorem sl3_thompson_centralizes_seed_of_cubic_outside
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) {x : G}
    (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3) (hxL : x ∉ L) :
    Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
  by_contra hj
  let F := D.fundamentalSetup S.source.toHypothesis1221
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.source.simpleQTKE T S.source.maximal_faithful.1
  have hjF : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (F.moduleSubgroup : Set G) := by rwa [S.unchanged_seed]
  have hc := F.actor_eq_commutator_of_thompson_not_centralizes hu hjF
  rw [D.localOrbit_eq] at hc
  exact hxL (sl3_orderThree_mem_of_thompson D S m heven hc hxM hx)

/-- In the remaining escaping-cubic branch, every actual H-star subgroup
centralizes Ω₁Z(T), as required by the nonmoving source 3.1.8 alternative. -/
theorem sl3_omega_central_in_HStar_of_cubic_outside
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (heven : Even S.field.degree) {x : G}
    (hxM : x ∈ normalizer (L : Set G)) (hx : orderOf x = 3) (hxL : x ∉ L)
    (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
  by_contra hz
  let F := D.fundamentalSetup S.source.toHypothesis1221
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.source.simpleQTKE T S.source.maximal_faithful.1
  obtain ⟨hM,_,huniq⟩ := F.lemma_3_2_3_uniqueness hu
  have hHF : H ∈ Chapter3.HStar (T : Subgroup G) F.maximalLocal := by
    change H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (Chapter3.Section02.localOrbit T L : Set G))
    rwa [D.localOrbit_eq]
  have hj := (F.qrcHypotheses hu hHF).thompson_moves_of_noncentral_omega
    F.simpleQTKE hM huniq F.module_ne_bot hz
  rw [S.unchanged_seed] at hj
  exact hj (sl3_thompson_centralizes_seed_of_cubic_outside D S m heven hxM hx hxL)

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
