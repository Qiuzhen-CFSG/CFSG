module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Natural
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Preparation.Orbit
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.Actor
public import Theory.Representation.SLThreeCentralExtension.ThompsonFixed
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import CFSG.Quasithin.Chapter10.SourceA5PointSylow.OriginalOrbits

/-!
# Preparation for every original binary-three natural cover

For a positive fixed kernel, the actual half-Sylow action factors through
SL₃(2). Its maximum elementary images fix a common plane in the four-space
cover. Transitivity outside the kernel gives an original Thompson-fixed
representative for every moved vector. Saturation then gives
J(C_T(v)) = J(T), including the positive-kernel case. Together with the
already proved centralizer bound this constructs Prepared and the literal
FF action. The zero-kernel case uses the original natural-three proof.

The containing-model recognition and the other retained rows remain with
qt-d-10-nona5-point-constrained. Source: Aschbacher--Smith 10.2.9, p.751.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}
local instance : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

/-- Every moved vector in a positive binary-three cover is fixed by an
L-conjugate of the original Thompson subgroup. -/
theorem thompson_conjugate_fixed_of_positive_binaryThree
    (hmodel : Selection.BinaryThreeNatural D)
    (hne : sourceMovedFixed D ≠ ⊥) {w : G} (hw : w ∈ ⁅D.fullModule,L⁆) :
    ∃ l : L, (elementaryAbelianMaxJ (T : Subgroup G)).map
      (MulAut.conj (l : G)).toMonoidHom ≤ centralizer ({w} : Set G) := by
  let W := ⁅D.fullModule,L⁆
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  have hSW : S ≤ normalizer (W : Set G) :=
    (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right).trans
      (source_moved_normalizer_local_containment D)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D.simpleQTKE T D.maximal
  have hWT : W ≤ (T : Subgroup G) :=
    (le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)).trans (D.fullModule_le_sylow hu)
  have hWS : W ≤ S := le_inf hWT ((source_full_moved_le_component D).trans L.le_normalizer)
  have hJ : elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) :=
    elementaryAbelianMaxJ_eq_of_intermediate _ _
      (le_inf (sSup_le fun _ hA => hA.1) D.thompson_normalizes_component) inf_le_left
  obtain ⟨e,σ,p,hp,hσ,hker⟩ := Selection.BinaryThree.moved_cover D hmodel
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  change ∀ (l : L) (x : Additive W), ((σ (q l) x).toMul : G) =
    l*x.toMul*(l : G)⁻¹ at hσ
  let τ := BinaryConjugationSection.originalNormalizerAction hSW
  have hex (a : S) : ∃ g, σ g = τ a := by
    obtain ⟨l,hl,hact⟩ := Selection.BinaryThree.common_normalizer_acts_through_component
      D hmodel a.property.2 (hSW a.property)
    refine ⟨q ⟨l,hl⟩,?_⟩
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [hσ,BinaryConjugationSection.originalNormalizerAction_apply_coe]
    exact (hact x.toMul x.toMul.property).symm
  have hσinj := OneCohomology.SLThreeCentralExtension.cover_faithful σ p hp
  choose θ hθ using hex
  let π : S →* BinaryLinearThree.Group := {
    toFun := θ
    map_one' := hσinj (by rw [hθ,map_one,map_one])
    map_mul' a b := hσinj (by simp only [map_mul,hθ]) }
  have hπact (a : S) : σ (π a) = τ a := hθ a
  let U := W.subgroupOf S
  let : U.Normal := normal_subgroupOf_of_le_normalizer hSW
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hWS
  let E : Additive U ≃ₗ[ZMod 2] Additive W :=
    LinearEquiv.ofBijective ((subgroupOfEquivOfLe hWS).toMonoidHom.toAdditive.toZModLinearMap 2)
      (subgroupOfEquivOfLe hWS).bijective
  have hπ : π.ker = centralizer (U : Set S) := by
    ext a
    constructor
    · intro ha u hu
      have hh := LinearMap.congr_fun (hθ a) (Additive.ofMul ⟨(u : G),hu⟩)
      change σ (π a) _ = _ at hh
      rw [show π a = 1 from ha,map_one] at hh
      have hh' := congrArg (fun x : Additive W => (x.toMul : G)) hh
      rw [BinaryConjugationSection.originalNormalizerAction_apply_coe] at hh'
      change (u : G) = (a : G)*(u : G)*(a : G)⁻¹ at hh'
      exact Subtype.ext (mul_inv_eq_iff_eq_mul.mp hh'.symm).symm
    · intro ha
      apply hσinj
      rw [hπact,map_one]
      apply LinearMap.ext
      intro x
      apply Additive.toMul.injective
      apply Subtype.ext
      have hh := congrArg S.subtype (ha ⟨x.toMul,hWS x.toMul.property⟩ x.toMul.property)
      rw [BinaryConjugationSection.originalNormalizerAction_apply_coe]
      change (a : G)*x.toMul*(a : G)⁻¹ = x.toMul
      exact mul_inv_eq_iff_eq_mul.mpr hh.symm
  have he (a : S) (x : Additive U) :
      E (NoncentralChiefRefinement.normalRepresentation U a x) = σ (π a) (E x) := by
    rw [hπact]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [BinaryConjugationSection.originalNormalizerAction_apply_coe]
    rfl
  have hd : Module.finrank (ZMod 2) (Additive W) = 4 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W)
    rw [Nat.card_zmod] at hc
    have hcard : Nat.card (Additive W) = 16 :=
      Selection.BinaryThree.moved_card_eq_sixteen D hmodel hne
    rw [hcard] at hc
    exact Nat.pow_right_injective (by decide : 2 ≤ 2)
      (hc.symm.trans (by decide : 16 = 2^4))
  obtain ⟨g,hg⟩ := OneCohomology.SLThreeCentralExtension.thompson_conjugate_fixed
    σ p hp hd U ⊤ le_top
    ((T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).to_subgroup ⊤)
    π hπ E he (Additive.ofMul ⟨w,hw⟩)
  obtain ⟨l,hl⟩ := hq g
  refine ⟨l,?_⟩
  have hjmap : (elementaryAbelianMaxJ (⊤ : Subgroup S)).map S.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective S.subtype S.subtype_injective,
      ←MonoidHom.range_eq_map,range_subtype,hJ]
  rintro _ ⟨j,hj,rfl⟩
  obtain ⟨a,ha,haj⟩ := hjmap.symm ▸ hj
  change (a : G) = j at haj
  have hh := hg a ha
  rw [map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,hπact] at hh
  have hlw : ((σ g⁻¹ (Additive.ofMul ⟨w,hw⟩)).toMul : G) = (l : G)⁻¹*w*l := by
    have h := hσ l⁻¹ (Additive.ofMul ⟨w,hw⟩)
    rw [map_inv,hl] at h
    simpa only [Subgroup.coe_inv,inv_inv,toMul_ofMul] using h
  have h := congrArg (fun x : Additive W => (x.toMul : G)) hh
  rw [←hl,hσ,hl,BinaryConjugationSection.originalNormalizerAction_apply_coe,hlw] at h
  apply mem_centralizer_singleton_iff.mpr
  apply mul_inv_eq_iff_eq_mul.mp
  change ((MulAut.conj (l : G)) j)*w*((MulAut.conj (l : G)) j)⁻¹ = w
  calc
    _ = (l : G)*((a : G)*((l : G)⁻¹*w*l)*(a : G)⁻¹)*(l : G)⁻¹ := by
      rw [haj]; simp only [MulAut.conj_apply]; group
    _ = w := h

/-- Positive fixed kernels now supply the Thompson equality on the literal point. -/
theorem Context.thompson_eq_of_positive_binaryThree
    (c : Context D t v I) (hmodel : Selection.BinaryThreeNatural D)
    (hne : sourceMovedFixed D ≠ ⊥) :
    elementaryAbelianMaxJ (pointSylow T v) = elementaryAbelianMaxJ (T : Subgroup G) := by
  have horbit : ∀ w ∈ ⁅D.fullModule,L⁆, ∃ l ∈ L,
      (MulAut.conj l) w ∈ ⁅D.fullModule,L⁆ ⊓
        centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    intro w hw
    obtain ⟨l,hl⟩ := thompson_conjugate_fixed_of_positive_binaryThree hmodel hne hw
    refine ⟨(l : G)⁻¹,L.inv_mem l.property,?_,?_⟩
    · exact (mem_normalizer_iff.mp ((normalizer_commutator_ge_right D.fullModule L)
        (L.inv_mem l.property)) w).mp hw
    · intro j hj
      apply (MulAut.conj (l : G)).injective
      have hc : (MulAut.conj (l : G)) ((MulAut.conj (l : G)⁻¹) w) = w := by
        simp only [MulAut.conj_apply,inv_inv]; group
      simpa only [map_mul,hc,MulEquiv.coe_toMonoidHom] using
        (mem_centralizer_singleton_iff.mp (hl (mem_map_of_mem _ hj)))
  obtain ⟨m,hm,hfix⟩ := source_a5_partner_baumann_conjugate_fixed_of_thompson_orbits D
    horbit c.escaping.t_mem c.escaping.v_mem
  apply source_point_thompson_eq_of_conjugate_fixed D
    (c.escaping.sylow.restrict
      (le_inf (inf_le_left.trans (le_normalizer_componentOrbit L T)) inf_le_right) inf_le_right)
  exact ⟨m,hm,(map_mono (ChapterB.elementaryAbelianMaxJ_le_baumann _)).trans hfix⟩

/-- Every binary-three natural cover supplies all preparation conclusions,
with no extra zero-kernel or full/local-module equality assumption. -/
theorem Context.prepared_of_binaryThreeNatural
    (c : Context D t v I) (hmodel : Selection.BinaryThreeNatural D) : Prepared D v I := by
  by_cases hz : sourceMovedFixed D = ⊥
  · obtain ⟨e,⟨s⟩⟩ := hmodel
    have hs : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
        ((specialLinearNatural 3).comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) := hz ▸ s
    exact c.prepared_of_natural_three e hs
  · exact c.prepared_of_centralizer_of_thompson_eq
      (c.centralizer_le_of_binaryThreeNatural hmodel)
      (c.thompson_eq_of_positive_binaryThree hmodel hz)

/-- Actual consumer: the same cover prepares the original reduced orbit FF action. -/
theorem Context.actionFacts_of_binaryThreeNatural
    (c : Context D t v I) (hmodel : Selection.BinaryThreeNatural D) : ActionFacts c :=
  c.actionFacts (c.prepared_of_binaryThreeNatural hmodel)
end CFSG.Quasithin.Chapter10.PointControl.Constrained
