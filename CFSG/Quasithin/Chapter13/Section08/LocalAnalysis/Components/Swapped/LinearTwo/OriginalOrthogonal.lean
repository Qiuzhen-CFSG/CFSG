module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.OriginalProjection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.OrthogonalEight.ActualConsequences
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.CriticalSource

/-!
# The original critical-pair contradiction for the orthogonal orbit

The actual cubic residual identity makes K₀* normal in H*. An explicit
whole-module orthogonal identification therefore excludes transvections
in H*. Original F.9 geometry constructs a critical pair with both strict
denominators, then selects its orientation so that the denominator rank
is at most the rank of its nontrivial quadratic actor.

Incidence places an actual H-conjugate of this actor inside O₂(L₁T).
The marked parabolic-core containment, retained explicitly here, puts the
actor in K₀*. The determinant-model quadratic bound gives rank at most
two. Its nonidentity elements have displacement rank at least four, which
contradicts the source displacement line on the selected subspace of
codimension at most two. This needs only the rank bound, not the additional
equality-case conclusions of F.9.16(2).

The final theorem combines this argument with the marked-seed projection
contradiction. The source module alternatives and the parabolic-core
containment are still independent inputs; this is a conditional assembly,
not the completed source assertion 13.8.16(1).
Source: Aschbacher--Smith, 13.8.16(1), printed pp.952--953 (PDF pp.969--970),
using F.9.13(6), F.9.16(2), and 13.8.8(2).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.Original
open ModuleAlternatives

private theorem orthogonal_actor_rank_le_two
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (N A : Subgroup D) (hAN : A ≤ N)
    (hm : HasOrthogonalFourOrbit ρ N) (hA : IsElementaryAbelian 2 A)
    (hq : IsQuadratic ρ A) : rank A ≤ 2 := by
  obtain ⟨f, e, he⟩ := hm
  let f' : N →* ClassicalOrthogonal.FourPlusMatrix.Binary.G :=
    (f.trans ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv.symm).toMonoidHom
  have hinj : Function.Injective f' :=
    (f.trans ClassicalOrthogonal.FourPlusMatrix.Binary.orthogonalEquiv.symm).injective
  let e' := e.trans ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates
  have he' (g : N) (v : U) : e' (ρ g v) =
      ClassicalOrthogonal.FourPlusMatrix.Binary.action (f' g) (e' v) := by
    change ClassicalOrthogonal.FourPlusMatrix.Binary.binaryCoordinates (e (ρ g v)) = _
    rw [he, OrthogonalEight.binaryCoordinates_equivariant]
    rfl
  let B := (A.subgroupOf N).map f'
  let : IsElementaryAbelian 2 A := hA
  let : IsElementaryAbelian 2 (A.subgroupOf N) := IsElementaryAbelian.subgroupOf hAN
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hqB : IsQuadratic ClassicalOrthogonal.FourPlusMatrix.Binary.action B := by
    rintro a ⟨a0, ha0, rfl⟩ b ⟨b0, hb0, rfl⟩ v
    have hh := congrArg e' (hq a0 ha0 b0 hb0 (e'.symm v))
    simpa only [map_sub, he', LinearEquiv.apply_symm_apply] using hh
  have hc := ClassicalOrthogonal.FourPlusMatrix.QuadraticActors.card_le_four B hB hqB
  have hcard : Nat.card A = Nat.card B :=
    (Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv).symm.trans
      (Nat.card_congr (equivMapOfInjective (A.subgroupOf N) f' hinj).toEquiv)
  rw [← hcard] at hc
  exact (Nat.log_mono_right hc : Nat.log 2 (Nat.card A) ≤ Nat.log 2 4)

open SourceCompletion TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
open CriticalGeometry CriticalGeometry.SectionActions CriticalGeometry.Reorientation
open ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
  (h : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple T L)
  (hF9all : ∀ J ∈ Source.Hz (one L T V₁) T G₁ M,
    (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ J).Hypothesis)
  (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
  (hcomm : ⁅V₃, G₁.pCoreIn 2⁆ ≠ ⊥)
  (hsource : SolvableExclusion.Residual.Source1339 L (one L T V₁) (plus L T V₁) T M V V₁)
  (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
  (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
  (hmoving : conjugateSpanBy K (T : Subgroup G) ≠ K)
include d h hF9all hcentral hcomm hsource hH hKH hK hmoving

/-- The literal selected critical actor contradicts the actual orthogonal
model after its marked parabolic two-core is placed inside the orbit. -/
theorem false_of_orthogonal_orbit_of_core_placement {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (horth : HasOrthogonalFourOrbit ρ
      (Source.starImage H (conjugateSpanBy K (T : Subgroup G))))
    (hcore : Source.starImage H ((one L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2) ≤
      Source.starImage H (conjugateSpanBy K (T : Subgroup G))) : False := by
  let : Module.Finite (ZMod 2) (SourceSpace H V₃ V₁) := Module.Finite.of_finite
  let N := Source.starImage H (conjugateSpanBy K (T : Subgroup G))
  have hres := threeResidual d h hF9all hcentral hcomm hsource hH hKH hK hmoving hn hmodel
  have hrel : (conjugateSpanBy K (T : Subgroup G)).subgroupOf H = primeToResidual 3 H := by
    rw [← hres]
    exact comap_map_eq_self_of_injective H.subtype_injective _
  let : N.Normal := by
    change (((conjugateSpanBy K (T : Subgroup G)).subgroupOf H).map
      (QuotientGroup.mk' (pCore 2 H))).Normal
    rw [hrel]
    exact Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have hno : ∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1 := by
    obtain ⟨f, e, he⟩ := horth
    let a : Source.Hstar H →* (SourceSpace H V₃ V₁ ≃ₗ[ZMod 2] SourceSpace H V₃ V₁) := {
      toFun := operator ρ
      map_one' := by ext u; change ρ 1 u = u; simp
      map_mul' := by intro x y; ext u; change ρ (x*y) u = ρ x (ρ y u); rw [map_mul]; rfl }
    exact OrthogonalEight.equivariant_extension_no_transvection a N f e he
  have hF9 := hF9all H hH
  let s := CriticalInputs.sourceSection H V₃ V₁ ρ hρ hF9.plus_le_H
    (d.line_le_plane.trans d.plane_le_seed) hF9.H_centralizes
  have er := CriticalSource.earlier_inputs d hH hF9 hcentral hcomm ρ hρ
  have hz : H ≤ normalizer (V₁ : Set G) :=
    hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨c, _, _⟩ := (localNaturalSetup d).exists_criticalPair d.abelian_span hF9
  obtain ⟨hd, hdg⟩ := c.strict_denominators_of_no_uStar_transvection V₃ V₁ d.seed_le hz
    hF9.commutator_UH_QH_le_point (er.geometry c) d.line_card er.centralizer (er.failure c)
    (CriticalInputs.no_source_transvection H V₃ V₁ ρ hρ hz
      hF9.commutator_UH_QH_le_point hno)
  obtain ⟨c, _, _, _, hcomp, hquad⟩ :=
    (localNaturalSetup d).exists_quadratic_selection d.abelian_span hF9 s c hd hdg
  obtain ⟨a, _, hplace, _⟩ := exists_second_to_base c (one L T V₁)
    ((one L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2)
    (by have := (er.geometry c).length; omega)
    (Comparison.local_edge d hF9) (er.initial_core c) le_rfl
  have hUN : Source.starImage H (c.Ugamma V₃) ≤ N := by
    rintro x ⟨u, hu, rfl⟩
    let q := QuotientGroup.mk' (pCore 2 H)
    have hconj : q a * q u * (q a)⁻¹ ∈ N := by
      apply hcore
      refine ⟨a * u * a⁻¹, hplace (mem_map_of_mem _ ?_), ?_⟩
      · exact (map_mono (conjugateSpanBy_mono d.seed_le le_rfl)) hu
      · simp only [map_mul, map_inv]
        rfl
    have hh := (inferInstance : N.Normal).conj_mem _ hconj (q a)⁻¹
    simpa only [inv_inv, inv_mul_cancel_left, mul_assoc, inv_mul_cancel, mul_one] using hh
  have hr := orthogonal_actor_rank_le_two ρ N _ hUN horth hquad.1.2 hquad.2.1
  have hUgH : c.Ugamma V₃ ≤ H :=
    (map_mono (conjugateSpanBy_mono d.seed_le le_rfl)).trans (er.geometry c).Vgamma_H
  have hUA : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G) :=
    ((conjugateSpanBy_mono d.seed_le le_rfl).trans (er.geometry c).VH_endpoint).trans
      (SectionActions.CriticalPair.normalizes_Aone c V₁ hz)
  have hcard : Nat.card (c.Aone V₁) = 2 :=
    (Nat.card_congr ((MulAut.conj (c.gb : G)).subgroupMap V₁).toEquiv.symm).trans d.line_card
  obtain ⟨hline, hdisp⟩ := s.critical_line_displacement (c.Ugamma V₃) (c.Aone V₁) hUA hcard
  have hcodim : Module.finrank (ZMod 2) (SourceSpace H V₃ V₁ ⧸
      s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁))) ≤ 2 := by
    rw [s.quotient_finrank _ (s.line_le_DH _ _ hUgH)]
    exact hcomp.trans hr
  obtain ⟨u, hne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hquad.1.1
  have hu := u.property
  obtain ⟨f, e, he⟩ := horth
  apply OrthogonalEight.no_critical_line_of_actual_model (ρ.comp N.subtype) f.toMonoidHom e he
    ⟨u, hUN hu⟩ (by
      intro hh
      apply hne
      apply Subtype.ext
      exact congrArg (fun x : N => (x : Source.Hstar H))
        (f.injective (hh.trans f.map_one.symm)))
    (s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)))
    (s.image (c.Aone V₁)) hcodim hline
  exact hdisp u hu

/-- Conditional final assembly on the actual source action. The two remaining
inputs are the module classification and the marked parabolic-core containment;
every residual, projection and critical-pair premise is discharged here. -/
theorem false_of_module_alternatives_of_core_placement {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (one L T V₁ ⊔ (T : Subgroup G)) = H)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    {t : G} (ht : t ∈ T) (htn : t ∉ normalizer (K : Set G))
    (halternative : HasCrossFactorQuotient ρ (Source.starImage H K)
        (Source.starImage H (K.conjBy t)) ∨
      HasOrthogonalFourOrbit ρ (Source.starImage H (conjugateSpanBy K (T : Subgroup G))))
    (hcore : HasOrthogonalFourOrbit ρ
        (Source.starImage H (conjugateSpanBy K (T : Subgroup G))) →
      Source.starImage H ((one L T V₁ ⊔ (T : Subgroup G)).pCoreIn 2) ≤
        Source.starImage H (conjugateSpanBy K (T : Subgroup G))) : False := by
  have ho := orthogonal_of_module_alternatives d h hF9all hcentral hcomm hsource
    hH hKH hK hgen hmoving hn hmodel ρ hρ ht htn halternative
  exact false_of_orthogonal_orbit_of_core_placement d h hF9all hcentral hcomm hsource
    hH hKH hK hmoving hn hmodel ρ hρ ho (hcore ho)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.Original
