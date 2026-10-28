module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Core
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPlaneCore
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
-- Reuse the literal component-to-automizer map in the original marking.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuPairCentralizers

/-!
# The original M24 cocode plane and its containing component

The marked offender's fixed three-space has solvable centralizer in L.
Its actual relative normalizer residual is a C-component and has centralizer
on U exactly its two-core, with quotient GL3(2). The native plane marking
retains the original component action and its full two-group kernel.

The original Sylow normalizes U and this residual. Source 1.2.4 therefore
constructs a normal C-component of N_G(U) containing the same residual.
Quasisimplicity and equality with that containing component are proved in
NonFFSourceMathieuM24Recognition. All cocode coordinates remain explicit;
the other Mathieu rows and final ambient J4 identification are separate.
Source: Aschbacher--Smith 8.2.5--6 and the paragraph preceding 8.2.7,
printed pp.716--717, using H.15.6 and 1.2.4, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
open MathieuCode MathieuCode.TrioCalculation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

private theorem fixedPlane_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    ∃ (q : L →* M24) (F : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode),
      Function.Surjective q ∧ IsPGroup 2 q.ker ∧
      (∀ (l : L) (w : D.sourceOrbit),
        F (Additive.ofMul (D.sourceOrbit.normalizerMonoidHom
          ⟨l,D.sourceOrbit_component_normalizes l.property⟩ w)) =
          cocodeRepresentation (q l) (F (Additive.ofMul w))) ∧
      ∀ w : D.sourceOrbit, (w : G) ∈ U ↔
        F (Additive.ofMul w) ∈ standardPlaneMap.range := by
  let W := D.sourceOrbit
  let A := offenderNormalizer W g
  let U := W ⊓ centralizer (A : Set G)
  obtain ⟨_,_,_,_,_,c,hc,hp,_,_⟩ :=
    D.sourceOrbit_m24_cocode_geometry_of_many h hmany hV hq hnon a E hE hg
  let C := LinearMap.GeneralLinearGroup.toLinearEquiv (cocodeRepresentation.asGroupHom c)
  let F := E.trans C
  let q : L →* M24 := (MulAut.conj c).toMonoidHom.comp
    (a.toMonoidHom.comp D.mathieuComponentAutomizer)
  have hqsur : Function.Surjective q := (MulAut.conj c).surjective.comp
    (a.surjective.comp (D.sourceOrbit_largeMathieu_component_surjective h.toHypothesis1221
      (D.sourceOrbit_chapterK_of_many h hmany hnon hV) (Or.inr hq)))
  have hF (l : L) (w : W) :
      F (Additive.ofMul (W.normalizerMonoidHom ⟨l,D.sourceOrbit_component_normalizes l.property⟩ w)) =
        cocodeRepresentation (q l) (F (Additive.ofMul w)) := by
    change cocodeRepresentation c
        (E (automizerRepresentation W (D.mathieuComponentAutomizer l) (Additive.ofMul w))) =
      cocodeRepresentation (c * a (D.mathieuComponentAutomizer l) * c⁻¹)
        (cocodeRepresentation c (E (Additive.ofMul w)))
    rw [hE]
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  have hplane (w : W) : (w : G) ∈ U ↔ F (Additive.ofMul w) ∈ standardPlaneMap.range := by
    rw [←hp]
    constructor
    · intro hw
      exact ⟨E (Additive.ofMul w),⟨Additive.ofMul w,
        (mem_fixedSpace_inducedAutomizer W A inf_le_right _).mpr hw.2,rfl⟩,rfl⟩
    · rintro ⟨v,⟨y,hy,rfl⟩,he⟩
      have hyw : y = Additive.ofMul w := F.injective he
      rw [hyw] at hy
      exact ⟨w.property,(mem_fixedSpace_inducedAutomizer W A inf_le_right _).mp hy⟩
  have hq2 : IsPGroup 2 q.ker := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj c).injective,
      MonoidHom.ker_comp_of_injective _ _ a.injective,
      D.sourceOrbit_largeMathieu_component_kernel h.toHypothesis1221 (Or.inr hq)]
    exact pCore_isPGroup
  exact ⟨q,F,hqsur,hq2,hF,hplane⟩

/-- The original offender plane has solvable relative centralizer and a
C-component residual inside its actual relative normalizer. -/
theorem sourceOrbit_m24_fixedPlane_residual_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) ∧
      ((Chapter8.Section02.Normalizer.localResidual L U).subgroupOf
        (normalizer (L : Set G) ⊓ normalizer (U : Set G))).IsCComponent := by
  let W := D.sourceOrbit
  let U := W ⊓ centralizer (offenderNormalizer W g : Set G)
  obtain ⟨q,F,hqsur,_,hF,hplane⟩ := D.fixedPlane_marking h hmany hV hq hnon a E hE hg
  have hL : (⊤ : Subgroup L).IsCComponent := by
    have hh := h.maximal_faithful.1.1.1.subgroupOf_of_le (K := L) le_rfl le_sup_left
    simpa only [subgroupOf_self] using hh
  exact ⟨MathieuTrio.plane_centralizer_solvable W L U hL
      D.sourceOrbit_component_normalizes inf_le_left q hqsur F hF hplane,
    MathieuTrio.plane_residual_relative_component W L U hL
      D.sourceOrbit_component_normalizes inf_le_left q hqsur F hF hplane⟩

/-- The original residual's centralizer of its fixed plane is its full
two-core; the resulting quotient is the actual GL3(2) action. -/
theorem sourceOrbit_m24_fixedPlane_residual_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    let R := Chapter8.Section02.Normalizer.localResidual L U
    R.pCoreIn 2 = R ⊓ centralizer (U : Set G) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* BinaryLinear.GL Vector) := by
  obtain ⟨q,F,hqsur,hq2,hF,hplane⟩ := D.fixedPlane_marking h hmany hV hq hnon a E hE hg
  exact MathieuTrio.plane_residual_core_quotient D.sourceOrbit L _
    D.sourceOrbit_component_normalizes inf_le_left q hqsur hq2 F hF hplane

private theorem fixed_overcomponent
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hUV : U ≤ D.sourceOrbit) (hUne : U ≠ ⊥)
    (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hR : (((solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
      (L ⊓ normalizer (U : Set G)).subtype).subgroupOf
        (normalizer (L : Set G) ⊓ normalizer (U : Set G))).IsCComponent) :
    ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
      (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
      (solvableResidual (L ⊓ normalizer (U : Set G) : Subgroup G)).map
        (L ⊓ normalizer (U : Set G)).subtype ≤ K ∧
      normalizer (U : Set G) ≤ normalizer (K : Set G) := by
  let R := Chapter8.Section02.Normalizer.localResidual L U
  let N := normalizer (U : Set G)
  let M := normalizer (L : Set G) ⊓ N
  have hRN : R ≤ N := (Chapter8.Section02.Normalizer.localResidual_le L U).trans inf_le_right
  have hRM : R ≤ M := (Chapter8.Section02.Normalizer.localResidual_le L U).trans
    (inf_le_inf_right _ L.le_normalizer)
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    Chapter8.Section02.Normalizer.normalizes_localResidual L U T D.sylow_normalizes_component hTU
  have hRTM : R ⊔ (T : Subgroup G) ≤ M := sup_le hRM
    (le_inf D.sylow_normalizes_component hTU)
  have hlocal : R ∈ Chapter1.L G (T : Subgroup G) := by
    refine ⟨hR.subgroupOf_of_le le_sup_left hRTM,?_,?_⟩
    · exact ⟨T.subtype le_sup_right,map_subgroupOf_eq_of_le le_sup_right⟩
    · have hUQ := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U)
        ((hUV.trans D.sourceOrbit_weakClosure_setup.le_sylow).trans
          (show (T : Subgroup G) ≤ R ⊔ (T : Subgroup G) from le_sup_right))
        (sup_le hRN hTU)
      exact ne_bot_of_le_ne_bot hUne hUQ
  let S := T.subtype hTU
  have hloc : R.subgroupOf N ∈ Chapter1.L N (S : Subgroup N) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTU hRN).mp ⟨hRN,hlocal⟩
  have hSN : (S : Subgroup N) ≤ normalizer (R.subgroupOf N : Set N) := by
    rw [← subgroupOf_normalizer_eq hRN]
    exact comap_mono hTR
  have hNH : N ∈ Chapter1.H G := ne_bot_of_le_ne_bot hUne
    (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 U) U.le_normalizer le_rfl)
  obtain ⟨K,⟨hK,hRK,hn⟩,_⟩ := Chapter1.Section02.lemma_1_2_4_containment_normality_source
    (Chapter1.Section02.uniqueness_local_quotient_sqtk h.simpleQTKE hNH) S hloc hSN
  let K' := K.map N.subtype
  have hKN : K' ≤ N := map_subtype_le _
  have hsub : K'.subgroupOf N = K := comap_map_eq_self_of_injective N.subtype_injective _
  refine ⟨K',hKN,hsub.symm ▸ hK,?_,?_⟩
  · intro x hx
    have hxR : x ∈ R := hx
    let y : N := ⟨x,hRN hxR⟩
    have hy : y ∈ R.subgroupOf N := hxR
    exact mem_map_of_mem N.subtype (hRK hy)
  · exact (normal_subgroupOf_iff_le_normalizer hKN).mp (hsub.symm ▸ hn)


/-- The same original plane places N_L(U)^∞ in a genuine normal
C-component of N_G(U), with all earlier component hypotheses discharged. -/
theorem sourceOrbit_m24_fixedPlane_containing_component
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    Group.IsSolvable (L ⊓ centralizer (U : Set G) : Subgroup G) ∧
      ((Chapter8.Section02.Normalizer.localResidual L U).subgroupOf
        (normalizer (L : Set G) ⊓ normalizer (U : Set G))).IsCComponent ∧
    ∃ K : Subgroup G, K ≤ normalizer (U : Set G) ∧
      (K.subgroupOf (normalizer (U : Set G))).IsCComponent ∧
      Chapter8.Section02.Normalizer.localResidual L U ≤ K ∧
      normalizer (U : Set G) ≤ normalizer (K : Set G) := by
  let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le
    (show U ≤ D.sourceOrbit from inf_le_left)
  obtain ⟨hs,hr⟩ := D.sourceOrbit_m24_fixedPlane_residual_component h hmany hV hq hnon a E hE hg
  obtain ⟨hu,hTU,_⟩ := D.sourceOrbit_m24_fixedPlane_local_of_offender_of_many
    h hmany hV hq hnon a E hE hg hAT
  have hn : U ≠ ⊥ := by
    intro hz
    change rank U = 3 at hu
    rw [hz,Representation.BinaryOffender.rank_bot] at hu
    omega
  exact ⟨hs,hr,D.fixed_overcomponent h.toHypothesis1221 U inf_le_left hn hTU hr⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
