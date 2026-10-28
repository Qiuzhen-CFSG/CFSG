module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.WitnessHall
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.Torus
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.CodePair
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M24Pair
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Pair
import all CFSG.Quasithin.Chapter8.Section02.HermitianSourceDihedralSelection
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# The original M24 code pair has degree one

The original E.2.2 component alternatives either give a dihedral pair or
construct Hall control on the same maximal subgroup. In the latter case the
pair's actual odd torus injects into the full original automizer, whose M24
Cartan bound forces its degree to at most two. The independent source
fixed-space argument removes degree two, leaving degree one. The orbit,
component, Sylow and all covering kernels remain unchanged.

Source: Aschbacher--Smith 8.2.2--3 and H.16.6--7, printed pp.714--716,
404--405, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu MathieuCode
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.MathieuShadowRows
open Chapter8.Section02.Offenders.Parabolic.Construction
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual geometric pair for an original M24 code marking has degree
one. Its marked original action and selected Sylow are returned unchanged. -/
theorem sourceOrbit_m24_code_pair_degree_one_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      codeRepresentation (a b) (E v))
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ (I : Subgroup G) (i : I) (S : Sylow 2 I),
      GeometricSelected H T (normalizer (L : Set G)) D.sourceOrbit I 1 i S := by
  let M := normalizer (L : Set G)
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_m24_hstar_setup h hmany hV hq hnon hH
  have hfit := generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar
  have hVH := h28.le_sylow.trans h28.le_ambient
  let : IsElementaryAbelian 2 (D.sourceOrbit.subgroupOf H) :=
    IsElementaryAbelian.subgroupOf hVH
  have hMV := D.m24_hstar_normalizes h hmany hV hnon hH
  have hwpos := D.sourceOrbit_m24_globalW_pos_of_many h hmany hV hq hnon
  obtain ⟨R,hR,hP,hM⟩ := h28.minimal
  have hRT : R = T.subtype h28.le_ambient := Sylow.ext hR
  subst R
  obtain ⟨hVR,_,hcore,hout⟩ := intrinsic_source_data h28 _ hR hP hM
  have hMV' : ChapterB.minimalParabolicMax (T.subtype h28.le_ambient) hP ≤
      normalizer (D.sourceOrbit.subgroupOf H : Set H) := by
    rw [←hM,←subgroupOf_normalizer_eq hVH]
    exact fun x hx => hMV ⟨x.property,hx⟩
  have hret : ∀ x : H,
      (D.sourceOrbit.subgroupOf H).map (MulAut.conj x).toMonoidHom ≤ T.subtype h28.le_ambient →
      (D.sourceOrbit.subgroupOf H).map (MulAut.conj x).toMonoidHom ≤
        centralizer (D.sourceOrbit.subgroupOf H : Set H) := by
    intro x hx
    have hh := local_conjugates_centralize H T D.sourceOrbit hVH hwpos x⁻¹
    simp only [inv_inv] at hh
    exact hh hx
  obtain ⟨n,w,hw⟩ : ∃ (n : ℕ),
      ∃ w : Witnesses.BenderPlacement.OriginalWitness (T.subtype h28.le_ambient)
        (M.subgroupOf H) (D.sourceOrbit.subgroupOf H) n,
        w.degree = 1 ∨ HallControl (T.subtype h28.le_ambient) hP := by
    have hW := original_witness_one_or_hall h28.sqtk _ hP
      (D.sourceOrbit.subgroupOf H) hVR hcore hout hMV' hfit hret
    rw [← hM] at hW
    exact hW
  obtain ⟨I,i,S,s⟩ := geometric_selected_of_original_witness h28 hfit _ hR w
    (D.m24_restricted_quadraticRatio h.toHypothesis1221 hnon M)
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)
  have hone : w.degree = 1 := by
    rcases hw with hw | hc
    · exact hw
    · have hk := m24_pair_degree_le_two_of_hall s h28.le_ambient hP hM.symm
        hMV h28.normalizer_le hc a
      have hrange := s.m24_code_parameter_one_or_three a E hE
      omega
  exact ⟨I,i,S,hone ▸ s⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
