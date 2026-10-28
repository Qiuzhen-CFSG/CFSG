module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuM24Parabolic
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuCompatiblePair

/-!
# Selecting the compatible M24 pair inside the original H-star group

The genuine E.2 witness constructor selects a rank-one pair inside H, with
its internal conjugator, actual quotient, Borel and Sylow intersection.
The preceding three-space is H-invariant, so the rank identity forces the
witness degree to be two. Its core actor is therefore an original w-offender.
Both its generator intersection and its fixed space contain the old
three-space and have rank three, so they equal that same subgroup.

The local TI/normalizer and restricted-ratio arguments are kept private here:
the corresponding Chapter12 Hermitian extension imports a second
declaration with the same omega-centralization name. All native
Chapter E/8 witness and module proofs are reused through their public APIs.
No E.2 callback, degree divisibility or J4 cover input remains in the exported
chosen-module application. Component recognition, other Mathieu rows and
the ambient isomorphism remain with qt-d-1222-nonff-mathieu.
Source: Aschbacher--Smith E.2.8--14, 8.2.2--5, printed pp.221--228,714--717,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource Sporadic.Mathieu
open Chapter8.Section02.HermitianSource
open Chapter8.Section02.Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem m24_hstar_normalizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    H ⊓ normalizer (L : Set G) ≤ normalizer (D.sourceOrbit : Set G) := by
  let Z := D.sourceOrbit ⊓ centralizer (T : Set G)
  have hZ : Z ≠ ⊥ := inf_centralizer_ne_bot_of_pGroups (T : Subgroup G)
    D.sourceOrbit T.isPGroup' (IsElementaryAbelian.isPGroup 2 D.sourceOrbit)
    D.sourceOrbit_weakClosure_setup.normalizes D.sourceOrbit_weakClosure_setup.nontrivial
  have hzOmega : Z ≤ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
    intro z hz
    exact (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨D.sourceOrbit_weakClosure_setup.le_sylow hz.1,
        elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz.1,hz.2⟩
  have hHZ : H ≤ centralizer (Z : Set G) :=
    (D.sourceOrbit_hstar_centralizes_omega h.toHypothesis1221 hnon hH).trans
      (centralizer_le hzOmega)
  exact (le_inf inf_le_right (inf_le_left.trans hHZ)).trans
    ((D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).localCentralizer_le_normalizer
      hZ (show Z ≤ D.sourceOrbit from inf_le_left))

private theorem m24_restricted_quadraticRatio
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation) (X : Subgroup G) :
    1 < quadraticRatio ((automizerRepresentation D.sourceOrbit).comp
      (inducedAutomizer D.sourceOrbit X).subtype) := by
  apply lt_of_not_ge
  intro hq
  have hff := isFFModule_of_quadraticRatio_le_one _ hq
  exact D.sourceOrbit_automizer_nonFF h hnon
    (IsFFModule.map_equivariant _ _ (inducedAutomizer D.sourceOrbit X).subtype
      Subtype.val_injective (LinearEquiv.refl _ _) (fun _ _ => rfl) hff)

private theorem sourceOrbit_m24_geometric_pair_of_positive
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hw : 0 < globalW D.sourceOrbit (T : Subgroup G)) :
    ∃ (I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I),
      GeometricSelected H T (normalizer (L : Set G)) D.sourceOrbit I k i S := by
  obtain ⟨h28,hchar⟩ := D.sourceOrbit_m24_hstar_setup h hmany hV hq hnon hH
  have hfit := generalizedFitting_eq_pCore_of_selfCentralizing 2 hchar
  obtain ⟨R,hR,n,⟨w⟩⟩ := exists_original_witness_of_positive_weak_closure h28 hfit
    (D.m24_hstar_normalizes h hmany hV hnon hH) hw
  obtain ⟨I,i,S,s⟩ := geometric_selected_of_original_witness h28 hfit R hR w
    (D.m24_restricted_quadraticRatio h.toHypothesis1221 hnon _)
    (D.sourceOrbit_hypothesisE61_of_invariant_nonFF h hmany hV hnon).ti
    (D.sourceOrbit_normalizer_le h.toHypothesis1221)
  exact ⟨I,w.degree,i,S,s⟩

/-- Construct the pair in the original H and identify both fixed subgroups
with the original offender three-space. -/
theorem sourceOrbit_m24_fixedPlane_compatible_pair
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M24))
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (a : Automizer D.sourceOrbit ≃* M24)
    (E : Additive D.sourceOrbit ≃ₗ[ZMod 2] MathieuCode.Cocode)
    (hE : ∀ b v, E (automizerRepresentation D.sourceOrbit b v) =
      MathieuCode.cocodeRepresentation (a b) (E v))
    {g : G} (hg : IsWOffenderAt D.sourceOrbit (T : Subgroup G) g)
    (hAT : offenderNormalizer D.sourceOrbit g ≤ T) :
    let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
    ∃ (H I : Subgroup G) (i : I) (S : Sylow 2 I),
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      H ≤ centralizer (U : Set G) ⊔ (T : Subgroup G) ∧
      H ≤ normalizer (U : Set G) ∧
      (pResidual 2 H).map H.subtype ≤ centralizer (U : Set G) ∧
      generationParameter H = 2 ∧
      Selected H T (normalizer (L : Set G)) D.sourceOrbit I 2 i S ∧
      IsWOffenderAt D.sourceOrbit (T : Subgroup G) i.val⁻¹ ∧
      offenderNormalizer D.sourceOrbit i.val⁻¹ =
        D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ I.pCoreIn 2 ∧
      offenderNormalizer D.sourceOrbit i.val⁻¹ ≤ T ∧
      U = D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom ∧
      U = D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G) ∧
      I ≤ centralizer (U : Set G) := by
  let U := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit g : Set G)
  obtain ⟨H,hH,hHC,hHN,hrH,hn,_,_,_⟩ :=
    D.sourceOrbit_m24_fixedPlane_parabolic_of_offender h hmany hV hq hnon a E hE hg hAT
  obtain ⟨_,hw,_,_,_,c,_,_,hU,_⟩ :=
    D.sourceOrbit_m24_cocode_geometry_of_many h hmany hV hq hnon a E hE hg
  obtain ⟨I,k,i,S,s⟩ := D.sourceOrbit_m24_geometric_pair_of_positive h hmany hV hq hnon hH
    (by rw [hw]; decide)
  change rank U = 3 at hU
  have hd : rank D.sourceOrbit = 11 :=
    (Chapter7.log_card_eq_finrank D.sourceOrbit).trans (E.finrank_eq.trans MathieuCode.finrank_cocode)
  obtain ⟨s2,ho,ha,ht,hz,hUZ⟩ := MathieuPair.compatible_offender s
    D.sourceOrbit_weakClosure_setup hw hd hU inf_le_left hHN hn
  obtain ⟨_,_,_,hrZ,_,d,_,_,hF,_⟩ :=
    D.sourceOrbit_m24_cocode_geometry_of_many h hmany hV hq hnon a E hE ho
  rw [hz] at hrZ
  let Z := D.sourceOrbit ⊓ D.sourceOrbit.map (MulAut.conj i.val⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le (show U ≤ D.sourceOrbit from inf_le_left)
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le (show Z ≤ D.sourceOrbit from inf_le_left)
  have hUn : U ≠ ⊥ := by intro he; rw [he,Representation.BinaryOffender.rank_bot] at hU; omega
  have hZn : Z ≠ ⊥ := by intro he; exact hUn (bot_unique (he ▸ hUZ))
  have he : U = Z := eq_of_le_of_card_ge hUZ (by
    rw [(show IsElementaryTwo Z from ⟨hZn,inferInstance⟩).card_eq_two_pow_rank,
      (show IsElementaryTwo U from ⟨hUn,inferInstance⟩).card_eq_two_pow_rank,hrZ,hU])
  have hIC : I ≤ centralizer (U : Set G) := by
    rw [he]
    apply le_centralizer_iff.mpr
    intro z hz x hx
    obtain ⟨w,hw,rfl⟩ := s2.intersection_central hz
    exact congrArg Subtype.val (mem_center_iff.mp hw ⟨x,hx⟩)
  let F := D.sourceOrbit ⊓ centralizer (offenderNormalizer D.sourceOrbit i.val⁻¹ : Set G)
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le (show F ≤ D.sourceOrbit from inf_le_left)
  change rank F = 3 at hF
  have hUF : U ≤ F := le_inf inf_le_left (le_centralizer_iff.mp
    (((ha.le.trans inf_le_right).trans (pCoreIn_le 2 I)).trans hIC))
  have hadd := offender_corank_add (B := (⊥ : Subgroup G)) bot_le hUF
  have hdim : rank F = subgroupCorank F U + rank U := by
    simpa only [subgroupCorank,relIndex_bot_left,rank] using hadd
  have heF : U = F := subgroup_eq_of_corank_zero hUF (by omega)
  exact ⟨H,I,i,S,hH,hHC,hHN,hrH,hn,s2,ho,ha,ht,he,heF,hIC⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
