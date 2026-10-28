module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Preparation
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Quotient
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Selection.Local
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Selection.Markings
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.Selection.WeakClosure
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Selecting the parabolic and marking its quotient

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Proposition 8.2.2(2–6), pp.714–715; E.2.9–14, pp.221–228.

E.2.9 supplies a family member and its own conjugator. The restricted Sylow
and E.2.10 hypotheses are constructed with that same conjugator. Positive
weak closure supplies E.2.13(6)'s commuting-conjugates premise; the ambient
quadratic bound and E.2.13(5) exclude a trivial intersection. The canonical
normal-core/two-core quotient equivalence preserves the center and Borel
markings. Concrete model Sylow facts then give the normalizer and rank.

`exists_selected_of_HStar` derives E.2.8 and characteristic two of H from
the actual HStar member, simple QTKE, relative normalization and the
independent noncontainment theorem. `exists_selected_of_parameter_gaps`
also applies the checked Chapter 7 positivity arguments to literal module
parameters. All universal B.6/E.2 and model premises are explicit; their
existing producers remain with the ancestor assembly.

This is a conditional selection result. Applicability under the complete
Hypotheses 7.0.2, 7.3.1 and 8.2.1 still requires the Chapter 7/8.1 source
interface, including the Hermitian-row 7.5.6(2) bound. Its existing owners
are `qt-7-01-05` and `qt-8-01`. The independent action/torus branch and
Proposition 8.2.2 assembly remain with the parent construction task.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
open Subgroup ChapterB ChapterE Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]

/-- Selection data delivered to the independent action and torus branch.
All maps refer to this same I and this same right conjugator i. -/
structure Selected (H T M V I : Subgroup G) [IsElementaryAbelian 2 V]
    (k : ℕ) (i : I) (S : Sylow 2 I) : Prop where
  family : Family H T M V I k
  generate : V ⊔ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom = I
  sylow_eq : (S : Subgroup I) = T.subgroupOf I
  twoConjugate : TwoConjugate.Hypotheses S (V.subgroupOf I) (M.subgroupOf I) i⁻¹
  core_eq : localCore M I = pCore 2 I
  characteristic_two : generalizedFitting I = pCore 2 I
  intersection_ne_bot : V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ≠ ⊥
  intersection_central : V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ≤
    (center I).map I.subtype
  local_normalizer : I ⊓ normalizer (V : Set G) ≤ M
  normalizer_eq : M ⊓ I = I ⊓ normalizer (V : Set G)
  positive : 0 < k
  divides : k ∣ generationParameter H
  models : RankOneAlternative (I ⧸ pCore 2 I) (coreImage I M) k
  center_eq : coreImage I V = embeddedCenter (coreImage I T)
  borel_eq : coreImage I M = normalizer (coreImage I T : Set (I ⧸ pCore 2 I))
  rank_eq : rank (coreImage I V) = k
  quadraticRatio_gt_one : 1 < quadraticRatio
    ((automizerRepresentation V).comp (inducedAutomizer V I).subtype)

/-- Select E.2.9's pair, exclude the symplectic alternative by E.2.13(6),
exclude a trivial intersection by E.2.13(5), and mark its actual quotient.
The E.2 premises are universal earlier-source theorems, explicitly supplied
by their producers. This theorem does not discharge the Chapter 7 setup. -/
theorem exists_selected {K : GroupClass} (earlier : SelectionSources (G := G) K)
    (models : SelectionModelSources) {H T M V : Subgroup G} [IsElementaryAbelian 2 V]
    (h : HypothesisE28 K H T M V) (hchar : generalizedFitting H = pCore 2 H)
    (hw : 0 < globalW V T)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M) :
    ∃ (I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I), Selected H T M V I k i S := by
  obtain ⟨I, k, f⟩ := earlier.e29 H T M V h
  obtain ⟨x, hx, hgen⟩ := f.generate
  let i : I := ⟨x, hx⟩
  obtain ⟨S, hS⟩ := f.sylow
  have hVI : V ≤ I := hgen ▸ le_sup_left
  have hNI : I ⊓ normalizer (V : Set G) ≤ M :=
    (inf_le_inf_right _ f.le_ambient).trans h.normalizer_le
  have hqH := selected_quadraticRatio_gt_one M H V h.normalizer_le hq
  have hZ : V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ≠ ⊥ := by
    intro hz
    exact (not_le_of_gt hqH) (earlier.e2135 h hchar f i hgen hz)
  have hc := earlier.e2115 h f
  have hsp : ¬ SymplecticAlternative (Star M H) (Star M I)
      (starImage M I M) (starImage M I T) (starImage M I V) k := by
    intro hs
    obtain ⟨e, _⟩ := hs.2.2
    exact earlier.e2136 h hchar f (local_conjugates_centralize I T V hVI hw)
      k hs.1 ⟨e⟩
  obtain ⟨hk, hdvd, hr⟩ := selected_quotient f hc hsp
  have hz := earlier.e2142_center h hchar f (fun x hx => hTI x hx.2) i hgen hZ
  obtain ⟨hzcore, hncore⟩ := core_markings_of_star M I T V hc hz (earlier.e2113 h f)
  have hTM : T ≤ M := by
    obtain ⟨R, hR, hP, hM⟩ := h.minimal
    intro t ht
    have htm := (minimalParabolicMax_spec R hP).2
    rw [hR, ← hM] at htm
    exact htm (show (⟨t, h.le_ambient ht⟩ : H) ∈ T.subgroupOf H from ht)
  obtain ⟨hnorm, hrank⟩ := selected_model_markings models M I T V k S hS hTM hr hzcore hncore
  refine ⟨I, k, i, S, f, hgen, hS, Family.twoConjugate h f S hS i hgen, hc,
    earlier.e292 h f hchar, hZ, ?_, hNI, ?_, hk, hdvd, hr, hzcore, hnorm, hrank,
    selected_quadraticRatio_gt_one M I V hNI hq⟩
  · exact intersection_central I V i.val hgen
  · exact relative_normalizer I M V i.val hgen hTI hNV hZ

/-- Apply selection to the actual HStar member. Characteristic two of H
is derived from even characteristic and 1.1.4(6), not supplied as a new
Chapter 8 hypothesis. The Chapter 7 weak-closure and module bounds remain
explicit until their source assembly is available. -/
theorem exists_selected_of_HStar {K : GroupClass}
    (earlier : SelectionSources (G := G) K) (models : SelectionModelSources)
    (hG : IsSimpleQTKE K G) (T : Sylow 2 G) {H M V : Subgroup G}
    [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hVT : V ≤ T) (hn : (V.subgroupOf (T : Subgroup G)).Normal)
    (hMV : H ⊓ M ≤ normalizer (V : Set G))
    (hout : ¬ V ≤ (pCore 2 H).map H.subtype)
    (b685 : ∀ (D : Subgroup G) (S : Sylow 2 D) (hP : IsMinimalParabolicOver S ⊤),
      IsTwoClosed (minimalParabolicMax S hP).normalCore)
    (hw : 0 < globalW V T)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M) :
    ∃ (I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I), Selected H T M V I k i S := by
  have h := hypothesisE28_of_HStar hG T hTM hH hVT hn hMV hout b685
  have hHe := Chapter1.lemma_1_1_4_6 T (hG.toIsQTKE.evenCharacteristic T) hH.1.1
  have hchar := generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp hHe)
  exact exists_selected earlier models h hchar hw hq hTI hNV

/-- An actual consumer of both Chapter 7 positivity arguments. The input
bounds are on the literal parameters of V, not on a group-family tag.
The Hermitian row's extra 7.5.6(2) argument is deliberately not asserted
by this parameter-gap corollary. -/
theorem exists_selected_of_parameter_gaps {K : GroupClass}
    (earlier : SelectionSources (G := G) K) (models : SelectionModelSources)
    (hG : IsSimpleQTKE K G) (T : Sylow 2 G) {H M V : Subgroup G}
    [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hVT : V ≤ T) (hn : (V.subgroupOf (T : Subgroup G)).Normal)
    (hMV : H ⊓ M ≤ normalizer (V : Set G))
    (hout : ¬ V ≤ (pCore 2 H).map H.subtype)
    (b685 : ∀ (D : Subgroup G) (S : Sylow 2 D) (hP : IsMinimalParabolicOver S ⊤),
      IsTwoClosed (minimalParabolicMax S hP).normalCore)
    (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hgap : ((localM V : ℕ∞) ≤ globalR V ∧ localA V < (localM V : ℕ∞)) ∨
      (primeRank 2 (Automizer V) : ℕ∞) < globalR V)
    (hq : 1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V M).subtype))
    (hTI : ∀ x ∈ M, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj x).toMonoidHom = V)
    (hNV : normalizer (V : Set G) ≤ M) :
    ∃ (I : Subgroup G) (k : ℕ) (i : I) (S : Sylow 2 I), Selected H T M V I k i S := by
  have hT : HypothesisE322 V T := ⟨fun he => hout (he ▸ bot_le), hVT,
    (normal_subgroupOf_iff_le_normalizer hVT).mp hn⟩
  have hw : 0 < globalW V T := by
    rcases hgap with ⟨hr, ha⟩ | hr
    · exact globalW_pos_of_local_parameter_gap hT hr ha
    · exact globalW_pos_of_fwci_gap hT hFF hr
  exact exists_selected_of_HStar earlier models hG T hTM hH hVT hn hMV hout b685 hw hq hTI hNV

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
