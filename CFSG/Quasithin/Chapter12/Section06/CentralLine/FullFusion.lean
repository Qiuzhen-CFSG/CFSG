module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.FixedSpaceFusion
public import Theory.GroupTheory.SylowNormalizerFrattini
public import Theory.GroupTheory.ReducedNormal.Equiv

/-!
# Full fusion control on the original orthogonal module

The last possible fusion failure interchanges a weight-two vector with its
complement in the original seven-dimensional core. Their full centralizers
are equal, so a failure supplies an element outside M normalizing that
centralizer. We prove the required normalizer containment, using the full
centralizer and its actual canonical residual throughout.

First place the point in the existing Sylow position. If J(T_v) lies in Q,
Thompson heredity controls N_G(T_v), and the relative Frattini argument
controls N_G(G_v). Otherwise local Thompson generation and the reduced
commutator identity recover V_v as [R₂(G_v),K_v], with K_v=L_v. Both factors
are characteristic constructions inside G_v, so its normalizer preserves
V_v and L_v. The weight-two residuals in the original V_v generate L;
their controlled full centralizers supply the point-normalizer hypotheses
of the existing local moved-space theorem. Thus N_G(G_v) lies in M in
both cases. Transport back uses the same original L-conjugator.

This excludes complementary fusion and proves 12.6.19(1) for both original
fixed-space cases. The literal centralizer conjugator of 12.6.20(2), the
compatible weight-four intersection marking, the intersection rank bound
and r(G,V)>=4 now have their fusion premises discharged.

The fixed-free HS/J4 exclusions, weak-closure calculation, splitting and
fixed-space elimination remain required; full 12.6.2 and 12.6.23 are not
asserted. Earlier invariance/TI retain qt-d-1222-source and final discharge
retains qt-d-12634-source.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.6--11 and 12.6.19--20, printed pp.824--825,828--829.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
open BinaryPermutation.EightNonsingular BinaryPermutation.TerminalOrthogonal
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem six_pair_of_weight (w : core (Fin 6)) (hw : hammingNorm w.val = 2) :
    ∃ a b : Fin 6, a ≠ b ∧ sixPair a b = w := by
  classical
  obtain ⟨a,b,hab,hs⟩ := Finset.card_eq_two.mp hw
  have hn (k : Fin 6) : w.val k ≠ 0 ↔ k = a ∨ k = b := by
    have hh := Finset.ext_iff.mp hs k
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,
      Finset.mem_insert,Finset.mem_singleton] using hh
  have hval (k : Fin 6) (hk : k = a ∨ k = b) : w.val k = 1 := by
    have hne := (hn k).mpr hk
    generalize w.val k = t at *
    fin_cases t
    · exact (hne rfl).elim
    · rfl
  refine ⟨a,b,hab,Subtype.ext ?_⟩
  funext k
  by_cases hka : k = a
  · subst k
    simp [sixPair,hab,hval a (Or.inl rfl)]
  by_cases hkb : k = b
  · subst k
    simp [sixPair,hab.symm,hval b (Or.inr rfl)]
  have hz : w.val k = 0 := by simpa [hka,hkb] using hn k
  simp [sixPair,hka,hkb,hz]

private theorem fixed_local_normalizers_le
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) :
    normalizer (Lv L (v : G) : Set G) ⊓ normalizer (Vv L V (v : G) : Set G) ≤ M L := by
  let := Vv_elementary H.chosen.normalizes (v : G)
  obtain ⟨i,j,hij,hp,E,hE,hproj,hgen⟩ := H.nonsingular_weightTwo_generation D v hv
  apply H.local_moved_normalizer_control D v hv E hgen
  rintro u ⟨w,hw,rfl⟩
  obtain ⟨a,b,hab,rfl⟩ := six_pair_of_weight w hw
  let u : V := ⟨(E (sixPair a b)).toMul,Vv_le_V H.chosen.normalizes _ (E (sixPair a b)).toMul.property⟩
  have hu : D.Nonsingular u := by
    change Eight.form (D.coordinates (Submodule.Quotient.mk _)) ≠ 0
    rw [hproj,extendSix_pair]
    have hab' : complementLetters i j hij a ≠ complementLetters i j hij b :=
      fun h => hab ((complementLetters i j hij).injective h)
    rw [(EightGeometry.nonsingular_core_iff _).mpr (Or.inl (EightCoreLine.pair_weight _ _ hab'))]
    exact one_ne_zero
  exact (le_inf (H.nonsingular_centralizer_le_of_fixed D hTV hTI hz u hu) le_rfl).trans
    (Mv_le_normalizer_Lv L _)

omit [Finite G] in
private theorem normalizer_le_normalizer_Kv (v : G) :
    normalizer (Gv v : Set G) ≤ normalizer (Kv v : Set G) := by
  let B := (primeToResidual 3 (solvableResidual (Gv v))).map
    (solvableResidual (Gv v)).subtype
  let : B.Characteristic := inferInstance
  exact normalizer_le_normalizer_characteristic_image (Gv v) B

private theorem selected_centralizer_normalizer_le
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G))) :
    normalizer (Gv (v : G) : Set G) ≤ M L := by
  have hc := H.nonsingular_centralizer_le_of_fixed D hTV hTI hz v hv
  have he : Mv L (v : G) = Gv (v : G) := inf_eq_right.mpr hc
  have hsg : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Gv (v : G)) := he ▸ hs
  by_cases hJ : elementaryAbelianMaxJ (Tv T (v : G)) ≤ Q T L
  · have hje : elementaryAbelianMaxJ (Tv T (v : G)) = elementaryAbelianMaxJ (Q T L) :=
      (elementaryAbelianMaxJ_eq_of_intermediate _ _ hJ (Q_le_Tv H.chosen v)).symm
    have hn : normalizer (Tv T (v : G) : Set G) ≤ M L := by
      apply (normalizer_le_normalizer_elementaryAbelianMaxJ _).trans
      rw [hje]
      exact H.core_thompson_normalizer
    obtain ⟨S,hS⟩ := hsg
    have hfr := le_normalizer_sylow_sup (Gv (v : G)) (normalizer (Gv (v : G) : Set G))
      (Gv (v : G)).le_normalizer le_rfl S
    rw [hS] at hfr
    exact hfr.trans (sup_le hn hc)
  · have hk := H.Kv_eq_Lv_of_le_normalizer D v hv ((Kv_le_Gv _).trans hc)
    have hn : normalizer (Gv (v : G) : Set G) ≤ normalizer (Lv L (v : G) : Set G) := by
      rw [←hk]
      exact normalizer_le_normalizer_Kv _
    have hr := H.reduced_point_commutator_eq D v hv hTV hs
      ((Gv (v : G)).le_normalizer.trans hn) (inf_le_left.trans hc)
      (H.local_thompson_generation D v hv hTV hs hJ)
    let A := Gv (v : G)
    let : (reducedTwoSubgroup A).Characteristic := characteristic_iff_map_le.mpr
      (fun e => (isPReduced_reducedPSubgroup.map_equiv e).le_reducedPSubgroup)
    have hred : normalizer (A : Set G) ≤
        normalizer ((reducedTwoSubgroup A).map A.subtype : Set G) :=
      normalizer_le_normalizer_characteristic_image A (reducedTwoSubgroup A)
    have hm : normalizer (Gv (v : G) : Set G) ≤ normalizer (Vv L V (v : G) : Set G) := by
      intro g hg
      rw [←hr,mem_normalizer_iff_map_conj_eq,map_commutator,
        mem_normalizer_iff_map_conj_eq.mp (hred hg),
        mem_normalizer_iff_map_conj_eq.mp (hn hg)]
    exact (le_inf hn hm).trans (fixed_local_normalizers_le H D hTV hTI hz v hv)

/-- Normalizer control for the full nonsingular centralizer, not merely its
intersection with the original maximal subgroup. -/
theorem SourceHypothesis.fixed_nonsingular_centralizer_normalizer_le
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    (v : V) (hv : D.Nonsingular v) :
    normalizer (Gv (v : G) : Set G) ≤ M L := by
  obtain ⟨l,hw,hs,_⟩ := D.exists_nonsingular_sylow_position H.chosen hTV hTI v hv
  let e := MulAut.conj (l : G)
  have he : (Gv (v : G)).map e.toMonoidHom =
      Gv (conjugation L V H.chosen.normalizes l v : G) := map_pointCentralizer e _
  have hn := selected_centralizer_normalizer_le H D hTV hTI hz _ hw hs
  rw [←he,←map_normalizer_eq_of_bijective _ e.bijective] at hn
  intro g hg
  have hh := hn (mem_map_of_mem e.toMonoidHom hg)
  exact ((M L).le_normalizer (L.le_normalizer l.property) g).mpr hh

/-- Source 12.6.19(1), with the complementary nonsingular fusion case
excluded using the normalizer of its actual full centralizer. -/
theorem SourceHypothesis.controls_element_fusion
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) :
    CentralLine.ControlsElementFusion L V := by
  by_contra hf
  have hz : ZV L V ≠ ⊥ := fun hz => hf (H.fixed_free_controls_element_fusion D hTV hTI hz)
  obtain ⟨E,u,g,_,hproj,hu,hn,hout,_⟩ := H.fusion_failure_has_complement_normalizer D hTV hTI hf
  have huN : D.Nonsingular u := by
    have hh := (EightGeometry.nonsingular_core_iff (E (Additive.ofMul u))).mpr (Or.inl hu)
    rw [hproj] at hh
    change Eight.form (D.coordinates (Submodule.Quotient.mk (Additive.ofMul u))) ≠ 0
    rw [hh]
    exact one_ne_zero
  exact hout (H.fixed_nonsingular_centralizer_normalizer_le D hTV hTI hz u huN hn)

/-- The correcting centralizer conjugator in source 12.6.20(2), for
all original intersection points and both fixed-space cases. -/
theorem SourceHypothesis.centralizer_conjugator
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    {v g : G} (hv : v ∈ V) (hvg : v ∈ V.map (MulAut.conj g).toMonoidHom) :
    ∃ c : Gv v, V.map (MulAut.conj (c : G)).toMonoidHom =
      V.map (MulAut.conj g).toMonoidHom :=
  CentralLine.centralizer_conjugator H.chosen.normalizes
    (H.controls_element_fusion D hTV hTI) hv hvg

/-- The original source 12.6.20(1,3) application with its fusion premise
now discharged. The chosen coordinates retain the actual fixed-space projection. -/
theorem SourceHypothesis.fixed_core_weight_four_intersections
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥) :
    ∃ E : Additive V ≃ₗ[ZMod 2] core (Fin 8),
      (∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
        alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w)) ∧
      (∀ w, coreToNatural (Fin 8) (E w) = D.coordinates (Submodule.Quotient.mk w)) ∧
      (∀ g ∉ normalizer (V : Set G),
        (∀ x ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom,
          x ≠ 1 → x ∈ CentralLine.markedVectors E CentralLine.coreWeightFour) ∧
        Nat.log 2 (Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) ≤ 3) ∧
      4 ≤ ChapterE.globalR V :=
  H.fixed_core_weight_four_intersections_of_fusion D hTV hTI hz
    (H.controls_element_fusion D hTV hTI)

/-- The actual intersection rank and r-parameter used by source 12.6.22. -/
theorem SourceHypothesis.fixed_core_intersections
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥) :
    (∀ g ∉ normalizer (V : Set G),
      Nat.log 2 (Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G)) ≤ 3) ∧
      4 ≤ ChapterE.globalR V :=
  H.fixed_core_intersections_of_fusion D hTV hTI hz (H.controls_element_fusion D hTV hTI)

end CFSG.Quasithin.Chapter12.Section06
