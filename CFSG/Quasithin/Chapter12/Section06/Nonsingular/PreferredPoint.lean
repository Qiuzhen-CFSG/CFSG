module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.NormalizerControl
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.SylowPosition
public import Theory.GroupTheory.PCoreImage

/-!
# The preferred nonsingular point and its residual centralizer

If any weight-two lift in the original augmentation cover has an escaping
centralizer, choose such a lift. Otherwise every weight-two point centralizer
is already contained in M. This choice survives the L-conjugation that puts
its T-centralizer in the source Sylow position.

The local core marking agrees with the restriction of that same cover:
the difference lies in the fixed space and vanishes by A₆ commutator
generation. Thus every actual weight-two point in V_v is a weight-two lift
in the chosen cover. In the first case all those lifts are L-conjugate to v;
in the second case their centralizers lie in M. If L_v is normal in G_v,
both cases make the centralizer of each weight-two point normalize its
residual. The six-letter orbit calculation then puts N_{G_v}(V_v) in M:
each of its elements agrees at every core vector with an L_v-element,
and the weight-two point residuals generate L by Lemma 12.6.10.

The literal L_v=K_v consumer obtains the required normality from the
canonical residual construction, and also places V_v in O₂(G_v). The
centralizer of that two-core is consequently contained in M as well.
The normality reduction of 12.6.11 is thus discharged;
its Thompson cases and the component, block, splitting and fixed-space
arguments remain open. T-invariance and TI remain earlier 12.2.2 inputs,
whose final discharge belongs to qt-d-1222-source.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the choice
following Lemma 12.6.10 and the first reduction in 12.6.11, printed p.825.
-/

public section

open Subgroup Theory.GroupTheory Representation BinaryPermutation BinaryPermutation.EightNonsingular
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem marked_core_agrees_cover
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (f : core (Fin 8) →ₗ[ZMod 2] Additive V)
    (hf : ∀ l w, f (alternatingCoreRepresentation (Fin 8) (D.actorMap l) w) =
      seedRepresentation L V chosen.normalizes l (f w))
    (hfp : ∀ w, D.coordinates (Submodule.Quotient.mk (f w)) = coreToNatural (Fin 8) w)
    (v : V) (i j : Fin 8) (hij : i ≠ j)
    (hp : coreToNatural (Fin 8) (pair i j) =
      D.coordinates (Submodule.Quotient.mk (Additive.ofMul v))) :
    let := Vv_elementary chosen.normalizes (v : G)
    ∀ (E : core (Fin 6) ≃ₗ[ZMod 2] Additive (Vv L V (v : G))),
      (∀ l : Lv L (v : G), ∀ w,
        E (alternatingCoreRepresentation (Fin 6) (D.localSixMap v i j hij hp l) w) =
          seedRepresentation (Lv L (v : G)) (Vv L V (v : G))
            (Lv_normalizes_Vv L V (v : G)) l (E w)) →
      (∀ w, D.coordinates (Submodule.Quotient.mk (Additive.ofMul
        (show V from ⟨(E w).toMul, Vv_le_V chosen.normalizes _ (E w).toMul.property⟩))) =
          coreToNatural (Fin 8) (extendSix i j hij w)) →
      ∀ w, ((E w).toMul : G) = ((f (extendSix i j hij w)).toMul : G) := by
  let := Vv_elementary chosen.normalizes (v : G)
  dsimp only
  intro E hE hEp
  let inc : Additive (Vv L V (v : G)) →ₗ[ZMod 2] Additive V :=
    (inclusion (Vv_le_V chosen.normalizes (v : G))).toAdditive.toZModLinearMap 2
  change ∀ w, D.coordinates (Submodule.Quotient.mk (inc (E w))) =
    coreToNatural (Fin 8) (extendSix i j hij w) at hEp
  let d := inc.comp E.toLinearMap - f.comp (extendSix i j hij)
  have hd (w) : d w ∈ (fixedSeed L V chosen.normalizes).toSubmodule := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply D.coordinates.injective
    change D.coordinates (Submodule.Quotient.mk (inc (E w) - f (extendSix i j hij w))) = _
    rw [Submodule.Quotient.mk_sub,map_sub,hEp,hfp,sub_self,map_zero]
  have hdc (a : alternatingGroup (Fin 6)) (w) :
      d (alternatingCoreRepresentation (Fin 6) a w) = d w := by
    obtain ⟨l,rfl⟩ := D.localSixMap_surjective v i j hij hp a
    change inc (E (alternatingCoreRepresentation (Fin 6) _ w)) -
      f (extendSix i j hij (alternatingCoreRepresentation (Fin 6) _ w)) = _
    rw [hE]
    change inc (seedRepresentation _ _ _ l (E w)) -
      f (extendSix i j hij (alternatingCoreRepresentation (Fin 6)
        (pointFixerEquiv i j hij (D.localPairMap v i j hij hp l)) w)) = _
    rw [extendSix_equivariant]
    change inc (seedRepresentation _ _ _ l (E w)) -
      f (alternatingCoreRepresentation (Fin 8)
        (D.actorMap (inclusion (Lv_le_L L (v : G)) l)) (extendSix i j hij w)) = _
    rw [hf]
    change seedRepresentation L V chosen.normalizes (inclusion (Lv_le_L L (v : G)) l)
      (inc (E w)) - seedRepresentation L V chosen.normalizes
        (inclusion (Lv_le_L L (v : G)) l) (f (extendSix i j hij w)) = _
    rw [←map_sub]
    exact hd w (inclusion (Lv_le_L L (v : G)) l)
  have hz : Coinvariants.ker (alternatingCoreRepresentation (Fin 6)) ≤ d.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,w⟩,rfl⟩
    change d (_ - _) = 0
    rw [map_sub,hdc,sub_self]
  rw [alternatingSix_core_generated] at hz
  intro w
  exact congrArg (fun x : Additive V => (x.toMul : G))
    (sub_eq_zero.mp (hz (Submodule.mem_top : w ∈ ⊤)))

private theorem pair_weight (i j : Fin 8) (hij : i ≠ j) :
    wordWeight (pair i j).val = 2 := by
  classical
  have hs : (Finset.univ.filter fun k => (pair i j).val k ≠ 0) = {i,j} := by
    ext k
    by_cases hki : k = i
    · subst k; simp [pair,hij,Finset.mem_filter,Pi.single_apply]
    by_cases hkj : k = j
    · subst k; simp [pair,hij.symm,Finset.mem_filter,Pi.single_apply]
    simp [pair,Pi.single_apply,hki,hkj]
  change (Finset.univ.filter _).card = 2
  rw [hs]
  simp [hij]

private theorem pair_nonsingular (i j : Fin 8) (hij : i ≠ j) :
    TerminalOrthogonal.Eight.form (coreToNatural (Fin 8) (pair i j)) ≠ 0 := by
  have hw : hammingNorm (pair i j).val = 2 := pair_weight i j hij
  rw [(EightGeometry.nonsingular_core_iff _).mpr (Or.inl hw)]
  exact one_ne_zero

private theorem sixPair_of_weight (w : core (Fin 6)) (hw : hammingNorm w.val = 2) :
    ∃ a b : Fin 6, a ≠ b ∧ sixPair a b = w := by
  have h : ∀ w : Full (Fin 6), hammingNorm w = 2 →
      ∃ a b : Fin 6, a ≠ b ∧ (sixPair a b).val = w := by decide +kernel
  obtain ⟨a,b,hab,he⟩ := h w.val hw
  exact ⟨a,b,hab,Subtype.ext he⟩

omit [Finite G] in
private theorem cover_pairs_conjugate
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (f : core (Fin 8) →ₗ[ZMod 2] Additive V)
    (hf : ∀ l w, f (alternatingCoreRepresentation (Fin 8) (D.actorMap l) w) =
      seedRepresentation L V chosen.normalizes l (f w))
    (i j a b : Fin 8) (hij : i ≠ j) (hab : a ≠ b) :
    ∃ l : L, conjugation L V chosen.normalizes l (f (pair i j)).toMul =
      (f (pair a b)).toMul := by
  have hm : pair a b ∈ (Set.range fun g : alternatingGroup (Fin 8) =>
      alternatingCoreRepresentation (Fin 8) g (pair i j)) := by
    rw [even_core_orbit_eq_weight (by decide)]
    exact (pair_weight a b hab).trans (pair_weight i j hij).symm
  obtain ⟨g,hg⟩ := hm
  obtain ⟨l,rfl⟩ := D.actorMap_surjective g
  refine ⟨l,?_⟩
  exact congrArg Additive.toMul ((hf l (pair i j)).symm.trans (congrArg f hg))

private theorem map_Lv_conjugation (l : L) (v : G) :
    (Lv L v).map (MulAut.conj (l : G)).toMonoidHom = Lv L ((l : G)*v*(l : G)⁻¹) := by
  have hL : L.map (MulAut.conj (l : G)).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp (L.le_normalizer l.property)
  have hp : (Gv v).map (MulAut.conj (l : G)).toMonoidHom =
      Gv ((l : G)*v*(l : G)⁻¹) := map_pointCentralizer (MulAut.conj (l : G)) v
  have hc : (CLv L v).map (MulAut.conj (l : G)).toMonoidHom =
      CLv L ((l : G)*v*(l : G)⁻¹) := by
    rw [CLv,map_inf _ _ _ (MulAut.conj (l : G)).injective,hL,hp]
    rfl
  rw [Lv,map_embedded_pResidual,hc]
  rfl

private theorem normalizes_Lv_conjugation (l : L) (v : G)
    (hn : Gv v ≤ normalizer (Lv L v : Set G)) :
    Gv ((l : G)*v*(l : G)⁻¹) ≤ normalizer (Lv L ((l : G)*v*(l : G)⁻¹) : Set G) := by
  have hp : (Gv v).map (MulAut.conj (l : G)).toMonoidHom =
      Gv ((l : G)*v*(l : G)⁻¹) := map_pointCentralizer (MulAut.conj (l : G)) v
  rw [←map_Lv_conjugation l v,←hp]
  exact (map_mono hn).trans (le_normalizer_map _)

private def PreferredPoint (f : core (Fin 8) →ₗ[ZMod 2] Additive V) (v : V) : Prop :=
  (∃ i j : Fin 8, i ≠ j ∧ (f (pair i j)).toMul = v) ∨
    ∀ i j : Fin 8, i ≠ j → Gv ((f (pair i j)).toMul : G) ≤ M L

omit [Finite G] in
private theorem preferred_conjugation
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (f : core (Fin 8) →ₗ[ZMod 2] Additive V)
    (hf : ∀ l w, f (alternatingCoreRepresentation (Fin 8) (D.actorMap l) w) =
      seedRepresentation L V chosen.normalizes l (f w))
    (v : V) (hv : PreferredPoint (L := L) f v) (l : L) :
    PreferredPoint (L := L) f (conjugation L V chosen.normalizes l v) := by
  rcases hv with ⟨i,j,hij,rfl⟩ | hv
  · left
    refine ⟨(D.actorMap l).val i,(D.actorMap l).val j,
      fun h => hij ((D.actorMap l).val.injective h),?_⟩
    have hh := hf l (pair i j)
    change f (coreRepresentation (Fin 8) (D.actorMap l).val (pair i j)) = _ at hh
    rw [pair_action] at hh
    exact congrArg Additive.toMul hh
  · exact Or.inr hv

omit [Finite G] in
private theorem exists_preferred_escape
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (f : core (Fin 8) →ₗ[ZMod 2] Additive V)
    (hfp : ∀ w, D.coordinates (Submodule.Quotient.mk (f w)) = coreToNatural (Fin 8) w)
    (v : V) (hv : D.Nonsingular v) (hescape : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧ PreferredPoint (L := L) f w := by
  classical
  by_cases h : ∃ i j : Fin 8, i ≠ j ∧ ¬ Gv ((f (pair i j)).toMul : G) ≤ M L
  · obtain ⟨i,j,hij,he⟩ := h
    refine ⟨(f (pair i j)).toMul,?_,he,Or.inl ⟨i,j,hij,rfl⟩⟩
    change TerminalOrthogonal.Eight.form (D.coordinates (Submodule.Quotient.mk (f (pair i j)))) ≠ 0
    rw [hfp]
    exact pair_nonsingular i j hij
  · refine ⟨v,hv,hescape,Or.inr ?_⟩
    intro i j hij
    by_contra he
    exact h ⟨i,j,hij,he⟩

private theorem cover_pair_normalized
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (f : core (Fin 8) →ₗ[ZMod 2] Additive V)
    (hf : ∀ l w, f (alternatingCoreRepresentation (Fin 8) (D.actorMap l) w) =
      seedRepresentation L V chosen.normalizes l (f w))
    (v : V) (hv : PreferredPoint (L := L) f v)
    (hn : Gv (v : G) ≤ normalizer (Lv L (v : G) : Set G))
    (a b : Fin 8) (hab : a ≠ b) :
    Gv ((f (pair a b)).toMul : G) ≤ normalizer (Lv L ((f (pair a b)).toMul : G) : Set G) := by
  rcases hv with ⟨i,j,hij,he⟩ | hv
  · obtain ⟨l,hl⟩ := cover_pairs_conjugate chosen D f hf i j a b hij hab
    rw [he] at hl
    have hc : (l : G)*(v : G)*(l : G)⁻¹ = ((f (pair a b)).toMul : G) :=
      congrArg Subtype.val hl
    rw [←hc]
    exact normalizes_Lv_conjugation l (v : G) hn
  · exact (le_inf (hv a b hab) le_rfl).trans (Mv_le_normalizer_Lv L _)

private theorem preferred_local_normalizer
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (f : core (Fin 8) →ₗ[ZMod 2] Additive V)
    (hf : ∀ l w, f (alternatingCoreRepresentation (Fin 8) (D.actorMap l) w) =
      seedRepresentation L V H.chosen.normalizes l (f w))
    (hfp : ∀ w, D.coordinates (Submodule.Quotient.mk (f w)) = coreToNatural (Fin 8) w)
    (v : V) (hv : D.Nonsingular v) (hpref : PreferredPoint (L := L) f v)
    (hn : Gv (v : G) ≤ normalizer (Lv L (v : G) : Set G)) :
    Gv (v : G) ⊓ normalizer (Vv L V (v : G) : Set G) ≤ M L := by
  let := Vv_elementary H.chosen.normalizes (v : G)
  obtain ⟨i,j,hij,hp⟩ := nonsingular_pair _ hv
  obtain ⟨E,hE,hEp⟩ := D.local_core_marking H.chosen v i j hij hp
  apply (inf_le_inf hn le_rfl).trans
  apply H.local_moved_normalizer_control D v hv E
    (H.weightTwoResiduals_eq D _ (Vv_le_V H.chosen.normalizes _) E i j hij hEp)
  intro u hu
  obtain ⟨w,hw,rfl⟩ := hu
  obtain ⟨a,b,hab,rfl⟩ := sixPair_of_weight w hw
  have he := marked_core_agrees_cover H.chosen D f hf hfp v i j hij hp E hE hEp (sixPair a b)
  rw [extendSix_pair] at he
  rw [he]
  exact cover_pair_normalized H.chosen D f hf v hpref hn _ _
    (fun h => hab ((complementLetters i j hij).injective h))

/-- In the contrary branch of 12.6.2 choose the source-preferred nonsingular
point in the actual Sylow position. Normality of its point residual suffices
to control the full relative normalizer of V_v, proving the nonnormality
reduction of 12.6.11; no orbit or point-normalizer premise remains.
The normalization and TI inputs are the earlier 12.2.2 clauses. -/
theorem SourceHypothesis.exists_preferred_nonsingular_normalizer_control
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (hescape : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      ((Gv (w : G) ≤ normalizer (Lv L (w : G) : Set G)) →
        Gv (w : G) ⊓ normalizer (Vv L V (w : G) : Set G) ≤ M L) := by
  obtain ⟨f,_,hf,hfp⟩ := D.core_cover H.chosen
  obtain ⟨u,hu,he,hpref⟩ := exists_preferred_escape H.chosen D f hfp v hv hescape
  obtain ⟨l,hw,hTv,hi⟩ := D.exists_nonsingular_sylow_position H.chosen hTV hTI u hu
  let w := conjugation L V H.chosen.normalizes l u
  refine ⟨w,hw,?_,hTv,hi,?_⟩
  · intro hh
    exact he ((centralizer_control_conjugation_iff H.chosen.normalizes l u).mp hh)
  · exact preferred_local_normalizer H D f hf hfp w hw
      (preferred_conjugation H.chosen D f hf u hpref l)

/-- In the contrary branch of 12.6.2 choose the source-preferred nonsingular
point in the actual Sylow position. Normality of its point residual suffices
for the centralizer-control step of 12.6.11; no permutation premise remains.
The normalization and TI inputs are the earlier 12.2.2 clauses. -/
theorem SourceHypothesis.exists_preferred_nonsingular_control
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (hescape : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      ((Gv (w : G) ≤ normalizer (Lv L (w : G) : Set G)) →
        Gv (w : G) ⊓ centralizer (Vv L V (w : G) : Set G) ≤ M L) := by
  obtain ⟨w,hw,he,hs,hi,hn⟩ :=
    H.exists_preferred_nonsingular_normalizer_control D hTV hTI v hv hescape
  refine ⟨w,hw,he,hs,hi,fun h => ?_⟩
  exact (inf_le_inf le_rfl (Subgroup.centralizer_le_normalizer _)).trans (hn h)

omit [Finite G] in
/-- Normality of L_v in G_v puts the literal moved subgroup in O₂(G_v).
This is the first core containment used in the proof of 12.6.11. -/
theorem Vv_le_core_Gv_of_normalized (chosen : Section02.ChosenModule T L V) (v : V)
    (hn : Gv (v : G) ≤ normalizer (Lv L (v : G) : Set G)) :
    Vv L V (v : G) ≤ (Gv (v : G)).pCoreIn 2 :=
  (Vv_le_core_Lv chosen v).trans (pCoreIn_mono_of_normalizes (Lv_le_Gv L (v : G)) hn)

/-- The literal 12.6.11 contradiction branch L_w=K_w. The canonical residual
is normal in G_w, so the preferred point's centralizer controls L without
an assumed permutation action on the weight-two residuals. The moved
subgroup lies in O₂(G_w), whose centralizer is consequently also in M. -/
theorem SourceHypothesis.exists_preferred_nonsingular_Kv_control
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (v : V) (hv : D.Nonsingular v) (hescape : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      (Lv L (w : G) = Kv (w : G) →
        Vv L V (w : G) ≤ (Gv (w : G)).pCoreIn 2 ∧
        Gv (w : G) ⊓ centralizer (Vv L V (w : G) : Set G) ≤ M L ∧
        Gv (w : G) ⊓ centralizer ((Gv (w : G)).pCoreIn 2 : Set G) ≤ M L) := by
  obtain ⟨w,hw,he,hs,hi,hc⟩ := H.exists_preferred_nonsingular_control D hTV hTI v hv hescape
  refine ⟨w,hw,he,hs,hi,fun h => ?_⟩
  have hn : Gv (w : G) ≤ normalizer (Lv L (w : G) : Set G) := by
    rw [h]
    exact (normal_subgroupOf_iff_le_normalizer (Kv_le_Gv (w : G))).mp (Kv_normalIn_Gv (w : G))
  have hW := Vv_le_core_Gv_of_normalized H.chosen w hn
  exact ⟨hW,hc hn,(inf_le_inf le_rfl (Subgroup.centralizer_le hW)).trans (hc hn)⟩

/-- Retain the source's preferred weight-two choice as well as its Sylow
position and normalizer control. This is the choice needed in 12.6.16(2). -/
theorem SourceHypothesis.exists_preferred_nonsingular_core_control
    {K : GroupClass} (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (hproj : ∀ w, coreToNatural (Fin 8) (E w) = D.coordinates (Submodule.Quotient.mk w))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ w : V, D.Nonsingular w ∧ ¬ Gv (w : G) ≤ M L ∧
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 4 ∧
      (∀ u : V, wordWeight (E (Additive.ofMul u)).val = 2 →
        ¬ Gv (u : G) ≤ M L → wordWeight (E (Additive.ofMul w)).val = 2) ∧
      (Gv (w : G) ≤ normalizer (Lv L (w : G) : Set G) →
        Gv (w : G) ⊓ normalizer (Vv L V (w : G) : Set G) ≤ M L) := by
  let f := E.symm.toLinearMap
  have hf (l : L) (x) : f (alternatingCoreRepresentation (Fin 8) (D.actorMap l) x) =
      seedRepresentation L V H.chosen.normalizes l (f x) := by
    apply E.injective
    change E (E.symm _) = E (seedRepresentation L V H.chosen.normalizes l (E.symm x))
    rw [E.apply_symm_apply,hE,E.apply_symm_apply]
  have hp (x) : D.coordinates (Submodule.Quotient.mk (f x)) = coreToNatural (Fin 8) x := by
    rw [←hproj]
    exact congrArg (coreToNatural (Fin 8)) (E.apply_symm_apply x)
  obtain ⟨u,hu,huE,huP⟩ := exists_preferred_escape H.chosen D f hp v hv he
  obtain ⟨l,hw,hs,hi⟩ := D.exists_nonsingular_sylow_position H.chosen hTV hTI u hu
  let w := conjugation L V H.chosen.normalizes l u
  have hwP := preferred_conjugation H.chosen D f hf u huP l
  refine ⟨w,hw,fun h => huE ((centralizer_control_conjugation_iff H.chosen.normalizes l u).mp h),
    hs,hi,?_,preferred_local_normalizer H D f hf hp w hw hwP⟩
  intro x hx hex
  rcases hwP with ⟨i,j,hij,hijw⟩ | hall
  · change (f (pair i j)).toMul = w at hijw
    rw [←hijw]
    change wordWeight (E (E.symm (pair i j))).val = 2
    rw [E.apply_symm_apply]
    exact pair_weight i j hij
  · have hpairs (y : core (Fin 8)) (hy : wordWeight y.val = 2) :
        ∃ i j : Fin 8, i ≠ j ∧ y = pair i j := by
      obtain ⟨i,j,hij,he⟩ := Finset.card_eq_two.mp hy
      refine ⟨i,j,hij,Subtype.ext ?_⟩
      have hc (k : Fin 8) : y.val k ≠ 0 ↔ k = i ∨ k = j := by
        have hh := congrArg (fun s : Finset (Fin 8) => k ∈ s) he
        simpa only [Finset.mem_filter,Finset.mem_univ,true_and,
          Finset.mem_insert,Finset.mem_singleton] using Iff.of_eq hh
      funext k
      have hb : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      by_cases hi : k = i
      · subst k
        simpa [pair,hij] using hb (y.val i) ((hc i).mpr (Or.inl rfl))
      by_cases hj : k = j
      · subst k
        simpa [pair,hij.symm] using hb (y.val j) ((hc j).mpr (Or.inr rfl))
      · have hz : y.val k = 0 := Classical.not_not.mp (fun hn => (hc k).mp hn |>.elim hi hj)
        simp [pair,hi,hj,hz]
    obtain ⟨i,j,hij,hxy⟩ := hpairs (E (Additive.ofMul x)) hx
    have hh : (f (pair i j)).toMul = x := by
      change (E.symm (pair i j)).toMul = x
      rw [←hxy,E.symm_apply_apply]
      rfl
    exact (hex (hh ▸ hall i j hij)).elim

end CFSG.Quasithin.Chapter12.Section06
