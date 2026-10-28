module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.WeakClosureSource
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.LocalContradiction.Actors
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.DoubleNaturalExcludedSetup
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.ChapterE.Section03.SourceContainment
public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence.LocalParameterModule

/-!
# Original local preparation and action contradiction for 12.6.23

The proved fixed-space rank and weak-closure bounds, together with original
normalizer uniqueness, give N_G(W₀) ≤ M and put every solvable overgroup of
T in M. The original fixed line controls C_G(Ω₁Z(T)). The existing reduced
omega-span theorem therefore applies to the literal V_H = ⟨Ω₁Z(T)^H⟩ and
gives C_T(V_H) = O₂(H). Consequently W₀ does not centralize V_H, and an
actual conjugate A = V^g inside the full original Q has nontrivial image in
H/C_H(V_H). Borel placement follows once its source containment in LT is
supplied. The literal M-intersection version of 12.6.22 uses only the earlier
same-ambient structural normalizer identification.

Original uniqueness also puts N_G(V) in N_G(L), so the compatible
seven-dimensional core marking extends to all of N_G(V). Transport by the
same g gives coordinates and the entire normalizer action on A. The local
contradiction then uses B = C_A(V_H), its exact quotient index, and r ≥ 4
to obtain reverse normalization. A marked five-point summand forces the
image down to order two; the eight-point action gives a reverse centralizer
index at most two, contradicting displacement on that same summand.

The final H-star application constructs the actor, the elementary local
span and both eight-letter markings. Its remaining inputs are a faithful
five-letter action of the actual H/C_H(V_H), evenness on Q intersect H,
and a compatible five-point core inside V_H. Their construction and H-star
existence remain source obligations; no unconditional C_V(L)=1 is asserted.
In particular, the proof does not assume C_H(V_H)=O₂(H).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
12.6.22–23, printed pp.829–830, using E.3.34–35 and the local omega-span
preparation for Corollary 12.3.2, printed p.807.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open CentralLine.LocalContradiction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [IsElementaryAbelian 2 V] in
/-- Original normalizer uniqueness applied to the T-invariant chosen module. -/
theorem SourceHypothesis.chosen_normalizer_le
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    normalizer (V : Set G) ≤ M L :=
  H.chosen.normal_subgroup_normalizer_le H.source.toHypothesis1221
    (H.chosen.le_component.trans le_sup_left) H.chosen.ne_bot
    (sup_le H.chosen.normalizes hTV)

omit [IsElementaryAbelian 2 V] in
/-- The literal C_T(V)=Q identity, retaining the full original two-core. -/
theorem SourceHypothesis.chosen_sylow_centralizer_eq_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) = Q T L := by
  have ho : componentOrbit V (T : Subgroup G) = V :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl hTV)
      (le_componentOrbit V T)
  simpa only [ho,Q,LT] using H.chosen.doubledOrbit_sylow_centralizer H.source

omit [IsElementaryAbelian 2 V] in
/-- The actual maximal-two-local uniqueness premise used by E.3.34–35. -/
theorem SourceHypothesis.chosen_centralizer_unique
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) = {M L} := by
  have ho : componentOrbit V (T : Subgroup G) = V :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl hTV)
      (le_componentOrbit V T)
  simpa only [ho,M] using H.chosen.doubledOrbit_centralizer_unique H.source

/-- Source E.3.34 applied to the proved 12.6.22 weak-closure bound. -/
theorem SourceHypothesis.fixed_weakClosure_normalizer_le
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥) :
    normalizer (ChapterE.indexedWeakClosure V T 0 : Set G) ≤ M L :=
  ChapterE.SourceContainment.normalizer_weakClosure_zero_le
    ⟨H.chosen.ne_bot,H.chosen.le_sylow,hTV⟩
    (lt_trans (by decide : (0 : ℕ∞) < 1) (H.fixed_globalW_gt_one D hTV hTI hz))
    (H.chosen_centralizer_unique hTV)

/-- The solvable-overgroup exclusion at the start of 12.6.23. -/
theorem SourceHypothesis.fixed_solvable_overgroup_le
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    {J : Subgroup G} [Group.IsSolvable J] (hTJ : (T : Subgroup G) ≤ J) : J ≤ M L := by
  apply ChapterE.SourceContainment.le_of_solvable
    ⟨H.chosen.ne_bot,H.chosen.le_sylow,hTV⟩ (T.subtype hTJ)
    (H.chosen_centralizer_unique hTV)
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (H.chosen_normalizer_le hTV))
  · simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ] using
      (inf_le_left : (T : Subgroup G) ⊓ centralizer (V : Set G) ≤ T)
  · exact lt_min (H.fixed_globalW_gt_one D hTV hTI hz)
      (lt_of_lt_of_le (by decide : (1 : ℕ∞) < 4) (H.fixed_core_intersections D hTV hTI hz).2)

/-- Every original escaping H-star member is nonsolvable in the fixed-space branch. -/
theorem SourceHypothesis.fixed_hstar_not_solvable
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    {J : Subgroup G} (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L)) :
    ¬ Group.IsSolvable J := by
  intro hs
  let := hs
  exact hJ.1.2 (H.fixed_solvable_overgroup_le D hTV hTI hz hJ.1.1.2)

/-- The original nonzero fixed line lies in the Sylow omega center and controls its full centralizer. -/
theorem SourceHypothesis.fixed_sylow_seed_centralizer_le
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hz : ZV L V ≠ ⊥) :
    centralizer (Z T : Set G) ≤ M L := by
  obtain ⟨z,hzV,hzne⟩ := (ZV L V).bot_or_exists_ne_one.resolve_left hz
  have hzT : z ∈ Z T := by
    rw [Z,←omegaCenterIn_eq_omegaOneAmbient]
    exact (mem_omegaCenterIn_iff _ _).mpr
      ⟨H.chosen.le_sylow hzV.1,
        (le_centralizer_iff.mp (le_sup_right.trans (D.join_centralizes_fixed H.chosen hTV))) hzV,
        elemPow_eq_one_of_isElementaryAbelian z hzV.1⟩
  exact (centralizer_le (Set.singleton_subset_iff.mpr hzT)).trans
    (H.fixed_vector_centralizer_le D hTV z hzV hzne)

omit [IsElementaryAbelian 2 V] in
/-- Identify M with N_G(V) using the precise earlier structural alternative. -/
theorem SourceHypothesis.fixed_normalizer_eq_of_structural
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (structural : Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hz : ZV L V ≠ ⊥) : normalizer (V : Set G) = M L := by
  have hs := (structural L H.source).2.2 V H.chosen
  exact le_antisymm (H.chosen_normalizer_le hs.1) (hs.2.2.2.resolve_right hz)

/-- Literal source 12.6.22(2), with V^g intersect M instead of an unnamed normalizer. -/
theorem SourceHypothesis.fixed_small_corank_intersection_M
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (structural : Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hz : ZV L V ≠ ⊥) (g : G)
    (hk : ChapterE.subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ M L) ≤ 1) :
    V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) := by
  have hs := (structural L H.source).2.2 V H.chosen
  apply H.fixed_small_corank_normalizes D hs.1 hs.2.2.1 hz g
  simpa only [ChapterE.offenderNormalizer,H.fixed_normalizer_eq_of_structural structural hz] using hk

omit [IsElementaryAbelian 2 V] in
/-- The existing reduced omega-span theorem on the identical source seed and H-star group. -/
theorem SourceHypothesis.local_span_elementary
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    {J : Subgroup G} (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L)) :
    IsElementaryAbelian 2 (localSpan T J) :=
  Section04.SLThreeCommutatorSource.ConjugateExistence.localModule_elementary H.source hJ

/-- The actual Sylow kernel is O₂(H); no full-H centralizer identity is inferred. -/
theorem SourceHypothesis.fixed_local_span_sylow_centralizer
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hz : ZV L V ≠ ⊥)
    {J : Subgroup G} (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L)) :
    (T : Subgroup G) ⊓ centralizer (localSpan T J : Set G) = J.pCoreIn 2 :=
  Section04.SLThreeCommutatorSource.ConjugateExistence.localModule_sylow_centralizer_eq_core
    H.source H.chosen.sylow_normalizes_component (H.fixed_sylow_seed_centralizer_le D hTV hz) hJ

/-- Weak-closure normalizer control excludes centralization of the original local span. -/
theorem SourceHypothesis.fixed_weakClosure_not_centralizing_local_span
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    {J : Subgroup G} (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L)) :
    ¬ ChapterE.indexedWeakClosure V T 0 ≤ centralizer (localSpan T J : Set G) := by
  intro hc
  have hWcore : ChapterE.indexedWeakClosure V T 0 ≤ J.pCoreIn 2 := by
    rw [←H.fixed_local_span_sylow_centralizer D hTV hz hJ]
    exact le_inf (ChapterE.indexedWeakClosure_le _ _ _) hc
  have ht : ((T.subtype hJ.1.1.2 : Sylow 2 J) : Subgroup J).map J.subtype = T :=
    map_subgroupOf_eq_of_le hJ.1.1.2
  have hnorm := ChapterE.normalizer_le_weakClosure_normalizer_of_two_overgroup V J
    (T.subtype hJ.1.1.2) (J.pCoreIn 2) 0 (isPGroup_pCoreIn 2 J) (pCoreIn_le 2 J)
    (by simpa only [ht] using hWcore)
  rw [ht] at hnorm
  have hJN : J ≤ normalizer (J.pCoreIn 2 : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  exact hJ.1.2 (hJN.trans (hnorm.trans (H.fixed_weakClosure_normalizer_le D hTV hTI hz)))

/-- Select an actual conjugate V^g inside Q with nontrivial image under the literal local quotient. -/
theorem SourceHypothesis.fixed_exists_nontrivial_local_actor
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    {J : Subgroup G} (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L)) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      V.map (MulAut.conj g).toMonoidHom ≤ Q T L ∧
      localImage T J (V.map (MulAut.conj g).toMonoidHom) ≠ ⊥ := by
  obtain ⟨g,hAT,hAW,_,hne⟩ := exists_conjugate_actor hJ.1.1.2
    (H.fixed_weakClosure_not_centralizing_local_span D hTV hTI hz hJ)
  refine ⟨g,hAT,?_,hne⟩
  rw [←H.chosen_sylow_centralizer_eq_core hTV]
  exact le_inf hAT (hAW.trans (H.fixed_weakClosure_zero_centralizes D hTV hTI hz))

/-- Place the selected conjugate in the Borel two-core once its source LT containment is proved. -/
theorem SourceHypothesis.fixed_local_actor_exists
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    {J : Subgroup G} (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L))
    (hJM : J ⊓ M L ≤ LT T L) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      V.map (MulAut.conj g).toMonoidHom ≤ (J ⊓ M L).pCoreIn 2 ∧
      localImage T J (V.map (MulAut.conj g).toMonoidHom) ≠ ⊥ :=
  exists_conjugate_actor_in_borel_core hJ.1.1.2 H.chosen.sylow_normalizes_component hJM
    (H.chosen_sylow_centralizer_eq_core hTV)
    (H.fixed_weakClosure_zero_centralizes D hTV hTI hz)
    (H.fixed_weakClosure_not_centralizing_local_span D hTV hTI hz hJ)

/-- Extend the original compatible core coordinates to the whole ambient normalizer of V. -/
theorem SourceHypothesis.exists_normalizer_core_action
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w)) :
    ∃ f : normalizer (V : Set G) →* Equiv.Perm (Fin 8),
      (∀ l : L, f (inclusion H.chosen.normalizes l) = (D.actorMap l).val) ∧
      ∀ n w, E (Representation.elementaryRepresentation (p := 2) V.normalizerMonoidHom n w) =
        coreRepresentation (Fin 8) (f n) (E w) := by
  let N := normalizer (V : Set G)
  let A := L.subgroupOf N
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer H.chosen.normalizes).mpr
    (H.chosen_normalizer_le hTV)
  let e : A ≃* L := subgroupOfEquivOfLe H.chosen.normalizes
  obtain ⟨f,hf,ha,_⟩ := EightCoreAction.exists_ambient_hom
    (Representation.elementaryRepresentation (p := 2) V.normalizerMonoidHom)
    A (D.actorMap.comp e.toMonoidHom) (D.actorMap_surjective.comp e.surjective) E
    (fun l w => hE (e l) w)
  exact ⟨f,(fun l => hf ⟨inclusion H.chosen.normalizes l,l.property⟩),ha⟩

/-- Transport the full normalizer action along the same conjugator, retaining the original coordinates. -/
theorem SourceHypothesis.exists_conjugate_normalizer_core_action
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w)) (g : G) :
    let A := V.map (MulAut.conj g).toMonoidHom
    letI : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
    ∃ (e8 : Additive A ≃ₗ[ZMod 2] core (Fin 8))
      (β : normalizer (A : Set G) →* Equiv.Perm (Fin 8)),
      (∀ w, e8 (ChapterE.automizerModuleEquiv V (MulAut.conj g) w) = E w) ∧
      ∀ n a, e8 (Representation.elementaryRepresentation (p := 2) A.normalizerMonoidHom n a) =
        coreRepresentation (Fin 8) (β n) (e8 a) := by
  let e := MulAut.conj g
  let A := V.map e.toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  obtain ⟨f,_,hf⟩ := H.exists_normalizer_core_action D hTV E hE
  have hn (n : normalizer (A : Set G)) : e.symm (n : G) ∈ normalizer (V : Set G) := by
    have hh : (n : G) ∈ (normalizer (V : Set G)).map e.toMonoidHom := by
      rw [map_equiv_normalizer_eq]
      exact n.property
    obtain ⟨x,hx,he⟩ := hh
    rw [←he]
    change e.symm (e x) ∈ normalizer (V : Set G)
    rw [e.symm_apply_apply]
    exact hx
  let φ : normalizer (A : Set G) →* normalizer (V : Set G) :=
    (e.symm.toMonoidHom.comp (normalizer (A : Set G)).subtype).codRestrict _ hn
  let F := ChapterE.automizerModuleEquiv V e
  let e8 := F.symm.trans E
  refine ⟨e8,f.comp φ,?_,?_⟩
  · intro w
    exact congrArg E (F.symm_apply_apply w)
  · intro n a
    change E (F.symm (Representation.elementaryRepresentation A.normalizerMonoidHom n a)) =
      coreRepresentation (Fin 8) (f (φ n)) (E (F.symm a))
    rw [←hf]
    apply congrArg E
    apply F.injective
    rw [F.apply_symm_apply]
    obtain ⟨b,rfl⟩ := F.surjective a
    rw [F.symm_apply_apply]
    have hnAut : ChapterE.automizerMapEquiv V e
        (V.normalizerMonoidHom.rangeRestrict (φ n)) = A.normalizerMonoidHom.rangeRestrict n := by
      apply Subtype.ext
      apply MulEquiv.ext
      intro x
      obtain ⟨y,rfl⟩ := (e.subgroupMap V).surjective x
      rw [ChapterE.automizerMapEquiv_apply]
      apply Subtype.ext
      change e (e.symm (n : G) * (y : G) * (e.symm (n : G))⁻¹) =
        (n : G) * e (y : G) * (n : G)⁻¹
      simp only [map_mul,map_inv,e.apply_symm_apply]
    have heq := ChapterE.automizerRepresentation_equivariant V e
      (V.normalizerMonoidHom.rangeRestrict (φ n)) b
    rw [hnAut] at heq
    exact heq.symm

/-- The source local action contradiction after selection of the actual
conjugate. The original global-r bound and both eight-letter coordinates
are supplied here; no equality C_H(V_H)=O₂(H) is needed. -/
theorem SourceHypothesis.fixed_marked_local_actor_contradiction
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    {J : Subgroup G} [IsElementaryAbelian 2 (localSpan T J)]
    {g : G} (hAJ : V.map (MulAut.conj g).toMonoidHom ≤ J)
    (hne : localImage T J (V.map (MulAut.conj g).toMonoidHom) ≠ ⊥)
    (α : LocalQuotient T J →* Equiv.Perm (Fin 5)) (hα : Function.Injective α)
    (heven : ∀ a : V.map (MulAut.conj g).toMonoidHom,
      α (localActorMap (T := T) hAJ a) ∈ alternatingGroup (Fin 5))
    (j : core (Fin 5) →ₗ[ZMod 2] Additive (localSpan T J)) (hj : Function.Injective j)
    (he : ∀ (a : V.map (MulAut.conj g).toMonoidHom) v,
      j (coreRepresentation (Fin 5) (α (localActorMap (T := T) hAJ a)) v) =
        seedRepresentation (V.map (MulAut.conj g).toMonoidHom) (localSpan T J)
          (hAJ.trans (normalizes_localSpan T J)) a (j v)) : False := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let B := A ⊓ centralizer (localSpan T J : Set G)
  have hk : ChapterE.subgroupCorank A B ≤ 2 := by
    change Nat.log 2 ((A ⊓ centralizer (localSpan T J : Set G)).relIndex A) ≤ 2
    rw [inf_relIndex_left,←localImage_card hAJ]
    exact (Nat.log_mono_right (b := 2) (localImage_card_le_four hAJ α hα heven)).trans
      (by decide)
  have hr := (H.fixed_core_intersections D hTV hTI hz).2
  have hnorm : localSpan T J ≤ normalizer (A : Set G) := by
    apply (le_centralizer_iff.mp (show B ≤ centralizer (localSpan T J : Set G) from inf_le_right)).trans
    apply ChapterE.centralizer_le_normalizer_of_corank_lt_globalR (show B ≤ A from inf_le_left)
    change (ChapterE.subgroupCorank A B : ℕ∞) < ChapterE.globalR (V.map (MulAut.conj g).toMonoidHom)
    rw [ChapterE.globalR_map_equiv]
    exact lt_of_lt_of_le (by exact_mod_cast (show ChapterE.subgroupCorank A B < 4 by omega)) hr
  have hquad := quadratic_of_commutator_le_actor
    (hAJ.trans (normalizes_localSpan T J)) (le_normalizer_iff_commutator_le_left.mp hnorm)
  have hsmall := localImage_card_le_two_of_quadratic hAJ α hα heven j hj he hquad
  rw [localImage_card hAJ] at hsmall
  obtain ⟨E,hE,_⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  obtain ⟨e8,β,_,he8⟩ := H.exists_conjugate_normalizer_core_action D hTV E hE g
  have hreverse := core_centralizer_index_le_two hnorm e8
    (β.comp (inclusion hnorm)) (fun u a => he8 (inclusion hnorm u) a) hsmall
  have hnot : ¬ A ≤ centralizer (localSpan T J : Set G) :=
    fun h => hne ((localImage_eq_bot_iff hAJ).mpr h)
  obtain ⟨a,ha,hna⟩ := SetLike.not_le_iff_exists.mp hnot
  let aA : A := ⟨a,ha⟩
  let αA : A →* alternatingGroup (Fin 5) :=
    (α.comp (localActorMap (T := T) hAJ)).codRestrict _ heven
  have hmove : αA aA ≠ 1 := by
    intro hz'
    have hq : localActorMap (T := T) hAJ aA = 1 := by
      apply hα
      exact (congrArg Subtype.val hz').trans α.map_one.symm
    have hh : aA ∈ (localActorMap (T := T) hAJ).ker := hq
    rw [localActorMap_ker] at hh
    exact hna hh
  have hlo := conjugation_displacement_ge_two
    (hAJ.trans (normalizes_localSpan T J)) αA j hj he aA hmove
  have hhi := conjugation_displacement_le_centralizer_corank
    (hAJ.trans (normalizes_localSpan T J)) (show A ≤ A from le_rfl) aA ha
  have hlog := Nat.log_mono_right (b := 2) hreverse
  norm_num at hlog
  omega


/-- The actual H-star application: source weak closure selects the conjugate
inside Q, so only the five-point marking on Q intersect J remains explicit.
The local span's elementary structure and the eight-point normalizer marking
are both constructed from the original source hypotheses. -/
theorem SourceHypothesis.fixed_hstar_five_action_contradiction
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥)
    {J : Subgroup G} (hJ : J ∈ Chapter3.HStar (T : Subgroup G) (M L)) :
    letI := H.local_span_elementary hJ
    ∀ (α : LocalQuotient T J →* Equiv.Perm (Fin 5)), Function.Injective α →
      (∀ a : (Q T L ⊓ J : Subgroup G),
        α (localActorMap (T := T) (show Q T L ⊓ J ≤ J from inf_le_right) a) ∈
          alternatingGroup (Fin 5)) →
      ∀ j : core (Fin 5) →ₗ[ZMod 2] Additive (localSpan T J), Function.Injective j →
      (∀ (a : (Q T L ⊓ J : Subgroup G)) v,
        j (coreRepresentation (Fin 5)
          (α (localActorMap (T := T) (show Q T L ⊓ J ≤ J from inf_le_right) a)) v) =
        seedRepresentation (Q T L ⊓ J) (localSpan T J)
          (inf_le_right.trans (normalizes_localSpan T J)) a (j v)) → False := by
  let := H.local_span_elementary hJ
  intro α hα heven j hj he
  obtain ⟨g,hAT,hAQ,hne⟩ := H.fixed_exists_nontrivial_local_actor D hTV hTI hz hJ
  have hAJ := hAT.trans hJ.1.1.2
  let i := inclusion (le_inf hAQ hAJ)
  apply H.fixed_marked_local_actor_contradiction D hTV hTI hz hAJ hne α hα
    (fun a => heven (i a)) j hj
  intro a v
  exact he (i a) v

end CFSG.Quasithin.Chapter12.Section06
