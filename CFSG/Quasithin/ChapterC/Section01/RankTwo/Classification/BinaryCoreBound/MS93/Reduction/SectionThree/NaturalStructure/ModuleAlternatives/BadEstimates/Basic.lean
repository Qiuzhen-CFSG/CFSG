module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.SourceCases
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.Conventions
public import Theory.GroupTheory.Commutator.NormalClosure

/-!
# Critical commutators and the remaining bad-case action inputs

Critical reversal gives the literal endpoint Z required by source 2.3(c).
The critical X commutator cannot be normal in the initial vertex group:
normal closure in the simple quotient and two-residual commutator idempotence
would make it trivial. This argument needs no module classification.

The Frattini condition makes the actual finite join elementary abelian, so Y
centralizes X_a and the source R = [Z_a,Z_a']. The correctly oriented estimate
from 3.3 then implies [Y,Z_a'] ≤ [X_a,X_a']. Normalization and equality of
endpoint images modulo Q_a give normality in the initial edge kernel and
commonness of these commutators. `badCaseEstimates_of_local_bounds` assembles
these deductions with its two remaining action inputs explicit.

Edge transitivity also supplies a critical endpoint through every prescribed
edge. The genuine source offender is transported into that edge's image under
the marked SL₃(2) quotient. Its bad-case uniqueness is not assumed or proved
here; `edgeActor_rank_le_fixedCodim` records the consequence of that eventual
uniqueness theorem needed for comparing the two critical endpoints.

`Source33Bound` and `CriticalImageControl` are output specifications, not
proved consequences of `BadCase`. The missing concrete action calculations
must be supplied before this becomes a proof of all bad-case estimates.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (2.2)--(2.3), notation (3.0), (3.3), and the initial argument of (3.8),
printed pp.856–859,866–868,877. In (3.3), R = [Z_a,Z_a'] and
A = X_a ∩ Q_a'; the intersection in (2.3)(c) has the opposite orientation.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}


private theorem quadratic_commutator_not_normal (source : LocalSource L R)
    (W A : Subgroup M) [W.Normal] (hpW : IsPGroup 2 W)
    (hcore : pCore 2 M ≤ centralizer (W : Set M))
    (hA : ¬ A ≤ pCore 2 M) (hquad : ⁅W, A⁆ ≤ centralizer (A : Set M))
    (hne : ⁅W, A⁆ ≠ ⊥) : ¬ (⁅W, A⁆).Normal := by
  intro hD
  let D := ⁅W, A⁆
  let : D.Normal := hD
  let N := normalClosure (A : Set M)
  have hLN : L ≤ N := by
    let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
    have hn : (N.map source.projection).Normal :=
      (inferInstance : N.Normal).map _ source.projection_surjective
    have htop : N.map source.projection = ⊤ := by
      rcases hn.eq_bot_or_eq_top with h | h
      · exact False.elim (hA (le_normalClosure.trans (by
          simpa only [source.projection_kernel] using (Subgroup.map_eq_bot_iff _).mp h)))
      · exact h
    exact source.residual_le_of_image_top N htop
  have hNC : N ≤ centralizer (D : Set M) :=
    normalClosure_le_normal (fun _ ha => (le_centralizer_iff.mp hquad) ha)
  have hWD : ⁅W, L⁆ ≤ D :=
    (commutator_mono le_rfl hLN).trans
      (commutator_normalClosure_le_of_normal W A D le_rfl)
  have hWL : ⁅W, L⁆ = ⊥ := by
    have hid := commutator_isPPerfect_idempotent L W
      (source.residual ▸ isPPerfect_pResidual 2) hpW le_normalizer_of_normal
    apply le_bot_iff.mp
    rw [← hid]
    exact (commutator_mono hWD le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp (hLN.trans hNC))).le
  have hall : (⊤ : Subgroup M) ≤ centralizer (W : Set M) := by
    rw [← source.residual_sup_core]
    exact sup_le (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp hWL)) hcore
  exact hne (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp (le_top.trans hall)))

/-- The endpoint choice in 2.3(c) is the actual Z at the critical endpoint. -/
theorem critical_endpoint_choice (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false)
    (a' : Vertex R) (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    Z R a' ≤ X R a' ∧ ¬ Z R a' ≤ Q R a := by
  have ha' := critical_endpoint_color R a ha _ hc
  exact ⟨geometry.omega_bound a' ha' (by
    rw [geometry.distance_constant a' ha']; exact hb),
    (source.critical_reverse geometry a ha a' ha' hc).2⟩

private theorem local_embedding (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) :
    ∃ f : M →* FreeAmalgam R, Function.Injective f ∧
      f.range = stabilizer R a ∧ (pCore 2 M).map f = Q R a := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  refine ⟨(MulAut.conj g⁻¹).toMonoidHom.comp (embedM R),
    (MulAut.conj g⁻¹).injective.comp (embedM_injective R), ?_, ?_⟩
  · rw [MonoidHom.range_comp]
    exact (stabilizer_mVertex R g).symm
  · rw [← Subgroup.map_map, ← Q_alpha R source.two_group source.core_le]
    have h := Q_act R g (alpha R)
    simpa only [alpha, act_mVertex, one_mul] using h.symm

/-- The auxiliary commutator is never normal in the initial vertex stabilizer.
This needs no classification of the local module. -/
theorem critical_commutator_not_normal (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false)
    (a' : Vertex R) (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    ¬ ((⁅X R a, X R a'⁆).subgroupOf (stabilizer R a)).Normal := by
  obtain ⟨f, hf, hrange, hcore⟩ := local_embedding source a ha
  have ha' := critical_endpoint_color R a ha _ hc
  have hrev := source.critical_reverse geometry a ha a' ha' hc
  have hX : X R a ≤ stabilizer R a := (omegaCenter_le _).trans (fun _ hx => hx.1)
  have hA := critical_X_le_stabilizer source geometry hb a' ha' a hrev
  let W := (X R a).comap f
  let A := (X R a').comap f
  have hWmap : W.map f = X R a := by
    rw [map_comap_eq, hrange, inf_eq_right.mpr hX]
  have hAmap : A.map f = X R a' := by
    rw [map_comap_eq, hrange, inf_eq_right.mpr hA]
  have hWnormal : W.Normal := by
    constructor
    intro w hw m
    change f (m * w * m⁻¹) ∈ X R a
    simpa only [map_mul, map_inv] using le_normalizer_iff.mp
      (X_normalized R a) (f m) (hrange ▸ ⟨m, rfl⟩) (f w) hw
  let : W.Normal := hWnormal
  have hpW : IsPGroup 2 W := pCore_isPGroup.to_le (by
    apply (Subgroup.map_le_map_iff_of_injective hf).mp
    rw [hWmap, hcore]
    exact omegaCenter_le _)
  have hDmap : (⁅W, A⁆).map f = ⁅X R a, X R a'⁆ := by
    rw [map_commutator, hWmap, hAmap]
  have hCA : pCore 2 M ≤ centralizer (W : Set M) := by
    intro q hq w hw
    apply hf
    simpa only [map_mul] using (Q_le_centralizer_X R a
      (hcore ▸ mem_map_of_mem f hq)) (f w) hw
  have hAout : ¬ A ≤ pCore 2 M := by
    intro h
    exact hrev.2 ((critical_endpoint_choice source geometry hb a ha a' hc).1.trans
      (hAmap ▸ hcore ▸ map_mono h))
  have hDle := critical_commutator_le_intersection source geometry hb a ha a' hc
  have hquad : ⁅W, A⁆ ≤ centralizer (A : Set M) := by
    intro d hd x hx
    apply hf
    have hd' : f d ∈ X R a' := hDle (hDmap ▸ mem_map_of_mem f hd) |>.2
    have hcomm := (mem_omegaCenter_iff.mp hd').2.2 (f x) (omegaCenter_le _ hx)
    simpa only [map_mul] using hcomm
  have hne : ⁅W, A⁆ ≠ ⊥ := by
    intro h
    have hzero : ⁅X R a, X R a'⁆ = ⊥ := by rw [← hDmap, h, Subgroup.map_bot]
    apply source.critical_noncommutation geometry a ha hc
    apply le_bot_iff.mp
    rw [← hzero]
    exact commutator_mono
      (geometry.omega_bound a ha (by rw [geometry.distance_constant a ha]; exact hb))
      (critical_endpoint_choice source geometry hb a ha a' hc).1
  intro hn
  apply quadratic_commutator_not_normal source W A
    hpW hCA hAout hquad hne
  have hnorm := (normal_subgroupOf_iff_le_normalizer (hDle.trans inf_le_left |>.trans hX)).mp hn
  constructor
  intro d hd m
  apply (mem_map_iff_mem hf).mp
  rw [hDmap]
  simpa only [map_mul, map_inv] using le_normalizer_iff.mp hnorm
    (f m) (hrange ▸ ⟨m, rfl⟩) (f d) (hDmap ▸ mem_map_of_mem f hd)

/-- Elementary abelianness of the finite join forces Y to centralize X_a. -/
theorem frattini_join_centralizes_X (source : LocalSource L R) (geometry : Geometry R)
    (a : Vertex R) (ha : color R a = false) (t : Vertex R)
    (ht : (cosetGraph R).dist a t < criticalDistance R a (geometry.exists_critical a ha))
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ Q R t)
    (hPhi : frattini (Y ⊔ X R a : Subgroup (FreeAmalgam R)) = ⊥) :
    Y ≤ centralizer (X R a : Set (FreeAmalgam R)) := by
  let := (frattini_join_iff source geometry a ha t ht Y hY).mp hPhi
  intro y hy x hx
  have he := mul_comm (⟨x, (le_sup_right : X R a ≤ Y ⊔ X R a) hx⟩ : (Y ⊔ X R a : Subgroup (FreeAmalgam R)))
    (⟨y, (le_sup_left : Y ≤ Y ⊔ X R a) hy⟩ : (Y ⊔ X R a : Subgroup (FreeAmalgam R)))
  exact congrArg Subtype.val he

/-- The Frattini hypothesis also discharges the exact centralizer premise
in printed 3.3: its R is [Z_a,Z_a']. -/
theorem frattini_join_centralizes_critical_Z (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (ht : (cosetGraph R).dist a t <
      criticalDistance R a (geometry.exists_critical a ha))
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ Q R t)
    (hPhi : frattini (Y ⊔ X R a : Subgroup (FreeAmalgam R)) = ⊥) :
    Y ≤ Q R t ⊓ centralizer ((⁅Z R a, Z R a'⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  refine le_inf hY ((frattini_join_centralizes_X source geometry a ha t ht Y hY hPhi).trans
    (centralizer_le ?_))
  exact (commutator_mono
    (geometry.omega_bound a ha (by rw [geometry.distance_constant a ha]; exact hb))
    (critical_endpoint_choice source geometry hb a ha a' hc).1).trans
      ((critical_commutator_le_intersection source geometry hb a ha a' hc).trans inf_le_left)

/-- The bad-branch local estimate with the literal orientation printed in
3.3, p.866. R on that page means [Z_a,Z_a']; A means X_a ∩ Q_a'.
This is an output specification for the remaining local-action calculation. -/
def Source33Bound (R : Subgroup M) (geometry : Geometry R) : Prop :=
  ∀ a (ha : color R a = false) a',
    CriticalPair R a a' (geometry.exists_critical a ha) →
    ∀ t, Adjacent R a' t →
    (cosetGraph R).dist a t + 1 = (cosetGraph R).dist a a' →
    ∀ Y : Subgroup (FreeAmalgam R),
    Y ≤ Q R t ⊓ centralizer ((⁅Z R a, Z R a'⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) →
    ⁅Z R a', Y⁆ ≤ ⁅X R a, X R a'⁆ ⊔ ⁅X R a ⊓ Q R a', Y⁆

/-- Under the source Frattini premise, the correctly oriented 3.3 bound
actually gives the stronger containment [Y,Z_a'] ≤ [X_a,X_a']. -/
theorem commutator_bound_of_source33 (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (h33 : Source33Bound R geometry)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a' t)
    (ht : (cosetGraph R).dist a t + 1 = (cosetGraph R).dist a a')
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ Q R t)
    (hPhi : frattini (Y ⊔ X R a : Subgroup (FreeAmalgam R)) = ⊥) :
    ⁅Y, Z R a'⁆ ≤ ⁅X R a, X R a'⁆ := by
  have hsmall : (cosetGraph R).dist a t <
      criticalDistance R a (geometry.exists_critical a ha) := by
    have hd := hc.1
    omega
  have hcentral := frattini_join_centralizes_X source geometry a ha t hsmall Y hY hPhi
  have hzero : ⁅X R a ⊓ Q R a', Y⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (inf_le_left.trans (le_centralizer_iff.mp hcentral))
  have h := h33 a ha a' hc t hat ht Y
    (frattini_join_centralizes_critical_Z source geometry hb a ha a' hc t hsmall Y hY hPhi)
  rwa [hzero, sup_bot_eq, commutator_comm] at h

/-- The two quotient-image properties used for the auxiliary subgroup.
Joins with Q are preimages of the actual endpoint images in G_a/Q_a.
The remaining comparison proof must derive this from edge offender rigidity. -/
structure CriticalImageControl (R : Subgroup M) (geometry : Geometry R) : Prop where
  normalized : ∀ a (ha : color R a = false) a',
    CriticalPair R a a' (geometry.exists_critical a ha) →
    ∀ t, Adjacent R a t →
    (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a' →
    Q R t ≤ normalizer ((X R a' ⊔ Q R a : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R))
  common : ∀ a (ha : color R a = false) a',
    CriticalPair R a a' (geometry.exists_critical a ha) →
    ∀ t, Adjacent R a t →
    (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a' →
    ∀ c, CriticalPair R a c (geometry.exists_critical a ha) →
    (cosetGraph R).dist t c + 1 = (cosetGraph R).dist a c →
    X R a' ⊔ Q R a = X R c ⊔ Q R a

private theorem commutator_join_kernel (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false)
    (a' : Vertex R) (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    ⁅X R a, X R a'⁆ = ⁅X R a, X R a' ⊔ Q R a⁆ := by
  have ha' := critical_endpoint_color R a ha _ hc
  have hrev := source.critical_reverse geometry a ha a' ha' hc
  exact commutator_eq_of_centralizing_sup (sup_comm _ _) (Q_le_centralizer_X R a)
    ((critical_X_le_stabilizer source geometry hb a' ha' a hrev).trans (X_normalized R a))

/-- Equal endpoint images give equal auxiliary commutators, without
identifying X and Z. -/
theorem critical_commutator_eq_of_join_eq (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false)
    (a' : Vertex R) (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (c : Vertex R) (hcc : CriticalPair R a c (geometry.exists_critical a ha))
    (heq : X R a' ⊔ Q R a = X R c ⊔ Q R a) :
    ⁅X R a, X R a'⁆ = ⁅X R a, X R c⁆ := by
  rw [commutator_join_kernel source geometry hb a ha a' hc, heq,
    ← commutator_join_kernel source geometry hb a ha c hcc]

/-- Normalization of the endpoint image lifts to normality of the actual
commutator in the initial edge kernel. -/
theorem critical_commutator_normal_of_join_normalized
    (source : LocalSource L R) (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a t)
    (hn : Q R t ≤ normalizer ((X R a' ⊔ Q R a : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R))) :
    ((⁅X R a, X R a'⁆).subgroupOf (Q R t)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [commutator_join_kernel source geometry hb a ha a' hc]
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq, map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hn hg),
    mem_normalizer_iff_map_conj_eq.mp (X_normalized R a
      (hg.2 a (adjacent_symm R hat)))]

/-- Conditional assembly of 2.3(c,d). Only the local-action calculation
and critical-image comparison remain as explicit inputs; endpoint
noncontainment and vertex nonnormality have independent proofs above. -/
theorem badCaseEstimates_of_local_bounds (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (h33 : Source33Bound R geometry)
    (himages : CriticalImageControl R geometry) : BadCaseEstimates R geometry where
  commutator_bound a ha a' hc t hat ht Y hY hPhi :=
    (commutator_bound_of_source33 source geometry (by omega) h33 a ha a' hc t hat ht Y hY hPhi).trans
      le_sup_left
  auxiliary_normal a ha a' hc t hat ht :=
    critical_commutator_normal_of_join_normalized source geometry (by omega) a ha a' hc t hat
      (himages.normalized a ha a' hc t hat ht)
  auxiliary_not_normal a ha a' hc :=
    critical_commutator_not_normal source geometry (by omega) a ha a' hc
  auxiliary_common a ha a' hc t hat ht c hcc htc :=
    (critical_commutator_eq_of_join_eq source geometry (by omega) a ha a' hc c hcc
      (himages.common a ha a' hc t hat ht c hcc htc)).le


omit [Finite M] in
/-- Every prescribed initial edge is on a critical geodesic. The endpoint
is transported using edge transitivity, keeping its initial vertex fixed. -/
theorem exists_critical_through_edge (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (t : Vertex R) (hat : Adjacent R a t) :
    ∃ a', CriticalPair R a a' (geometry.exists_critical a ha) ∧
      (cosetGraph R).dist t a' + 1 = (cosetGraph R).dist a a' := by
  obtain ⟨a', hc⟩ := criticalPair_exists R a (geometry.exists_critical a ha)
  obtain ⟨s, has, hs⟩ := exists_adjacent_dist_sub_one R a a' (by
    rw [hc.1, geometry.distance_constant a ha]; exact hb)
  obtain ⟨f, hf | hf⟩ := edge_transitive R has hat
  · obtain ⟨hfa, hfs⟩ := hf
    have hfcol : color R (act R f a) = false := by rw [hfa, ha]
    have hc' := (criticalPair_act_iff R f a a' (geometry.exists_critical a ha)
      (geometry.exists_critical (act R f a) hfcol)).mpr hc
    refine ⟨act R f a', by simpa only [hfa] using hc', ?_⟩
    calc
      _ = (cosetGraph R).dist (act R f s) (act R f a') + 1 := by rw [hfs]
      _ = (cosetGraph R).dist s a' + 1 := by rw [dist_act]
      _ = (cosetGraph R).dist a a' := hs
      _ = (cosetGraph R).dist (act R f a) (act R f a') := (dist_act R f a a').symm
      _ = _ := by rw [hfa]
  · have htcol : color R t = false := by rw [← hf.1, action_preserves_color, ha]
    exact (adjacent_color_ne R hat (ha.trans htcol.symm)).elim

/-- Actual offenders exist in every marked edge image, before any bad-case
classification or uniqueness calculation. -/
theorem edgeActor_has_offender (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (t : Vertex R) (hat : Adjacent R (alpha R) t) :
    letI := X_elementary R (alpha R)
    ∃ A ≤ edgeActor source t,
      Representation.BinaryOffender.IsOffender (Offenders.linearize (xAction source)) A := by
  let := Q_normal R (alpha R)
  let := X_elementary R (alpha R)
  let := finite_X R (alpha R)
  obtain ⟨a', hc, ht⟩ := exists_critical_through_edge geometry hb (alpha R) rfl t hat
  obtain ⟨w⟩ := (source.factorization_offenders geometry hb (alpha R) rfl a' hc t hat ht).2
  let := w.finite
  let := w.normal
  have hAS : w.A ≤ stabilizer R (alpha R) :=
    w.le_edge.trans (fun _ hx => hx.2 (alpha R) (adjacent_symm R hat))
  let i := Offenders.quotientInclusion w.A (stabilizer R (alpha R)) (Q R (alpha R))
    hAS w.normal (Q_normal R (alpha R))
  have hoff := w.linear_offender (stabilizer R (alpha R)) hAS (Q_normal R (alpha R))
    (X_normalized R (alpha R)) (Q_le_centralizer_X R (alpha R))
  let e := quotientMarking source
  refine ⟨i.range.map e.toMonoidHom, ?_, ?_⟩
  · rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
    induction q using QuotientGroup.induction_on with
    | H x =>
      refine ⟨⟨x.val, hAS x.property⟩, w.le_edge x.property, ?_⟩
      exact (quotientMarking_mk source ⟨x.val, hAS x.property⟩).symm
  · apply Representation.BinaryOffender.IsOffender.map_equivariant
      (Offenders.linearize (X_quotientConjugation R (alpha R)))
      (Offenders.linearize (xAction source)) e.toMonoidHom e.injective
      (LinearEquiv.refl (ZMod 2) _) ?_ hoff
    intro g v
    change Additive.ofMul (X_quotientConjugation R (alpha R) g v.toMul) =
      Additive.ofMul (X_quotientConjugation R (alpha R) (e.symm (e g)) v.toMul)
    rw [MulEquiv.symm_apply_apply]


/-- Equality for the unique offender rules out every strict offender on
that actual edge. This is the numerical input for endpoint reciprocity. -/
theorem edgeActor_rank_le_fixedCodim (source : LocalSource L R)
    (hu : EdgeOffenderUniqueness source) (t : Vertex R)
    (hat : Adjacent R (alpha R) t) :
    letI := X_elementary R (alpha R)
    ∀ B ≤ edgeActor source t, Representation.BinaryOffender.IsElementaryTwo B →
      Representation.BinaryOffender.rank B ≤
        Representation.BinaryOffender.fixedCodim (Offenders.linearize (xAction source)) B := by
  let := X_elementary R (alpha R)
  obtain ⟨A, _, _, hunique, heq, _⟩ := hu t hat
  intro B hB helem
  by_contra h
  have hoff : Representation.BinaryOffender.IsOffender (Offenders.linearize (xAction source)) B :=
    ⟨helem, (lt_of_not_ge h).le⟩
  have hBA := hunique B hB hoff
  exact h (by rw [hBA, heq])

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
