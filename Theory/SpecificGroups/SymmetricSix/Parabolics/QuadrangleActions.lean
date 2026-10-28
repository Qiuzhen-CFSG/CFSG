module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.Actions

/-!
# Actions on the duad–syntheme quadrangle

Permuting six letters sends a syntheme to the syntheme consisting of the three
permuted duads. We construct this action from the table of pairwise disjoint
triples, prove equivariance of incidence and of the actual isotropic planes in
the natural binary module, and identify its base stabilizers with the concrete
parabolics. Incidence recovers the faithful point action; the already proved
maximality of the parabolics gives primitivity of the line action.

Small tables of even permutations supply transporters from one representative
of each stabilizer orbit. Composition and conjugation give transitivity on the
six collinear and eight distinct noncollinear objects at every base, for both
S₆ and A₆. The line stabilizer also transports its three incident duads, giving
transitivity on incident flags. All table claims are checked by kernel reduction.

`Duad` and `Syntheme` are both `Fin 15`. Consequently `synthemeAction` and
`a6SynthemeAction` are named structures, **not global instances**; `synthemeAct`
is used explicitly in the public geometric statements. The global smul remains
`duadAction`. The cardinalities of the two nontrivial stabilizer orbits are the
existing `duad_collinear_six`, `duad_noncollinear_eight`, and their syntheme
counterparts.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.4 and
the local polar-space facts used in the proofs of I.5.8–I.5.9, printed pp.420–422.
These are the concrete rank-two action facts used in those residue arguments.
-/

public section

open Finset
namespace Theory.SpecificGroups.SymmetricSix
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

private theorem synthemeDuads_inj : Function.Injective synthemeDuads := by decide

private theorem syntheme_pairwise (s : Syntheme) (d e : Duad)
    (hd : d ∈ synthemeDuads s) (he : e ∈ synthemeDuads s) (hne : d ≠ e) :
    duadCollinear d e := by decide +revert

private theorem syntheme_of_triple (d e f : Duad)
    (hde : duadCollinear d e) (hdf : duadCollinear d f) (hef : duadCollinear e f) :
    ∃ s, synthemeDuads s = {d, e, f} := by decide +revert

private theorem syntheme_image_exists (g : S6) (s : Syntheme) :
    ∃ t, synthemeDuads t = (synthemeDuads s).image (fun d => g • d) := by
  obtain ⟨d, e, f, hde, hdf, hef, hs⟩ := card_eq_three.mp (syntheme_is_partition s).1
  have hd : d ∈ synthemeDuads s := by simp [hs]
  have he : e ∈ synthemeDuads s := by simp [hs]
  have hf : f ∈ synthemeDuads s := by simp [hs]
  obtain ⟨t, ht⟩ := syntheme_of_triple (g • d) (g • e) (g • f)
    ((duadCollinear_smul_iff g d e).2 (syntheme_pairwise s d e hd he hde))
    ((duadCollinear_smul_iff g d f).2 (syntheme_pairwise s d f hd hf hdf))
    ((duadCollinear_smul_iff g e f).2 (syntheme_pairwise s e f he hf hef))
  exact ⟨t, by simpa [hs] using ht⟩

/-- Permute the letters in each of the three duads of a syntheme. -/
noncomputable def synthemeAct (g : S6) (s : Syntheme) : Syntheme :=
  (syntheme_image_exists g s).choose

theorem synthemeDuads_act (g : S6) (s : Syntheme) :
    synthemeDuads (synthemeAct g s) =
      (synthemeDuads s).image (fun d => @SMul.smul S6 Duad duadAction.toSMul g d) :=
  (syntheme_image_exists g s).choose_spec

@[simp] theorem synthemeAct_one (s : Syntheme) : synthemeAct 1 s = s := by
  apply synthemeDuads_inj
  rw [synthemeDuads_act]
  change (synthemeDuads s).image (fun d => (1 : S6) • d) = _
  simp

@[simp] theorem synthemeAct_mul (g h : S6) (s : Syntheme) :
    synthemeAct (g * h) s = synthemeAct g (synthemeAct h s) := by
  apply synthemeDuads_inj
  simp only [synthemeDuads_act, Finset.image_image]
  change (synthemeDuads s).image (fun d => (g * h) • d) =
    (synthemeDuads s).image (fun d => g • (h • d))
  simp only [mul_smul]

/-- The line action, deliberately not registered as a global instance. -/
@[expose, instance_reducible] noncomputable def synthemeAction : MulAction S6 Syntheme where
  smul := synthemeAct
  one_smul := synthemeAct_one
  mul_smul := synthemeAct_mul

theorem synthemeAct_injective (g : S6) : Function.Injective (synthemeAct g) := by
  intro s t h
  have := congrArg (synthemeAct g⁻¹) h
  simpa only [← synthemeAct_mul, inv_mul_cancel, synthemeAct_one] using this

theorem incident_act_iff (g : S6) (d : Duad) (s : Syntheme) :
    incident (g • d) (synthemeAct g s) ↔ incident d s := by
  unfold incident
  rw [synthemeDuads_act, Finset.mem_image]
  constructor
  · rintro ⟨e, he, h⟩
    exact smul_left_cancel g h ▸ he
  · intro h
    exact ⟨d, h, rfl⟩

theorem synthemeCollinear_act_iff (g : S6) (s t : Syntheme) :
    synthemeCollinear (synthemeAct g s) (synthemeAct g t) ↔ synthemeCollinear s t := by
  unfold synthemeCollinear
  rw [(synthemeAct_injective g).ne_iff, synthemeDuads_act, synthemeDuads_act]
  change (s ≠ t ∧ ((synthemeDuads s).image (fun d => g • d) ∩
    (synthemeDuads t).image (fun d => g • d)).card = 1) ↔ _
  rw [← Finset.image_inter _ _ (MulAction.injective g),
    Finset.card_image_of_injective _ (MulAction.injective g)]

/-- The unordered partition of the six letters represented by a syntheme. -/
@[expose] def synthemePartition (s : Syntheme) : Finset (Finset Letter) :=
  (synthemeDuads s).image duadSet

theorem synthemePartition_injective : Function.Injective synthemePartition :=
  (Finset.image_injective duadSet_injective).comp synthemeDuads_inj

theorem synthemePartition_act (g : S6) (s : Syntheme) :
    synthemePartition (synthemeAct g s) =
      (synthemePartition s).image (fun p => p.image g) := by
  unfold synthemePartition
  rw [synthemeDuads_act]
  change ((synthemeDuads s).image (fun d => g • d)).image duadSet = _
  simp only [Finset.image_image, Function.comp_def, duadSet_smul]

theorem synthemeAct_eq_iff (g : S6) (s t : Syntheme) :
    synthemeAct g s = t ↔
      (synthemePartition s).image (fun p => p.image g) = synthemePartition t := by
  rw [← synthemePartition_injective.eq_iff, synthemePartition_act]

private theorem duad_smul_eq_iff (g : S6) (d e : Duad) :
    g • d = e ↔ (duadSet d).image g = duadSet e := by
  rw [← duadSet_injective.eq_iff, duadSet_smul]

@[simp] theorem synthemePartition_zero : synthemePartition 0 = baseSyntheme := by decide

theorem syntheme_stabilizer_zero :
    @MulAction.stabilizer S6 Syntheme _ synthemeAction 0 = synthemeStabilizer := by
  ext g
  change synthemeAct g 0 = 0 ↔ _
  rw [synthemeAct_eq_iff, synthemePartition_zero]
  rfl

/-- Restrict the explicitly named line action to the even permutations. -/
@[expose, instance_reducible] noncomputable def a6SynthemeAction : MulAction A6 Syntheme :=
  @MulAction.compHom S6 A6 Syntheme _ synthemeAction _ A6.subtype

theorem a6_syntheme_stabilizer_zero :
    @MulAction.stabilizer A6 Syntheme _ a6SynthemeAction 0 = a6SynthemeStabilizer := by
  ext g
  change synthemeAct g.val 0 = 0 ↔ g.val ∈ synthemeStabilizer
  exact SetLike.ext_iff.mp syntheme_stabilizer_zero g.val

private theorem duads_determined_by_incidence (d e : Duad)
    (h : ∀ s, incident d s ↔ incident e s) : d = e := by decide +revert

/-- Faithfulness of the line action follows from its incidence with the faithful point action. -/
theorem synthemeAct_faithful {g h : S6}
    (heq : ∀ s, synthemeAct g s = synthemeAct h s) : g = h := by
  apply FaithfulSMul.eq_of_smul_eq_smul (α := Duad)
  intro d
  apply duads_determined_by_incidence
  intro t
  have ht : t = synthemeAct g (synthemeAct g⁻¹ t) := by
    simp only [← synthemeAct_mul, mul_inv_cancel, synthemeAct_one]
  rw [ht]
  rw [incident_act_iff, heq, incident_act_iff]

/-- Equivariance on the actual isotropic two-dimensional subspaces. -/
theorem polarLine_act (g : S6) (s : Syntheme) :
    polarLine (synthemeAct g s) = (polarLine s).map (polarLinearMap g) := by
  ext v
  change v ∈ polarLineSet (synthemeAct g s) ↔ _
  rw [Submodule.mem_map]
  constructor
  · intro hv
    simp only [polarLineSet, Finset.mem_insert, Finset.mem_image] at hv
    rcases hv with rfl | ⟨d, hd, rfl⟩
    · exact ⟨0, (polarLine s).zero_mem, (polarLinearMap g).map_zero⟩
    · rw [synthemeDuads_act] at hd
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
      exact ⟨(polarVector e).val, (incident_iff_mem_polarLine e s).mp he,
        polarAction_vector g e⟩
  · rintro ⟨w, hw, rfl⟩
    change w ∈ polarLineSet s at hw
    simp only [polarLineSet, Finset.mem_insert, Finset.mem_image] at hw
    rcases hw with rfl | ⟨d, hd, rfl⟩
    · exact Finset.mem_insert_self _ _
    · change polarAction g (polarVector d).val ∈ _
      rw [polarAction_vector]
      exact (incident_iff_mem_polarLine _ _).mp ((incident_act_iff g d s).mpr hd)

-- Each nonidentity representative is a product of two transpositions.
namespace QuadrangleCertificate

private def lineFromZero : Fin 15 → A6 :=
  ![⟨1, by decide⟩,
    ⟨Equiv.swap 3 4 * Equiv.swap 4 5, by decide⟩,
    ⟨Equiv.swap 3 5 * Equiv.swap 5 4, by decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 4 5, by decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 3 5, by decide⟩,
    ⟨Equiv.swap 1 3 * Equiv.swap 3 2, by decide⟩,
    ⟨Equiv.swap 1 3 * Equiv.swap 3 5, by decide⟩,
    ⟨Equiv.swap 1 3 * Equiv.swap 3 4, by decide⟩,
    ⟨Equiv.swap 1 4 * Equiv.swap 4 3, by decide⟩,
    ⟨Equiv.swap 1 4 * Equiv.swap 4 2, by decide⟩,
    ⟨Equiv.swap 1 4 * Equiv.swap 4 5, by decide⟩,
    ⟨Equiv.swap 1 5 * Equiv.swap 5 3, by decide⟩,
    ⟨Equiv.swap 1 5 * Equiv.swap 5 2, by decide⟩,
    ⟨Equiv.swap 1 5 * Equiv.swap 5 4, by decide⟩]

private def pointOrbit : Fin 15 → A6 :=
  ![⟨1, by decide⟩,
    ⟨1, by decide⟩,
    ⟨Equiv.swap 2 3 * Equiv.swap 4 5, by decide⟩,
    ⟨Equiv.swap 2 4 * Equiv.swap 4 3, by decide⟩,
    ⟨Equiv.swap 2 5 * Equiv.swap 5 3, by decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 4 5, by decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 2 4, by decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 2 5, by decide⟩,
    ⟨1, by decide⟩,
    ⟨Equiv.swap 3 4 * Equiv.swap 4 5, by decide⟩,
    ⟨Equiv.swap 3 5 * Equiv.swap 5 4, by decide⟩,
    ⟨Equiv.swap 2 3 * Equiv.swap 3 4, by decide⟩,
    ⟨Equiv.swap 2 3 * Equiv.swap 3 5, by decide⟩,
    ⟨Equiv.swap 2 4 * Equiv.swap 3 5, by decide⟩]

private def lineOrbit : Fin 15 → A6 :=
  ![⟨1, by decide⟩,
    ⟨1, by decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 4 5, by decide⟩,
    ⟨Equiv.swap 0 4 * Equiv.swap 1 5, by decide⟩,
    ⟨1, by decide⟩,
    ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide⟩,
    ⟨Equiv.swap 0 5 * Equiv.swap 1 4, by decide⟩,
    ⟨Equiv.swap 0 5 * Equiv.swap 1 4, by decide⟩,
    ⟨Equiv.swap 2 3 * Equiv.swap 4 5, by decide⟩,
    ⟨Equiv.swap 2 4 * Equiv.swap 3 5, by decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by decide⟩,
    ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide⟩,
    ⟨Equiv.swap 0 1 * Equiv.swap 4 5, by decide⟩,
    ⟨Equiv.swap 2 5 * Equiv.swap 3 4, by decide⟩,
    ⟨Equiv.swap 0 3 * Equiv.swap 1 2, by decide⟩]

end QuadrangleCertificate

private theorem lineFromZero_spec (s : Syntheme) :
    (synthemePartition 0).image (fun p => p.image (QuadrangleCertificate.lineFromZero s).val) =
      synthemePartition s := by decide +revert

private theorem pointOrbit_spec (d : Duad) :
    (duadSet 0).image (QuadrangleCertificate.pointOrbit d).val = duadSet 0 ∧
    (duadSet (if d = 0 then 0 else if duadCollinear 0 d then 9 else 1)).image
      (QuadrangleCertificate.pointOrbit d).val = duadSet d := by decide +revert

private theorem lineOrbit_spec (s : Syntheme) :
    (synthemePartition 0).image (fun p => p.image (QuadrangleCertificate.lineOrbit s).val) =
      synthemePartition 0 ∧
    (synthemePartition (if s = 0 then 0 else if synthemeCollinear 0 s then 1 else 4)).image
      (fun p => p.image (QuadrangleCertificate.lineOrbit s).val) =
      synthemePartition s := by decide +revert

private theorem a6_syntheme_from_zero (s : Syntheme) :
    ∃ g : A6, synthemeAct g.val 0 = s :=
  ⟨QuadrangleCertificate.lineFromZero s, (synthemeAct_eq_iff _ _ _).mpr (lineFromZero_spec s)⟩

/-- The even permutations act transitively on the actual synthemes. -/
theorem a6_syntheme_transitive (s t : Syntheme) :
    ∃ g : A6, synthemeAct g.val s = t := by
  let := a6SynthemeAction
  obtain ⟨a, ha⟩ := a6_syntheme_from_zero s
  obtain ⟨b, hb⟩ := a6_syntheme_from_zero t
  change a • (0 : Syntheme) = s at ha
  change b • (0 : Syntheme) = t at hb
  refine ⟨b * a⁻¹, ?_⟩
  change (b * a⁻¹) • s = t
  rw [mul_smul, ← ha, inv_smul_smul, hb]

theorem syntheme_transitive (s t : Syntheme) : ∃ g : S6, synthemeAct g s = t := by
  obtain ⟨g, hg⟩ := a6_syntheme_transitive s t
  exact ⟨g.val, hg⟩

/-- This action structure must be supplied explicitly: the global `Fin 15` action is on duads. -/
theorem syntheme_pretransitive :
    @MulAction.IsPretransitive S6 Syntheme synthemeAction.toSMul := by
  let := synthemeAction
  exact ⟨syntheme_transitive⟩

theorem a6_syntheme_pretransitive :
    @MulAction.IsPretransitive A6 Syntheme a6SynthemeAction.toSMul := by
  let := a6SynthemeAction
  exact ⟨a6_syntheme_transitive⟩

theorem syntheme_preprimitive :
    @MulAction.IsPreprimitive S6 Syntheme synthemeAction.toSMul := by
  let := synthemeAction
  let := syntheme_pretransitive
  rw [← MulAction.isCoatom_stabilizer_iff_preprimitive S6 (0 : Syntheme),
    syntheme_stabilizer_zero]
  exact synthemeStabilizer_isCoatom

theorem a6_syntheme_preprimitive :
    @MulAction.IsPreprimitive A6 Syntheme a6SynthemeAction.toSMul := by
  let := a6SynthemeAction
  let := a6_syntheme_pretransitive
  rw [← MulAction.isCoatom_stabilizer_iff_preprimitive A6 (0 : Syntheme),
    a6_syntheme_stabilizer_zero]
  exact a6SynthemeStabilizer_isCoatom

theorem syntheme_faithful : @FaithfulSMul S6 Syntheme synthemeAction.toSMul := by
  let := synthemeAction
  exact ⟨synthemeAct_faithful⟩

theorem a6_syntheme_faithful : @FaithfulSMul A6 Syntheme a6SynthemeAction.toSMul := by
  let := a6SynthemeAction
  constructor
  intro g h hgh
  exact Subtype.ext (synthemeAct_faithful hgh)

private theorem transporter_via_reference {G X : Type*} [Group G] [act : MulAction G X]
    {b r x y : X} (hx : ∃ g : G, g • b = b ∧ g • r = x)
    (hy : ∃ g : G, g • b = b ∧ g • r = y) :
    ∃ g : G, g • b = b ∧ g • x = y := by
  obtain ⟨a, ha0, ha⟩ := hx
  obtain ⟨c, hc0, hc⟩ := hy
  refine ⟨c * a⁻¹, ?_, ?_⟩
  · rw [mul_smul, ← ha0, inv_smul_smul, hc0]
    exact ha0.symm
  · rw [mul_smul, ← ha, inv_smul_smul, hc]

private theorem a6_duad_reference (d : Duad) :
    ∃ g : A6, g • (0 : Duad) = 0 ∧
      g • (if d = 0 then 0 else if duadCollinear 0 d then 9 else 1 : Duad) = d := by
  refine ⟨QuadrangleCertificate.pointOrbit d, ?_, ?_⟩
  · exact (duad_smul_eq_iff _ _ _).mpr (pointOrbit_spec d).1
  · exact (duad_smul_eq_iff _ _ _).mpr (pointOrbit_spec d).2

private theorem a6_syntheme_reference (s : Syntheme) :
    ∃ g : A6, synthemeAct g.val 0 = 0 ∧
      synthemeAct g.val (if s = 0 then 0 else if synthemeCollinear 0 s then 1 else 4) = s := by
  refine ⟨QuadrangleCertificate.lineOrbit s, ?_, ?_⟩
  · exact (synthemeAct_eq_iff _ _ _).mpr (lineOrbit_spec s).1
  · exact (synthemeAct_eq_iff _ _ _).mpr (lineOrbit_spec s).2

private theorem a6_duad_collinear_zero (d e : Duad)
    (hd : duadCollinear 0 d) (he : duadCollinear 0 e) :
    ∃ g : A6, g • (0 : Duad) = 0 ∧ g • d = e := by
  have hdz : d ≠ 0 := hd.1.symm
  have hez : e ≠ 0 := he.1.symm
  apply transporter_via_reference (r := (9 : Duad))
  · simpa only [if_neg hdz, if_pos hd] using a6_duad_reference d
  · simpa only [if_neg hez, if_pos he] using a6_duad_reference e

private theorem a6_duad_noncollinear_zero (d e : Duad)
    (hd : d ≠ 0 ∧ ¬duadCollinear 0 d) (he : e ≠ 0 ∧ ¬duadCollinear 0 e) :
    ∃ g : A6, g • (0 : Duad) = 0 ∧ g • d = e := by
  apply transporter_via_reference (r := (1 : Duad))
  · simpa only [if_neg hd.1, if_neg hd.2] using a6_duad_reference d
  · simpa only [if_neg he.1, if_neg he.2] using a6_duad_reference e

private theorem a6_syntheme_collinear_zero (s t : Syntheme)
    (hs : synthemeCollinear 0 s) (ht : synthemeCollinear 0 t) :
    ∃ g : A6, synthemeAct g.val 0 = 0 ∧ synthemeAct g.val s = t := by
  let := a6SynthemeAction
  have hsz : s ≠ 0 := hs.1.symm
  have htz : t ≠ 0 := ht.1.symm
  change ∃ g : A6, g • (0 : Syntheme) = 0 ∧ g • s = t
  apply transporter_via_reference (act := a6SynthemeAction) (r := (1 : Syntheme))
  · change ∃ g : A6, synthemeAct g.val 0 = 0 ∧ synthemeAct g.val 1 = s
    simpa only [if_neg hsz, if_pos hs] using a6_syntheme_reference s
  · change ∃ g : A6, synthemeAct g.val 0 = 0 ∧ synthemeAct g.val 1 = t
    simpa only [if_neg htz, if_pos ht] using a6_syntheme_reference t

private theorem a6_syntheme_noncollinear_zero (s t : Syntheme)
    (hs : s ≠ 0 ∧ ¬synthemeCollinear 0 s) (ht : t ≠ 0 ∧ ¬synthemeCollinear 0 t) :
    ∃ g : A6, synthemeAct g.val 0 = 0 ∧ synthemeAct g.val s = t := by
  let := a6SynthemeAction
  change ∃ g : A6, g • (0 : Syntheme) = 0 ∧ g • s = t
  apply transporter_via_reference (act := a6SynthemeAction) (r := (4 : Syntheme))
  · change ∃ g : A6, synthemeAct g.val 0 = 0 ∧ synthemeAct g.val 4 = s
    simpa only [if_neg hs.1, if_neg hs.2] using a6_syntheme_reference s
  · change ∃ g : A6, synthemeAct g.val 0 = 0 ∧ synthemeAct g.val 4 = t
    simpa only [if_neg ht.1, if_neg ht.2] using a6_syntheme_reference t

/-- Conjugate a transporter in the base stabilizer to an arbitrary stabilizer. -/
private theorem stabilizer_transporter_of_base {G X : Type*} [Group G] [act : MulAction G X]
    (R : X → X → Prop) (b : X)
    (hR : ∀ (g : G) x y, R (g • x) (g • y) ↔ R x y)
    (htrans : ∀ x, ∃ g : G, g • b = x)
    (hbase : ∀ x y, R b x → R b y → ∃ g : G, g • b = b ∧ g • x = y)
    (a x y : X) (hx : R a x) (hy : R a y) :
    ∃ g : G, g • a = a ∧ g • x = y := by
  obtain ⟨c, hc⟩ := htrans a
  have hx' : R b (c⁻¹ • x) := by
    have h := (hR c⁻¹ a x).mpr hx
    rwa [← hc, inv_smul_smul] at h
  have hy' : R b (c⁻¹ • y) := by
    have h := (hR c⁻¹ a y).mpr hy
    rwa [← hc, inv_smul_smul] at h
  obtain ⟨k, hk0, hk⟩ := hbase _ _ hx' hy'
  refine ⟨c * k * c⁻¹, ?_, ?_⟩
  · calc
      (c * k * c⁻¹) • a = c • (k • (c⁻¹ • a)) := by simp only [mul_smul]
      _ = c • (k • b) := by rw [← hc, inv_smul_smul]
      _ = a := by rw [hk0, hc]
  · calc
      (c * k * c⁻¹) • x = c • (k • (c⁻¹ • x)) := by simp only [mul_smul]
      _ = c • (c⁻¹ • y) := congrArg (fun z => c • z) hk
      _ = y := smul_inv_smul c y

/-- The six duads collinear with any fixed duad form one orbit under its A₆ stabilizer. -/
theorem a6_duad_collinear_transporter (b d e : Duad)
    (hd : duadCollinear b d) (he : duadCollinear b e) :
    ∃ g : A6, g • b = b ∧ g • d = e := by
  exact stabilizer_transporter_of_base duadCollinear 0
    (fun g d e => duadCollinear_smul_iff g.val d e)
    (a6_duad_transitive 0) a6_duad_collinear_zero b d e hd he

/-- The eight other, noncollinear duads form one orbit under the A₆ stabilizer. -/
theorem a6_duad_noncollinear_transporter (b d e : Duad)
    (hd : d ≠ b ∧ ¬duadCollinear b d) (he : e ≠ b ∧ ¬duadCollinear b e) :
    ∃ g : A6, g • b = b ∧ g • d = e := by
  apply stabilizer_transporter_of_base (fun b d => d ≠ b ∧ ¬duadCollinear b d) 0
    (G := A6) ?_ (a6_duad_transitive 0) a6_duad_noncollinear_zero b d e hd he
  intro g x y
  change (g.val • y ≠ g.val • x ∧
    ¬duadCollinear (g.val • x) (g.val • y)) ↔ _
  simp only [ne_eq, smul_left_cancel_iff, duadCollinear_smul_iff]

theorem duad_collinear_transporter (b d e : Duad)
    (hd : duadCollinear b d) (he : duadCollinear b e) :
    ∃ g : S6, g • b = b ∧ g • d = e := by
  obtain ⟨g, hg⟩ := a6_duad_collinear_transporter b d e hd he
  exact ⟨g.val, hg⟩

theorem duad_noncollinear_transporter (b d e : Duad)
    (hd : d ≠ b ∧ ¬duadCollinear b d) (he : e ≠ b ∧ ¬duadCollinear b e) :
    ∃ g : S6, g • b = b ∧ g • d = e := by
  obtain ⟨g, hg⟩ := a6_duad_noncollinear_transporter b d e hd he
  exact ⟨g.val, hg⟩

/-- The six synthemes meeting a fixed syntheme form one orbit under its A₆ stabilizer. -/
theorem a6_syntheme_collinear_transporter (b s t : Syntheme)
    (hs : synthemeCollinear b s) (ht : synthemeCollinear b t) :
    ∃ g : A6, synthemeAct g.val b = b ∧ synthemeAct g.val s = t := by
  let := a6SynthemeAction
  exact stabilizer_transporter_of_base synthemeCollinear 0
    (fun g s t => synthemeCollinear_act_iff g.val s t)
    (a6_syntheme_transitive 0) a6_syntheme_collinear_zero b s t hs ht

/-- The eight distinct noncollinear synthemes form one orbit under the A₆ stabilizer. -/
theorem a6_syntheme_noncollinear_transporter (b s t : Syntheme)
    (hs : s ≠ b ∧ ¬synthemeCollinear b s) (ht : t ≠ b ∧ ¬synthemeCollinear b t) :
    ∃ g : A6, synthemeAct g.val b = b ∧ synthemeAct g.val s = t := by
  let := a6SynthemeAction
  apply stabilizer_transporter_of_base (fun b s => s ≠ b ∧ ¬synthemeCollinear b s) 0
    (G := A6) ?_ (a6_syntheme_transitive 0) a6_syntheme_noncollinear_zero b s t hs ht
  intro g x y
  change (synthemeAct g.val y ≠ synthemeAct g.val x ∧
    ¬synthemeCollinear (synthemeAct g.val x) (synthemeAct g.val y)) ↔ _
  rw [(synthemeAct_injective g.val).ne_iff, synthemeCollinear_act_iff]

theorem syntheme_collinear_transporter (b s t : Syntheme)
    (hs : synthemeCollinear b s) (ht : synthemeCollinear b t) :
    ∃ g : S6, synthemeAct g b = b ∧ synthemeAct g s = t := by
  obtain ⟨g, hg⟩ := a6_syntheme_collinear_transporter b s t hs ht
  exact ⟨g.val, hg⟩

theorem syntheme_noncollinear_transporter (b s t : Syntheme)
    (hs : s ≠ b ∧ ¬synthemeCollinear b s) (ht : t ≠ b ∧ ¬synthemeCollinear b t) :
    ∃ g : S6, synthemeAct g b = b ∧ synthemeAct g s = t := by
  obtain ⟨g, hg⟩ := a6_syntheme_noncollinear_transporter b s t hs ht
  exact ⟨g.val, hg⟩

private def baseLinePointTransport (d : Duad) : A6 :=
  if d = 0 then ⟨1, by decide⟩ else
    if d = 9 then ⟨Equiv.swap 0 2 * Equiv.swap 1 3, by decide⟩ else
      ⟨Equiv.swap 0 4 * Equiv.swap 1 5, by decide⟩

private theorem baseLinePointTransport_spec (d : Duad) (hd : incident d 0) :
    (synthemePartition 0).image (fun p => p.image (baseLinePointTransport d).val) =
      synthemePartition 0 ∧
    (duadSet 0).image (baseLinePointTransport d).val = duadSet d := by decide +revert

private theorem a6_baseLinePoint_transitive (d : Duad) (hd : incident d 0) :
    ∃ g : A6, synthemeAct g.val 0 = 0 ∧ g • (0 : Duad) = d := by
  exact ⟨baseLinePointTransport d,
    (synthemeAct_eq_iff _ _ _).mpr (baseLinePointTransport_spec d hd).1,
    (duad_smul_eq_iff _ _ _).mpr (baseLinePointTransport_spec d hd).2⟩

private theorem a6_flag_from_zero (d : Duad) (s : Syntheme) (hds : incident d s) :
    ∃ g : A6, g • (0 : Duad) = d ∧ synthemeAct g.val 0 = s := by
  obtain ⟨a, ha⟩ := a6_syntheme_from_zero s
  have hd : incident (a.val⁻¹ • d) 0 := by
    have h := (incident_act_iff a.val⁻¹ d s).mpr hds
    rwa [← ha, ← synthemeAct_mul, inv_mul_cancel, synthemeAct_one] at h
  obtain ⟨b, hb0, hbd⟩ := a6_baseLinePoint_transitive _ hd
  refine ⟨a * b, ?_, ?_⟩
  · change (a.val * b.val) • (0 : Duad) = d
    rw [mul_smul]
    change a.val • (b • (0 : Duad)) = d
    rw [hbd, smul_inv_smul]
  · change synthemeAct (a.val * b.val) 0 = s
    rw [synthemeAct_mul, hb0, ha]

/-- A single even permutation transports both entries of any incident flag. -/
theorem a6_flag_transitive (d e : Duad) (s t : Syntheme)
    (hds : incident d s) (het : incident e t) :
    ∃ g : A6, g • d = e ∧ synthemeAct g.val s = t := by
  obtain ⟨a, had, has⟩ := a6_flag_from_zero d s hds
  obtain ⟨b, hbe, hbt⟩ := a6_flag_from_zero e t het
  refine ⟨b * a⁻¹, ?_, ?_⟩
  · rw [mul_smul, ← had, inv_smul_smul, hbe]
  · change synthemeAct (b.val * a.val⁻¹) s = t
    have hai : synthemeAct a.val⁻¹ s = 0 := by
      rw [← has, ← synthemeAct_mul, inv_mul_cancel, synthemeAct_one]
    rw [synthemeAct_mul, hai, hbt]

theorem flag_transitive (d e : Duad) (s t : Syntheme)
    (hds : incident d s) (het : incident e t) :
    ∃ g : S6, g • d = e ∧ synthemeAct g s = t := by
  obtain ⟨g, hg⟩ := a6_flag_transitive d e s t hds het
  exact ⟨g.val, hg⟩

end Theory.SpecificGroups.SymmetricSix
