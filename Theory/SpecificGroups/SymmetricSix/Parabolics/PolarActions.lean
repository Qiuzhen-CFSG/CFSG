module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.QuadrangleActions

/-!
# Faithful primitive actions on the binary symplectic quadrangle

The duad and syntheme equivalences identify the concrete six-letter geometry
with all nonzero vectors and all isotropic planes of the four-dimensional
binary symplectic module. This module completes the action side of that
identification on the actual polar objects. In particular, the action on a
plane is its image under `polarLinearMap`, and the point action is multiplication
by `polarRepresentation` in the standard symplectic matrix convention.

We transport the proved syntheme action through `synthemePolarEquiv`, preserving
incidence and identifying its stabilizers with the original parabolics. Both
S₆ and A₆ act faithfully and primitively on points and planes, transitively on
incident flags, and transitively on each of the six collinear and eight other
noncollinear objects in every stabilizer. The cardinalities and transporters
are stated for the actual vectors and subspaces as well as the finite tables.

This discharges the concrete polar-space action inputs used in the proofs of
I.5.8 and I.5.9, with the incidence identification of I.5.4 supplied by
`PolarSpace`. It does not assume a recognition theorem for an ambient D-system.
The underlying `Parabolics` module owns the tables and parabolic subgroups;
this extension imports the completed geometry and action developments without
a reverse import into that foundational module.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.4 and
the proofs of I.5.8–I.5.9, printed pp.420–422.
-/

public section

open scoped Matrix
namespace Theory.SpecificGroups.SymmetricSix

/-- The action on actual isotropic planes, transported from synthemes. -/
noncomputable instance polarLineAction : MulAction S6 BinaryLine where
  smul g L := synthemePolarEquiv (synthemeAct g (synthemePolarEquiv.symm L))
  one_smul L := by
    change synthemePolarEquiv (synthemeAct 1 (synthemePolarEquiv.symm L)) = L
    rw [synthemeAct_one, Equiv.apply_symm_apply]
  mul_smul g h L := by
    change synthemePolarEquiv (synthemeAct (g * h) (synthemePolarEquiv.symm L)) =
      synthemePolarEquiv (synthemeAct g (synthemePolarEquiv.symm
        (synthemePolarEquiv (synthemeAct h (synthemePolarEquiv.symm L)))))
    rw [Equiv.symm_apply_apply, synthemeAct_mul]

theorem synthemePolarEquiv_equivariant (g : S6) (s : Syntheme) :
    synthemePolarEquiv (synthemeAct g s) = g • synthemePolarEquiv s := by
  change _ = synthemePolarEquiv (synthemeAct g (synthemePolarEquiv.symm _))
  rw [Equiv.symm_apply_apply]

/-- This transported action is the image of the plane under the actual linear map. -/
theorem polarLine_smul_val (g : S6) (L : BinaryLine) :
    (g • L).val = L.val.map (polarLinearMap g) := by
  obtain ⟨s, rfl⟩ := synthemePolarEquiv.surjective L
  rw [← synthemePolarEquiv_equivariant]
  exact polarLine_act g s

theorem polarPoint_smul_val (g : S6) (v : BinaryPoint) :
    (g • v).val = (polarRepresentation g).val *ᵥ v.val := by
  rw [polarRepresentation_apply]
  exact (polarAction_point g v).symm

/-- Incidence is preserved by the actions on the actual vector and subspace. -/
theorem polar_incidence_smul_iff (g : S6) (v : BinaryPoint) (L : BinaryLine) :
    (g • v).val ∈ (g • L).val ↔ v.val ∈ L.val := by
  obtain ⟨d, rfl⟩ := duadPolarEquiv.surjective v
  obtain ⟨s, rfl⟩ := synthemePolarEquiv.surjective L
  rw [← duadPolarEquiv_equivariant, ← synthemePolarEquiv_equivariant,
    ← polar_incidence_equivalence, ← polar_incidence_equivalence]
  exact incident_act_iff g d s

section
attribute [local instance] synthemeAction

private noncomputable def synthemeToPolarHom : Syntheme →[S6] BinaryLine where
  toFun := synthemePolarEquiv
  map_smul' := synthemePolarEquiv_equivariant

end

instance polarLine_preprimitive : MulAction.IsPreprimitive S6 BinaryLine := by
  let := synthemeAction
  let := syntheme_preprimitive
  exact MulAction.IsPreprimitive.of_surjective (f := synthemeToPolarHom)
    synthemePolarEquiv.surjective

instance polarLine_faithful : FaithfulSMul S6 BinaryLine := by
  let := synthemeAction
  let := syntheme_faithful
  exact FaithfulSMul.of_injective synthemeToPolarHom synthemePolarEquiv.injective

section
attribute [local instance] a6SynthemeAction

private noncomputable def a6SynthemeToPolarHom : Syntheme →[A6] BinaryLine where
  toFun := synthemePolarEquiv
  map_smul' g s := synthemePolarEquiv_equivariant g.val s

end

instance a6_polarLine_preprimitive : MulAction.IsPreprimitive A6 BinaryLine := by
  let := a6SynthemeAction
  let := a6_syntheme_preprimitive
  exact MulAction.IsPreprimitive.of_surjective (f := a6SynthemeToPolarHom)
    synthemePolarEquiv.surjective

instance a6_polarLine_faithful : FaithfulSMul A6 BinaryLine := inferInstance

theorem polarLine_transitive (L M : BinaryLine) : ∃ g : S6, g • L = M :=
  MulAction.exists_smul_eq S6 L M

theorem a6_polarLine_transitive (L M : BinaryLine) : ∃ g : A6, g • L = M :=
  MulAction.exists_smul_eq A6 L M

theorem polarPoint_stabilizer_base :
    MulAction.stabilizer S6 (duadPolarEquiv 0) = duadStabilizer := by
  rw [← duad_stabilizer_zero]
  ext g
  change g • duadPolarEquiv 0 = duadPolarEquiv 0 ↔ g • (0 : Duad) = 0
  rw [← duadPolarEquiv_equivariant, duadPolarEquiv.injective.eq_iff]

theorem a6_polarPoint_stabilizer_base :
    MulAction.stabilizer A6 (duadPolarEquiv 0) = a6DuadStabilizer := by
  ext g
  change g.val • duadPolarEquiv 0 = duadPolarEquiv 0 ↔ g.val ∈ duadStabilizer
  exact SetLike.ext_iff.mp polarPoint_stabilizer_base g.val

theorem polarLine_stabilizer_base :
    MulAction.stabilizer S6 (synthemePolarEquiv 0) = synthemeStabilizer := by
  rw [← syntheme_stabilizer_zero]
  ext g
  change g • synthemePolarEquiv 0 = synthemePolarEquiv 0 ↔ synthemeAct g 0 = 0
  rw [← synthemePolarEquiv_equivariant, synthemePolarEquiv.injective.eq_iff]

theorem a6_polarLine_stabilizer_base :
    MulAction.stabilizer A6 (synthemePolarEquiv 0) = a6SynthemeStabilizer := by
  ext g
  change g.val • synthemePolarEquiv 0 = synthemePolarEquiv 0 ↔ g.val ∈ synthemeStabilizer
  exact SetLike.ext_iff.mp polarLine_stabilizer_base g.val

/-- The same even permutation transports the two members of an incident polar flag. -/
theorem a6_polar_flag_transitive (v w : BinaryPoint) (L M : BinaryLine)
    (hv : v.val ∈ L.val) (hw : w.val ∈ M.val) :
    ∃ g : A6, g • v = w ∧ g • L = M := by
  obtain ⟨d, rfl⟩ := duadPolarEquiv.surjective v
  obtain ⟨e, rfl⟩ := duadPolarEquiv.surjective w
  obtain ⟨s, rfl⟩ := synthemePolarEquiv.surjective L
  obtain ⟨t, rfl⟩ := synthemePolarEquiv.surjective M
  obtain ⟨g, hd, hs⟩ := a6_flag_transitive d e s t
    ((polar_incidence_equivalence d s).mpr hv) ((polar_incidence_equivalence e t).mpr hw)
  refine ⟨g, ?_, ?_⟩
  · exact (duadPolarEquiv_equivariant g.val d).symm.trans (congrArg duadPolarEquiv hd)
  · exact (synthemePolarEquiv_equivariant g.val s).symm.trans (congrArg synthemePolarEquiv hs)

theorem polar_flag_transitive (v w : BinaryPoint) (L M : BinaryLine)
    (hv : v.val ∈ L.val) (hw : w.val ∈ M.val) :
    ∃ g : S6, g • v = w ∧ g • L = M := by
  obtain ⟨g, hg⟩ := a6_polar_flag_transitive v w L M hv hw
  exact ⟨g.val, hg⟩

/-- Distinct orthogonal binary points are collinear in the polar space. -/
@[expose] def polarPointCollinear (v w : BinaryPoint) : Prop :=
  v ≠ w ∧ polarForm v.val w.val = 0

/-- Distinct isotropic planes are collinear in the dual geometry when they share a point. -/
@[expose] def polarLineCollinear (L M : BinaryLine) : Prop :=
  L ≠ M ∧ ∃ v : BinaryPoint, v.val ∈ L.val ∧ v.val ∈ M.val

theorem duadPolarEquiv_collinear_iff (d e : Duad) :
    polarPointCollinear (duadPolarEquiv d) (duadPolarEquiv e) ↔ duadCollinear d e := by
  change (polarVector d ≠ polarVector e ∧
    polarForm (polarVector d).val (polarVector e).val = 0) ↔ _
  rw [polarVector_injective.ne_iff, polarVector_orthogonal]
  exact ⟨fun ⟨hne, h⟩ => h.resolve_left hne, fun h => ⟨h.1, Or.inr h⟩⟩

theorem synthemePolarEquiv_collinear_iff (s t : Syntheme) :
    polarLineCollinear (synthemePolarEquiv s) (synthemePolarEquiv t) ↔
      synthemeCollinear s t := by
  rw [syntheme_collinear_iff_common_duad]
  unfold polarLineCollinear
  rw [synthemePolarEquiv.injective.ne_iff]
  constructor
  · rintro ⟨hne, v, hv, hw⟩
    obtain ⟨d, rfl⟩ := duadPolarEquiv.surjective v
    exact ⟨hne, d, (polar_incidence_equivalence d s).mpr hv,
      (polar_incidence_equivalence d t).mpr hw⟩
  · rintro ⟨hne, d, hd, he⟩
    exact ⟨hne, duadPolarEquiv d, (polar_incidence_equivalence d s).mp hd,
      (polar_incidence_equivalence d t).mp he⟩

private theorem transport_stabilizer_orbit {G X Y : Type*}
    [Group G] [actX : MulAction G X] [MulAction G Y]
    (e : X ≃ Y) (he : ∀ (g : G) x, e (g • x) = g • e x)
    (R : X → X → Prop) (S : Y → Y → Prop)
    (hR : ∀ x y, S (e x) (e y) ↔ R x y)
    (h : ∀ b x y, R b x → R b y → ∃ g : G, g • b = b ∧ g • x = y)
    (b x y : Y) (hx : S b x) (hy : S b y) :
    ∃ g : G, g • b = b ∧ g • x = y := by
  obtain ⟨b, rfl⟩ := e.surjective b
  obtain ⟨x, rfl⟩ := e.surjective x
  obtain ⟨y, rfl⟩ := e.surjective y
  obtain ⟨g, hb, hg⟩ := h b x y ((hR b x).mp hx) ((hR b y).mp hy)
  exact ⟨g, (he g b).symm.trans (congrArg e hb),
    (he g x).symm.trans (congrArg e hg)⟩

theorem a6_polarPoint_collinear_transporter (b v w : BinaryPoint)
    (hv : polarPointCollinear b v) (hw : polarPointCollinear b w) :
    ∃ g : A6, g • b = b ∧ g • v = w :=
  transport_stabilizer_orbit duadPolarEquiv (fun g => duadPolarEquiv_equivariant g.val)
    duadCollinear polarPointCollinear duadPolarEquiv_collinear_iff
    a6_duad_collinear_transporter b v w hv hw

theorem a6_polarPoint_noncollinear_transporter (b v w : BinaryPoint)
    (hv : v ≠ b ∧ ¬polarPointCollinear b v) (hw : w ≠ b ∧ ¬polarPointCollinear b w) :
    ∃ g : A6, g • b = b ∧ g • v = w := by
  apply transport_stabilizer_orbit duadPolarEquiv (fun g => duadPolarEquiv_equivariant g.val)
    (fun b d => d ≠ b ∧ ¬duadCollinear b d)
    (fun b v => v ≠ b ∧ ¬polarPointCollinear b v) ?_
    a6_duad_noncollinear_transporter b v w hv hw
  intro d e
  rw [duadPolarEquiv.injective.ne_iff, duadPolarEquiv_collinear_iff]

theorem a6_polarLine_collinear_transporter (B L M : BinaryLine)
    (hL : polarLineCollinear B L) (hM : polarLineCollinear B M) :
    ∃ g : A6, g • B = B ∧ g • L = M := by
  let := a6SynthemeAction
  exact transport_stabilizer_orbit (G := A6) (actX := a6SynthemeAction) synthemePolarEquiv
    (fun g => synthemePolarEquiv_equivariant g.val) synthemeCollinear polarLineCollinear
    synthemePolarEquiv_collinear_iff a6_syntheme_collinear_transporter B L M hL hM

theorem a6_polarLine_noncollinear_transporter (B L M : BinaryLine)
    (hL : L ≠ B ∧ ¬polarLineCollinear B L) (hM : M ≠ B ∧ ¬polarLineCollinear B M) :
    ∃ g : A6, g • B = B ∧ g • L = M := by
  let := a6SynthemeAction
  apply transport_stabilizer_orbit (G := A6) (actX := a6SynthemeAction) synthemePolarEquiv
    (fun g => synthemePolarEquiv_equivariant g.val)
    (fun b s => s ≠ b ∧ ¬synthemeCollinear b s)
    (fun B L => L ≠ B ∧ ¬polarLineCollinear B L) ?_
    a6_syntheme_noncollinear_transporter B L M hL hM
  intro s t
  rw [synthemePolarEquiv.injective.ne_iff, synthemePolarEquiv_collinear_iff]

theorem polarPoint_collinear_transporter (b v w : BinaryPoint)
    (hv : polarPointCollinear b v) (hw : polarPointCollinear b w) :
    ∃ g : S6, g • b = b ∧ g • v = w := by
  obtain ⟨g, hg⟩ := a6_polarPoint_collinear_transporter b v w hv hw
  exact ⟨g.val, hg⟩

theorem polarPoint_noncollinear_transporter (b v w : BinaryPoint)
    (hv : v ≠ b ∧ ¬polarPointCollinear b v) (hw : w ≠ b ∧ ¬polarPointCollinear b w) :
    ∃ g : S6, g • b = b ∧ g • v = w := by
  obtain ⟨g, hg⟩ := a6_polarPoint_noncollinear_transporter b v w hv hw
  exact ⟨g.val, hg⟩

theorem polarLine_collinear_transporter (B L M : BinaryLine)
    (hL : polarLineCollinear B L) (hM : polarLineCollinear B M) :
    ∃ g : S6, g • B = B ∧ g • L = M := by
  obtain ⟨g, hg⟩ := a6_polarLine_collinear_transporter B L M hL hM
  exact ⟨g.val, hg⟩

theorem polarLine_noncollinear_transporter (B L M : BinaryLine)
    (hL : L ≠ B ∧ ¬polarLineCollinear B L) (hM : M ≠ B ∧ ¬polarLineCollinear B M) :
    ∃ g : S6, g • B = B ∧ g • L = M := by
  obtain ⟨g, hg⟩ := a6_polarLine_noncollinear_transporter B L M hL hM
  exact ⟨g.val, hg⟩

theorem polarPoint_collinear_six (v : BinaryPoint) :
    Nat.card {w // polarPointCollinear v w} = 6 := by
  obtain ⟨d, rfl⟩ := duadPolarEquiv.surjective v
  rw [← Nat.card_congr (duadPolarEquiv.subtypeEquiv
    (fun e => (duadPolarEquiv_collinear_iff d e).symm))]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact duad_collinear_six d

theorem polarPoint_noncollinear_eight (v : BinaryPoint) :
    Nat.card {w // w ≠ v ∧ ¬polarPointCollinear v w} = 8 := by
  obtain ⟨d, rfl⟩ := duadPolarEquiv.surjective v
  have h (e : Duad) : (e ≠ d ∧ ¬duadCollinear d e) ↔
      (duadPolarEquiv e ≠ duadPolarEquiv d ∧
        ¬polarPointCollinear (duadPolarEquiv d) (duadPolarEquiv e)) := by
    rw [duadPolarEquiv.injective.ne_iff, duadPolarEquiv_collinear_iff]
  rw [← Nat.card_congr (duadPolarEquiv.subtypeEquiv h)]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact duad_noncollinear_eight d

theorem polarLine_collinear_six (L : BinaryLine) :
    Nat.card {M // polarLineCollinear L M} = 6 := by
  obtain ⟨s, rfl⟩ := synthemePolarEquiv.surjective L
  rw [← Nat.card_congr (synthemePolarEquiv.subtypeEquiv
    (fun t => (synthemePolarEquiv_collinear_iff s t).symm))]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact syntheme_collinear_six s

theorem polarLine_noncollinear_eight (L : BinaryLine) :
    Nat.card {M // M ≠ L ∧ ¬polarLineCollinear L M} = 8 := by
  obtain ⟨s, rfl⟩ := synthemePolarEquiv.surjective L
  have h (t : Syntheme) : (t ≠ s ∧ ¬synthemeCollinear s t) ↔
      (synthemePolarEquiv t ≠ synthemePolarEquiv s ∧
        ¬polarLineCollinear (synthemePolarEquiv s) (synthemePolarEquiv t)) := by
    rw [synthemePolarEquiv.injective.ne_iff, synthemePolarEquiv_collinear_iff]
  rw [← Nat.card_congr (synthemePolarEquiv.subtypeEquiv h)]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact syntheme_noncollinear_eight s

end Theory.SpecificGroups.SymmetricSix
