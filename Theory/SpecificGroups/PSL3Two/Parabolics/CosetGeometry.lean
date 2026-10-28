module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Actions
public import Theory.GroupAction.TypedCosetGeometry

/-!
# The PSL₃(2) parabolic coset geometry is the Fano plane

The orbit maps identify the actual point and line coset spaces equivariantly
with nonzero vectors and covectors. Flag transitivity proves that intersection
of cosets is precisely vanishing of the coordinate pairing. Thus these maps
identify the whole incidence geometry, including its faithful primitive
seven-point and seven-line actions.

The same construction at translated base flags identifies the geometry for
all conjugate pairs. Sylow conjugacy and the exhaustive coatom theorem show
that every supplied pair of distinct maximal Sylow overgroups is one of these
translated pairs, with a possible interchange of point and line types.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.3–4
and I.5.8–9, printed pp.419–422.
-/

public section

namespace Matrix.PSL3Two.Fano

private noncomputable def cosetEquiv {X : Type*} [MulAction PSL X]
    [MulAction.IsPretransitive PSL X] (x : X) (P : Subgroup PSL)
    (hP : MulAction.stabilizer PSL x = P) : PSL ⧸ P ≃ X :=
  (Subgroup.quotientEquivOfEq hP.symm).trans
    (Equiv.ofBijective (MulAction.ofQuotientStabilizer PSL x)
      ⟨MulAction.injective_ofQuotientStabilizer PSL x, fun y => by
        obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL x y
        exact ⟨QuotientGroup.mk g, hg⟩⟩)

private theorem cosetEquiv_mk {X : Type*} [MulAction PSL X]
    [MulAction.IsPretransitive PSL X] (x : X) (P : Subgroup PSL)
    (hP : MulAction.stabilizer PSL x = P) (g : PSL) :
    cosetEquiv x P hP (QuotientGroup.mk g) = g • x := rfl

private theorem cosetEquiv_smul {X : Type*} [MulAction PSL X]
    [MulAction.IsPretransitive PSL X] (x : X) (P : Subgroup PSL)
    (hP : MulAction.stabilizer PSL x = P) (g : PSL) (q : PSL ⧸ P) :
    cosetEquiv x P hP (g • q) = g • cosetEquiv x P hP q := by
  induction q using Quotient.inductionOn with | h a => exact mul_smul g a x

/-- The actual point-parabolic cosets, in binary coordinates. -/
noncomputable def pointCosetEquiv : PSL ⧸ pointParabolic ≃ Point :=
  cosetEquiv flagPoint pointParabolic stabilizer_flagPoint

/-- The actual line-parabolic cosets, in dual binary coordinates. -/
noncomputable def lineCosetEquiv : PSL ⧸ lineParabolic ≃ Line :=
  cosetEquiv flagLine lineParabolic stabilizer_flagLine

@[simp] theorem pointCosetEquiv_mk (g : PSL) :
    pointCosetEquiv (QuotientGroup.mk g) = g • flagPoint :=
  cosetEquiv_mk _ _ _ _

@[simp] theorem lineCosetEquiv_mk (g : PSL) :
    lineCosetEquiv (QuotientGroup.mk g) = g • flagLine :=
  cosetEquiv_mk _ _ _ _

theorem pointCosetEquiv_smul (g : PSL) (q : PSL ⧸ pointParabolic) :
    pointCosetEquiv (g • q) = g • pointCosetEquiv q :=
  cosetEquiv_smul _ _ _ _ _

theorem lineCosetEquiv_smul (g : PSL) (q : PSL ⧸ lineParabolic) :
    lineCosetEquiv (g • q) = g • lineCosetEquiv q :=
  cosetEquiv_smul _ _ _ _ _

/-- The parabolic family defining the Fano coset geometry. -/
@[expose] def parabolicFamily : Bool → Subgroup PSL
  | false => pointParabolic
  | true => lineParabolic

abbrev CosetIncident (q : PSL ⧸ pointParabolic) (r : PSL ⧸ lineParabolic) : Prop :=
  Subgroup.CosetGeometry.Incident parabolicFamily ⟨false, q⟩ ⟨true, r⟩

/-- Nonempty intersection of cosets is exactly binary point-line incidence. -/
theorem coset_incident_iff (q : PSL ⧸ pointParabolic) (r : PSL ⧸ lineParabolic) :
    CosetIncident q r ↔ Incident (pointCosetEquiv q) (lineCosetEquiv r) := by
  constructor
  · intro h
    change ∃ g : PSL, (QuotientGroup.mk g : PSL ⧸ pointParabolic) = q ∧
      (QuotientGroup.mk g : PSL ⧸ lineParabolic) = r at h
    obtain ⟨g, rfl, rfl⟩ := h
    exact (incident_smul g _ _).mpr flag_incident
  · intro h
    obtain ⟨g, hp, hl⟩ := flag_transitive _ _ h
    exact ⟨g, pointCosetEquiv.injective hp, lineCosetEquiv.injective hl⟩

theorem card_point_cosets : Nat.card (PSL ⧸ pointParabolic) = 7 := by
  rw [Nat.card_congr pointCosetEquiv, Nat.card_eq_fintype_card, card_point]

theorem card_line_cosets : Nat.card (PSL ⧸ lineParabolic) = 7 := by
  rw [Nat.card_congr lineCosetEquiv, Nat.card_eq_fintype_card, card_line]

instance : FaithfulSMul PSL (PSL ⧸ pointParabolic) where
  eq_of_smul_eq_smul he := by
    apply eq_of_smul_eq_smul (α := Point)
    intro p
    obtain ⟨q, rfl⟩ := pointCosetEquiv.surjective p
    simpa only [pointCosetEquiv_smul] using congrArg pointCosetEquiv (he q)

instance : FaithfulSMul PSL (PSL ⧸ lineParabolic) where
  eq_of_smul_eq_smul he := by
    apply eq_of_smul_eq_smul (α := Line)
    intro l
    obtain ⟨r, rfl⟩ := lineCosetEquiv.surjective l
    simpa only [lineCosetEquiv_smul] using congrArg lineCosetEquiv (he r)

instance : MulAction.IsPreprimitive PSL (PSL ⧸ pointParabolic) :=
  MulAction.IsPreprimitive.of_prime_card (by rw [card_point_cosets]; decide)

instance : MulAction.IsPreprimitive PSL (PSL ⧸ lineParabolic) :=
  MulAction.IsPreprimitive.of_prime_card (by rw [card_line_cosets]; decide)

/-- The degree-seven natural permutation representation of the actual projective group. -/
noncomputable def pointAction : PSL →* Equiv.Perm Point := MulAction.toPermHom PSL Point

/-- The degree-seven contragredient permutation representation. -/
noncomputable def lineAction : PSL →* Equiv.Perm Line := MulAction.toPermHom PSL Line

theorem pointAction_faithful : Function.Injective pointAction := MulAction.toPerm_injective

theorem lineAction_faithful : Function.Injective lineAction := MulAction.toPerm_injective

/-- The coordinate description for any conjugate point parabolic. -/
noncomputable def conjugatePointCosetEquiv (g : PSL) :
    PSL ⧸ pointParabolic.map (MulAut.conj g).toMonoidHom ≃ Point :=
  cosetEquiv (g • flagPoint) _ (by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_flagPoint])

/-- The coordinate description for any conjugate line parabolic. -/
noncomputable def conjugateLineCosetEquiv (g : PSL) :
    PSL ⧸ lineParabolic.map (MulAut.conj g).toMonoidHom ≃ Line :=
  cosetEquiv (g • flagLine) _ (by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, stabilizer_flagLine])

@[simp] theorem conjugatePointCosetEquiv_mk (g a : PSL) :
    conjugatePointCosetEquiv g (QuotientGroup.mk a) = a • g • flagPoint :=
  cosetEquiv_mk _ _ _ _

@[simp] theorem conjugateLineCosetEquiv_mk (g a : PSL) :
    conjugateLineCosetEquiv g (QuotientGroup.mk a) = a • g • flagLine :=
  cosetEquiv_mk _ _ _ _

theorem conjugatePointCosetEquiv_smul (g a : PSL)
    (q : PSL ⧸ pointParabolic.map (MulAut.conj g).toMonoidHom) :
    conjugatePointCosetEquiv g (a • q) = a • conjugatePointCosetEquiv g q :=
  cosetEquiv_smul _ _ _ _ _

theorem conjugateLineCosetEquiv_smul (g a : PSL)
    (q : PSL ⧸ lineParabolic.map (MulAut.conj g).toMonoidHom) :
    conjugateLineCosetEquiv g (a • q) = a • conjugateLineCosetEquiv g q :=
  cosetEquiv_smul _ _ _ _ _

/-- The translated family over the conjugate Sylow subgroup. -/
@[expose] def conjugateFamily (g : PSL) (i : Bool) : Subgroup PSL :=
  (parabolicFamily i).map (MulAut.conj g).toMonoidHom

theorem conjugate_coset_incident_iff (g : PSL)
    (q : PSL ⧸ pointParabolic.map (MulAut.conj g).toMonoidHom)
    (r : PSL ⧸ lineParabolic.map (MulAut.conj g).toMonoidHom) :
    Subgroup.CosetGeometry.Incident (conjugateFamily g) ⟨false, q⟩ ⟨true, r⟩ ↔
      Incident (conjugatePointCosetEquiv g q) (conjugateLineCosetEquiv g r) := by
  constructor
  · intro h
    change ∃ a : PSL,
      (QuotientGroup.mk a : PSL ⧸ pointParabolic.map (MulAut.conj g).toMonoidHom) = q ∧
      (QuotientGroup.mk a : PSL ⧸ lineParabolic.map (MulAut.conj g).toMonoidHom) = r at h
    obtain ⟨a, rfl, rfl⟩ := h
    exact (incident_smul a _ _).mpr ((incident_smul g _ _).mpr flag_incident)
  · intro h
    obtain ⟨a, ha, hb⟩ := flag_transitive _ _ h
    refine ⟨a * g⁻¹, (conjugatePointCosetEquiv g).injective ?_,
      (conjugateLineCosetEquiv g).injective ?_⟩
    · change conjugatePointCosetEquiv g (QuotientGroup.mk (a * g⁻¹)) = _
      rw [conjugatePointCosetEquiv_mk, mul_smul, inv_smul_smul]
      exact ha
    · change conjugateLineCosetEquiv g (QuotientGroup.mk (a * g⁻¹)) = _
      rw [conjugateLineCosetEquiv_mk, mul_smul, inv_smul_smul]
      exact hb

instance (g : PSL) : FaithfulSMul PSL
    (PSL ⧸ pointParabolic.map (MulAut.conj g).toMonoidHom) where
  eq_of_smul_eq_smul he := by
    apply eq_of_smul_eq_smul (α := Point)
    intro p
    obtain ⟨q, rfl⟩ := (conjugatePointCosetEquiv g).surjective p
    simpa only [conjugatePointCosetEquiv_smul] using
      congrArg (conjugatePointCosetEquiv g) (he q)

instance (g : PSL) : FaithfulSMul PSL
    (PSL ⧸ lineParabolic.map (MulAut.conj g).toMonoidHom) where
  eq_of_smul_eq_smul he := by
    apply eq_of_smul_eq_smul (α := Line)
    intro l
    obtain ⟨q, rfl⟩ := (conjugateLineCosetEquiv g).surjective l
    simpa only [conjugateLineCosetEquiv_smul] using
      congrArg (conjugateLineCosetEquiv g) (he q)

theorem card_conjugate_point_cosets (g : PSL) :
    Nat.card (PSL ⧸ pointParabolic.map (MulAut.conj g).toMonoidHom) = 7 := by
  rw [Nat.card_congr (conjugatePointCosetEquiv g), Nat.card_eq_fintype_card, card_point]

theorem card_conjugate_line_cosets (g : PSL) :
    Nat.card (PSL ⧸ lineParabolic.map (MulAut.conj g).toMonoidHom) = 7 := by
  rw [Nat.card_congr (conjugateLineCosetEquiv g), Nat.card_eq_fintype_card, card_line]

instance (g : PSL) : MulAction.IsPreprimitive PSL
    (PSL ⧸ pointParabolic.map (MulAut.conj g).toMonoidHom) :=
  MulAction.IsPreprimitive.of_prime_card (by rw [card_conjugate_point_cosets]; decide)

instance (g : PSL) : MulAction.IsPreprimitive PSL
    (PSL ⧸ lineParabolic.map (MulAut.conj g).toMonoidHom) :=
  MulAction.IsPreprimitive.of_prime_card (by rw [card_conjugate_line_cosets]; decide)

/-- Every Sylow gives exactly one translated point-line pair. Together with
`conjugate_coset_incident_iff`, this identifies the geometry over any Sylow. -/
theorem sylow_parabolics_conjugate (S : Sylow 2 PSL) :
    ∃ g : PSL,
      borel.map (MulAut.conj g).toMonoidHom = (S : Subgroup PSL) ∧
      conjugateFamily g false ≠ conjugateFamily g true ∧
      conjugateFamily g false ⊓ conjugateFamily g true = (S : Subgroup PSL) ∧
      ∀ U : Subgroup PSL,
        (IsCoatom U ∧ (S : Subgroup PSL) ≤ U) ↔
          U = conjugateFamily g false ∨ U = conjugateFamily g true := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL borelSylow S
  let e := (MulAut.conj g).mapSubgroup
  have hs : e borel = (S : Subgroup PSL) := by rw [← hg]; rfl
  refine ⟨g, hs, ?_, ?_, ?_⟩
  · exact fun h => pointParabolic_ne_line (e.injective h)
  · change e pointParabolic ⊓ e lineParabolic = _
    rw [← e.map_inf, pointParabolic_inf_line, hs]
  · intro U
    change (IsCoatom U ∧ (S : Subgroup PSL) ≤ U) ↔
      U = e pointParabolic ∨ U = e lineParabolic
    constructor
    · rintro ⟨hU, hS⟩
      have hc : IsCoatom (e.symm U) := (e.symm.isCoatom_iff _).mpr hU
      have hb : borel ≤ e.symm U := by
        apply e.le_iff_le.mp
        simpa only [e.apply_symm_apply, hs] using hS
      rcases (coatoms_over_borel _).mp ⟨hc, hb⟩ with hp | hl
      · exact Or.inl (by simpa using congrArg e hp)
      · exact Or.inr (by simpa using congrArg e hl)
    · rintro (rfl | rfl)
      · exact ⟨(e.isCoatom_iff _).mpr isCoatom_pointParabolic,
          hs ▸ e.monotone (pointParabolic_inf_line ▸ inf_le_left)⟩
      · exact ⟨(e.isCoatom_iff _).mpr isCoatom_lineParabolic,
          hs ▸ e.monotone (pointParabolic_inf_line ▸ inf_le_right)⟩

/-- An arbitrary supplied pair of distinct maximal Sylow overgroups is the
translated geometric pair, with the possible interchange of the two types. -/
theorem identify_parabolics (S : Sylow 2 PSL) (P L : Subgroup PSL)
    (hP : IsCoatom P) (hL : IsCoatom L) (hne : P ≠ L)
    (hSP : (S : Subgroup PSL) ≤ P) (hSL : (S : Subgroup PSL) ≤ L) :
    ∃ g : PSL,
      (P = conjugateFamily g false ∧ L = conjugateFamily g true) ∨
      (P = conjugateFamily g true ∧ L = conjugateFamily g false) := by
  obtain ⟨g, _, _, _, h⟩ := sylow_parabolics_conjugate S
  refine ⟨g, ?_⟩
  rcases (h P).mp ⟨hP, hSP⟩ with hp | hp <;>
    rcases (h L).mp ⟨hL, hSL⟩ with hl | hl
  · exact (hne (hp.trans hl.symm)).elim
  · exact Or.inl ⟨hp, hl⟩
  · exact Or.inr ⟨hp, hl⟩
  · exact (hne (hp.trans hl.symm)).elim


end Matrix.PSL3Two.Fano
