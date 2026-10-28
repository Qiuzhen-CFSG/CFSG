module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Models
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Natural and dual actions on the Fano plane

The actual PSL₃(2) acts on nonzero binary vectors and on nonzero covectors.
The central quotient is an isomorphism; the actions are matrix multiplication
and inverse-transpose multiplication. The point and line parabolics are exactly
the stabilizers of the standard incident flag.

The two matrix actions are faithful. Orbit–stabilizer, using the parabolic
orders 24 and the Borel order eight, proves transitivity on the seven points,
seven lines and 21 flags. Prime degree then gives primitivity. Incidence is
preserved by the natural pairing of vectors and covectors.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.4,
I.5.8 and I.5.9, printed pp.420–422 (the binary projective-plane model).
-/

@[expose] public section

namespace Matrix.PSL3Two.Fano

instance : MulAction SL Point where
  smul g p := ⟨g • p.val, (smul_ne_zero_iff_ne g).mpr p.property⟩
  one_smul p := Subtype.ext (one_smul SL p.val)
  mul_smul g h p := Subtype.ext (mul_smul g h p.val)

instance : MulAction SL Line where
  smul g l := ⟨MarkedAutomorphisms.inverseTranspose g • l.normal⟩
  one_smul l := by
    change Line.mk (MarkedAutomorphisms.inverseTranspose 1 • l.normal) = l
    rw [map_one, one_smul]
  mul_smul g h l := by
    change Line.mk (MarkedAutomorphisms.inverseTranspose (g * h) • l.normal) =
      Line.mk (MarkedAutomorphisms.inverseTranspose g • (MarkedAutomorphisms.inverseTranspose h • l.normal))
    rw [map_mul, mul_smul]

noncomputable instance : MulAction PSL Point :=
  MulAction.compHom Point equiv.symm.toMonoidHom
noncomputable instance : MulAction PSL Line :=
  MulAction.compHom Line equiv.symm.toMonoidHom

@[simp] theorem project_smul_point (g : SL) (p : Point) : project g • p = g • p := by
  change equiv.symm (project g) • p = g • p
  rw [← equiv_apply, equiv.symm_apply_apply]

@[simp] theorem project_smul_line (g : SL) (l : Line) : project g • l = g • l := by
  change equiv.symm (project g) • l = g • l
  rw [← equiv_apply, equiv.symm_apply_apply]

theorem incident_smul_SL (g : SL) (p : Point) (l : Line) :
    Incident (g • p) (g • l) ↔ Incident p l := by
  change (g.val *ᵥ p.val) ⬝ᵥ
    ((MarkedAutomorphisms.inverseTranspose g).val *ᵥ l.normal.val) = 0 ↔ _
  have hi : (MarkedAutomorphisms.inverseTranspose g).val = ((g⁻¹).val)ᵀ := by
    change adjugate g.valᵀ = (adjugate g.val)ᵀ
    exact (adjugate_transpose g.val).symm
  rw [hi]
  rw [dotProduct_transpose_mulVec, mulVec_mulVec]
  change l.normal.val ⬝ᵥ ((g⁻¹ * g).val *ᵥ p.val) = 0 ↔ _
  simp [Incident, dotProduct_comm]

theorem incident_smul (g : PSL) (p : Point) (l : Line) :
    Incident (g • p) (g • l) ↔ Incident p l :=
  incident_smul_SL (equiv.symm g) p l

private theorem point_eq_flag : ∀ p : Point,
    p = flagPoint ↔ p.val 1 = 0 ∧ p.val 2 = 0 := by decide +kernel

private theorem normal_eq_flag : ∀ p : Point,
    p = flagLine.normal ↔ p.val 0 = 0 ∧ p.val 1 = 0 := by decide +kernel

theorem stabilizer_flagPoint_SL : MulAction.stabilizer SL flagPoint = pointParabolicSL := by
  ext g
  change g • flagPoint = flagPoint ↔ g ∈ pointParabolicSL
  rw [point_eq_flag, mem_pointParabolicSL_iff]
  change (g.val *ᵥ ![1, 0, 0]) 1 = 0 ∧ (g.val *ᵥ ![1, 0, 0]) 2 = 0 ↔ _
  simp [mulVec, dotProduct, Fin.sum_univ_three]

theorem stabilizer_flagLine_SL : MulAction.stabilizer SL flagLine = lineParabolicSL := by
  ext g
  change Line.mk (MarkedAutomorphisms.inverseTranspose g • flagLine.normal) =
    Line.mk flagLine.normal ↔ g ∈ lineParabolicSL
  rw [Line.mk.injEq]
  change (SpecialLinearGroup.transpose g)⁻¹ • flagLine.normal = flagLine.normal ↔ _
  rw [inv_smul_eq_iff, eq_comm, normal_eq_flag, mem_lineParabolicSL_iff]
  change (g.valᵀ *ᵥ ![0, 0, 1]) 0 = 0 ∧ (g.valᵀ *ᵥ ![0, 0, 1]) 1 = 0 ↔ _
  simp [mulVec, dotProduct, Fin.sum_univ_three]

theorem stabilizer_flagPoint : MulAction.stabilizer PSL flagPoint = pointParabolic := by
  ext g
  obtain ⟨a, rfl⟩ := project_surjective g
  change project a • flagPoint = flagPoint ↔ _
  rw [project_smul_point]
  change a ∈ MulAction.stabilizer SL flagPoint ↔ _
  rw [stabilizer_flagPoint_SL, mem_pointParabolicSL_iff, mem_pointParabolic_project]

theorem stabilizer_flagLine : MulAction.stabilizer PSL flagLine = lineParabolic := by
  ext g
  obtain ⟨a, rfl⟩ := project_surjective g
  change project a • flagLine = flagLine ↔ _
  rw [project_smul_line]
  change a ∈ MulAction.stabilizer SL flagLine ↔ _
  rw [stabilizer_flagLine_SL, mem_lineParabolicSL_iff, mem_lineParabolic_project]

instance : FaithfulSMul SL Point where
  eq_of_smul_eq_smul {g h} he := by
    apply Subtype.ext
    apply Matrix.mulVec_injective
    funext v
    by_cases hv : v = 0
    · simp [hv]
    · exact congrArg Subtype.val (he ⟨v, hv⟩)

instance : FaithfulSMul SL Line where
  eq_of_smul_eq_smul {g h} he := by
    apply MarkedAutomorphisms.inverseTranspose.injective
    apply eq_of_smul_eq_smul (α := Point)
    intro p
    exact congrArg Line.normal (he ⟨p⟩)

instance : FaithfulSMul PSL Point where
  eq_of_smul_eq_smul he :=
    equiv.symm.injective (eq_of_smul_eq_smul (α := Point) he)

instance : FaithfulSMul PSL Line where
  eq_of_smul_eq_smul he :=
    equiv.symm.injective (eq_of_smul_eq_smul (α := Line) he)

private theorem full_orbit_of_card {X : Type*} [Finite X] [MulAction PSL X]
    (x : X) (hc : Nat.card X * Nat.card (MulAction.stabilizer PSL x) = 168) :
    ∀ y : X, ∃ g : PSL, g • x = y := by
  have hq : Nat.card (PSL ⧸ MulAction.stabilizer PSL x) = Nat.card X := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := MulAction.stabilizer PSL x))
    exact (MulAction.stabilizer PSL x).index_mul_card.trans (card_PSL.trans hc.symm)
  have hs := ((Nat.bijective_iff_injective_and_card
    (MulAction.ofQuotientStabilizer PSL x)).mpr
      ⟨MulAction.injective_ofQuotientStabilizer PSL x, hq⟩).surjective
  intro y
  obtain ⟨q, hq⟩ := hs y
  induction q using Quotient.inductionOn with | h g => exact ⟨g, hq⟩

instance : MulAction.IsPretransitive PSL Point :=
  MulAction.IsPretransitive.of_orbit (full_orbit_of_card flagPoint (by
    rw [stabilizer_flagPoint, card_pointParabolic, Nat.card_eq_fintype_card, card_point]))

instance : MulAction.IsPretransitive PSL Line :=
  MulAction.IsPretransitive.of_orbit (full_orbit_of_card flagLine (by
    rw [stabilizer_flagLine, card_lineParabolic, Nat.card_eq_fintype_card, card_line]))

instance : MulAction.IsPreprimitive PSL Point :=
  MulAction.IsPreprimitive.of_prime_card (by rw [Nat.card_eq_fintype_card, card_point]; decide)

instance : MulAction.IsPreprimitive PSL Line :=
  MulAction.IsPreprimitive.of_prime_card (by rw [Nat.card_eq_fintype_card, card_line]; decide)

abbrev Flag := {pl : Point × Line // Incident pl.1 pl.2}

def baseFlag : Flag := ⟨(flagPoint, flagLine), flag_incident⟩

noncomputable instance : MulAction PSL Flag where
  smul g f := ⟨(g • f.val.1, g • f.val.2), (incident_smul g _ _).mpr f.property⟩
  one_smul f := by apply Subtype.ext; exact Prod.ext (one_smul _ _) (one_smul _ _)
  mul_smul g h f := by apply Subtype.ext; exact Prod.ext (mul_smul _ _ _) (mul_smul _ _ _)

theorem stabilizer_baseFlag : MulAction.stabilizer PSL baseFlag = borel := by
  rw [← pointParabolic_inf_line, ← stabilizer_flagPoint, ← stabilizer_flagLine]
  ext g
  change g • baseFlag = baseFlag ↔ g • flagPoint = flagPoint ∧ g • flagLine = flagLine
  rw [Subtype.ext_iff, Prod.ext_iff]
  rfl

instance : MulAction.IsPretransitive PSL Flag :=
  MulAction.IsPretransitive.of_orbit (full_orbit_of_card baseFlag (by
    rw [stabilizer_baseFlag, card_borel, Nat.card_eq_fintype_card, card_flags]))

theorem flag_transitive (p : Point) (l : Line) (h : Incident p l) :
    ∃ g : PSL, g • flagPoint = p ∧ g • flagLine = l := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL baseFlag (⟨(p, l), h⟩ : Flag)
  exact ⟨g, Prod.mk.inj (congrArg Subtype.val hg)⟩


end Matrix.PSL3Two.Fano
