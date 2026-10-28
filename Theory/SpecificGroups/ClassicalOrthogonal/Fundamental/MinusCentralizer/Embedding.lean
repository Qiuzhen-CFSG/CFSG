module

public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Commutator
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.MinusCentralizer.Blocks
public import Theory.GroupTheory.PResidual.PrimeTo
import Lean.Elab.Tactic.Omega

/-!
# Fundamental SL₂ and centralizer blocks in projective minus Omega

The four-space elementary action is first placed in the full isometry
commutator subgroup. Extension by the identity on the nonzero complement
remains injective after the literal scalar quotient. Its left SL₂ factor is
proper and injective. The right factor and the complementary commutator Omega
embed as a product in the ambient cover and centralize the left factor.

The projective kernel is exactly the common scalar on these two blocks,
with square-one multiplier. A complementary scalar is required to belong to
the actual complementary commutator carrier. This module does not assert
which nonidentity scalars have that membership, or identify the whole residual
with the constructed block image. It defines the literal nested residual for
that remaining calculation. A cubic is constructed in every minus cover of
dimension at least six; the four-dimensional cover is a separate case.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.17,
printed p.39. Rank `r + 3` here has complement of rank `r + 1`.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

open Matrix Theory.AlgebraicGroup
namespace ClassicalOrthogonal.Fundamental.MinusCentralizer
open FourPlusMatrix TheoremDRootNormalizer.HigherRanks
variable {F : Type*} [Field F]

/-- The split elementary carrier lies in the full orthogonal commutator group.
This comparison includes the field with three elements. -/
def fourElementaryDerived [Finite F] (hq : 2 < Nat.card F) :
    OmegaPlus 2 F →* commutator (O 2 F) :=
  (elementarySubgroup (formD 2 F)).subtype.codRestrict _ (by
    intro g
    obtain ⟨x, rfl⟩ := fourMap_surjective g
    exact fourMap_mem_commutator hq x)

theorem fourElementaryDerived_injective [Finite F] (hq : 2 < Nat.card F) :
    Function.Injective (fourElementaryDerived (F := F) hq) := by
  intro g h he
  exact Subtype.ext (congrArg (fun x : commutator (O 2 F) => x.val) he)

/-- Extension of the full marked four-space carrier and the complementary Omega. -/
def elementaryBlockHom [Finite F] (r : ℕ) (a : F) (hq : 2 < Nat.card F) :
    OmegaPlus 2 F × Minus.Omega F (Minus.Space F r) (Minus.form F r a) →*
      Minus.Omega F (Minus.Space F (r + 2)) (Minus.form F (r + 2) a) :=
  (derivedBlockHom r a).comp ((fourElementaryDerived hq).prodMap (MonoidHom.id _))

theorem elementaryBlockHom_injective [Finite F] (r : ℕ) (a : F)
    (hq : 2 < Nat.card F) : Function.Injective (elementaryBlockHom r a hq) := by
  intro g h he
  have hh := derivedBlockHom_injective r a he
  change (fourElementaryDerived hq g.1, g.2) = (fourElementaryDerived hq h.1, h.2) at hh
  have hh2 := congrArg Prod.snd hh
  exact Prod.ext (fourElementaryDerived_injective hq (congrArg Prod.fst hh)) hh2

/-- The marked split four-space acts trivially on the entire minus complement. -/
def splitOmegaHom [Finite F] (r : ℕ) (a : F) (hq : 2 < Nat.card F) :
    OmegaPlus 2 F →* Minus.Omega F (Minus.Space F (r + 2)) (Minus.form F (r + 2) a) :=
  (elementaryBlockHom r a hq).comp (MonoidHom.inl _ _)

theorem splitOmegaHom_coordinates [Finite F] (r : ℕ) (a : F) (hq : 2 < Nat.card F)
    (g : OmegaPlus 2 F) (x : Minus.Space F (r + 2)) :
    splitCoordinates r ((splitOmegaHom r a hq g).val.val x) =
      (g.val.val (splitCoordinates r x).1, (splitCoordinates r x).2) :=
  blockHom_coordinates r a (g.val, 1) x

theorem splitOmegaHom_injective [Finite F] (r : ℕ) (a : F) (hq : 2 < Nat.card F) :
    Function.Injective (splitOmegaHom r a hq) := by
  intro g h he
  exact congrArg Prod.fst (elementaryBlockHom_injective r a hq he)

/-- The literal scalar quotient, retaining the marked four-space. -/
def splitProjectiveHom [Finite F] (r : ℕ) (a : F) (hq : 2 < Nat.card F) :
    OmegaPlus 2 F →* Minus.ProjectiveOmega F (Minus.Space F (r + 2))
      (Minus.form F (r + 2) a) :=
  (QuotientGroup.mk' (Minus.scalarSubgroup F _ _)).comp (splitOmegaHom r a hq)

/-- Fixing a nonzero vector in the complement prevents any scalar collapse. -/
theorem splitProjectiveHom_injective [Finite F] (r : ℕ) (a : F)
    (hq : 2 < Nat.card F) : Function.Injective (splitProjectiveHom r a hq) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  obtain ⟨c, hc⟩ := (Minus.projectiveOmega_mk_eq_one_iff F _ _ _).mp hg
  have hcoord (y : VectorD 2 F × Minus.Space F r) :=
    congrArg (splitCoordinates r) (hc ((splitCoordinates r).symm y))
  simp only [splitOmegaHom_coordinates, LinearEquiv.apply_symm_apply,
    map_smul] at hcoord
  have hc1 : (c : F) = 1 := by
    have ht := congrArg (fun y : VectorD 2 F × Minus.Space F r => y.2.2.1)
      (hcoord (0, (0, (1, 0))))
    simpa using ht.symm
  apply splitOmegaHom_injective r a hq
  rw [map_one]
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (splitOmegaHom r a hq g).val.val x = x
  simpa only [hc1, one_smul] using hc x

/-- The fundamental SL₂, in the actual projective minus model. -/
def fundamentalHom [Finite F] (r : ℕ) (hq : 2 < Nat.card F) :
    SpecialLinearGroup (Fin 2) F →* ClassicalGroup.POmegaMinus (r + 3) F :=
  (splitProjectiveHom r (Minus.parameter F) hq).comp fourLeft

theorem fundamentalHom_injective [Finite F] (r : ℕ) (hq : 2 < Nat.card F) :
    Function.Injective (fundamentalHom r hq) :=
  (splitProjectiveHom_injective r (Minus.parameter F) hq).comp fourLeft_injective

/-- The second marked factor witnesses properness of the fundamental subgroup. -/
theorem fundamentalHom_proper [Finite F] (r : ℕ) (hq : 2 < Nat.card F) :
    (fundamentalHom r hq).range ≠ ⊤ := by
  intro ht
  apply fourLeft_proper (F := F)
  apply top_unique
  intro g _
  have hm : splitProjectiveHom r (Minus.parameter F) hq g ∈ (fundamentalHom r hq).range :=
    ht ▸ Subgroup.mem_top _
  obtain ⟨a, ha⟩ := hm
  exact ⟨a, splitProjectiveHom_injective r (Minus.parameter F) hq ha⟩

/-- The covering centralizer blocks use the commuting right SL₂ factor. -/
def coverBlockHom [Finite F] (r : ℕ) (hq : 2 < Nat.card F) :
    SpecialLinearGroup (Fin 2) F ×
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) →*
      Minus.Omega F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3)) :=
  (elementaryBlockHom r (Minus.parameter F) hq).comp (fourRight.prodMap (MonoidHom.id _))

theorem coverBlockHom_injective [Finite F] (r : ℕ) (hq : 2 < Nat.card F) :
    Function.Injective (coverBlockHom r hq) := by
  intro g h he
  have hh := elementaryBlockHom_injective r (Minus.parameter F) hq he
  change (fourRight g.1, g.2) = (fourRight h.1, h.2) at hh
  have hh2 := congrArg Prod.snd hh
  exact Prod.ext (fourRight_injective (congrArg Prod.fst hh)) hh2

/-- The blocks commute with the fundamental factor before taking any quotient. -/
theorem coverBlockHom_commute [Finite F] (r : ℕ) (hq : 2 < Nat.card F)
    (a : SpecialLinearGroup (Fin 2) F)
    (g : SpecialLinearGroup (Fin 2) F ×
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    Commute (splitOmegaHom r (Minus.parameter F) hq (fourLeft a)) (coverBlockHom r hq g) := by
  change Commute (elementaryBlockHom r (Minus.parameter F) hq (fourLeft a, 1))
    (elementaryBlockHom r (Minus.parameter F) hq (fourRight g.1, g.2))
  apply Commute.map
  exact Prod.ext (fourFactors_commute a g.1).eq (by simp)

/-- Every minus cover of dimension at least six already contains a marked cubic. -/
theorem higherMinus_exists_cubic [Finite F] (r : ℕ) (hq : 2 < Nat.card F) :
    ∃ b : Minus.Omega F (Minus.Space F (r + 2)) (Minus.quadraticForm F (r + 3)),
      orderOf b = 3 := by
  refine ⟨splitOmegaHom r (Minus.parameter F) hq (fourLeft cubicSL), ?_⟩
  rw [orderOf_injective _ (splitOmegaHom_injective r (Minus.parameter F) hq),
    orderOf_injective _ fourLeft_injective, cubicSL_order]

/-- Projectivization of the literal covering block map. -/
def projectiveBlockHom [Finite F] (r : ℕ) (hq : 2 < Nat.card F) :
    SpecialLinearGroup (Fin 2) F ×
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)) →*
      ClassicalGroup.POmegaMinus (r + 3) F :=
  (QuotientGroup.mk' (Minus.scalarSubgroup F _ _)).comp (coverBlockHom r hq)

/-- The constructed blocks belong to the centralizer of the marked fundamental subgroup. -/
theorem projectiveBlockHom_le_centralizer [Finite F] (r : ℕ) (hq : 2 < Nat.card F) :
    (projectiveBlockHom r hq).range ≤
      Subgroup.centralizer ((fundamentalHom r hq).range : Set (ClassicalGroup.POmegaMinus (r + 3) F)) := by
  rintro _ ⟨g, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨a, rfl⟩
  exact (coverBlockHom_commute r hq a g).map
    (QuotientGroup.mk' (Minus.scalarSubgroup F _ _))

/-- Being scalar on the orthogonal direct sum means the same scalar on both blocks. -/
theorem blockHom_scalar_iff (r : ℕ) (a c : F)
    (g : O 2 F × Minus.Orthogonal F (Minus.Space F r) (Minus.form F r a)) :
    (∀ x, (blockHom r a g).val x = c • x) ↔
      (∀ v, g.1.val v = c • v) ∧ (∀ w, g.2.val w = c • w) := by
  constructor
  · intro h
    have hh (y : VectorD 2 F × Minus.Space F r) :=
      congrArg (splitCoordinates r) (h ((splitCoordinates r).symm y))
    simp only [blockHom_coordinates, LinearEquiv.apply_symm_apply, map_smul] at hh
    exact ⟨fun v => congrArg Prod.fst (hh (v, 0)),
      fun w => congrArg Prod.snd (hh (0, w))⟩
  · rintro ⟨h1, h2⟩ x
    apply (splitCoordinates r).injective
    rw [blockHom_coordinates, map_smul, h1, h2]
    rfl

/-- The scalar equation on determinant space is detected by the identity matrix. -/
theorem fourRight_scalar_iff (B : SpecialLinearGroup (Fin 2) F) (c : F) :
    (∀ v, (fourRight B).val.val v = c • v) ↔ B⁻¹.val = c • (1 : Mat (F := F)) := by
  constructor
  · intro h
    have hh := congrArg coordinates (h (coordinates.symm 1))
    change coordinates ((toOrthogonal (1, B)).val (coordinates.symm 1)) = _ at hh
    rw [toOrthogonal_coordinates, LinearEquiv.apply_symm_apply, map_smul,
      LinearEquiv.apply_symm_apply] at hh
    simpa using hh
  · intro h v
    apply coordinates.injective
    change coordinates ((toOrthogonal (1, B)).val v) = _
    rw [toOrthogonal_coordinates, map_smul, h]
    simp

/-- Exact common-scalar kernel, with the complement an element of its actual Omega carrier. -/
theorem projectiveBlockHom_kernel_iff [Finite F] (r : ℕ) (hq : 2 < Nat.card F)
    (g : SpecialLinearGroup (Fin 2) F ×
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    projectiveBlockHom r hq g = 1 ↔
      ∃ c : Fˣ, g.1⁻¹.val = (c : F) • (1 : Mat (F := F)) ∧
        ∀ w, g.2.val.val w = (c : F) • w := by
  change QuotientGroup.mk' (Minus.scalarSubgroup F _ _) (coverBlockHom r hq g) = 1 ↔ _
  rw [Minus.projectiveOmega_mk_eq_one_iff]
  change (∃ c : Fˣ, ∀ x, (blockHom r (Minus.parameter F) ((fourRight g.1).val, g.2.val)).val x =
    (c : F) • x) ↔ _
  simp_rw [blockHom_scalar_iff, fourRight_scalar_iff]

/-- The common-scalar kernel has exponent at most two. -/
theorem projectiveBlockHom_kernel_square [Finite F] (r : ℕ) (hq : 2 < Nat.card F)
    (g : SpecialLinearGroup (Fin 2) F ×
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1)))
    (hg : projectiveBlockHom r hq g = 1) : g ^ 2 = 1 := by
  apply omegaProjective_kernel_square (Minus.quadraticForm F (r + 3)) _
    (coverBlockHom r hq) (coverBlockHom_injective r hq) g hg
  exact ⟨(0, (1, 0)), by simp [Minus.quadraticForm, Minus.plane_apply]⟩

/-- The block quotient is identified with its literal image under the projective map. -/
def blockQuotientEquivRange [Finite F] (r : ℕ) (hq : 2 < Nat.card F) :
    (SpecialLinearGroup (Fin 2) F ×
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) ⧸
      (projectiveBlockHom r hq).ker ≃* (projectiveBlockHom r hq).range :=
  QuotientGroup.quotientKerEquivRange (projectiveBlockHom r hq)

/-- For a special linear two-by-two matrix, an inverse scalar is the same scalar. -/
theorem sl_inverse_scalar_iff (B : SpecialLinearGroup (Fin 2) F) (c : F) :
    B⁻¹.val = c • (1 : Mat (F := F)) ↔
      c ^ 2 = 1 ∧ B.val = c • (1 : Mat (F := F)) := by
  constructor
  · intro h
    have hc : c ^ 2 = 1 := by
      have hh := congrArg Matrix.det h
      have ht : c ^ 2 = B⁻¹.val.det := by
        simpa only [Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one] using hh.symm
      exact ht.trans B⁻¹.property
    refine ⟨hc, ?_⟩
    have hh := congrArg (fun M : Mat (F := F) => B.val * M) h
    have hm : B.val * B⁻¹.val = 1 :=
      congrArg (fun A : SpecialLinearGroup (Fin 2) F => A.val) (mul_inv_cancel B)
    rw [hm, Matrix.mul_smul, mul_one] at hh
    have ht := congrArg (fun M : Mat (F := F) => c • M) hh
    rw [smul_smul, ← pow_two, hc, one_smul] at ht
    exact ht.symm
  · rintro ⟨hc, hB⟩
    have hh : B * B = 1 := by
      apply Subtype.ext
      change B.val * B.val = (1 : Mat (F := F))
      rw [hB, Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, ← pow_two, hc, one_smul]
    have hi : B⁻¹ = B := (eq_inv_iff_mul_eq_one.mpr hh).symm
    simpa only [hi] using hB

/-- Symmetric common-scalar form of the exact kernel calculation. -/
theorem projectiveBlockHom_kernel_commonScalar [Finite F] (r : ℕ) (hq : 2 < Nat.card F)
    (g : SpecialLinearGroup (Fin 2) F ×
      Minus.Omega F (Minus.Space F r) (Minus.quadraticForm F (r + 1))) :
    projectiveBlockHom r hq g = 1 ↔
      ∃ c : Fˣ, (c : F) ^ 2 = 1 ∧ g.1.val = (c : F) • (1 : Mat (F := F)) ∧
        ∀ w, g.2.val.val w = (c : F) • w := by
  rw [projectiveBlockHom_kernel_iff]
  simp_rw [sl_inverse_scalar_iff, and_assoc]

/-- The literal centralizer of the constructed fundamental subgroup. -/
abbrev fundamentalCentralizer [Finite F] (r : ℕ) (hq : 2 < Nat.card F) :=
  Subgroup.centralizer ((fundamentalHom r hq).range : Set (ClassicalGroup.POmegaMinus (r + 3) F))

/-- The source residual remains a subgroup of the centralizer. -/
def centralizerResidual [Finite F] (p r : ℕ) (hq : 2 < Nat.card F) :
    Subgroup (fundamentalCentralizer r hq) :=
  Subgroup.primeToResidual p (fundamentalCentralizer r hq)

/-- Its image under the literal inclusion of the centralizer in the ambient model. -/
def centralizerResidualImage [Finite F] (p r : ℕ) (hq : 2 < Nat.card F) :
    Subgroup (ClassicalGroup.POmegaMinus (r + 3) F) :=
  (centralizerResidual p r hq).map (fundamentalCentralizer r hq).subtype

/-- Odd prime characteristic supplies the only field-size bound used by the embeddings. -/
theorem field_card_gt_two [Finite F] {p : ℕ} [CharP F p] (hp : p.Prime) (ho : Odd p) :
    2 < Nat.card F := by
  let := Fintype.ofFinite F
  obtain ⟨e, _, he⟩ := FiniteField.card F p
  have hp2 : 2 < p := by
    obtain ⟨k, hk⟩ := ho
    have := hp.two_le
    omega
  rw [Nat.card_eq_fintype_card, he]
  exact hp2.trans_le (le_self_pow (by omega : 1 ≤ p) e.ne_zero)


end ClassicalOrthogonal.Fundamental.MinusCentralizer
