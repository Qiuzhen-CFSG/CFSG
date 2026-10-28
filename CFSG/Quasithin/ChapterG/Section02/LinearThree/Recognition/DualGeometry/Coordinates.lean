module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Models
public import Theory.Combinatorics.ProjectivePlaneMatrixAction
public import Theory.Representation.QuadraticDuality
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The actual dual coordinate frame in G.2.5

The source multiplicative coordinates send the three marked point groups to
three independent F-lines. Their pair planes therefore have one-dimensional
annihilators, giving the three literal dual projective marks. Inverse transpose
and the dot-product duality construct a natural marking of the contragredient
representation. Annihilator transport identifies its point stabilizer with the
natural plane stabilizer and exchanges the two root-group descriptions.

These are geometric inputs to the binary quotient criterion. This module does
not assert a point map into S₃/S₂ or full I-invariance of S₃.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.1.1 and G.2.5(6), printed pp.327,335–336, PDF pp.338,346–347.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
open Subgroup Setup Projective Matrix
namespace DualGeometry
open CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.Hypothesis
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)

omit [Finite F] in
private theorem inverseTranspose_twice (a : Matrix.SpecialLinearGroup (Fin 3) F) :
    Matrix.SpecialLinearGroup.inverseTranspose (Matrix.SpecialLinearGroup.inverseTranspose a) = a := by
  change ((Matrix.SpecialLinearGroup.inverseTranspose a)⁻¹).transpose = a
  rw [← map_inv]
  change ((a⁻¹)⁻¹).transpose.transpose = a
  rw [inv_inv]
  apply Subtype.ext
  rfl

def contragredientEquiv : Matrix.SpecialLinearGroup (Fin 3) F ≃*
    Matrix.SpecialLinearGroup (Fin 3) F :=
  { Matrix.SpecialLinearGroup.inverseTranspose with
    invFun := Matrix.SpecialLinearGroup.inverseTranspose
    left_inv := by exact inverseTranspose_twice
    right_inv := by exact inverseTranspose_twice }

/-- The natural marking of the dual uses the genuine inverse-transpose automorphism. -/
def dualMarking : NaturalMarking (dualAction d) where
  groupEquiv := d.model.trans contragredientEquiv
  coordinates := (dotProductEquiv F (Fin 3)).symm
  equivariant := by
    intro a f
    apply (dotProductEquiv F (Fin 3)).injective
    rw [LinearEquiv.apply_symm_apply]
    obtain ⟨v, rfl⟩ := (dotProductEquiv F (Fin 3)).surjective f
    rw [LinearEquiv.symm_apply_apply]
    apply LinearMap.ext
    intro w
    change v ⬝ᵥ ((d.model a⁻¹).val *ᵥ w) =
      ((d.model a)⁻¹).val.transpose.mulVec v ⬝ᵥ w
    rw [map_inv, dotProduct_comm _ w, Matrix.dotProduct_transpose_mulVec]

/-- Right conjugation on the literal natural subgroup. -/
def conjugateVector (x : D.L) (v : D.V) : D.V :=
  ⟨(x : G)⁻¹ * v * (x : G), by
    simpa using (mem_normalizer_iff.mp
      (normalizes_of_span D d.span_eq (D.L.inv_mem x.property)) v).mp v.property⟩

/-- Coordinates intertwine right conjugation with the inverse actor. -/
theorem coordinates_conjugateVector (x : D.L) (v : D.V) :
    (d.coordinates (conjugateVector d x v)).toAdd =
      naturalAction d ((starProjection D x)⁻¹) (d.coordinates v).toAdd := by
  simpa only [conjugateVector, naturalAction, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, map_inv, Subgroup.coe_inv, inv_inv, Representation.specialLinearNatural_apply]
    using d.equivariant x⁻¹ v

/-- The coordinate mark has exactly the source's right-conjugation convention. -/
theorem conjugatePoint_mem (x : D.L) (v : D.V) :
    (v : G) ∈ conjugate D.V₁ (x : G) ↔
      (d.coordinates v).toAdd ∈ (conjugatePoint d x).val := by
  constructor
  · rintro ⟨a, ha, he⟩
    refine ⟨(d.coordinates ⟨a, d.setup.point_le ha⟩).toAdd,
      (d.point_mem _).mp ha, ?_⟩
    rw [← coordinates_conjugateVector]
    exact congrArg (fun z : D.V => (d.coordinates z).toAdd) (Subtype.ext (by simpa [conjugateVector] using he))
  · rintro ⟨w, hw, he⟩
    let a : D.V := d.coordinates.symm (Multiplicative.ofAdd w)
    have ha : (a : G) ∈ D.V₁ := (d.point_mem a).mpr (by simpa [a] using hw)
    refine ⟨(a : G), ha, ?_⟩
    suffices hz : ((conjugateVector d x a : D.V) : G) = v by
      simpa [conjugateVector] using hz
    apply congrArg Subtype.val
    apply d.coordinates.injective
    change (d.coordinates (conjugateVector d x a)).toAdd = (d.coordinates v).toAdd
    rw [coordinates_conjugateVector]
    simpa [a] using he

/-- The two first source points remain disjoint in the actual F-coordinates. -/
theorem natural_points_disjoint :
    Disjoint d.point (conjugatePoint d ⟨g, d.g_mem⟩).val := by
  apply Submodule.disjoint_def.mpr
  intro v hv hg
  let a : D.V := d.coordinates.symm (Multiplicative.ofAdd v)
  have ha : (a : G) ∈ D.V₁ := (d.point_mem a).mpr (by simpa [a] using hv)
  have hag : (a : G) ∈ conjugate D.V₁ g :=
    (conjugatePoint_mem d ⟨g, d.g_mem⟩ a).mpr (by simpa [a] using hg)
  have ha1 : (a : G) = 1 := Subgroup.disjoint_def.mp d.points_disjoint ha hag
  have ha1' : a = 1 := Subtype.ext ha1
  have he := congrArg (fun z : D.V => (d.coordinates z).toAdd) ha1'
  simpa [a] using he

/-- The third marked point is disjoint from the coordinate plane of the first two. -/
theorem natural_third_disjoint :
    Disjoint (pairPlane d) (conjugatePoint d ⟨h, d.h_mem⟩).val := by
  apply Submodule.disjoint_def.mpr
  intro v hv hh
  obtain ⟨a, ha, b, hb, he⟩ := Submodule.mem_sup.mp hv
  let aV : D.V := d.coordinates.symm (Multiplicative.ofAdd a)
  let bV : D.V := d.coordinates.symm (Multiplicative.ofAdd b)
  have haV : (aV : G) ∈ D.V₁ := (d.point_mem aV).mpr (by simpa [aV] using ha)
  have hbV : (bV : G) ∈ conjugate D.V₁ g :=
    (conjugatePoint_mem d ⟨g, d.g_mem⟩ bV).mpr (by simpa [bV] using hb)
  have hab : (d.coordinates (aV * bV)).toAdd = v := by
    simpa [aV, bV] using he
  have hhV : ((aV * bV : D.V) : G) ∈ conjugate D.V₁ h :=
    (conjugatePoint_mem d ⟨h, d.h_mem⟩ (aV * bV)).mpr (hab.symm ▸ hh)
  have h1 : ((aV * bV : D.V) : G) = 1 :=
    Subgroup.disjoint_def.mp d.third_disjoint
      ((D.V₁ ⊔ conjugate D.V₁ g).mul_mem (mem_sup_left haV) (mem_sup_right hbV)) hhV
  have h1' : aV * bV = 1 := Subtype.ext h1
  rw [h1', map_one] at hab
  exact hab.symm

/-- The source pair spans a genuine plane, rather than a repeated point. -/
theorem pairPlane_dimension : Module.finrank F (pairPlane d) = 2 := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq d.point
    (conjugatePoint d ⟨g, d.g_mem⟩).val
  rw [(natural_points_disjoint d).eq_bot, finrank_bot,
    d.point_dimension, (conjugatePoint d ⟨g, d.g_mem⟩).property] at hd
  change Module.finrank F ↥(d.point ⊔ (conjugatePoint d ⟨g, d.g_mem⟩).val) = 2
  omega

/-- The marked annihilator is a one-dimensional F-subspace of the dual. -/
theorem pairAnnihilator_dimension : Module.finrank F (pairAnnihilator d) = 1 := by
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq (pairPlane d)
  rw [pairPlane_dimension, Module.finrank_pi, Fintype.card_fin,
] at hd
  change Module.finrank F (pairPlane d).dualAnnihilator = 1
  omega

/-- The actual dual projective mark attached to W ∩ Wᵍ. -/
def dualPoint : Point F (Module.Dual F (Fin 3 → F)) :=
  ⟨pairAnnihilator d, pairAnnihilator_dimension d⟩

/-- Annihilators are transported by the actual contragredient action. -/
theorem dualAnnihilator_map (A : Submodule F (Fin 3 → F)) (a : D.star D.L) :
    (A.map (naturalAction d a)).dualAnnihilator =
      A.dualAnnihilator.map (dualAction d a) := by
  ext f
  constructor
  · intro hf
    refine ⟨dualAction d a⁻¹ f, ?_, (dualAction d).self_inv_apply a f⟩
    change dualAction d a⁻¹ f ∈ A.dualAnnihilator
    rw [Submodule.mem_dualAnnihilator] at hf ⊢
    intro v hv
    change f (naturalAction d a⁻¹⁻¹ v) = 0
    rw [inv_inv]
    exact hf _ (Submodule.mem_map_of_mem hv)
  · rintro ⟨f, hf, rfl⟩
    change f ∈ A.dualAnnihilator at hf
    rw [Submodule.mem_dualAnnihilator] at hf ⊢
    rintro _ ⟨v, hv, rfl⟩
    change f (naturalAction d a⁻¹ (naturalAction d a v)) = 0
    rw [(naturalAction d).inv_self_apply]
    exact hf v hv

/-- The stabilizer of the actual dual mark is precisely the plane stabilizer. -/
theorem dualPoint_stabilizer_iff (a : D.star D.L) :
    (pairAnnihilator d).map (dualAction d a) = pairAnnihilator d ↔
      (pairPlane d).map (naturalAction d a) = pairPlane d := by
  rw [pairAnnihilator, ← dualAnnihilator_map, Subspace.dualAnnihilator_inj]

/-- Transvections with natural center A and axis B have dual center Bᵃⁿⁿ
and axis Aᵃⁿⁿ, for the literal root-group definitions. -/
theorem dual_rootGroup (A B : Submodule F (Fin 3 → F)) :
    rootGroup (naturalAction d) A B =
      rootGroup (dualAction d) B.dualAnnihilator A.dualAnnihilator := by
  ext a
  constructor
  · intro ha
    have hai := (rootGroup (naturalAction d) A B).inv_mem ha
    change (∀ f, dualAction d a f - f ∈ B.dualAnnihilator) ∧
      (∀ f ∈ A.dualAnnihilator, dualAction d a f = f)
    constructor
    · intro f
      rw [Submodule.mem_dualAnnihilator]
      intro v hv
      change f (naturalAction d a⁻¹ v) - f v = 0
      rw [hai.2 v hv, sub_self]
    · intro f hf
      apply LinearMap.ext
      intro v
      rw [Submodule.mem_dualAnnihilator] at hf
      have he := hf _ (hai.1 v)
      change f (naturalAction d a⁻¹ v) = f v
      exact sub_eq_zero.mp (by simpa only [map_sub] using he)
  · intro ha
    have hai := (rootGroup (dualAction d) B.dualAnnihilator A.dualAnnihilator).inv_mem ha
    change (∀ v, naturalAction d a v - v ∈ A) ∧
      (∀ v ∈ B, naturalAction d a v = v)
    constructor
    · intro v
      apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff A _).mp
      intro f hf
      have he := LinearMap.congr_fun (hai.2 f hf) v
      change f (naturalAction d a⁻¹⁻¹ v) = f v at he
      simpa only [inv_inv, map_sub, sub_eq_zero] using he
    · intro v hv
      apply Module.eval_apply_injective F
      apply LinearMap.ext
      intro f
      have hf := hai.1 f
      rw [Submodule.mem_dualAnnihilator] at hf
      have he := hf v hv
      change f (naturalAction d a⁻¹⁻¹ v) - f v = 0 at he
      change f (naturalAction d a v) = f v
      simpa only [inv_inv] using sub_eq_zero.mp he

/-- The three source coordinate lines span the natural space. -/
theorem natural_points_span :
    pairPlane d ⊔ (conjugatePoint d ⟨h, d.h_mem⟩).val = ⊤ := by
  apply Submodule.eq_top_of_disjoint _ _ _ (natural_third_disjoint d)
  rw [pairPlane_dimension, (conjugatePoint d ⟨h, d.h_mem⟩).property]
  simp

/-- The other plane through the original point. -/
def pairPlaneH : Submodule F (Fin 3 → F) :=
  d.point ⊔ (conjugatePoint d ⟨h, d.h_mem⟩).val

/-- The plane through the two conjugate points. -/
def pairPlaneGH : Submodule F (Fin 3 → F) :=
  (conjugatePoint d ⟨g, d.g_mem⟩).val ⊔ (conjugatePoint d ⟨h, d.h_mem⟩).val

/-- The second marked plane has dimension two. -/
theorem pairPlaneH_dimension : Module.finrank F (pairPlaneH d) = 2 := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq d.point
    (conjugatePoint d ⟨h, d.h_mem⟩).val
  have hdis := (natural_third_disjoint d).mono_left (show d.point ≤ pairPlane d from le_sup_left)
  rw [hdis.eq_bot, finrank_bot, d.point_dimension,
    (conjugatePoint d ⟨h, d.h_mem⟩).property] at hd
  change Module.finrank F ↥(d.point ⊔ (conjugatePoint d ⟨h, d.h_mem⟩).val) = 2
  omega

/-- The third marked plane has dimension two. -/
theorem pairPlaneGH_dimension : Module.finrank F (pairPlaneGH d) = 2 := by
  have hd := Submodule.finrank_sup_add_finrank_inf_eq
    (conjugatePoint d ⟨g, d.g_mem⟩).val (conjugatePoint d ⟨h, d.h_mem⟩).val
  have hdis := (natural_third_disjoint d).mono_left
    (show (conjugatePoint d ⟨g, d.g_mem⟩).val ≤ pairPlane d from le_sup_right)
  rw [hdis.eq_bot, finrank_bot, (conjugatePoint d ⟨g, d.g_mem⟩).property,
    (conjugatePoint d ⟨h, d.h_mem⟩).property] at hd
  change Module.finrank F ↥((conjugatePoint d ⟨g, d.g_mem⟩).val ⊔
    (conjugatePoint d ⟨h, d.h_mem⟩).val) = 2
  omega

/-- The second dual mark is the annihilator of V₁+V₁ʰ. -/
def dualPointH : Point F (Module.Dual F (Fin 3 → F)) :=
  ⟨(pairPlaneH d).dualAnnihilator, by
    rw [Subspace.finrank_dualAnnihilator, pairPlaneH_dimension]
    simp⟩

/-- The third dual mark is the annihilator of V₁ᵍ+V₁ʰ. -/
def dualPointGH : Point F (Module.Dual F (Fin 3 → F)) :=
  ⟨(pairPlaneGH d).dualAnnihilator, by
    rw [Subspace.finrank_dualAnnihilator, pairPlaneGH_dimension]
    simp⟩

/-- The first two dual marks are disjoint; their planes together span V. -/
theorem dual_points_disjoint : Disjoint (dualPoint d).val (dualPointH d).val := by
  change Disjoint (pairPlane d).dualAnnihilator (pairPlaneH d).dualAnnihilator
  rw [disjoint_iff, ← Submodule.dualAnnihilator_sup_eq]
  have he : pairPlane d ⊔ pairPlaneH d = ⊤ := by
    rw [pairPlaneH, ← sup_assoc, sup_eq_left.mpr (show d.point ≤ pairPlane d from le_sup_left)]
    exact natural_points_span d
  rw [he, Submodule.dualAnnihilator_top]

/-- The dual marks form the corresponding internal direct decomposition. -/
theorem dual_third_complement :
    IsCompl ((dualPoint d).val ⊔ (dualPointH d).val) (dualPointGH d).val := by
  have hA : IsCompl d.point (pairPlaneGH d) := by
    refine ⟨(natural_points_disjoint d).disjoint_sup_right_of_disjoint_sup_left
      (natural_third_disjoint d), ?_⟩
    apply codisjoint_iff.mpr
    simpa only [pairPlaneGH, pairPlane, sup_assoc] using natural_points_span d
  have hinter : pairPlane d ⊓ pairPlaneH d = d.point := by
    rw [inf_comm, pairPlaneH, sup_inf_assoc_of_le _
      (show d.point ≤ pairPlane d from le_sup_left),
      (natural_third_disjoint d).symm.eq_bot, sup_bot_eq]
  have hd := Subspace.isCompl_dualAnnihilator hA
  rw [← hinter, Subspace.dualAnnihilator_inf_eq] at hd
  exact hd

/-- Spanning is retained even when the later binary quotient has multiplicity zero. -/
theorem dual_points_span :
    ((dualPoint d).val ⊔ (dualPointH d).val) ⊔ (dualPointGH d).val = ⊤ :=
  (dual_third_complement d).codisjoint.eq_top

end DualGeometry
end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition
