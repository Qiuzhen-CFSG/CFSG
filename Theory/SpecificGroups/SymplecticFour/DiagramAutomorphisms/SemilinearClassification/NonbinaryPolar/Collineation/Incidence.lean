module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.ProjectiveAction

/-!
# Subspace transport under projective collineations

A permutation preserving incidence on projective lines induces an order
isomorphism of the vector-subspace lattice. The preimage of a subspace is
closed under addition because the point of a nonzero sum lies on the line
through the two summand points. This supplies span transport without any
assumption of semilinearity.

We also fix explicit coordinate points on the actual four-space and construct
the projective action of a linear equivalence. These are the common interfaces
for frame normalization, coordinate-line arithmetic, and recovery of all points.

Source context: the geometric automorphism fact used in Aschbacher--Smith
F.1.12, printed pp.263--264 of `refs/quasithin.pdf`. The present development
is the projective-geometric ingredient, independent of form preservation.
-/

@[expose] public section
noncomputable section
open Projectivization Module
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.Collineation
variable {F : Type*} [Field F]

/-- Preservation of incidence with the span of two projective points. -/
abbrev PreservesLines (φ : Equiv.Perm (ProjectivePoint F)) : Prop :=
  ∀ p q r, (φ r).submodule ≤ (φ p).submodule ⊔ (φ q).submodule ↔
    r.submodule ≤ p.submodule ⊔ q.submodule

theorem PreservesLines.symm {φ : Equiv.Perm (ProjectivePoint F)}
    (hφ : PreservesLines φ) : PreservesLines φ.symm := by
  intro p q r
  simpa only [Equiv.apply_symm_apply] using
    (hφ (φ.symm p) (φ.symm q) (φ.symm r)).symm

/-- Pull a vector subspace back through the projective permutation. -/
def pullSubmodule (φ : Equiv.Perm (ProjectivePoint F)) (hφ : PreservesLines φ)
    (U : Submodule F (Vector F)) : Submodule F (Vector F) :=
  { carrier := {v | ∀ hv : v ≠ 0, (φ (mk F v hv)).submodule ≤ U}
    zero_mem' := fun h => (h rfl).elim
    add_mem' := by
      intro v w hp hq hvw
      by_cases hv : v = 0
      · subst v
        simpa only [zero_add] using hq (by simpa only [zero_add] using hvw)
      by_cases hw : w = 0
      · subst w
        simpa only [add_zero] using hp (by simpa only [add_zero] using hvw)
      apply le_trans ((hφ (mk F v hv) (mk F w hw) (mk F (v + w) hvw)).mpr ?_)
        (sup_le (hp hv) (hq hw))
      simp only [submodule_mk, Submodule.span_singleton_le_iff_mem]
      exact Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self w))
    smul_mem' := by
      intro c v hp hcv
      have hv : v ≠ 0 := right_ne_zero_of_smul hcv
      have he : mk F (c • v) hcv = mk F v hv :=
        (mk_eq_mk_iff' F _ _ _ _).mpr ⟨c, rfl⟩
      simpa only [he] using hp hv }

theorem le_pullSubmodule_iff (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : PreservesLines φ) (U : Submodule F (Vector F)) (p : ProjectivePoint F) :
    p.submodule ≤ pullSubmodule φ hφ U ↔ (φ p).submodule ≤ U := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [submodule_mk, Submodule.span_singleton_le_iff_mem]
    exact ⟨fun h => h hv, fun h _ => h⟩

theorem submodule_ext_points {U W : Submodule F (Vector F)}
    (h : ∀ p : ProjectivePoint F, p.submodule ≤ U ↔ p.submodule ≤ W) : U = W := by
  ext v
  by_cases hv : v = 0
  · simp [hv]
  simpa only [submodule_mk, Submodule.span_singleton_le_iff_mem] using h (mk F v hv)

/-- The order isomorphism of all vector subspaces induced by a collineation. -/
def submoduleOrderIso (φ : Equiv.Perm (ProjectivePoint F)) (hφ : PreservesLines φ) :
    Submodule F (Vector F) ≃o Submodule F (Vector F) where
  toFun := pullSubmodule φ.symm hφ.symm
  invFun := pullSubmodule φ hφ
  left_inv U := by
    apply submodule_ext_points
    intro p
    simp only [le_pullSubmodule_iff, Equiv.symm_apply_apply]
  right_inv U := by
    apply submodule_ext_points
    intro p
    simp only [le_pullSubmodule_iff, Equiv.apply_symm_apply]
  map_rel_iff' := by
    intro U W
    constructor
    · intro h v hv
      by_cases hv0 : v = 0
      · simp [hv0]
      have hU : (φ (mk F v hv0)).submodule ≤ pullSubmodule φ.symm hφ.symm U := by
        simpa only [le_pullSubmodule_iff, Equiv.symm_apply_apply] using
          (show (mk F v hv0).submodule ≤ U by
            simpa only [submodule_mk, Submodule.span_singleton_le_iff_mem] using hv)
      have hW := (le_pullSubmodule_iff φ.symm hφ.symm W (φ (mk F v hv0))).mp (hU.trans h)
      simpa only [Equiv.symm_apply_apply, submodule_mk,
        Submodule.span_singleton_le_iff_mem] using hW
    · intro h
      exact fun v hv hv0 => (hv hv0).trans h

theorem point_submodule_le_iff (p q : ProjectivePoint F) :
    p.submodule ≤ q.submodule ↔ p = q := by
  induction p using Projectivization.ind with
  | h v hv =>
    induction q using Projectivization.ind with
    | h w hw =>
      simp only [submodule_mk, Submodule.span_singleton_le_iff_mem,
        Submodule.mem_span_singleton, mk_eq_mk_iff']

theorem submoduleOrderIso_point (φ : Equiv.Perm (ProjectivePoint F))
    (hφ : PreservesLines φ) (p : ProjectivePoint F) :
    submoduleOrderIso φ hφ p.submodule = (φ p).submodule := by
  apply submodule_ext_points
  intro q
  change q.submodule ≤ pullSubmodule φ.symm hφ.symm p.submodule ↔ _
  rw [le_pullSubmodule_iff, point_submodule_le_iff, point_submodule_le_iff]
  exact φ.symm_apply_eq

/-- The coordinate index of the actual symplectic four-space. -/
abbrev Index := Fin 2 ⊕ Fin 2

/-- A standard coordinate point. -/
def axis (i : Index) : ProjectivePoint F :=
  mk F (Pi.single i 1) (Pi.single_ne_zero_iff.mpr one_ne_zero)

@[simp] theorem axis_submodule (i : Index) :
    (axis (F := F) i).submodule = F ∙ (Pi.single i 1) := rfl

/-- The fifth point of the standard projective frame, represented by all ones. -/
def diagonalPoint : ProjectivePoint F :=
  mk F (fun _ => 1) (by intro h; exact one_ne_zero (congrFun h (.inl 0)))

/-- The point represented by `eᵢ + t eⱼ`, with its `i` coordinate normalized to one. -/
def pairPoint (i j : Index) (hij : i ≠ j) (t : F) : ProjectivePoint F :=
  mk F (Pi.single i 1 + t • Pi.single j 1) (by
    intro h
    have hi := congrFun h i
    simp [hij] at hi)

@[simp] theorem pairPoint_zero (i j : Index) (hij : i ≠ j) :
    pairPoint (F := F) i j hij 0 = axis i := by
  simp only [pairPoint, zero_smul, add_zero, axis]

theorem pairPoint_injective (i j : Index) (hij : i ≠ j) :
    Function.Injective (pairPoint (F := F) i j hij) := by
  intro s t h
  obtain ⟨c, hc⟩ := (mk_eq_mk_iff' F _ _ _ _).mp h
  have hc1 : c = 1 := by
    simpa [Pi.single_apply, hij, hij.symm] using congrFun hc i
  have hts : t = s := by
    simpa [hc1, Pi.single_apply, hij, hij.symm] using congrFun hc j
  exact hts.symm

theorem pairPoint_le_axes (i j : Index) (hij : i ≠ j) (t : F) :
    (pairPoint i j hij t).submodule ≤ (axis i).submodule ⊔ (axis j).submodule := by
  simp only [pairPoint, submodule_mk, Submodule.span_singleton_le_iff_mem,
    axis_submodule]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
    (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))

theorem fieldProjective_pairPoint (σ : F ≃+* F) (i j : Index) (hij : i ≠ j) (t : F) :
    fieldProjective σ (pairPoint i j hij t) = pairPoint i j hij (σ t) := by
  simp only [pairPoint, fieldProjective_mk]
  congr 1
  ext k
  change σ ((Pi.single i 1 + t • Pi.single j 1 : Vector F) k) = _
  simp [Pi.single_apply, apply_ite σ]

theorem iSup_axis : (⨆ i, (axis (F := F) i).submodule) = ⊤ := by
  simpa only [axis_submodule, ← Pi.basisFun_apply, ← Submodule.span_range_eq_iSup] using
    (Pi.basisFun F Index).span_eq

/-- The projective permutation induced by an invertible linear map. -/
def linearProjective (A : Vector F ≃ₗ[F] Vector F) : Equiv.Perm (ProjectivePoint F) where
  toFun := Projectivization.map A.toLinearMap A.injective
  invFun := Projectivization.map A.symm.toLinearMap A.symm.injective
  left_inv p := by
    induction p using Projectivization.ind with
    | h v hv => simp only [Projectivization.map_mk, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
  right_inv p := by
    induction p using Projectivization.ind with
    | h v hv => simp only [Projectivization.map_mk, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply]

@[simp] theorem linearProjective_apply (A : Vector F ≃ₗ[F] Vector F)
    (p : ProjectivePoint F) :
    linearProjective A p = Projectivization.map A.toLinearMap A.injective p := rfl

theorem linearProjective_submodule (A : Vector F ≃ₗ[F] Vector F) (p : ProjectivePoint F) :
    (linearProjective A p).submodule = p.submodule.map A.toLinearMap := by
  induction p using Projectivization.ind with
  | h v hv => simp [linearProjective_apply, Projectivization.map_mk, Submodule.map_span]

theorem linearProjective_preservesLines (A : Vector F ≃ₗ[F] Vector F) :
    PreservesLines (linearProjective A) := by
  intro p q r
  simp only [linearProjective_submodule, ← Submodule.map_sup,
    Submodule.map_le_map_iff_of_injective A.injective]

theorem PreservesLines.trans {φ ψ : Equiv.Perm (ProjectivePoint F)}
    (hφ : PreservesLines φ) (hψ : PreservesLines ψ) : PreservesLines (φ.trans ψ) := by
  intro p q r
  exact (hψ (φ p) (φ q) (φ r)).trans (hφ p q r)

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.Collineation
