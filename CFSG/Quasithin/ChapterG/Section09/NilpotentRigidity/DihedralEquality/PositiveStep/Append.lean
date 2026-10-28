module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.BlockContracts
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.Transport
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.SpaceTransport
public import Mathlib.LinearAlgebra.Projection

/-!
# Appending the retained block in the equality induction

The complementary index sets give an actual product equivalence from the
fixed-space actors and the retained subgroup to the original dihedral product.
Each already classified factor embeds through the fixed subproduct, and its
displacement space embeds through the inclusion of the rotation-fixed space.
Pointwise fixation of the complement identifies this with its ambient
displacement space. The complementary-space equivalence then appends the
retained displacement summand.

The new count is the smaller classification's count plus one: any orthogonal
pairs already formed by induction remain intact. Appending at the last index
preserves the exceptional first factor and its dimension. Both equivalences
are checked on every canonical single-coordinate inclusion.

Source: Aschbacher--Smith, G.9.2, printed p.353 (combined manuscript, 1 March 2004).
-/

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.Append

universe u v
variable {G : Type u} [Group G] {n : ℕ}

/-- Append the retained subgroup at the last index. -/
def family (F : Fin n → Subgroup G) (K : Subgroup G) : Fin (n + 1) → Subgroup G :=
  @Fin.snoc n (fun _ => Subgroup G) F K

@[simp] theorem family_castSucc (F : Fin n → Subgroup G) (K : Subgroup G) (j : Fin n) :
    family F K j.castSucc = F j := Fin.snoc_castSucc _ _ _

@[simp] theorem family_last (F : Fin n → Subgroup G) (K : Subgroup G) :
    family F K (Fin.last n) = K := Fin.snoc_last _ _

noncomputable def groupCoordinates (F : Fin n → Subgroup G) (K : Subgroup G) :
    (∀ j, family F K j) ≃* (∀ j, F j) × K where
  toFun g := (fun j => ⟨g j.castSucc, by simpa using (g j.castSucc).property⟩,
    ⟨g (Fin.last n), by simpa using (g (Fin.last n)).property⟩)
  invFun g j := ⟨Fin.snoc (α := fun _ => G) (fun k => (g.1 k : G)) (g.2 : G) j, by
    cases j using Fin.lastCases <;> simp⟩
  left_inv g := by ext j; cases j using Fin.lastCases <;> simp
  right_inv g := by ext <;> simp
  map_mul' g h := rfl

theorem groupCoordinates_castSucc (F : Fin n → Subgroup G) (K : Subgroup G)
    (j : Fin n) (g : family F K j.castSucc) :
    groupCoordinates F K (Pi.mulSingle j.castSucc g) =
      (Pi.mulSingle j ⟨g, by simpa using g.property⟩, 1) := by
  apply Prod.ext
  · ext k
    by_cases h : k = j
    · subst k; simp [groupCoordinates]
    · simp [groupCoordinates, Pi.mulSingle_eq_of_ne h,
        Pi.mulSingle_eq_of_ne ((Fin.castSucc_injective n).ne h)]
  · apply Subtype.ext
    simp [groupCoordinates]

theorem groupCoordinates_last (F : Fin n → Subgroup G) (K : Subgroup G)
    (g : family F K (Fin.last n)) :
    groupCoordinates F K (Pi.mulSingle (Fin.last n) g) =
      (1, ⟨g, by simpa using g.property⟩) := by
  apply Prod.ext
  · ext j
    simp [groupCoordinates]
  · apply Subtype.ext
    simp [groupCoordinates]

variable {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

noncomputable def spaceCoordinates (σ : Representation (ZMod 2) G W)
    (F : Fin n → Subgroup G) (K : Subgroup G) :
    (∀ j, movedSpace σ (family F K j)) ≃ₗ[ZMod 2]
      (∀ j, movedSpace σ (F j)) × movedSpace σ K where
  toFun g := (fun j => ⟨g j.castSucc, by simpa using (g j.castSucc).property⟩,
    ⟨g (Fin.last n), by simpa using (g (Fin.last n)).property⟩)
  invFun g j := ⟨Fin.snoc (α := fun _ => W) (fun k => (g.1 k : W)) (g.2 : W) j, by
    cases j using Fin.lastCases <;> simp⟩
  left_inv g := by ext j; cases j using Fin.lastCases <;> simp
  right_inv g := by ext <;> simp
  map_add' g h := rfl
  map_smul' a g := rfl

theorem spaceCoordinates_castSucc (σ : Representation (ZMod 2) G W)
    (F : Fin n → Subgroup G) (K : Subgroup G)
    (j : Fin n) (g : movedSpace σ (family F K j.castSucc)) :
    spaceCoordinates σ F K (Pi.single j.castSucc g) =
      (Pi.single j ⟨g, by simpa using g.property⟩, 0) := by
  apply Prod.ext
  · ext k
    by_cases h : k = j
    · subst k; simp [spaceCoordinates]
    · simp [spaceCoordinates, Pi.single_eq_of_ne h,
        Pi.single_eq_of_ne ((Fin.castSucc_injective n).ne h)]
  · apply Subtype.ext
    simp [spaceCoordinates]

theorem spaceCoordinates_last (σ : Representation (ZMod 2) G W)
    (F : Fin n → Subgroup G) (K : Subgroup G)
    (g : movedSpace σ (family F K (Fin.last n))) :
    spaceCoordinates σ F K (Pi.single (Fin.last n) g) =
      (0, ⟨g, by simpa using g.property⟩) := by
  apply Prod.ext
  · ext j
    simp [spaceCoordinates]
  · apply Subtype.ext
    simp [spaceCoordinates]

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.Append

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.Append

open DihedralDegree
variable {ι : Type} [DecidableEq ι] {p : ι → ℕ}

theorem subproduct_injective (I : Finset ι) :
    Function.Injective (subproductHom (p := p) I) := by
  intro g h he
  funext j
  simpa [subproductHom, j.property] using congrFun he j.val

noncomputable def partitionEquiv (I R : Finset ι)
    (hR : ∀ j, j ∈ R ↔ j ∉ I) :
    ((∀ j : I, DihedralGroup (p j)) × (∀ j : R, DihedralGroup (p j))) ≃*
      (∀ j, DihedralGroup (p j)) where
  toFun g := subproductHom I g.1 * subproductHom R g.2
  invFun g := (fun j => g j, fun j => g j)
  left_inv g := by
    apply Prod.ext
    · funext j
      have hjR : j.val ∉ R := by simp [hR, j.property]
      simp [subproductHom, j.property, hjR]
    · funext j
      have hjI : j.val ∉ I := (hR _).mp j.property
      simp [subproductHom, j.property, hjI]
  right_inv g := by
    funext j
    by_cases hj : j ∈ I
    · have hjR : j ∉ R := by simpa [hR] using hj
      simp [subproductHom, hj, hjR]
    · have hjR : j ∈ R := (hR _).mpr hj
      simp [subproductHom, hj, hjR]
  map_mul' g h := by
    funext j
    by_cases hj : j ∈ I
    · have hjR : j ∉ R := by simpa [hR] using hj
      simp [subproductHom, hj, hjR]
    · have hjR : j ∈ R := (hR _).mpr hj
      simp [subproductHom, hj, hjR]

noncomputable def retainedEquiv (I R : Finset ι)
    (hR : ∀ j, j ∈ R ↔ j ∉ I) :
    ((∀ j : I, DihedralGroup (p j)) × (subproductHom (p := p) R).range) ≃*
      (∀ j, DihedralGroup (p j)) :=
  (MulEquiv.prodCongr (MulEquiv.refl _)
    (MonoidHom.ofInjective (subproduct_injective R)).symm).trans (partitionEquiv I R hR)

theorem retainedEquiv_apply (I R : Finset ι)
    (hR : ∀ j, j ∈ R ↔ j ∉ I)
    (g : (∀ j : I, DihedralGroup (p j)) × (subproductHom (p := p) R).range) :
    retainedEquiv I R hR g = subproductHom I g.1 * g.2 := by
  change subproductHom I g.1 *
    subproductHom R ((MonoidHom.ofInjective (subproduct_injective R)).symm g.2) = _
  congr 1
  exact congrArg Subtype.val
    ((MonoidHom.ofInjective (subproduct_injective R)).apply_symm_apply g.2)

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.Append

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep

open DihedralDegree
open CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep.Append
universe v

/-- Glue the smaller classified action and the retained ordinary block along
both genuine internal decompositions. Existing factors keep their indices. -/
public noncomputable def appendClassified
    {ι : Type} [Fintype ι] [DecidableEq ι] {p : ι → ℕ}
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) (∀ j, DihedralGroup (p j)) W}
    {i : ι} {exceptional : Prop} (s : PreparedSplit σ i exceptional)
    (hc : IsCompl (rotationFixed (factorRep σ i)) (rotationMoved (factorRep σ i)))
    (b : CompletedBlock s) : ClassifiedDecomposition σ ⊤ exceptional := by
  classical
  let I := s.fixedIndices
  let R := s.retainedIndices
  let K := s.retainedGroup
  let C := rotationFixed (factorRep σ i)
  let M := rotationMoved (factorRep σ i)
  let f := subproductHom (p := p) I
  have hf : Function.Injective f := subproduct_injective I
  have hpart : ∀ j, j ∈ R ↔ j ∉ I := by
    intro j
    simp only [R, I, PreparedSplit.retainedIndices, PreparedSplit.fixedIndices,
      Finset.mem_insert, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true]
    tauto
  let τ := Representation.subrepresentation (σ.comp f) C s.actions.fixed_stable
  let d : ClassifiedDecomposition τ ⊤ exceptional := s.fixed_classification
  let F : Fin d.count → Subgroup (∀ j, DihedralGroup (p j)) :=
    fun j => (d.internal.factor j).map f
  let eg (j : Fin d.count) := (d.internal.factor j).equivMapOfInjective f hf
  let oldGroup : (∀ j, F j) ≃* (∀ j : I, DihedralGroup (p j)) :=
    (MulEquiv.piCongrRight fun j => (eg j).symm).trans
      (d.internal.groupEquiv.trans Subgroup.topEquiv)
  have oldGroup_single (j : Fin d.count) (g : F j) :
      f (oldGroup (Pi.mulSingle j g)) = (g : ∀ j, DihedralGroup (p j)) := by
    have hs : (MulEquiv.piCongrRight fun k => (eg k).symm) (Pi.mulSingle j g) =
        Pi.mulSingle j ((eg j).symm g) := by
      ext k
      by_cases hk : k = j
      · subst k; simp
      · simp [MulEquiv.piCongrRight, Pi.mulSingle_eq_of_ne hk]
    change f (d.internal.groupEquiv
      ((MulEquiv.piCongrRight fun k => (eg k).symm) (Pi.mulSingle j g))) = _
    rw [hs, d.internal.group_inclusion]
    exact congrArg Subtype.val ((eg j).apply_symm_apply g)
  let ev (j : Fin d.count) : movedSpace σ (F j) ≃ₗ[ZMod 2]
      movedSpace τ (d.internal.factor j) :=
    (LinearEquiv.ofEq _ _ (movedSpace_map σ f (d.internal.factor j))).trans
      (movedSpace_subrepresentation_equiv (σ.comp f) s.actions.fixed_stable
        hc.sup_eq_top (d.internal.factor j) (fun g => b.fixed_complement g)).symm
  have ev_val (j : Fin d.count) (v : movedSpace σ (F j)) :
      ((ev j v : C) : W) = v := by
    exact movedSpace_subrepresentation_equiv_symm_apply (σ.comp f)
      s.actions.fixed_stable hc.sup_eq_top (d.internal.factor j)
      (fun g => b.fixed_complement g)
      ((LinearEquiv.ofEq _ _ (movedSpace_map σ f (d.internal.factor j))) v)
  let oldSpace : (∀ j, movedSpace σ (F j)) ≃ₗ[ZMod 2] C :=
    (LinearEquiv.piCongrRight ev).trans d.internal.spaceEquiv
  have oldSpace_single (j : Fin d.count) (v : movedSpace σ (F j)) :
      (oldSpace (Pi.single j v) : W) = v := by
    have hs : (LinearEquiv.piCongrRight ev) (Pi.single j v) =
        Pi.single j (ev j v) := by
      ext k
      by_cases hk : k = j
      · subst k; simp
      · simp [LinearEquiv.piCongrRight_apply, Pi.single_eq_of_ne hk]
    change (d.internal.spaceEquiv ((LinearEquiv.piCongrRight ev) (Pi.single j v)) : W) = _
    rw [hs, d.internal.space_inclusion]
    exact ev_val j v
  let eM : movedSpace σ K ≃ₗ[ZMod 2] M := LinearEquiv.ofEq _ _ b.retained_moved
  let wholeGroup : ((∀ j, F j) × K) ≃* (∀ j, DihedralGroup (p j)) :=
    (oldGroup.prodCongr (MulEquiv.refl K)).trans (retainedEquiv I R hpart)
  let wholeSpace : ((∀ j, movedSpace σ (F j)) × movedSpace σ K) ≃ₗ[ZMod 2] W :=
    (oldSpace.prodCongr eM).trans (Submodule.prodEquivOfIsCompl C M hc)
  let D : InternalDecomposition σ ⊤ (d.count + 1) :=
    { factor := family F K
      groupEquiv := (groupCoordinates F K).trans (wholeGroup.trans Subgroup.topEquiv.symm)
      group_inclusion := by
        intro j g
        change wholeGroup (groupCoordinates F K (Pi.mulSingle j g)) = _
        cases j using Fin.lastCases with
        | last =>
          rw [groupCoordinates_last]
          change retainedEquiv I R hpart (oldGroup 1, _) = _
          rw [retainedEquiv_apply]
          simp
        | cast j =>
          rw [groupCoordinates_castSucc]
          change retainedEquiv I R hpart (oldGroup (Pi.mulSingle j _), 1) = _
          rw [retainedEquiv_apply]
          simpa using oldGroup_single j ⟨g, by simpa using g.property⟩
      spaceEquiv := (spaceCoordinates σ F K).trans wholeSpace
      space_inclusion := by
        intro j v
        change wholeSpace (spaceCoordinates σ F K (Pi.single j v)) = _
        cases j using Fin.lastCases with
        | last =>
          rw [spaceCoordinates_last]
          change (oldSpace 0 : W) + (v : W) = _
          simp
        | cast j =>
          rw [spaceCoordinates_castSucc]
          change (oldSpace (Pi.single j _) : W) + (eM 0 : W) = _
          simpa using oldSpace_single j ⟨v, by simpa using v.property⟩ }
  refine
    { count := d.count + 1
      internal := D
      exceptional_factor := ?_
      ordinary_factor := ?_ }
  · intro he
    obtain ⟨hpos, ⟨e⟩, hd⟩ := d.exceptional_factor he
    refine ⟨by omega, ?_⟩
    have hzero : (⟨0, by omega⟩ : Fin (d.count + 1)) = (⟨0, hpos⟩ : Fin d.count).castSucc := rfl
    change Nonempty (family F K ⟨0, _⟩ ≃* DihedralGroup 5) ∧
      Module.finrank (ZMod 2) (movedSpace σ (family F K ⟨0, _⟩)) = 4
    rw [hzero, family_castSucc]
    exact ⟨⟨(eg ⟨0, hpos⟩).symm.trans e⟩, (ev ⟨0, hpos⟩).finrank_eq.trans hd⟩
  · intro j hj
    change IsOrdinaryFactor σ (family F K j)
    cases j using Fin.lastCases with
    | last => simpa using b.ordinary
    | cast j =>
      rw [family_castSucc]
      exact isOrdinaryFactor_map σ f hf _
        (isOrdinaryFactor_of_subrepresentation (σ.comp f) s.actions.fixed_stable
          hc.sup_eq_top (d.internal.factor j) (fun g => b.fixed_complement g)
          (d.ordinary_factor j hj))

/-- The unconditional append contract. The retained block is the explicit
input required by the contract; no further classification premise is used. -/
public theorem appendClassifiedTheorem : AppendClassifiedTheorem.{v} := by
  intro ι _ _ p W _ _ _ σ i exceptional s hc b
  exact ⟨appendClassified s hc b⟩

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep

open DihedralDegree
universe v
variable {ι : Type} [Fintype ι] [DecidableEq ι] {p : ι → ℕ}
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) (∀ j, DihedralGroup (p j)) W}
  {i : ι} {exceptional : Prop} (s : PreparedSplit σ i exceptional)
  (hc : IsCompl (rotationFixed (factorRep σ i)) (rotationMoved (factorRep σ i)))
  (b : CompletedBlock s)

@[simp] public theorem appendClassified_count :
    (appendClassified s hc b).count = s.fixed_classification.count + 1 := by
  rfl

@[simp] public theorem appendClassified_factor_castSucc (j : Fin s.fixed_classification.count) :
    (appendClassified s hc b).internal.factor
      (Fin.cast (appendClassified_count s hc b).symm j.castSucc) =
      (s.fixed_classification.internal.factor j).map (subproductHom s.fixedIndices) :=
  by
    change Append.family
      (fun k => (s.fixed_classification.internal.factor k).map (subproductHom s.fixedIndices))
      s.retainedGroup j.castSucc = _
    exact Append.family_castSucc _ _ _

@[simp] public theorem appendClassified_factor_last :
    (appendClassified s hc b).internal.factor
      (Fin.cast (appendClassified_count s hc b).symm (Fin.last s.fixed_classification.count)) =
      s.retainedGroup := by
    change Append.family
      (fun k => (s.fixed_classification.internal.factor k).map (subproductHom s.fixedIndices))
      s.retainedGroup (Fin.last s.fixed_classification.count) = _
    exact Append.family_last _ _

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality.PositiveStep
