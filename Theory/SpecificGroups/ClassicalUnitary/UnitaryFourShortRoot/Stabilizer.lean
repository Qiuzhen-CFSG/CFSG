module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot.RadicalFixed

/-!
# The actual short-root centralizer and its orthogonal radical

A determinant-one Levi matrix fixes the off-diagonal short-root parameter
exactly when all its entries lie in the fixed field. Restriction therefore
identifies the entire local centralizer, as a set, with the plane radical
times SL₂ of the fixed field. Its invariant orthogonal three-space consists
of the symmetric matrices over that fixed field and has order q³.

The short-root unipotent has its nilpotent image equal to the marked plane,
so its full special-unitary centralizer preserves that same plane. These
are the literal local inputs to Aschbacher–Smith F.4.42, printed pp.295–296.
-/

open Matrix BenderSuzuki.MatrixGroups
open Representation.OrthogonalFourMinus
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPlaneRadical UnitaryFourPlaneLocal UnitaryFourShortRoot
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

theorem short_fixed_iff (A : SpecialLinearGroup (Fin 2) F) :
    hermitianCongruence F σ hσ A (shortParameter F σ) = shortParameter F σ ↔
      ∀ i j, σ (A.val i j) = A.val i j := by
  have hd : A.val 0 0 * A.val 1 1 + A.val 0 1 * A.val 1 0 = 1 := by
    simpa only [det_fin_two, CharTwo.sub_eq_add] using A.property
  constructor
  · intro he
    have h00 := congrArg (fun X : hermitianMatrices F σ => X.val 0 0) he
    have h01 := congrArg (fun X : hermitianMatrices F σ => X.val 0 1) he
    have h10 := congrArg (fun X : hermitianMatrices F σ => X.val 1 0) he
    have h11 := congrArg (fun X : hermitianMatrices F σ => X.val 1 1) he
    simp [hermitianCongruence, shortParameter, adjoint, mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
    intro i j
    fin_cases i <;> fin_cases j
    · linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) A.val 1 0 * h00 + A.val 0 0 * h10 - σ (A.val 0 0) * hd
    · linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) A.val 1 1 * h00 + A.val 0 1 * h10 - σ (A.val 0 1) * hd
    · linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) A.val 1 0 * h01 + A.val 0 0 * h11 - σ (A.val 1 0) * hd
    · linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) A.val 1 1 * h01 + A.val 0 1 * h11 - σ (A.val 1 1) * hd
  · intro he
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hermitianCongruence, shortParameter, adjoint, mul_apply, Fin.sum_univ_two, he, mul_comm, CharTwo.add_self_eq_zero]
    · simpa only [add_comm] using hd
    · simpa only [mul_comm, add_comm] using hd

def fixedSL : Subgroup (SpecialLinearGroup (Fin 2) F) :=
  (SpecialLinearGroup.map (FixedBy.subfield F σ).subtype).range

omit [CharP F 2] in
theorem mem_fixedSL (A : SpecialLinearGroup (Fin 2) F) :
    A ∈ fixedSL F σ ↔ ∀ i j, σ (A.val i j) = A.val i j := by
  constructor
  · rintro ⟨B,rfl⟩ i j
    exact (B.val i j).property
  · intro h
    let B : Matrix (Fin 2) (Fin 2) (FixedBy.subfield F σ) := fun i j => ⟨A.val i j,h i j⟩
    have hd : B.det = 1 := by
      apply (FixedBy.subfield F σ).subtype.injective
      exact ((FixedBy.subfield F σ).subtype.map_det B).trans A.property
    exact ⟨⟨B,hd⟩, Subtype.ext rfl⟩

def fixedSLEquiv : fixedSL F σ ≃* SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ) :=
  (MonoidHom.ofInjective (f := SpecialLinearGroup.map (n := Fin 2) (FixedBy.subfield F σ).subtype) (by
    intro A B he
    apply Subtype.ext
    ext i j
    exact congrArg (fun C : SpecialLinearGroup (Fin 2) F => C.val i j) he)).symm

variable [Finite F]
def shortLocal : localFactor F (form F σ hσ) :=
  (radicalEquiv F σ hσ (Multiplicative.ofAdd (shortParameter F σ))).val

def shortCentralizer : Subgroup (localFactor F (form F σ hσ)) :=
  Subgroup.centralizer ({shortLocal F σ hσ} : Set _)

theorem mem_shortCentralizer (g : localFactor F (form F σ hσ)) :
    g ∈ shortCentralizer F σ hσ ↔ factorRestriction F (form F σ hσ) g ∈ fixedSL F σ := by
  rw [mem_fixedSL, ← short_fixed_iff F σ hσ]
  rw [shortCentralizer, Subgroup.mem_centralizer_singleton_iff]
  have hc := unipotentSU_conj F σ hσ g (shortParameter F σ)
  constructor
  · intro he
    apply Subtype.ext
    apply unipotentMatrix_injective F
    have h : g.val * unipotentSU F σ hσ (shortParameter F σ) * g.val⁻¹ =
        unipotentSU F σ hσ (shortParameter F σ) := by
      have h' := congrArg Subtype.val he
      exact (congrArg (fun x => x * g.val⁻¹) h').trans (by simp; rfl)
    exact congrArg (fun x : SU F (form F σ hσ) => x.val.val) (hc.symm.trans h)
  · intro he
    have h : g * shortLocal F σ hσ * g⁻¹ = shortLocal F σ hσ := by
      apply Subtype.ext
      exact hc.trans (congrArg (unipotentSU F σ hσ) he)
    exact (mul_inv_eq_iff_eq_mul.mp h)


/-- Coordinates on the complete short-root centralizer. -/
def shortCentralizerEquiv : shortCentralizer F σ hσ ≃
    radical F σ hσ × fixedSL F σ where
  toFun g := (⟨g.val * levi F σ hσ (factorRestriction F (form F σ hσ) g.val)⁻¹, by
    change factorRestriction F (form F σ hσ) _ = 1
    simp only [map_mul, map_inv, factorRestriction_levi, mul_inv_cancel]⟩,
    ⟨factorRestriction F (form F σ hσ) g.val,
      (mem_shortCentralizer F σ hσ g.val).mp g.property⟩)
  invFun p := ⟨p.1.val * levi F σ hσ p.2.val, by
    apply (mem_shortCentralizer F σ hσ _).mpr
    have hp : factorRestriction F (form F σ hσ) p.1.val = 1 := p.1.property
    simpa only [map_mul, hp, factorRestriction_levi, one_mul] using p.2.property⟩
  left_inv g := by apply Subtype.ext; simp
  right_inv p := by
    have hp : factorRestriction F (form F σ hσ) p.1.val = 1 := p.1.property
    apply Prod.ext
    · apply Subtype.ext
      simp only [map_mul, hp, factorRestriction_levi, one_mul, map_inv, mul_inv_cancel_right]
    · apply Subtype.ext
      simp only [map_mul, hp, factorRestriction_levi, one_mul]

theorem shortCentralizer_card :
    Nat.card (shortCentralizer F σ hσ) =
      Nat.card (radical F σ hσ) * Nat.card (SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ)) := by
  rw [Nat.card_congr (shortCentralizerEquiv F σ hσ), Nat.card_prod,
    Nat.card_congr (fixedSLEquiv F σ).toEquiv]

omit [Finite F] [CharP F 2] in
def fixedHermitian : AddSubgroup (hermitianMatrices F σ) where
  carrier := {X | ∀ i j, σ (X.val i j) = X.val i j}
  zero_mem' := by intro i j; exact map_zero σ
  add_mem' := by intro X Y hX hY i j; exact (map_add σ _ _).trans (congrArg₂ (· + ·) (hX i j) (hY i j))
  neg_mem' := by intro X hX i j; exact (map_neg σ _).trans (congrArg Neg.neg (hX i j))

omit [Finite F] [CharP F 2] in
def fixedHermitianEquiv : fixedHermitian F σ ≃
    FixedBy.subfield F σ × FixedBy.subfield F σ × FixedBy.subfield F σ where
  toFun X := (⟨X.val.val 0 0,X.property 0 0⟩,⟨X.val.val 0 1,X.property 0 1⟩,⟨X.val.val 1 1,X.property 1 1⟩)
  invFun p := ⟨⟨!![p.1.val,p.2.1.val;p.2.1.val,p.2.2.val], by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [adjoint] <;> first | exact p.1.property | exact p.2.1.property | exact p.2.2.property⟩, by
    intro i j
    fin_cases i <;> fin_cases j <;> first | exact p.1.property | exact p.2.1.property | exact p.2.2.property⟩
  left_inv X := by
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · rfl
    · rfl
    · exact (X.property 0 1).symm.trans (congrFun (congrFun X.val.property 1) 0)
    · rfl
  right_inv p := by rfl

omit [Finite F] [CharP F 2] in
theorem fixedHermitian_card :
    Nat.card (fixedHermitian F σ) = Nat.card (FixedBy.subfield F σ) ^ 3 := by
  rw [Nat.card_congr (fixedHermitianEquiv F σ), Nat.card_prod, Nat.card_prod]
  ring

omit [Finite F] [CharP F 2] in
theorem fixedHermitian_congruence
    (A : SpecialLinearGroup (Fin 2) F) (hA : A ∈ fixedSL F σ)
    (X : hermitianMatrices F σ) (hX : X ∈ fixedHermitian F σ) :
    hermitianCongruence F σ hσ A X ∈ fixedHermitian F σ := by
  have ha := (mem_fixedSL F σ A).mp hA
  have hx : ∀ i j, σ (X.val i j) = X.val i j := hX
  intro i j
  simp [hermitianCongruence, adjoint, mul_apply, ha, hx]



/-- The orthogonal three-space in the actual plane radical. -/
def orthogonalRadical : Subgroup (localFactor F (form F σ hσ)) :=
  (fixedHermitian F σ).toSubgroup.map
    ((radical F σ hσ).subtype.comp (radicalEquiv F σ hσ).toMonoidHom)

theorem orthogonalRadical_le_radical : orthogonalRadical F σ hσ ≤ radical F σ hσ := by
  rintro x ⟨X,hX,rfl⟩
  exact (radicalEquiv F σ hσ X).property

theorem radical_le_shortCentralizer : radical F σ hσ ≤ shortCentralizer F σ hσ := by
  intro g hg
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val
    (radical_mul_comm F σ hσ ⟨g,hg⟩ (radicalEquiv F σ hσ (Multiplicative.ofAdd (shortParameter F σ))))

theorem orthogonalRadical_le_shortCentralizer :
    orthogonalRadical F σ hσ ≤ shortCentralizer F σ hσ :=
  (orthogonalRadical_le_radical F σ hσ).trans (radical_le_shortCentralizer F σ hσ)

theorem orthogonalRadical_card :
    Nat.card (orthogonalRadical F σ hσ) = Nat.card (FixedBy.subfield F σ) ^ 3 := by
  have hf : Function.Injective ((radical F σ hσ).subtype.comp
      (radicalEquiv F σ hσ).toMonoidHom) :=
    (radical F σ hσ).subtype_injective.comp (radicalEquiv F σ hσ).injective
  exact (Subgroup.card_map_of_injective hf).trans (fixedHermitian_card F σ)


instance orthogonalRadical_normal :
    ((orthogonalRadical F σ hσ).subgroupOf (shortCentralizer F σ hσ)).Normal := by
  constructor
  rintro x hx g
  obtain ⟨X,hX,he⟩ := hx
  change (radicalEquiv F σ hσ X).val = x.val at he
  let Y := hermitianCongruence F σ hσ
    (factorRestriction F (form F σ hσ) g.val) X.toAdd
  have hY : Y ∈ fixedHermitian F σ := fixedHermitian_congruence F σ hσ _
    ((mem_shortCentralizer F σ hσ g.val).mp g.property) _ hX
  refine ⟨Multiplicative.ofAdd Y,hY,?_⟩
  change (radicalEquiv F σ hσ (Multiplicative.ofAdd Y)).val = g.val * x.val * g.val⁻¹
  rw [← he]
  exact (congrArg Subtype.val (radicalEquiv_conj F σ hσ g.val X)).symm



/-- The image of the marked short-root nilpotent matrix is the marked plane,
so every commuting special-unitary matrix preserves that plane. -/
theorem centralizer_short_le_plane :
    Subgroup.centralizer ({unipotentSU F σ hσ (shortParameter F σ)} : Set (SU F (form F σ hσ))) ≤
      planeParabolicSU F (form F σ hσ) := by
  intro g hg
  have he := congrArg (fun a : SU F (form F σ hσ) => a.val.val)
    (Subgroup.mem_centralizer_singleton_iff.mp hg)
  change g.val.val * unipotentMatrix F (shortParameter F σ).val =
    unipotentMatrix F (shortParameter F σ).val * g.val.val at he
  have h20 := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 2 2) he
  have h30 := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 3 2) he
  have h21 := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 2 3) he
  have h31 := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 3 3) he
  simp [unipotentMatrix, shortParameter, mul_apply, Fin.sum_univ_succ] at h20 h30 h21 h31
  rw [mem_planeParabolicSU]
  exact ⟨h20,h30,h21,h31⟩

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourShortRoot
