module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Recognition.Twenty.CharacterCalculation.ExtensionRigidity.Injectivity.RealizationInputs
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.CubicCalculation.FieldTransport

/-!
# Transport of marked Bruhat reference models between matrix fields

A conjugation-compatible field equivalence transports standard SU₃ matrices
entrywise. The induced multiplicative equivalence of unipotent coordinates
preserves their centers, the embedded root center, and both literal Bruhat
actors. The second-coordinate-zero branch is preserved as well.

Pulling back a reference representation therefore keeps its coefficient field
and basis, pulls back its two marked points and center enumeration, and
preserves both center conditions. Uniqueness of the finite field of order 25
then transports an explicitly supplied polynomial-field model to every matrix
field in the original contract. Existence of that supplied model remains the
independent `TableBruhatModels` premise.

Source: the root multiplication and Bruhat formulas of Huppert II.10.12,
proved in `BenderSuzuki.External.Huppert.II.theorem_10_12` and used by
`ExtensionRigidity.Averaging`. The two-coset conventions are recorded in
`Injectivity/source/README.md`. The consumer is
`twenty_rootCoset_injectivity_of_reference_models` in the assembly module;
no extension-rigidity assembly is imported here.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups BenderSuzuki.External Matrix Subgroup
open HermitianForm.OddPrimeSylow.NormalizedOuter HermitianForm.BorelTorus
namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.ReferenceFieldTransport
open Degrees.RootEigenline Degrees.CubicCalculation
noncomputable section
variable {F E : Type*} [Field F] [Field E]
variable (J : HermitianForm 3 F) (L : HermitianForm 3 E)
variable (e : F ≃+* E) (hc : ∀ x, e (J.conj x) = L.conj (e x))

include hc in
private theorem inverse_conj (x : E) : e.symm (L.conj x) = J.conj (e.symm x) := by
  apply e.injective
  simpa only [e.apply_symm_apply] using (hc (e.symm x)).symm

/-- Entrywise transport of the actual unipotent coordinates. -/
def rootEquiv : hermitianUnipotentCoord (FormTransport.standardForm J) ≃*
    hermitianUnipotentCoord (FormTransport.standardForm L) where
  toFun z := ⟨(e z.val.1, e z.val.2), by
    change e z.val.2 + L.conj (e z.val.2) + e z.val.1 * L.conj (e z.val.1) = 0
    rw [← hc, ← hc, ← map_mul, ← map_add, ← map_add, ← map_zero e]
    exact congrArg e z.property⟩
  invFun z := ⟨(e.symm z.val.1, e.symm z.val.2), by
    change e.symm z.val.2 + J.conj (e.symm z.val.2) +
      e.symm z.val.1 * J.conj (e.symm z.val.1) = 0
    rw [← inverse_conj J L e hc, ← inverse_conj J L e hc,
      ← map_mul, ← map_add, ← map_add, ← map_zero e.symm]
    exact congrArg e.symm z.property⟩
  left_inv z := by apply Subtype.ext; simp
  right_inv z := by apply Subtype.ext; simp
  map_mul' z w := by
    apply Subtype.ext
    change (e (z.val.1 + w.val.1),
      e (z.val.2 + w.val.2 - z.val.1 * J.conj w.val.1)) =
      (e z.val.1 + e w.val.1, e z.val.2 + e w.val.2 - e z.val.1 * L.conj (e w.val.1))
    simp only [map_add, map_sub, map_mul, hc]

@[simp] theorem rootEquiv_fst (z : hermitianUnipotentCoord (FormTransport.standardForm J)) :
    (rootEquiv J L e hc z).val.1 = e z.val.1 := rfl
@[simp] theorem rootEquiv_snd (z : hermitianUnipotentCoord (FormTransport.standardForm J)) :
    (rootEquiv J L e hc z).val.2 = e z.val.2 := rfl
@[simp] theorem rootEquiv_snd_eq_zero (z : hermitianUnipotentCoord (FormTransport.standardForm J)) :
    (rootEquiv J L e hc z).val.2 = 0 ↔ z.val.2 = 0 := by
  simp only [rootEquiv_snd, map_eq_zero]

theorem standardFieldEquiv_root (z : hermitianUnipotentCoord (FormTransport.standardForm J)) :
    standardFieldEquiv J L e hc (hermitianUnipotentSU _ rfl z) =
      hermitianUnipotentSU _ rfl (rootEquiv J L e hc z) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [standardFieldEquiv_entry]
  change e ((hermitianUnipotentMatrix _ z) i j) =
    (hermitianUnipotentMatrix _ (rootEquiv J L e hc z)) i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianUnipotentMatrix, FormTransport.standardForm_conj, hc]

theorem standardFieldEquiv_torus (k : Fˣ) :
    standardFieldEquiv J L e hc (hermitianTorusSU _ rfl k) =
      hermitianTorusSU _ rfl (Units.map e.toMonoidHom k) := by
  apply Subtype.ext
  apply Units.ext
  ext i j
  rw [standardFieldEquiv_entry]
  change e ((hermitianTorusMatrix _ k) i j) =
    (hermitianTorusMatrix _ (Units.map e.toMonoidHom k)) i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusMatrix, FormTransport.standardForm_conj, hc]

theorem rootEquiv_bruhatLeft (z : hermitianUnipotentCoord (FormTransport.standardForm J))
    (hz : z.val.2 ≠ 0) :
    rootEquiv J L e hc (hermitianBruhatLeft _ z hz) =
      hermitianBruhatLeft _ (rootEquiv J L e hc z)
        (fun h => hz ((rootEquiv_snd_eq_zero J L e hc z).mp h)) := by
  apply Subtype.ext
  apply Prod.ext <;> simp [rootEquiv, hermitianBruhatLeft, FormTransport.standardForm_conj, hc]

theorem rootEquiv_bruhatRight (z : hermitianUnipotentCoord (FormTransport.standardForm J))
    (hz : z.val.2 ≠ 0) :
    rootEquiv J L e hc (hermitianBruhatRight _ z hz) =
      hermitianBruhatRight _ (rootEquiv J L e hc z)
        (fun h => hz ((rootEquiv_snd_eq_zero J L e hc z).mp h)) := by
  apply Subtype.ext
  apply Prod.ext <;> simp [rootEquiv, hermitianBruhatRight]

/-- Coordinate transport restricts to the actual coordinate centers. -/
def centerEquiv := Subgroup.centerCongr (rootEquiv J L e hc)

private def coordRootEquiv (J : HermitianForm 3 F) :
    hermitianUnipotentCoord (FormTransport.standardForm J) ≃* standardRoot J :=
  MulEquiv.ofBijective (hermitianUnipotentSU _ rfl).rangeRestrict
    ⟨by
      intro z t h
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun x : standardRoot J => x.val.val.val 0 1) h
      · exact congrArg (fun x : standardRoot J => x.val.val.val 0 2) h,
      (hermitianUnipotentSU _ rfl).rangeRestrict_surjective⟩

private theorem rootCenter_mem_iff (g : standardGroup J) :
    g ∈ standardRootCenter J ↔
      ∃ c : Subgroup.center (hermitianUnipotentCoord (FormTransport.standardForm J)),
        hermitianUnipotentSU _ rfl c.val = g := by
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨c, h⟩ := (Subgroup.centerCongr (coordRootEquiv J)).surjective ⟨r, hr⟩
    exact ⟨c, congrArg (fun t : Subgroup.center (standardRoot J) => t.val.val) h⟩
  · rintro ⟨c, rfl⟩
    exact ⟨coordRootEquiv J c.val, (Subgroup.centerCongr (coordRootEquiv J) c).property, rfl⟩

/-- The entrywise SU equivalence preserves the embedded center of the root subgroup. -/
theorem standardFieldEquiv_rootCenter_iff (g : standardGroup J) :
    standardFieldEquiv J L e hc g ∈ standardRootCenter L ↔ g ∈ standardRootCenter J := by
  rw [rootCenter_mem_iff, rootCenter_mem_iff]
  constructor
  · rintro ⟨d, hd⟩
    obtain ⟨c, rfl⟩ := (centerEquiv J L e hc).surjective d
    refine ⟨c, (standardFieldEquiv J L e hc).injective ?_⟩
    rw [standardFieldEquiv_root]
    exact hd
  · rintro ⟨c, rfl⟩
    exact ⟨centerEquiv J L e hc c, (standardFieldEquiv_root J L e hc c.val).symm⟩


variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem leftCoefficient_comp (τ : Representation K (standardGroup L) V)
    (z : hermitianUnipotentCoord (FormTransport.standardForm J)) :
    leftCoefficient (FormTransport.standardForm J) rfl
        (τ.comp (standardFieldEquiv J L e hc).toMonoidHom) z =
      leftCoefficient (FormTransport.standardForm L) rfl τ (rootEquiv J L e hc z) := by
  classical
  unfold leftCoefficient
  by_cases hz : z.val.2 = 0
  · rw [dif_pos hz, dif_pos ((rootEquiv_snd_eq_zero J L e hc z).mpr hz)]
  · have hz' : (rootEquiv J L e hc z).val.2 ≠ 0 :=
      fun h => hz ((rootEquiv_snd_eq_zero J L e hc z).mp h)
    rw [dif_neg hz, dif_neg hz']
    change τ (standardFieldEquiv J L e hc (_ * _)) = _
    rw [map_mul, standardFieldEquiv_root, standardFieldEquiv_torus, rootEquiv_bruhatLeft]
    have hu : Units.map e.toMonoidHom (Units.mk0 z.val.2 hz) =
        Units.mk0 (rootEquiv J L e hc z).val.2 hz' := Units.ext rfl
    rw [hu]

theorem rightCoefficient_comp (τ : Representation K (standardGroup L) V)
    (z : hermitianUnipotentCoord (FormTransport.standardForm J)) :
    rightCoefficient (FormTransport.standardForm J) rfl
        (τ.comp (standardFieldEquiv J L e hc).toMonoidHom) z =
      rightCoefficient (FormTransport.standardForm L) rfl τ (rootEquiv J L e hc z) := by
  classical
  unfold rightCoefficient
  by_cases hz : z.val.2 = 0
  · rw [dif_pos hz, dif_pos ((rootEquiv_snd_eq_zero J L e hc z).mpr hz)]
  · have hz' : (rootEquiv J L e hc z).val.2 ≠ 0 :=
      fun h => hz ((rootEquiv_snd_eq_zero J L e hc z).mp h)
    rw [dif_neg hz, dif_neg hz']
    change τ (standardFieldEquiv J L e hc _) = _
    rw [standardFieldEquiv_root, rootEquiv_bruhatRight]

/-- Pull back the two points and the center enumeration, keeping the basis. -/
def coordinates (τ : Representation K (standardGroup L) V)
    (C : Coordinates (FormTransport.standardForm L) rfl τ) :
    Coordinates (FormTransport.standardForm J) rfl
      (τ.comp (standardFieldEquiv J L e hc).toMonoidHom) where
  basis := C.basis
  point s := (rootEquiv J L e hc).symm (C.point s)
  centerEquiv := (centerEquiv J L e hc).toEquiv.trans C.centerEquiv
  left_eq s c := by
    rw [leftCoefficient_comp, map_mul, MulEquiv.apply_symm_apply]
    exact C.left_eq s (centerEquiv J L e hc c)
  right_eq s c := by
    rw [rightCoefficient_comp, map_mul, MulEquiv.apply_symm_apply]
    exact C.right_eq s (centerEquiv J L e hc c)

end
noncomputable section
variable {F E : Type} [Field F] [Field E]
variable (J : HermitianForm 3 F) (L : HermitianForm 3 E)
variable (e : F ≃+* E) (hc : ∀ x, e (J.conj x) = L.conj (e x))
variable {K : Type*} [Field K]

/-- Pullback preserves the actual SU center and the embedded root-center invariants. -/
def model (M : ReferenceModel L K) : ReferenceModel J K where
  representation := M.representation.comp (standardFieldEquiv J L e hc).toMonoidHom
  center_le_ker := by
    intro g hg
    exact M.center_le_ker (Subgroup.centerCongr (standardFieldEquiv J L e hc) ⟨g, hg⟩).property
  rootCenter_invariants := by
    apply le_antisymm _ bot_le
    intro v hv
    have hm : v ∈ invariants (M.representation.comp (standardRootCenter L).subtype) := by
      rw [mem_invariants]
      rintro ⟨g, hg⟩
      change M.representation g v = v
      let g' := (standardFieldEquiv J L e hc).symm g
      have hg' : g' ∈ standardRootCenter J := by
        apply (standardFieldEquiv_rootCenter_iff J L e hc g').mp
        simpa only [g', MulEquiv.apply_symm_apply] using hg
      have hv' := hv ⟨g', hg'⟩
      change M.representation (standardFieldEquiv J L e hc g') v = v at hv'
      simpa only [g', MulEquiv.apply_symm_apply] using hv'
    simpa only [M.rootCenter_invariants, Submodule.mem_bot] using hm
  coordinates := coordinates J L e hc M.representation M.coordinates

end
end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty.ExtensionRigidity.Injectivity.ReferenceFieldTransport

namespace Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
open HermitianForm.InvolutionConjugateBounds.Five.Embedding
open Degrees.TrivialCalculation.MiddleFactors
universe v

/-- A fixed polynomial-field model supplies the marked reference model over
all order-25 matrix fields, without changing the coefficient field. -/
theorem twenty_bruhat_reference_models_of_table
    (hmodels : TableBruhatModels.{v}) : TwentyBruhatReferenceModels.{v} := by
  intro F _ _ J hF hconj K _ _ _
  let : Fintype F := Fintype.ofFinite F
  let e : F ≃+* F25 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, F25.card])
  have hc (x : F) : e (J.conj x) = Realization.tableForm.conj (e x) := by
    change e (J.conj x) = F25.conjugation (e x)
    rw [hconj, map_pow, F25.conjugation_eq_fifth]
  obtain ⟨M⟩ := hmodels K
  exact ⟨ExtensionRigidity.Injectivity.ReferenceFieldTransport.model
    J Realization.tableForm e hc M⟩

end Representation.SU3.FiveSmallModules.SevenRestriction.Twenty
