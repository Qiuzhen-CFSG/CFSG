module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.CoreModel
public import Theory.Representation.BinaryPermutationAlternatingActions

/-!
# Literal six- and seven-dimensional eight-letter coordinates

The augmentation core has coordinates in the seven vectors e_i+e_7.
The natural quotient uses the six classes e_i+e_6, with representative
(x₀,…,x₅,Σxᵢ,0). Its coordinate map sends every even word v to
(v₀+v₇,…,v₅+v₇), so the constant line is killed exactly.
The original adjacent permutations act by Model.A and CoreModel.CoreA.
The checked tables concern only the 256 binary eight-coordinate words.

Source: Aschbacher–Smith B.3.1 and the natural-module case of 14.7.51,
printed pp.83 and 1065, refs/quasithin.pdf.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
open BinaryPermutation

private def firstSix (i : Fin 6) : Fin 8 := ⟨i.val,by omega⟩

private def fullCoordinates : Full (Fin 8) →ₗ[ZMod 2] V where
  toFun v i := v (firstSix i) + v 7
  map_add' v w := by ext i; simp only [Pi.add_apply]; abel
  map_smul' a v := by ext i; simp [mul_add]

private theorem constants_le_ker : constants (Fin 8) ≤ fullCoordinates.ker := by
  apply Submodule.span_le.mpr
  intro v hv
  rcases hv with rfl
  ext i
  change (1 : ZMod 2) + 1 = 0
  decide

private def naturalCoordinates : natural (Fin 8) →ₗ[ZMod 2] V :=
  ((constants (Fin 8)).liftQ fullCoordinates constants_le_ker).comp (natural (Fin 8)).subtype

private def naturalLift (x : V) : core (Fin 8) :=
  ⟨![x 0,x 1,x 2,x 3,x 4,x 5,x 0+x 1+x 2+x 3+x 4+x 5,0],by
    simp only [mem_core,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.sum_univ_zero,add_zero]
    have hh : ∀ a : ZMod 2, a+a=0 := by decide
    convert hh (x 0+x 1+x 2+x 3+x 4+x 5) using 1; abel⟩

private theorem coordinates_lift (x : V) :
    naturalCoordinates (coreToNatural (Fin 8) (naturalLift x)) = x := by
  ext i
  change (naturalLift x).val (firstSix i) + (naturalLift x).val 7 = x i
  fin_cases i <;> simp [naturalLift,firstSix]

private theorem naturalCoordinates_surjective : Function.Surjective naturalCoordinates :=
  fun x => ⟨coreToNatural (Fin 8) (naturalLift x),coordinates_lift x⟩

/-- Coordinates in the classes of e_i+e_6, with the representative's last
coordinate zero. -/
def eNatural : natural (Fin 8) ≃ₗ[ZMod 2] V :=
  LinearEquiv.ofBijective naturalCoordinates
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [finrank_natural_even (Fin 8) (by decide),Module.finrank_fin_fun]
      decide)).mpr naturalCoordinates_surjective,naturalCoordinates_surjective⟩

/-- On any actual even word, subtracting its last coordinate gives these
six natural quotient coordinates. -/
theorem eNatural_core (v : core (Fin 8)) (i : Fin 6) :
    eNatural (coreToNatural (Fin 8) v) i = v.val ⟨i.val,by omega⟩ + v.val 7 := by rfl

/-- The seven standard adjacent transpositions in the original eight letters. -/
@[expose] def adjacent (i : Fin 7) : Equiv.Perm (Fin 8) := Equiv.swap i.castSucc i.succ

private theorem word_action : ∀ (i : Fin 7) (w : Fin 8 → ZMod 2),
    (∑ j, w j) = 0 → ∀ r : Fin 6,
      w ((adjacent i).symm (firstSix r)) + w ((adjacent i).symm 7) =
        Matrix.mulVec (A i) (fun j : Fin 6 => w (firstSix j) + w 7) r := by
  decide +kernel

/-- Every adjacent transposition acts by the literal matrix in the shared
selfextension model. -/
theorem eNatural_adjacent (i : Fin 7) (v : natural (Fin 8)) :
    eNatural (naturalRepresentation (Fin 8) (adjacent i) v) =
      (A i).mulVecLin (eNatural v) := by
  obtain ⟨w,hw,he⟩ := v.property
  have hv : coreToNatural (Fin 8) (⟨w,hw⟩ : core (Fin 8)) = v := Subtype.ext he
  rw [←hv]
  ext r
  change w ((adjacent i).symm (firstSix r)) + w ((adjacent i).symm 7) =
    Matrix.mulVec (A i) (fun j => w (firstSix j)+w 7) r
  exact word_action i w hw r

/-- The permutation generators have the standard square relation. -/
theorem adjacent_square (i : Fin 7) : adjacent i * adjacent i = 1 := by
  exact Equiv.swap_mul_self _ _

/-- Disjoint adjacent transpositions commute. -/
theorem adjacent_commute (i j : Fin 7) (hij : i.val + 1 < j.val) :
    adjacent i * adjacent j = adjacent j * adjacent i := by
  exact (show ∀ i j : Fin 7, i.val + 1 < j.val →
    adjacent i * adjacent j = adjacent j * adjacent i by decide +kernel) i j hij

/-- The neighboring permutation generators satisfy the braid relation. -/
theorem adjacent_braid (i j : Fin 7) (hij : j.val = i.val + 1) :
    adjacent i * adjacent j * adjacent i = adjacent j * adjacent i * adjacent j := by
  exact (show ∀ i j : Fin 7, j.val = i.val + 1 →
    adjacent i * adjacent j * adjacent i = adjacent j * adjacent i * adjacent j
    by decide +kernel) i j hij

private def firstSeven (i : Fin 7) : Fin 8 := i.castSucc

private def coreCoordinates : core (Fin 8) →ₗ[ZMod 2] CoreV where
  toFun v i := v.val (firstSeven i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def coreLift (x : CoreV) : core (Fin 8) :=
  ⟨![x 0,x 1,x 2,x 3,x 4,x 5,x 6,x 0+x 1+x 2+x 3+x 4+x 5+x 6],by
    simp only [mem_core,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
      Fin.sum_univ_zero,add_zero]
    have hh : ∀ a : ZMod 2, a+a=0 := by decide
    convert hh (x 0+x 1+x 2+x 3+x 4+x 5+x 6) using 1; abel⟩

private theorem coreCoordinates_lift (x : CoreV) : coreCoordinates (coreLift x) = x := by
  ext i
  change (coreLift x).val (firstSeven i) = x i
  fin_cases i <;> rfl

private theorem coreCoordinates_surjective : Function.Surjective coreCoordinates :=
  fun x => ⟨coreLift x,coreCoordinates_lift x⟩

/-- Coordinates of the augmentation core in the basis e_i+e_7. -/
def eCore : core (Fin 8) ≃ₗ[ZMod 2] CoreV :=
  LinearEquiv.ofBijective coreCoordinates
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [finrank_core,Module.finrank_fin_fun]
      decide)).mpr coreCoordinates_surjective,coreCoordinates_surjective⟩

/-- The core coordinates are exactly the first seven entries. -/
theorem eCore_apply (v : core (Fin 8)) (i : Fin 7) : eCore v i = v.val i.castSucc := by rfl

private theorem core_word_action : ∀ (i : Fin 7) (w : Fin 8 → ZMod 2),
    (∑ j, w j) = 0 → ∀ r : Fin 7,
      w ((adjacent i).symm r.castSucc) =
        Matrix.mulVec (CoreA i) (fun j : Fin 7 => w j.castSucc) r := by
  decide +kernel

/-- Adjacent transpositions on the original augmentation core have exactly
the seven-dimensional matrices used in the rectangular extension equations. -/
theorem eCore_adjacent (i : Fin 7) (v : core (Fin 8)) :
    eCore (coreRepresentation (Fin 8) (adjacent i) v) =
      (CoreA i).mulVecLin (eCore v) := by
  ext r
  change v.val ((adjacent i).symm r.castSucc) =
    Matrix.mulVec (CoreA i) (fun j => v.val j.castSucc) r
  exact core_word_action i v.val v.property r

/-- The actual natural eight-letter action in the explicit six coordinates. -/
@[expose] def naturalSix : Representation (ZMod 2) (Equiv.Perm (Fin 8)) V :=
  eNatural.conjRingEquiv.toMonoidHom.comp (naturalRepresentation (Fin 8))

/-- The actual augmentation-core action in the explicit seven coordinates. -/
@[expose] def coreSeven : Representation (ZMod 2) (Equiv.Perm (Fin 8)) CoreV :=
  eCore.conjRingEquiv.toMonoidHom.comp (coreRepresentation (Fin 8))

/-- Natural coordinates intertwine the action of every original permutation. -/
theorem eNatural_equivariant (g : Equiv.Perm (Fin 8)) (v : natural (Fin 8)) :
    eNatural (naturalRepresentation (Fin 8) g v) = naturalSix g (eNatural v) := by
  change _ = eNatural (naturalRepresentation (Fin 8) g (eNatural.symm (eNatural v)))
  rw [eNatural.symm_apply_apply]

/-- Core coordinates intertwine the action of every original permutation. -/
theorem eCore_equivariant (g : Equiv.Perm (Fin 8)) (v : core (Fin 8)) :
    eCore (coreRepresentation (Fin 8) g v) = coreSeven g (eCore v) := by
  change _ = eCore (coreRepresentation (Fin 8) g (eCore.symm (eCore v)))
  rw [eCore.symm_apply_apply]

/-- The natural action on each adjacent generator is the shared matrix. -/
theorem naturalSix_adjacent (i : Fin 7) : naturalSix (adjacent i) = (A i).mulVecLin := by
  apply LinearMap.ext
  intro x
  obtain ⟨v,rfl⟩ := eNatural.surjective x
  rw [←eNatural_equivariant,eNatural_adjacent]

/-- The core action on each adjacent generator is the shared matrix. -/
theorem coreSeven_adjacent (i : Fin 7) : coreSeven (adjacent i) = (CoreA i).mulVecLin := by
  apply LinearMap.ext
  intro x
  obtain ⟨v,rfl⟩ := eCore.surjective x
  rw [←eCore_equivariant,eCore_adjacent]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
