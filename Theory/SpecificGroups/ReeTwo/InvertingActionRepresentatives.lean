module

public import Theory.SpecificGroups.ReeTwo.InvertingActionReconstruction

/-!
# The twenty explicit inverting squaring actions

Each row lists the integer codes of the ten root images; bit `j` is the
coordinate of root `j`. The rows are ordered by the code of the image of
root 0. Kernel-checked square and commutator certificates give homomorphisms
from the core presentation. Their fourth iterates are the identity, giving
explicit automorphisms, each of which squares `c` and inverts root 2.
Exhaustiveness of this list is proved in `InvertingActionCensus`.

Source: direct finite certificates in the verified Shinoda (1975), (2.3),
core coordinates, evaluated through `CoreActionPacking`.
-/

@[expose] public section
namespace ReeTwo.Core.InvertingActionCensus
open CensusPacked

def seedCode : Fin 20 → Nat := ![1, 16, 29, 33, 55, 59, 65, 97, 144, 151, 272, 349, 400, 475, 763, 765, 795, 855, 957, 1015]

def representativeCodes (i : Fin 20) : CoreRoot → Nat :=
  ![![1, 515, 516, 559, 765, 32, 96, 736, 928, 512],
    ![16, 536, 516, 590, 475, 256, 384, 704, 480, 512],
    ![29, 367, 516, 1022, 55, 928, 736, 960, 864, 512],
    ![33, 611, 516, 207, 349, 32, 96, 736, 928, 512],
    ![55, 1022, 516, 152, 400, 864, 960, 384, 256, 512],
    ![59, 142, 516, 611, 33, 480, 704, 96, 32, 512],
    ![65, 35, 516, 911, 957, 32, 96, 736, 928, 512],
    ![97, 67, 516, 367, 29, 32, 96, 736, 928, 512],
    ![144, 280, 516, 430, 763, 256, 384, 704, 480, 512],
    ![151, 670, 516, 920, 272, 864, 960, 384, 256, 512],
    ![272, 920, 516, 142, 59, 256, 384, 704, 480, 512],
    ![349, 207, 516, 670, 151, 928, 736, 960, 864, 512],
    ![400, 152, 516, 878, 795, 256, 384, 704, 480, 512],
    ![475, 590, 516, 515, 1, 480, 704, 96, 32, 512],
    ![763, 430, 516, 35, 65, 480, 704, 96, 32, 512],
    ![765, 559, 516, 350, 1015, 928, 736, 960, 864, 512],
    ![795, 878, 516, 67, 97, 480, 704, 96, 32, 512],
    ![855, 62, 516, 280, 144, 864, 960, 384, 256, 512],
    ![957, 911, 516, 62, 855, 928, 736, 960, 864, 512],
    ![1015, 350, 516, 536, 16, 864, 960, 384, 256, 512]] i

def representativeRoots (i : Fin 20) (j : CoreRoot) : Core := decode (representativeCodes i j)

theorem representativeRoots_code : ∀ i j,
    code (representativeRoots i j) = representativeCodes i j := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem representativeRelations (i : Fin 20) : CoreRelations (representativeRoots i) where
  square j := by
    apply code_injective
    rw [← pmul_code, ← peval_code]
    simp only [representativeRoots_code]
    exact (by decide +kernel : ∀ (i : Fin 20) (j : CoreRoot),
      pmul (representativeCodes i j) (representativeCodes i j) =
        peval (representativeCodes i) (coreSquare j)) i j
  commutator j k hjk := by
    apply code_injective
    rw [← pcomm_code, ← peval_code]
    simp only [representativeRoots_code]
    exact (by decide +kernel : ∀ (i : Fin 20) (j k : CoreRoot), j < k →
      pcomm (representativeCodes i j) (representativeCodes i k) =
        peval (representativeCodes i) (coreCommutator j k)) i j k hjk

def representativeMap (i : Fin 20) (x : Core) : Core :=
  normalWord (representativeRoots i) (coords x)

theorem representativeMap_code (i : Fin 20) (x : Core) :
    code (representativeMap i x) = act (representativeCodes i) (code x) := by
  rw [representativeMap, ← act_code]
  simp only [representativeRoots_code]

theorem representativeMap_eq_lift (i : Fin 20) (x : Core) :
    representativeMap i x = lift (representativeRelations i) x :=
  (lift_apply (representativeRelations i) x).symm

theorem representativeMap_root (i : Fin 20) (j : CoreRoot) :
    representativeMap i (root j) = representativeRoots i j := by
  rw [representativeMap_eq_lift, lift_root]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem representativeMap_four (i : Fin 20) (x : Core) :
    representativeMap i (representativeMap i (representativeMap i (representativeMap i x))) = x := by
  have he : (lift (representativeRelations i)).comp ((lift (representativeRelations i)).comp
      ((lift (representativeRelations i)).comp (lift (representativeRelations i)))) =
      MonoidHom.id Core := by
    apply hom_ext
    intro j
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, ← representativeMap_eq_lift]
    apply code_injective
    simp only [representativeMap_code]
    exact (by decide +kernel : ∀ (i : Fin 20) (j : CoreRoot),
      act (representativeCodes i) (act (representativeCodes i)
        (act (representativeCodes i) (act (representativeCodes i) (code (root j))))) =
          code (root j)) i j
  simpa only [MonoidHom.comp_apply, MonoidHom.id_apply, ← representativeMap_eq_lift] using
    DFunLike.congr_fun he x

/-- The twenty inverting squaring actions, given by their ten root images. -/
def representative (i : Fin 20) : MulAut Core where
  toFun := representativeMap i
  invFun x := representativeMap i (representativeMap i (representativeMap i x))
  left_inv := representativeMap_four i
  right_inv := representativeMap_four i
  map_mul' x y := by
    simpa only [representativeMap_eq_lift] using map_mul (lift (representativeRelations i)) x y

theorem representative_apply (i : Fin 20) (x : Core) :
    representative i x = representativeMap i x := rfl

theorem representative_root (i : Fin 20) (j : CoreRoot) :
    representative i (root j) = representativeRoots i j := representativeMap_root i j

theorem representative_four (i : Fin 20) : representative i ^ 4 = 1 := by
  apply aut_four_of_apply
  intro j
  simp only [representative_apply]
  exact representativeMap_four i (root j)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem representative_conj_c (i : Fin 20) :
    representative i * c * (representative i)⁻¹ = c ^ 2 := by
  apply squaring_conj_of_apply
  intro j
  apply code_injective
  calc
    code (representative i (c (root j))) = act (representativeCodes i) (cRoots j) :=
      (representativeMap_code i (c (root j))).trans
        (congrArg (act (representativeCodes i)) (cRoots_eq j).symm)
    _ = (cAct^[2]) (representativeCodes i j) :=
      (by decide +kernel : ∀ (i : Fin 20) (j : CoreRoot),
        act (representativeCodes i) (cRoots j) = (cAct^[2]) (representativeCodes i j)) i j
    _ = code ((c ^ 2) (representative i (root j))) :=
      (congrArg (cAct^[2]) (representativeRoots_code i j).symm).trans
        ((cAct_iterate_code 2 (representativeRoots i j)).trans
          (congrArg (fun x => code ((c ^ 2) x)) (representative_root i j).symm))

theorem representative_root_two (i : Fin 20) :
    representative i (root 2) = (root 2)⁻¹ := by
  rw [representative_root]
  exact (by decide +kernel : ∀ i : Fin 20, representativeRoots i 2 = (root 2)⁻¹) i

end ReeTwo.Core.InvertingActionCensus
