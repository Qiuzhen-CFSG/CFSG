module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.OrbitCounts.Algebra

/-!
# Checked PC conjugation on the original candidate coordinates

The proposed images from the orbit discovery are verified on each original
basis word using the checked PC collection equations. The binary product law
extends them to every coordinate, with the exact convention g⁻¹ x g.
Source: Aschbacher–Smith A.3.12, pp.47–48; Kleidman–Wilson (1988), pp.484–510.
No discovery equation is assumed.
-/

@[expose] public section
open Janko4 Janko4.LocalStructure.SylowNormalEights
open Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
attribute [local irreducible] modelGroup matrixA matrixB pairRank
def orbitBasisWords6 : Fin 7 → List (Fin 21) := ![[13],[15],[16],[17],[18],[19],[20]]

def orbitImages6 : Fin 21 → Fin 7 → Fin 128 :=
  ![![125,118,68,72,16,96,64],![3,2,84,104,16,32,64],![53,18,4,8,112,32,64],![53,50,4,72,16,32,64],![1,2,36,8,16,32,64],![1,2,4,8,80,96,64],![97,98,4,8,16,32,64],![1,2,4,104,16,32,64],![1,2,4,8,80,32,64],![33,2,4,8,16,32,64],![1,2,68,8,16,32,64],![1,66,4,8,16,32,64],![1,2,4,72,16,32,64],![1,2,4,8,16,32,64],![65,2,4,8,16,32,64],![1,2,4,8,16,32,64],![1,2,4,8,16,32,64],![1,2,4,8,16,32,64],![1,2,4,8,16,32,64],![1,2,4,8,16,32,64],![1,2,4,8,16,32,64]]
def orbitAction6 (j : Fin 21) (n : Fin 128) : Fin 128 :=
  orbitFold 6 (List.ofFn (orbitImages6 j)) n.val

private theorem orbitBasisCollect6 : ∀ (j : Fin 21) (k : Fin 7),
    collect 128 ((orbitBasisWords6 k) ++ [j]) =
      collect 128 ([j] ++ selectWords (candidateWords 6) (orbitImages6 j k).val) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem orbitBasisConjugate6 (j : Fin 21) (k : Fin 7) :
    (MatrixWords.pcGenerator j : Model)⁻¹ * realization (wordValue ((orbitBasisWords6 k))) *
      (MatrixWords.pcGenerator j : Model) = point 6 (orbitImages6 j k) := by
  have he : wordValue ((orbitBasisWords6 k)) * Presentation.generator j =
      Presentation.generator j * abstractPoint 6 (orbitImages6 j k) := by
    have h := (collect_sound 128 _).symm.trans
      ((congrArg wordValue (orbitBasisCollect6 j k)).trans (collect_sound 128 _))
    simpa only [wordValue_append, wordValue_cons, wordValue_nil, mul_one, abstractPoint] using h
  have hm : realization (wordValue ((orbitBasisWords6 k))) *
      (MatrixWords.pcGenerator j : Model) =
      (MatrixWords.pcGenerator j : Model) * point 6 (orbitImages6 j k) := by
    simpa only [map_mul, realization_generator, point] using congrArg realization he
  rw [mul_assoc, hm, inv_mul_cancel_left]

/-- Actual inverse conjugation by each original PC generator on every coordinate. -/
theorem orbitAction6_conjugate (j : Fin 21) (n : Fin 128) :
    (MatrixWords.pcGenerator j : Model)⁻¹ * point 6 n * (MatrixWords.pcGenerator j : Model) =
      point 6 (orbitAction6 j n) := by
  let f : Model →* Model := (MulAut.conj (MatrixWords.pcGenerator j : Model)⁻¹).toMonoidHom
  have hlist : (candidateWords 6).map (fun w => f (realization (wordValue w))) =
      (List.ofFn (orbitImages6 j)).map (fun x : Fin 128 => point 6 x) := by
    have hw : candidateWords 6 = List.ofFn (fun k : Fin 7 => (orbitBasisWords6 k)) := by
      decide +kernel
    rw [hw]
    simp only [List.map_ofFn]
    apply congrArg List.ofFn
    funext k
    simpa only [Function.comp_def, f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      orbitBasisConjugate6 j k
  simpa only [Function.comp_def, f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, orbitAction6] using
    point_map_of_basis 6 f (List.ofFn (orbitImages6 j)) hlist n
def orbitBasisWords8 : Fin 8 → List (Fin 21) := ![[9],[14],[15],[16],[17],[18],[19],[20]]

def orbitImages8 : Fin 21 → Fin 8 → Fin 256 :=
  ![![211,2,236,136,144,32,192,128],![193,98,4,168,208,32,64,128],![17,18,36,8,16,224,64,128],![33,130,100,8,144,32,64,128],![1,130,4,72,16,32,64,128],![163,130,4,8,16,160,192,128],![1,2,196,8,16,32,64,128],![97,98,4,8,208,32,64,128],![17,130,4,8,16,160,64,128],![1,2,4,8,16,32,64,128],![193,130,4,136,16,32,64,128],![1,2,132,8,16,32,64,128],![97,2,4,8,144,32,64,128],![65,130,4,8,16,32,64,128],![1,2,4,8,16,32,64,128],![1,2,4,8,16,32,64,128],![1,2,4,8,16,32,64,128],![1,2,4,8,16,32,64,128],![1,2,4,8,16,32,64,128],![1,2,4,8,16,32,64,128],![1,2,4,8,16,32,64,128]]
def orbitAction8 (j : Fin 21) (n : Fin 256) : Fin 256 :=
  orbitFold 8 (List.ofFn (orbitImages8 j)) n.val

private theorem orbitBasisCollect8 : ∀ (j : Fin 21) (k : Fin 8),
    collect 128 ((orbitBasisWords8 k) ++ [j]) =
      collect 128 ([j] ++ selectWords (candidateWords 8) (orbitImages8 j k).val) := by
  intro j
  fin_cases j <;> decide +kernel

private theorem orbitBasisConjugate8 (j : Fin 21) (k : Fin 8) :
    (MatrixWords.pcGenerator j : Model)⁻¹ * realization (wordValue ((orbitBasisWords8 k))) *
      (MatrixWords.pcGenerator j : Model) = point 8 (orbitImages8 j k) := by
  have he : wordValue ((orbitBasisWords8 k)) * Presentation.generator j =
      Presentation.generator j * abstractPoint 8 (orbitImages8 j k) := by
    have h := (collect_sound 128 _).symm.trans
      ((congrArg wordValue (orbitBasisCollect8 j k)).trans (collect_sound 128 _))
    simpa only [wordValue_append, wordValue_cons, wordValue_nil, mul_one, abstractPoint] using h
  have hm : realization (wordValue ((orbitBasisWords8 k))) *
      (MatrixWords.pcGenerator j : Model) =
      (MatrixWords.pcGenerator j : Model) * point 8 (orbitImages8 j k) := by
    simpa only [map_mul, realization_generator, point] using congrArg realization he
  rw [mul_assoc, hm, inv_mul_cancel_left]

/-- Actual inverse conjugation by each original PC generator on every coordinate. -/
theorem orbitAction8_conjugate (j : Fin 21) (n : Fin 256) :
    (MatrixWords.pcGenerator j : Model)⁻¹ * point 8 n * (MatrixWords.pcGenerator j : Model) =
      point 8 (orbitAction8 j n) := by
  let f : Model →* Model := (MulAut.conj (MatrixWords.pcGenerator j : Model)⁻¹).toMonoidHom
  have hlist : (candidateWords 8).map (fun w => f (realization (wordValue w))) =
      (List.ofFn (orbitImages8 j)).map (fun x : Fin 256 => point 8 x) := by
    have hw : candidateWords 8 = List.ofFn (fun k : Fin 8 => (orbitBasisWords8 k)) := by
      decide +kernel
    rw [hw]
    simp only [List.map_ofFn]
    apply congrArg List.ofFn
    funext k
    simpa only [Function.comp_def, f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      orbitBasisConjugate8 j k
  simpa only [Function.comp_def, f, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, orbitAction8] using
    point_map_of_basis 8 f (List.ofFn (orbitImages8 j)) hlist n
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
