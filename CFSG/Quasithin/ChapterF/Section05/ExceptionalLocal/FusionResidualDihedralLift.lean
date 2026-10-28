module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.FusionResidualDihedralModel
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.SourceUpper

/-!
# An explicit dihedral subgroup of the source upper group

The eight binary matrices lift to SU₄(2), and hence through the faithful
common subgroup of the original completion. This retains the literal maps
needed to identify the endpoint residual-core join in F.5.5.
Source: Aschbacher–Smith F.5.5, printed pp.301–302.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.ResidualJoinModel
open Subgroup Matrix
open GreenBook.LieModels.UnitaryFour
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag
local notation "hn" => Nat.le_refl 1
local notation "F" => MatrixField 1
local notation "σ" => fieldConj 1
local notation "hσ" => fieldConj_involutive 1 hn
local notation "D8" => DihedralGroup 4

def binaryCast : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F
def liftedMatrix (a : D8) : Matrix (Fin 4) (Fin 4) F :=
  (binaryMatrix a).map binaryCast
private theorem cast_fixed (x : ZMod 2) : σ (binaryCast x) = binaryCast x :=
  DFunLike.congr_fun (Subsingleton.elim ((σ).toRingHom.comp binaryCast) binaryCast) x
private theorem gram_cast : (gram (ZMod 2)).map binaryCast = gram F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram]
private theorem lifted_det (a : D8) : (liftedMatrix a).det=1 := by
  change (binaryCast.mapMatrix (binaryMatrix a)).det=1
  rw [←binaryCast.map_det,binary_det,map_one]
private theorem lifted_unitary (a : D8) :
    (form F σ hσ).conjTranspose (liftedMatrix a)*gram F*liftedMatrix a=gram F := by
  have hf : (form F σ hσ).conjTranspose (liftedMatrix a)=(liftedMatrix a).transpose := by
    ext i j
    exact cast_fixed _
  rw [hf,liftedMatrix,←Matrix.transpose_map,←gram_cast,
    ←Matrix.map_mul,←Matrix.map_mul,(binary_valid a).1]

def matrixElement (a : D8) : SU F (form F σ hσ) :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (liftedMatrix a)
    (by rw [lifted_det]; exact one_ne_zero),by exact lifted_unitary a,by exact Units.ext (lifted_det a)⟩

def matrixHom : D8 →* SU F (form F σ hσ) where
  toFun := matrixElement
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change binaryCast.mapMatrix (binaryHom 1)=1
    rw [map_one,map_one]
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    change binaryCast.mapMatrix (binaryHom (a*b)) =
      binaryCast.mapMatrix (binaryHom a)*binaryCast.mapMatrix (binaryHom b)
    rw [map_mul,map_mul]

theorem matrixHom_injective : Function.Injective matrixHom := by
  intro a b hab
  have hmat := congrArg (fun x : SU F (form F σ hσ) => x.val.val) hab
  exact binary_injective (Matrix.map_injective binaryCast.injective hmat)

theorem matrixElement_upper (a : D8) : matrixElement a∈upperMatrix 1 hn := by
  apply (UnitaryFourSylow.mem_upper F σ hσ _).mpr
  rcases (binary_valid a).2 with ⟨hd,h10,h20,h30,h21,h31,h32⟩
  constructor
  · apply (UnitaryFourPointLocal.mem_localSU F _ _).mpr
    change binaryCast (binaryMatrix a 0 0)=1 ∧ binaryCast (binaryMatrix a 1 0)=0 ∧
      binaryCast (binaryMatrix a 2 0)=0 ∧ binaryCast (binaryMatrix a 3 0)=0
    simp only [hd,h10,h20,h30,map_one,map_zero,and_self]
  · change binaryCast (binaryMatrix a 1 1)=1 ∧ binaryCast (binaryMatrix a 2 1)=0 ∧
      binaryCast (binaryMatrix a 2 2)=1
    simp only [hd,h21,map_one,map_zero,and_self]

def upperHom : D8 →* upperMatrix 1 hn :=
  matrixHom.codRestrict _ matrixElement_upper

def projectiveUpperHom : D8 →* upperProjective 1 hn :=
  (upperProjectEquiv 1 hn).toMonoidHom.comp upperHom

theorem projectiveUpperHom_injective : Function.Injective projectiveUpperHom :=
  (upperProjectEquiv 1 hn).injective.comp (fun _ _ h => matrixHom_injective (congrArg Subtype.val h))

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
    (Extension.amalgam 1 hn) (G := G0)) (i : G0 →* G)

def sourceHom : D8 →* G := (sourceOrdinaryUpperMap c i).comp projectiveUpperHom

theorem sourceHom_injective (hi : Function.Injective i) : Function.Injective (sourceHom c i) :=
  (sourceOrdinaryUpperMap_injective c i hi).comp projectiveUpperHom_injective

theorem sourceHom_mem_ordinary (a : D8) : sourceHom c i a∈sourceOrdinaryUpper c i :=
  ⟨projectiveUpperHom a,rfl⟩

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.ResidualJoinModel
