module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction.Generation.ModelInput
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SevenSylowOvergroups.Basic

/-!
# Checked binary octonion matrix words

Equality on the eight basis columns determines the original linear automorphism.
The word checker composes small checked column steps; a separate inverse rule
uses injectivity of the actual automorphism. This avoids repeatedly expanding
long products of root maps. The Sylow supplement certificates consume these rules.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 4.3,
manuscript pp.10--11. Root conventions are inherited from the ATLAS port;
Gerald Höhn and the ATLAS contributors, ATLAS Research and Attribution License
1.0 (LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff).
-/

@[expose] public section

open Atlas.G2 Atlas.G2.Explicit Atlas.SplitOctonion
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.FiniteSylow
local notation "G" => Model (ZMod 2)
namespace Certificate

def column (n : ℕ) (c : Fin 8) : Carrier (ZMod 2) :=
  fun r => ((n >>> (8*r.val + c.val)) % 2 : ℕ)

def linear (n : ℕ) : Carrier (ZMod 2) →ₗ[ZMod 2] Carrier (ZMod 2) :=
  Matrix.mulVecLin (fun r c => column n c r)

theorem linear_basis (n : ℕ) (c : Fin 8) : linear n (basisVector c) = column n c := by
  change Matrix.mulVec (fun r c => column n c r) (basisVector c) = column n c
  exact Matrix.mulVec_single_one (fun r c => column n c r) c

def HasMatrix (g : G) (n : ℕ) : Prop := g.val.toLinearMap = linear n

theorem hasMatrix_of_columns {g : G} {n : ℕ}
    (h : ∀ c, g.val (basisVector c) = column n c) : HasMatrix g n := by
  apply linearMap_ext
  intro c
  exact (h c).trans (linear_basis n c).symm

theorem hasMatrix_one : HasMatrix 1 9241421688590303745 := by
  apply hasMatrix_of_columns
  exact fun c => funext ((by decide +kernel : ∀ c r : Fin 8,
    basisVector (F := ZMod 2) c r = column 9241421688590303745 c r) c)

theorem HasMatrix.mul {g h : G} {a b c : ℕ} (hg : HasMatrix g a) (hh : HasMatrix h b)
    (step : ∀ j, linear a (column b j) = column c j) : HasMatrix (g*h) c := by
  change g.val.toLinearMap.comp h.val.toLinearMap = linear c
  rw [hg, hh]
  apply linearMap_ext
  intro j
  simpa only [LinearMap.comp_apply, linear_basis] using step j

theorem HasMatrix.inv {g : G} {a b : ℕ} (hg : HasMatrix g a)
    (step : ∀ j, linear a (column b j) = basisVector j) : HasMatrix g⁻¹ b := by
  apply hasMatrix_of_columns
  intro j
  apply g.val.injective
  change g.val (g.val.symm (basisVector j)) = g.val (column b j)
  rw [LinearEquiv.apply_symm_apply]
  exact (step j).symm.trans (congrArg (fun f : Carrier (ZMod 2) →ₗ[ZMod 2] Carrier (ZMod 2) =>
    f (column b j)) hg).symm

theorem HasMatrix.eq {g h : G} {n : ℕ} (hg : HasMatrix g n) (hh : HasMatrix h n) : g=h := by
  apply Subtype.ext
  exact LinearEquiv.toLinearMap_injective (hg.trans hh.symm)

def word {n : ℕ} (letters : Fin n → G) (w : List (Fin n)) : G := (w.map letters).prod

theorem word_mem {n : ℕ} (letters : Fin n → G) (K : Subgroup G)
    (h : ∀ i, letters i ∈ K) (w : List (Fin n)) : word letters w ∈ K := by
  induction w with
  | nil => exact K.one_mem
  | cons i w ih => exact K.mul_mem (h i) ih

inductive Check {n : ℕ} (labels : Fin n → ℕ) : List (Fin n) → ℕ → Prop
  | nil : Check labels [] 9241421688590303745
  | cons {i : Fin n} {w : List (Fin n)} {a b : ℕ}
      (step : ∀ c, linear (labels i) (column b c) = column a c)
      (tail : Check labels w b) : Check labels (i::w) a

theorem Check.hasMatrix {n : ℕ} {labels : Fin n → ℕ} {letters : Fin n → G}
    (h : ∀ i, HasMatrix (letters i) (labels i)) {w : List (Fin n)} {a : ℕ}
    (hc : Check labels w a) : HasMatrix (word letters w) a := by
  induction hc with
  | nil => exact hasMatrix_one
  | @cons i w a b hs ht ih => exact (h i).mul ih hs

end Certificate
end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.BinaryObstruction.FiniteSylow
