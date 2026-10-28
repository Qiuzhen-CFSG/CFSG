module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.RepresentativeBridges.Checker

/-!
# Rectangular packed binary multiplication

This dimension-polymorphic extension of the existing J₄ packed checker
identifies list XOR certificates with ordinary rectangular matrix products.
It is used for the numerator, denominator and quotient coordinates of the
literal max4 section; no external arithmetic is trusted.
-/

@[expose] public section
open Matrix
namespace Janko4.LocalStructure.SymmetricLinear.Projection.LinearSection
open GeneratorCertificates Simplicity.Elevens.BridgeCertificate

def unpack {n m : ℕ} (v : Vector ℕ n) : Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun i j => bit (v.get i) j.val

def vectorRows {n : ℕ} (xs : List ℕ) (h : xs.length = n) : Vector ℕ n :=
  ⟨xs.toArray, by simpa using h⟩

lemma vector_list {n : ℕ} (v : Vector ℕ n) : List.ofFn v.get = v.toList := by
  have hv : Vector.ofFn v.get = v := Vector.ofFn_getElem
  exact Vector.toList_ofFn.symm.trans (congrArg Vector.toList hv)

lemma decode_fastRow {n m : ℕ} (x : ℕ) (v : Vector ℕ n) :
    (fun j : Fin m => bit (fastRow x v.toList) j.val) =
      (fun i : Fin n => bit x i.val) ᵥ* unpack v := by
  rw [← vector_list, fastRow_ofFn]
  funext j
  rw [bit_xorList, List.map_ofFn, List.sum_ofFn]
  rw [Matrix.vecMul_apply_eq_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [unpack, bit]
  cases h : x.testBit k.val <;> simp [h]

lemma product_vectors {n m p : ℕ} (xs : Vector ℕ n) (ys : Vector ℕ m)
    (zs : Vector ℕ n) (h : xs.toList.map (fun x => fastRow x ys.toList) = zs.toList) :
    (unpack xs : Matrix (Fin n) (Fin m) (ZMod 2)) * unpack ys =
      (unpack zs : Matrix _ (Fin p) _) := by
  funext i j
  have e := congrArg (fun l : List ℕ => l[i.val]?) h
  have ee : fastRow (xs.get i) ys.toList = zs.get i := by
    simpa [List.getElem?_map, Vector.getElem?_toList, i.isLt, Vector.get] using e
  have d := congrFun (decode_fastRow (m := p) (xs.get i) ys) j
  rw [ee] at d
  exact d.symm

lemma product_lists {n m p : ℕ} (xs ys zs : List ℕ)
    (hx : xs.length = n) (hy : ys.length = m) (hz : zs.length = n)
    (h : xs.map (fun x => fastRow x ys) = zs) :
    (unpack (vectorRows xs hx) : Matrix (Fin n) (Fin m) (ZMod 2)) *
      unpack (vectorRows ys hy) = (unpack (vectorRows zs hz) : Matrix _ (Fin p) _) := by
  apply product_vectors
  simpa [vectorRows] using h
lemma product_eq_lists {n m k p : ℕ} (xs ys us vs : List ℕ)
    (hx : xs.length = n) (hy : ys.length = m)
    (hu : us.length = n) (hv : vs.length = k)
    (h : xs.map (fun x => fastRow x ys) = us.map (fun x => fastRow x vs)) :
    (unpack (vectorRows xs hx) : Matrix (Fin n) (Fin m) (ZMod 2)) *
      (unpack (vectorRows ys hy) : Matrix _ (Fin p) _) =
    unpack (vectorRows us hu) * unpack (vectorRows vs hv) := by
  let zs := xs.map (fun x => fastRow x ys)
  have hz : zs.length = n := by simp [zs, hx]
  exact (product_lists xs ys zs hx hy hz rfl).trans
    (product_lists us vs zs hu hv hz h.symm).symm

end Janko4.LocalStructure.SymmetricLinear.Projection.LinearSection
