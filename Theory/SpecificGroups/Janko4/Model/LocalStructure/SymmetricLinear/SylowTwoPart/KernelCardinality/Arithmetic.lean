module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Elevens.RepresentativeBridges.Checker

/-!
# Arithmetic for the max4 binary-product certificate

Packed binary multiplication on the first 28 coordinates. The bit checker is proved equal to matrix multiplication, so numerical certificates are checked by the Lean kernel.

The concrete consumer is `KernelCardinality.lean`; matrix and word sources
are the ATLAS representation and J4G1-max4W1, attributed in Model.Data and
SymmetricLinear.Model. See SylowTwoPart/source/README.md.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality
open GeneratorCertificates Simplicity.Elevens.BridgeCertificate
abbrev SmallMatrix := Matrix (Fin 28) (Fin 28) (ZMod 2)
def decode (v : Vector ℕ 28) : SmallMatrix := fun i j => bit (v.get i) j.val
lemma vector_list (v : Vector ℕ 28) : List.ofFn v.get = v.toList := by
  have hv : Vector.ofFn v.get = v := Vector.ofFn_getElem
  exact Vector.toList_ofFn.symm.trans (congrArg Vector.toList hv)
lemma product (xs ys zs : Vector ℕ 28)
    (h : ∀ i : Fin 28, fastRow (xs.get i) ys.toList = zs.get i) :
    decode xs * decode ys = decode zs := by
  ext i j
  change (∑ k : Fin 28, bit (xs.get i) k.val * bit (ys.get k) j.val) = bit (zs.get i) j.val
  rw [← h i, ← vector_list, fastRow_ofFn, bit_xorList, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  simp only [bit]
  cases hh : (xs.get i).testBit k.val <;> simp [hh]
end Janko4.LocalStructure.SymmetricLinear.SylowTwoPart.KernelCardinality
