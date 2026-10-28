module
public import Theory.Representation.MathieuCodeRestriction.CodeLocal

/-!
# Lifting fixed vectors from the code quotient

A permutation fixing a coordinate cannot move a Golay word by a nonzero
constant word. Thus, for every subgroup fixing a point, the inverse image
of its code fixed space is exactly its Golay fixed space. The constant line
is contained in every Golay fixed space. Rank-nullity therefore says that
quotienting reduces the fixed dimension by exactly one.

This connects finite calculations on the native twelve-dimensional rows to
the literal eleven-dimensional quotient. In particular it applies to every
subgroup of a native octad pointwise kernel and to the native M23 image.

Source: Aschbacher--Smith, H.13.1 and H.16.2, printed pp.395,402--403.
-/

public section
noncomputable section
open Sporadic.Mathieu
open Representation.BinaryOffender
namespace MathieuCode

/-- An actor fixing a coordinate fixes every representative of a fixed code class. -/
theorem golay_fixed_of_code_fixed (g : M24) (i : Fin 24) (hi : g • i = i)
    (v : golay) (hv : codeRepresentation g (codeLine.mkQ v) = codeLine.mkQ v) :
    golayRepresentation g v = v := by
  rw [codeRepresentation_mk] at hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((Submodule.Quotient.eq codeLine).mp hv)
  change c • BinaryPermutation.allOne (Fin 24) = (golayRepresentation g v).val - v.val at hc
  have hi' : g⁻¹ • i = i := by
    have h := congrArg (fun j : Fin 24 => g⁻¹ • j) hi
    simpa only [inv_smul_smul] using h.symm
  have hci := congrFun hc i
  change c * 1 = v.val (g⁻¹ • i) - v.val i at hci
  rw [hi', sub_self, mul_one] at hci
  rw [hci, zero_smul] at hc
  exact Subtype.ext (sub_eq_zero.mp hc.symm)

/-- Fixed spaces lift exactly when the subgroup fixes an actual coordinate. -/
theorem fixedSpace_golay_eq_comap (A : Subgroup M24) (i : Fin 24)
    (hi : ∀ g ∈ A, g • i = i) :
    fixedSpace golayRepresentation A = (fixedSpace codeRepresentation A).comap codeLine.mkQ := by
  ext v
  constructor
  · intro hv g
    change codeRepresentation g.val (codeLine.mkQ v) = codeLine.mkQ v
    rw [codeRepresentation_mk]
    exact congrArg codeLine.mkQ (hv g)
  · intro hv g
    exact golay_fixed_of_code_fixed g.val i (hi g.val g.property) v (hv g)

/-- The constant line is pointwise fixed by every native subgroup. -/
theorem codeLine_le_fixedSpace_golay (A : Subgroup M24) :
    codeLine ≤ fixedSpace golayRepresentation A := by
  intro v hv g
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  apply Subtype.ext
  change BinaryPermutation.representation (Fin 24) g.val.val v.val = v.val
  change c • BinaryPermutation.allOne (Fin 24) = v.val at hc
  rw [← hc, map_smul, BinaryPermutation.permute_allOne]

/-- For a subgroup fixing a point, quotienting by constants subtracts one fixed dimension. -/
theorem finrank_fixedSpace_golay (A : Subgroup M24) (i : Fin 24)
    (hi : ∀ g ∈ A, g • i = i) :
    Module.finrank (ZMod 2) (fixedSpace golayRepresentation A) =
      Module.finrank (ZMod 2) (fixedSpace codeRepresentation A) + 1 := by
  let W := fixedSpace golayRepresentation A
  let f : W →ₗ[ZMod 2] Code := codeLine.mkQ.comp W.subtype
  have hr : LinearMap.range f = fixedSpace codeRepresentation A := by
    ext q
    constructor
    · rintro ⟨v, rfl⟩
      exact (show W ≤ (fixedSpace codeRepresentation A).comap codeLine.mkQ from
        (fixedSpace_golay_eq_comap A i hi).le) v.property
    · intro hq
      obtain ⟨v, rfl⟩ := codeLine.mkQ_surjective q
      refine ⟨⟨v, ?_⟩, rfl⟩
      change v ∈ fixedSpace golayRepresentation A
      rw [fixedSpace_golay_eq_comap A i hi]
      exact hq
  have hk : LinearMap.ker f = codeLine.comap W.subtype := by
    ext v
    change codeLine.mkQ v.val = 0 ↔ v.val ∈ codeLine
    exact Submodule.Quotient.mk_eq_zero codeLine
  have hd := f.finrank_range_add_finrank_ker
  rw [hr, hk, (Submodule.comapSubtypeEquivOfLe (codeLine_le_fixedSpace_golay A)).finrank_eq,
    finrank_codeLine] at hd
  exact hd.symm

end MathieuCode
