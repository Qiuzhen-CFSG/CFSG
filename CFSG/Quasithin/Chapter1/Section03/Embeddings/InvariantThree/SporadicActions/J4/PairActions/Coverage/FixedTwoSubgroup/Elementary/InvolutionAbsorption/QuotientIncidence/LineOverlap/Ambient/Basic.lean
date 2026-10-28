module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Model
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.NormalClosureControl.ActionKernel.Presentation.Relators.FastArithmetic

/-!
# Actual subgroup membership from packed matrix words

The certificates in this directory multiply and invert actual elements of the
ATLAS max4 subgroup. The faithful 112-dimensional representation identifies
their results with the fifteen prescribed source words after one conjugation.
No assertion about a quotient image or an elementary subgroup normalizer is
used to infer ambient membership.

Source context: Aschbacher–Smith, Proposition 1.3.4, printed p.511;
GLS3 Table 5.3i; ATLAS `J4G1-max4W1`, as retained with
`Janko4.LocalStructure.SymmetricLinear.max4Program`.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.AmbientLineCertificates

open Janko4 Janko4.GeneratorCertificates Janko4.LocalStructure.SymmetricLinear

attribute [local irreducible] Janko4.modelGroup

theorem eval_mul {g h : Model} {rs ss ts : Vector ℕ 112}
    (hg : toMatrix g = decodeRows rs) (hh : toMatrix h = decodeRows ss)
    (hc : packedMul rs ss = ts) : toMatrix (g * h) = decodeRows ts := by
  rw [map_mul, hg, hh, ← decode_packedMul, hc]

theorem eval_pow_add {g : Model} {m n : ℕ} {rs ss ts : Vector ℕ 112}
    (hg : toMatrix (g ^ m) = decodeRows rs) (hh : toMatrix (g ^ n) = decodeRows ss)
    (hc : packedMul rs ss = ts) : toMatrix (g ^ (m + n)) = decodeRows ts := by
  rw [pow_add]
  exact eval_mul hg hh hc

theorem eval_inv {g : Model} {rs ss : Vector ℕ 112}
    (hg : toMatrix g = decodeRows rs) (hc : packedMul rs ss = packedOne) :
    toMatrix g⁻¹ = decodeRows ss := by
  have h : toMatrix g * decodeRows ss = 1 := by
    rw [hg, ← decode_packedMul, hc, decode_packedOne]
  calc
    toMatrix g⁻¹ = toMatrix g⁻¹ * 1 := (mul_one _).symm
    _ = toMatrix g⁻¹ * (toMatrix g * decodeRows ss) := by rw [h]
    _ = decodeRows ss := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]

/-- A packed matrix represented by an actual member of the specified max4. -/
def InMax4 (rs : Vector ℕ 112) : Prop :=
  ∃ g : Model, g ∈ max4Subgroup ∧ toMatrix g = decodeRows rs

theorem InMax4.mul {rs ss ts : Vector ℕ 112}
    (hr : InMax4 rs) (hs : InMax4 ss) (hc : packedMul rs ss = ts) : InMax4 ts := by
  obtain ⟨g, hg, eg⟩ := hr
  obtain ⟨h, hh, eh⟩ := hs
  exact ⟨g * h, max4Subgroup.mul_mem hg hh, eval_mul eg eh hc⟩

theorem InMax4.inv {rs ss : Vector ℕ 112}
    (hr : InMax4 rs) (hc : packedMul rs ss = packedOne) : InMax4 ss := by
  obtain ⟨g, hg, eg⟩ := hr
  exact ⟨g⁻¹, max4Subgroup.inv_mem hg, eval_inv eg hc⟩

theorem InMax4.mem {rs : Vector ℕ 112} (hr : InMax4 rs) {g : Model}
    (hg : toMatrix g = decodeRows rs) : g ∈ max4Subgroup := by
  obtain ⟨h, hh, eh⟩ := hr
  exact (toMatrix_injective (hg.trans eh.symm)).symm ▸ hh

/-- A full matrix identity transports actual max4 membership by conjugation. -/
theorem conjugate_mem {g e : Model} {gr er mr zr : Vector ℕ 112}
    (eg : toMatrix g = decodeRows gr) (ee : toMatrix e = decodeRows er)
    (hm : InMax4 mr) (h₁ : packedMul mr gr = zr) (h₂ : packedMul gr er = zr) :
    e ∈ max4Subgroup.map (MulAut.conj g⁻¹).toMonoidHom := by
  obtain ⟨m, hm, em⟩ := hm
  have he : m * g = g * e := by
    apply toMatrix_injective
    exact (eval_mul em eg h₁).trans (eval_mul eg ee h₂).symm
  refine ⟨m, hm, ?_⟩
  change g⁻¹ * m * (g⁻¹)⁻¹ = e
  rw [inv_inv, mul_assoc, he, inv_mul_cancel_left]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.AmbientLineCertificates
