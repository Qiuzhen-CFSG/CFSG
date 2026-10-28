module

public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Comparison
public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Hexacode
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage
public import Theory.Representation.HexacodeAction
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# A full-weight translation representing M₂₄ class 2B

The native Witt-design/hexacode equivalence embeds the affine sextet group
in M₂₄. The chosen full-weight word yields a fixed-point-free involution.
The certified two-class fusion theorem identifies it with the marked 2B
representative, since the 2A representative has a fixed point. Consequently
their full ambient centralizers are genuinely isomorphic.

Source: Aschbacher–Smith 16.1.5(7), printed p.1171. The coordinate and
hexacode definitions are the existing ATLAS ports with attribution and
license retained in their modules and LICENSES/ATLAS.txt.
-/

@[expose] public section

open Atlas.Codes Subgroup SemidirectProduct
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24InvolutionCentralizers
open MathieuCode

namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoB
noncomputable section

abbrev vector : Multiplicative hexacode :=
  Multiplicative.ofAdd Representation.Hexacode.fullWeightWord

def nativeAffineEquiv : SextetAffineGroup ≃* sextetStabilizer standardSextet :=
  sextetAffineEquiv.trans SextetCore.sextetEquiv.symm

def nativeEmbedding : SextetAffineGroup →* M24 :=
  (sextetStabilizer standardSextet).subtype.comp nativeAffineEquiv.toMonoidHom

theorem nativeEmbedding_injective : Function.Injective nativeEmbedding :=
  (sextetStabilizer standardSextet).subtype_injective.comp nativeAffineEquiv.injective

def translation : M24 := nativeEmbedding (inl vector)

theorem translation_coordinates (i : HexIndex) (k : Fin 4) :
    translation.val (atlasPointEquiv (i,k)) =
      atlasPointEquiv (i,rowLabel.symm (rowLabel k + vector.toAdd.val i)) := by
  change (nativeAffineEquiv (inl vector)).val.val (atlasPointEquiv (i,k)) = _
  have h := SextetCore.sextetEquiv_apply (nativeAffineEquiv (inl vector))
  have he : SextetCore.sextetEquiv (nativeAffineEquiv (inl vector)) =
      sextetTranslation vector := by
    simp only [nativeAffineEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    rfl
  rw [he] at h
  have h' := congrArg (fun p : Equiv.Perm Omega => atlasPointEquiv (p (i,k))) h
  simpa only [sextetTranslation_coordinates, Equiv.permCongr_apply,
    Equiv.symm_symm, Equiv.symm_apply_apply, Equiv.apply_symm_apply] using h'.symm

theorem vector_order : orderOf vector = 2 := by
  apply orderOf_eq_prime
  · change (Multiplicative.ofAdd Representation.Hexacode.fullWeightWord) ^ 2 = 1
    decide +kernel
  · intro h
    have h' := congrArg (fun v : Multiplicative hexacode => v.toAdd.val (hexPos 0)) h
    have hn : vector.toAdd.val (hexPos 0) ≠ 0 := by decide +kernel
    exact hn h'

theorem translation_order : orderOf translation = 2 := by
  rw [translation, orderOf_injective nativeEmbedding nativeEmbedding_injective,
    orderOf_injective (inl : Multiplicative hexacode →* SextetAffineGroup) inl_injective]
  exact vector_order

theorem translation_fixedPointFree (x : Fin 24) : translation.val x ≠ x := by
  obtain ⟨⟨i,k⟩, rfl⟩ := atlasPointEquiv.surjective x
  rw [translation_coordinates]
  intro h
  have hk := congrArg (fun p : Omega => rowLabel p.2) (atlasPointEquiv.injective h)
  have he : rowLabel k + vector.toAdd.val i = rowLabel k + 0 := by
    simpa only [rowLabel.apply_symm_apply, add_zero] using hk
  have hn : ∀ j : HexIndex, vector.toAdd.val j ≠ 0 := by decide +kernel
  exact hn i (add_left_cancel he)

theorem translation_isConj : IsConj involution2B translation := by
  rcases involution_classes translation translation_order with h | h
  · obtain ⟨g, hg⟩ := isConj_iff.mp h
    have hg' : g * involution2A = translation * g := (mul_inv_eq_iff_eq_mul).mp hg
    have he := congrArg (fun t : M24 => t.val 0) hg'
    have hf : involution2A.val 0 = 0 := by decide +kernel
    have hfix : translation.val (g.val 0) = g.val 0 := by
      simpa only [Subgroup.coe_mul, Equiv.Perm.mul_apply, hf] using he.symm
    exact (translation_fixedPointFree _ hfix).elim
  · exact h

/-- The full ambient centralizer of the chosen hexacode translation. -/
abbrev nativeCentralizer := Subgroup.centralizer ({translation} : Set M24)

/-- Conjugacy transports the literal marked centralizer, not an abstract group tag. -/
def markedCentralizerEquiv : centralizer2B ≃* nativeCentralizer := by
  let g := Classical.choose (isConj_iff.mp translation_isConj)
  have hg := Classical.choose_spec (isConj_iff.mp translation_isConj)
  exact (MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj involution2B)).symm.trans
    ((MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj involution2B)).trans
      (MulEquiv.subgroupCongr (by
        rw [MulAut.congr_conj, show MulAut.conj g involution2B = translation from hg,
          MulAut.fixedSubgroup_conj])))

end
end Sporadic.Mathieu.M24InvolutionCentralizers.TwoB
