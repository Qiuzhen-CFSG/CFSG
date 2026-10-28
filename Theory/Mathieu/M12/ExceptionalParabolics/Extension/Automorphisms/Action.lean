module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Automorphisms.Centralizer
public import Theory.Mathieu.M12.A5Fixer.Automorphisms.OuterIndex
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Full automorphism coverage from the marked inner model

Conjugation on the index-two inner subgroup is faithful: the centralizer of
its two literal generators in Sym(24) is trivial. The intrinsic bound
|Out(M₁₂)| ≤ 2, proved for every abstract automorphism, then forces conjugation
to cover Aut(M₁₂). Thus this is full automorphism coverage, conditional only on
an actual `InnerModel`, whose construction is separate.

Source: ATLAS M12d2G1-p24B0; Aschbacher–Smith F.1.12(I)(13).
-/

public section
namespace Sporadic.Mathieu.M12ExceptionalExtension
open Subgroup
set_option maxHeartbeats 100000

namespace InnerModel

/-- Conjugation on the actual normal inner subgroup, transported to M₁₂. -/
noncomputable def automorphismHom (m : InnerModel) : Carrier →* MulAut M12 := by
  letI : inner.Normal := normal_of_index_eq_two m.index
  exact (MulAut.congr m.equiv.symm).toMonoidHom.comp MulAut.conjNormal

/-- The transported action agrees with literal conjugation after embedding. -/
theorem embedding_automorphismHom (m : InnerModel) (g : Carrier) (x : M12) :
    m.embedding (m.automorphismHom g x) = g * m.embedding x * g⁻¹ := by
  change ((m.equiv (m.equiv.symm _)) : Carrier) = _
  rw [m.equiv.apply_symm_apply]
  rfl

/-- The inner-model embedding corresponds to the original inner automorphisms. -/
theorem automorphismHom_embedding (m : InnerModel) (g : M12) :
    m.automorphismHom (m.embedding g) = MulAut.conj g := by
  apply MulEquiv.ext
  intro x
  apply m.embedding_injective
  rw [embedding_automorphismHom]
  simp only [MulAut.conj_apply, map_mul, map_inv]

theorem automorphismHom_injective (m : InnerModel) :
    Function.Injective m.automorphismHom := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have hc (x : M12) : g * m.embedding x = m.embedding x * g := by
    have he := m.embedding_automorphismHom g x
    rw [hg] at he
    change m.embedding x = g * m.embedding x * g⁻¹ at he
    exact mul_inv_eq_iff_eq_mul.mp he.symm
  apply Subtype.ext
  apply centralizer_lifts_trivial
  · have ha : Commute g innerA := by
      simpa only [commute_iff_eq, m.embedding_originalA] using hc originalA
    exact ha.map group.subtype
  · have hb : Commute g innerB := by
      simpa only [commute_iff_eq, m.embedding_originalB] using hc originalB
    exact hb.map group.subtype

/-- The previously established outer-index bound includes all abstract automorphisms. -/
theorem card_full_automorphism_le : Nat.card (MulAut M12) ≤ 190080 := by
  have hi := M12A5Fixer.Automorphisms.outerIndexBound
  change (MulAut.innerSubgroup M12).index ≤ 2 at hi
  have hc : Nat.card (MulAut.innerSubgroup M12) ≤ 95040 := by
    rw [← m12_order]
    exact Nat.card_le_card_of_surjective
      (MulAut.conj : M12 →* MulAut M12).rangeRestrict
      (MulAut.conj : M12 →* MulAut M12).rangeRestrict_surjective
  calc
    Nat.card (MulAut M12) =
        Nat.card (MulAut.innerSubgroup M12) * (MulAut.innerSubgroup M12).index :=
      (MulAut.innerSubgroup M12).card_mul_index.symm
    _ ≤ 95040 * 2 := Nat.mul_le_mul hc hi
    _ = 190080 := rfl

/-- Conjugation by the fixed degree-24 carrier covers every automorphism of M₁₂. -/
theorem automorphismHom_surjective (m : InnerModel) :
    Function.Surjective m.automorphismHom := by
  apply (m.automorphismHom_injective.bijective_of_nat_card_le ?_).surjective
  rw [m.card_carrier]
  exact card_full_automorphism_le

/-- The full automorphism identification, for an actual marked inner model. -/
noncomputable def automorphismEquiv (m : InnerModel) : Carrier ≃* MulAut M12 :=
  MulEquiv.ofBijective m.automorphismHom
    ⟨m.automorphismHom_injective, m.automorphismHom_surjective⟩

theorem automorphismEquiv_embedding (m : InnerModel) (g : M12) :
    m.automorphismEquiv (m.embedding g) = MulAut.conj g :=
  m.automorphismHom_embedding g

end InnerModel
end Sporadic.Mathieu.M12ExceptionalExtension
