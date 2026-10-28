module
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Tactic.Group

/-!
# Subgroup conjugacy through a common representative

If inner automorphisms carry a subgroup `R` to both `U` and `V`, another
inner automorphism carries `V` to `U`. Conjugators `p` and `q` combine as
`p * q⁻¹`; functoriality of subgroup images and the inner-automorphism
composition identity give the equality with the stated orientation.

This general group-theoretic fact is used to transport the subgroup classes
in Alperin–Brauer–Gorenstein, Chapter II, §1, Lemma 1(ii), and the joins with
the derived subgroup in the subsequent fusion analysis. It needs no
finiteness or normality assumption.
-/

namespace Subgroup
/-- Subgroups conjugate to one representative are conjugate to each other, oriented `V` to `U`. -/
public theorem conjugate_of_same_class {H : Type*} [Group H]
    (R U V : Subgroup H)
    (hU : ∃ p : H, R.map (MulAut.conj p).toMonoidHom = U)
    (hV : ∃ q : H, R.map (MulAut.conj q).toMonoidHom = V) :
    ∃ s : H, V.map (MulAut.conj s).toMonoidHom = U := by
  obtain ⟨p, hp⟩ := hU
  obtain ⟨q, hq⟩ := hV
  refine ⟨p * q⁻¹, ?_⟩
  rw [← hq, Subgroup.map_map]
  have he : (MulAut.conj (p * q⁻¹)).toMonoidHom.comp (MulAut.conj q).toMonoidHom =
      (MulAut.conj p).toMonoidHom := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply]
    group
  rw [he, hp]

end Subgroup
