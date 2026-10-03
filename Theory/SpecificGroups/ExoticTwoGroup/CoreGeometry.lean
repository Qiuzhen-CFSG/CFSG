module

public import Theory.SpecificGroups.ExoticTwoGroup.CoreClassGeometry
public import Theory.SpecificGroups.ExoticTwoGroup.LocalModelPresentation
public import Mathlib.Algebra.Group.Conj
public import Mathlib.GroupTheory.Coset.Card

/-!
# Intrinsic conjugacy coverage for every exotic presentation

The concrete core calculation is transported across the marked equivalence
from the generator presentation. The equivalence identifies the square-generated
normal four and the four-generator special core, and carries elementary fours,
disjointness, centralization and conjugacy in both directions.

This constructs the coverage predicate from the presentation alone. No ambient
fusion, local-structure witness or classification theorem enters the proof.
Source: Janko–Thompson, Math. Z. 113 (1970), pp.395–396.
-/

namespace ExoticTwoGroup.Presentation

variable {P Q : Type*} [Group P] [Group Q]

/-- Intrinsic coverage is preserved by an equivalence identifying the marked
normal fours and special cores. -/
public theorem CoreFusionCover.of_equiv
    {d : ExoticTwoGroup.Presentation P} {e : ExoticTwoGroup.Presentation Q}
    (f : P ≃* Q) (hf : d.four.map f.toMonoidHom = e.four)
    (hc : d.core.map f.toMonoidHom = e.core) (he : e.CoreFusionCover) :
    d.CoreFusionCover := by
  apply CoreFusionCover.of_forall
  intro V hV hcard hd hcomm x hx ho
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 V := hV
  let V' := V.map f.toMonoidHom
  let : IsElementaryAbelian 2 V' := IsElementaryAbelian.map f.toMonoidHom
  have hcard' : Nat.card V' = 4 := by
    rw [Subgroup.card_map_of_injective f.injective, hcard]
  have hd' : Disjoint e.four V' := by
    apply Subgroup.disjoint_def.mpr
    intro y hy hz
    rw [← hf] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    obtain ⟨v, hv, huv⟩ := hz
    have hvu : v = u := f.injective huv
    subst v
    have hu1 : u = 1 := Subgroup.disjoint_def.mp hd hu hv
    simp [hu1]
  have hcomm' : V' ≤ Subgroup.centralizer (e.four : Set Q) := by
    rintro y ⟨v, hv, rfl⟩ w hw
    rw [← hf] at hw
    obtain ⟨u, hu, rfl⟩ := hw
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg f (hcomm hv u hu)
  have hx' : f x ∈ e.core := by
    rw [← hc]
    exact Subgroup.mem_map_of_mem f.toMonoidHom hx
  obtain ⟨y, hy, hxy⟩ := he.apply V' hcard' hd' hcomm' (f x) hx'
    ((f.orderOf_eq x).trans ho)
  refine ⟨f.symm y, ?_, ?_⟩
  · rcases hy with hy | hy
    · left
      rw [← hf] at hy
      obtain ⟨u, hu, rfl⟩ := hy
      simpa using hu
    · right
      obtain ⟨v, hv, rfl⟩ := hy
      simpa using hv
  · simpa only [MulEquiv.coe_toMonoidHom, f.symm_apply_apply] using f.symm.toMonoidHom.map_isConj hxy

/-- Every finite group with the exotic marked presentation has intrinsic
conjugacy coverage of its special core. -/
public theorem coreFusionCover [Finite P] (d : ExoticTwoGroup.Presentation P) :
    d.CoreFusionCover := by
  obtain ⟨e, ha, hb, hg₁, hg₂, _ht, _hz₀⟩ := LocalModel.exists_marked_equiv d
  have hfour : LocalModel.presentation.four.map e.toMonoidHom = d.four := by
    change (Subgroup.closure ({LocalModel.a ^ 2, LocalModel.b ^ 2} : Set LocalModel.Model)).map
      e.toMonoidHom = Subgroup.closure ({d.a ^ 2, d.b ^ 2} : Set P)
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom,
      map_pow, ha, hb]
  have hcore : LocalModel.presentation.core.map e.toMonoidHom = d.core := by
    change (Subgroup.closure
      ({LocalModel.a, LocalModel.b, LocalModel.g₁, LocalModel.g₂} : Set LocalModel.Model)).map
      e.toMonoidHom = Subgroup.closure ({d.a, d.b, d.g₁, d.g₂} : Set P)
    rw [MonoidHom.map_closure]
    simp only [Set.image_insert_eq, Set.image_singleton, MulEquiv.coe_toMonoidHom,
      ha, hb, hg₁, hg₂]
  have hfour' : d.four.map e.symm.toMonoidHom = LocalModel.presentation.four := by
    rw [← hfour, Subgroup.map_map]
    simp
  have hcore' : d.core.map e.symm.toMonoidHom = LocalModel.presentation.core := by
    rw [← hcore, Subgroup.map_map]
    simp
  exact CoreFusionCover.of_equiv e.symm hfour' hcore' LocalModel.CoreGeometry.coreFusionCover

end ExoticTwoGroup.Presentation
