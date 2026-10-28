module
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.Coordinates
public import Theory.GroupTheory.SubgroupConjugation
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic
/-!
# The component and index-two subgroup in the marked A₆ model

The supplied isomorphism LE ≃ S₆ × C₂ identifies L with A₆ × 1.
Normality pulls back through this isomorphism. Adjoining the marked central
involution gives exactly A₆ × C₂, so its index in LE, and in every simultaneous
conjugate, is two. Restriction to the first coordinate constructs L ≃ A₆
and identifies the actual conjugation action of LE with permutation conjugation.

These are model calculations used by the geometry in source 16.4.9(2).
They do not assert Sylow placement, conjugate overgroup containment, or any
ambient fusion statement.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192 (PDF p.1209).
-/

@[expose] public section
open Subgroup
open Equiv Equiv.Perm
namespace CFSG.Quasithin.Chapter16.Intersections.Six
variable {G : Type*} [Group G] {L : Subgroup G} {z r : G}

/-- The component is normal inside its actual marked product overgroup. -/
theorem overgroup_normalizes (M : AlternatingProductModel L z r 6) :
    AlternatingOvergroup L z r ≤ normalizer (L : Set G) := by
  have he : L.subgroupOf (AlternatingOvergroup L z r) =
      ((alternatingGroup (Fin 6)).prod (⊥ : Subgroup (Multiplicative (ZMod 2)))).comap
        M.equiv.toMonoidHom := by
    ext a
    exact M.component_iff a
  have hnormal : (L.subgroupOf (AlternatingOvergroup L z r)).Normal := by
    rw [he]
    infer_instance
  exact (normal_subgroupOf_iff_le_normalizer
    (show L ≤ AlternatingOvergroup L z r from le_sup_left.trans le_sup_left)).mp hnormal


/-- The subgroup L⟨z⟩ is precisely the inverse image of A₆ × C₂. -/
theorem component_central_model (M : AlternatingProductModel L z r 6) :
    (L ⊔ zpowers z).subgroupOf (AlternatingOvergroup L z r) =
      ((alternatingGroup (Fin 6)).prod (⊤ : Subgroup (Multiplicative (ZMod 2)))).comap
        M.equiv.toMonoidHom := by
  let H := AlternatingOvergroup L z r
  let P := ((alternatingGroup (Fin 6)).prod
    (⊤ : Subgroup (Multiplicative (ZMod 2)))).comap M.equiv.toMonoidHom
  have hL : L ≤ P.map H.subtype := by
    intro a ha
    refine ⟨⟨a, mem_sup_left (mem_sup_left ha)⟩, ?_, rfl⟩
    exact ⟨((M.component_iff _).mp ha).1, mem_top _⟩
  have hZ : zpowers z ≤ P.map H.subtype := by
    apply zpowers_le.mpr
    refine ⟨⟨z, mem_sup_right (mem_zpowers z)⟩, ?_, rfl⟩
    change (M.equiv _).1 ∈ alternatingGroup (Fin 6) ∧ _
    rw [M.central_image]
    exact ⟨one_mem _, mem_top _⟩
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb, hab⟩ := sup_le hL hZ ha
    have he : b = a := Subtype.ext hab
    exact he ▸ hb
  · intro ha
    have hp : (M.equiv a).1 ∈ alternatingGroup (Fin 6) := ha.1
    have hc : (M.equiv a).2 = 1 ∨
        (M.equiv a).2 = Multiplicative.ofAdd 1 := by
      generalize (M.equiv a).2 = c
      change ZMod 2 at c
      change c = (0 : ZMod 2) ∨ c = (1 : ZMod 2)
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with hc | hc
    · exact mem_sup_left ((M.component_iff a).mpr ⟨hp, hc⟩)
    · let zz : H := ⟨z, mem_sup_right (mem_zpowers z)⟩
      have hprod : (a * zz⁻¹ : H) ∈ L.subgroupOf H := by
        change ((a * zz⁻¹ : H) : G) ∈ L
        apply (M.component_iff _).mpr
        rw [map_mul, map_inv, M.central_image]
        simp only [Prod.fst_mul, Prod.fst_inv, inv_one, mul_one,
          Prod.snd_mul, Prod.snd_inv, hc, mul_inv_cancel]
        exact ⟨hp, trivial⟩
      have := (L ⊔ zpowers z).mul_mem (mem_sup_left hprod)
        (mem_sup_right (mem_zpowers z))
      change (a : G) ∈ L ⊔ zpowers z
      simpa [zz] using this

/-- The source index is relative to LE, not to the ambient group. -/
theorem component_central_relIndex (M : AlternatingProductModel L z r 6) :
    (L ⊔ zpowers z).relIndex (AlternatingOvergroup L z r) = 2 := by
  rw [relIndex, component_central_model M,
    index_comap_of_surjective _ M.equiv.surjective, index_prod, index_top, mul_one]
  have hc := (alternatingGroup (Fin 6)).card_mul_index
  rw [Nat.card_eq_fintype_card, card_alternatingGroup,
    Nat.card_eq_fintype_card, Fintype.card_perm] at hc
  norm_num [Nat.factorial] at hc ⊢

/-- The index-two calculation in every simultaneous conjugate. -/
theorem component_central_conj_relIndex (M : AlternatingProductModel L z r 6) (x : G) :
    ((L ⊔ zpowers z).conjBy x).relIndex ((AlternatingOvergroup L z r).conjBy x) = 2 := by
  rw [conjBy, conjBy, relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]
  exact component_central_relIndex M


/-- Restrict the product model to the original component L. -/
noncomputable def modelComponentEquiv (M : AlternatingProductModel L z r 6) :
    L ≃* alternatingGroup (Fin 6) where
  toFun a := ⟨(M.equiv ⟨a, mem_sup_left (mem_sup_left a.property)⟩).1,
    ((M.component_iff _).mp a.property).1⟩
  invFun p := ⟨(M.equiv.symm ((p : Perm (Fin 6)), 1) : G), by
    apply (M.component_iff _).mpr
    rw [M.equiv.apply_symm_apply]
    exact ⟨p.property, rfl⟩⟩
  left_inv a := by
    apply Subtype.ext
    have hs := ((M.component_iff ⟨a, mem_sup_left (mem_sup_left a.property)⟩).mp
      a.property).2
    change (M.equiv.symm ((M.equiv ⟨a, mem_sup_left (mem_sup_left a.property)⟩).1, 1) : G) = a
    rw [← hs, Prod.mk.eta, M.equiv.symm_apply_apply]
  right_inv p := by
    apply Subtype.ext
    change (M.equiv (M.equiv.symm ((p : Perm (Fin 6)), 1))).1 = p
    rw [M.equiv.apply_symm_apply]
  map_mul' a b := by
    apply Subtype.ext
    exact congrArg Prod.fst (M.equiv.map_mul
      ⟨a, mem_sup_left (mem_sup_left a.property)⟩
      ⟨b, mem_sup_left (mem_sup_left b.property)⟩)


/-- The restricted equivalence respects the actual ambient conjugation action. -/
theorem modelComponentEquiv_conjugation (M : AlternatingProductModel L z r 6)
    (a : AlternatingOvergroup L z r) (l : L) :
    (modelComponentEquiv M
      (L.normalizerMonoidHom ⟨a, overgroup_normalizes M a.property⟩ l) : Perm (Fin 6)) =
      (M.equiv a).1 * (modelComponentEquiv M l : Perm (Fin 6)) * (M.equiv a).1⁻¹ := by
  change (M.equiv (a * ⟨l, mem_sup_left (mem_sup_left l.property)⟩ * a⁻¹)).1 = _
  rw [map_mul, map_mul, map_inv]
  rfl

end CFSG.Quasithin.Chapter16.Intersections.Six
