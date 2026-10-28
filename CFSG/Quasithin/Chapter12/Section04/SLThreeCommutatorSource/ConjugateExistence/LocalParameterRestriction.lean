module
public import Theory.Representation.SubmoduleCopies
public import Theory.Representation.Quotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearLayer
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.ElementaryAbelian.VectorSpace

/-!
# Restricting the marked A₅ module sum

A nonzero normalized subgroup of a sum of one or two A₅ modules is again
one or two copies. Apply the finite-copy restriction theorem to the literal
subgroup inclusion and its conjugation action. The quotient K/O₂(K) and
its common marking are retained throughout.

This is the restriction needed in 12.2.7(3i) and 12.3.2, printed pp.797,807;
the earlier source theorem producing the whole sum remains independent.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source
variable {G : Type*} [Group G] {L V W : Subgroup G}

private def subgroupAction (hn : L ≤ normalizer (V : Set G))
    [IsElementaryAbelian 2 V] : Representation (ZMod 2) L (Additive V) where
  toFun l := (V.normalizerMonoidHom (inclusion hn l)).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    rw [map_one,map_one]
    rfl
  map_mul' a b := by
    rw [map_mul,map_mul]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem restrict_copies {m : ℕ} (hVW : V ≤ W)
    (hn : L ≤ normalizer (V : Set G)) (hV : V ≠ ⊥)
    [IsElementaryAbelian 2 V]
    (hm : IsConjugationModel L W (a5Copies m)) :
    ∃ n : ℕ, 0 < n ∧ n ≤ m ∧ IsConjugationModel L V (a5Copies n) := by
  obtain ⟨a,b,hb⟩ := hm
  let q := a.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let σ := a5Module.comp q
  let : IsIrreducible σ := (irreducible_comp_surjective_iff q
    (a.surjective.comp (QuotientGroup.mk'_surjective _)) a5Module).mpr
      (BinaryPermutation.alternatingNatural_isIrreducible (by decide))
  let τ := subgroupAction hn
  let c : V →* Multiplicative (Fin m → BinaryPermutation.natural (Fin 5)) :=
    b.toMonoidHom.comp (inclusion hVW)
  let cA : Additive V →+ (Fin m → BinaryPermutation.natural (Fin 5)) := c.toAdditive
  let f : Additive V →ₗ[ZMod 2] (Fin m → BinaryPermutation.natural (Fin 5)) :=
    { cA with map_smul' := ZMod.map_smul cA }
  have hf : Function.Injective f := b.injective.comp (inclusion_injective hVW)
  have ha (l : L) (v : Additive V) (i : Fin m) :
      f (τ l v) i = σ l (f v i) := by
    apply congrFun (a := i)
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    apply Subtype.ext
    change ((b.symm (b (inclusion hVW ((τ l v).toMul)))) : G) = _
    rw [b.symm_apply_apply]
    exact (hb l (inclusion hVW v.toMul)).symm
  obtain ⟨n,hnm,e,he⟩ := Representation.coordinates_of_embedding_copies τ σ f hf ha
  have hn0 : 0 < n := by
    by_contra hn0
    have hnzero : n = 0 := by omega
    subst n
    let : Nontrivial V := (Subgroup.nontrivial_iff_ne_bot V).mpr hV
    exact not_subsingleton (Additive V) e.injective.subsingleton
  let d : V ≃* Multiplicative (Fin n → BinaryPermutation.natural (Fin 5)) := {
    toFun v := Multiplicative.ofAdd (e (Additive.ofMul v))
    invFun w := (e.symm w.toAdd).toMul
    left_inv v := e.symm_apply_apply (Additive.ofMul v)
    right_inv w := e.apply_symm_apply w.toAdd
    map_mul' v w := e.map_add (Additive.ofMul v) (Additive.ofMul w) }
  refine ⟨n,hn0,hnm,a,d,?_⟩
  intro l v
  have hh : e (τ l (Additive.ofMul v)) =
      a5Copies n (a (QuotientGroup.mk' (pCore 2 L) l)) (e (Additive.ofMul v)) :=
    funext (he l (Additive.ofMul v))
  change ((e.symm (a5Copies n (a (QuotientGroup.mk' (pCore 2 L) l))
    (e (Additive.ofMul v)))).toMul : G) = _
  rw [←hh,e.symm_apply_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A normalized nonzero subgroup of one or two A₅ copies is again one or two
copies, retaining the original L/O₂(L) marking on every summand. -/
theorem IsOneOrTwoA5Modules.of_le (hm : IsOneOrTwoA5Modules L W)
    (hVW : V ≤ W) (hn : L ≤ normalizer (V : Set G)) (hV : V ≠ ⊥)
    [IsElementaryAbelian 2 V] : IsOneOrTwoA5Modules L V := by
  have hm' : ∃ m : ℕ, m ≤ 2 ∧ IsConjugationModel L W (a5Copies m) := by
    rcases hm with hm | hm
    · let e : BinaryPermutation.natural (Fin 5) ≃ₗ[ZMod 2]
          (Fin 1 → BinaryPermutation.natural (Fin 5)) :=
        (LinearEquiv.funUnique (Fin 1) (ZMod 2) (BinaryPermutation.natural (Fin 5))).symm
      exact ⟨1,by decide,hm.of_linearEquiv e (fun _ _ => rfl)⟩
    · exact ⟨2,le_rfl,hm.of_linearEquiv
        (LinearEquiv.finTwoArrow (ZMod 2) (BinaryPermutation.natural (Fin 5))).symm
        (fun _ _ => by funext i; fin_cases i <;> rfl)⟩
  obtain ⟨m,hm2,hm⟩ := hm'
  obtain ⟨n,hn0,hnm,hn⟩ := restrict_copies hVW hn hV hm
  exact oneOrTwoA5Modules_of_copies hn0 (hnm.trans hm2) hn
end CFSG.Quasithin.Chapter6.Source
