module
public import Stellmacher.ElementaryAbelianMaxFamilyMap
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Normalizer indices from maximum elementary families

The cosets of the relative normalizer of Q inject into any invariant
maximum elementary family containing Q, by conjugation. A cardinality
bound therefore bounds the index. Equality makes the whole family a single
orbit, retaining the actual ambient conjugating elements.

Source application: Aschbacher–Smith C.6.4, printed pp.168–169, where this
counts the conjugates of Q in an elementary-by-dihedral overgroup.
-/

public noncomputable section
open Subgroup Stellmacher
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem exists_coset_family_embedding (N M Q : Subgroup G)
    (hNM : N ≤ normalizer (M : Set G)) (hQ : Q ∈ elementaryAbelianMaxSubgroups M) :
    ∃ f : (N ⧸ (normalizer (Q : Set G)).subgroupOf N) ↪
      {A : Subgroup G // A ∈ elementaryAbelianMaxSubgroups M},
      ∀ n : N, (f (QuotientGroup.mk n)).val = Q.map (MulAut.conj (n : G)).toMonoidHom := by
  let f : N ⧸ (normalizer (Q : Set G)).subgroupOf N →
      {A : Subgroup G // A ∈ elementaryAbelianMaxSubgroups M} :=
    Quotient.lift (fun n : N => ⟨Q.map (MulAut.conj (n : G)).toMonoidHom,by
      have hh := (maxFamily_map_injective_iff (MulAut.conj (n : G)).toMonoidHom
        (MulAut.conj (n : G)).injective M Q).mpr hQ
      have hfix : M.map (MulAut.conj (n : G)).toMonoidHom = M :=
        mem_normalizer_iff_map_conj_eq.mp (hNM n.property)
      rwa [hfix] at hh⟩) (by
        intro a b hab
        apply Subtype.ext
        have hn : (a : G)⁻¹ * b ∈ normalizer (Q : Set G) := (QuotientGroup.leftRel_apply (s := (normalizer (Q : Set G)).subgroupOf N)).mp hab
        have he : Q.map (MulAut.conj ((a : G)⁻¹ * b)).toMonoidHom = Q :=
          mem_normalizer_iff_map_conj_eq.mp hn
        have he' := congrArg (fun A : Subgroup G => A.map (MulAut.conj (a : G)).toMonoidHom) he
        rw [map_map] at he'
        have hc : (MulAut.conj (a : G)).toMonoidHom.comp
            (MulAut.conj ((a : G)⁻¹ * b)).toMonoidHom = (MulAut.conj (b : G)).toMonoidHom := by
          ext x
          simp [MulAut.conj_apply,mul_assoc]
        rw [hc] at he'
        exact he'.symm)
  have hf : Function.Injective f := by
    intro a b hab
    induction a using Quotient.inductionOn with | h a =>
      induction b using Quotient.inductionOn with | h b =>
        apply Quotient.sound
        apply QuotientGroup.leftRel_apply.mpr
        change (a : G)⁻¹ * b ∈ normalizer (Q : Set G)
        apply mem_normalizer_iff_map_conj_eq.mpr
        have he : Q.map (MulAut.conj (a : G)).toMonoidHom =
            Q.map (MulAut.conj (b : G)).toMonoidHom := congrArg Subtype.val hab
        have he' := congrArg (fun A : Subgroup G => A.map (MulAut.conj (a : G)⁻¹).toMonoidHom) he
        rw [map_map,map_map] at he'
        have hc : (MulAut.conj (a : G)⁻¹).toMonoidHom.comp
            (MulAut.conj (a : G)).toMonoidHom = MonoidHom.id G := by
          ext x
          simp [MulAut.conj_apply,mul_assoc]
        have hc' : (MulAut.conj (a : G)⁻¹).toMonoidHom.comp
            (MulAut.conj (b : G)).toMonoidHom =
            (MulAut.conj ((a : G)⁻¹ * b)).toMonoidHom := by
          ext x
          simp [MulAut.conj_apply,mul_assoc]
        rw [hc,hc',map_id] at he'
        exact he'.symm
  exact ⟨⟨f,hf⟩,fun _ => rfl⟩


/-- The normalizer index is bounded by the invariant elementary family. -/
theorem normalizer_index_le_max_family_card (N M Q : Subgroup G)
    (hNM : N ≤ normalizer (M : Set G)) (hQ : Q ∈ elementaryAbelianMaxSubgroups M) :
    (normalizer (Q : Set G)).relIndex N ≤
      Nat.card {A : Subgroup G // A ∈ elementaryAbelianMaxSubgroups M} := by
  obtain ⟨f,_⟩ := exists_coset_family_embedding N M Q hNM hQ
  exact Nat.card_le_card_of_injective f f.injective

/-- Equality in the orbit bound makes the maximum elementary family a
single orbit, with its actual ambient conjugating elements. -/
theorem max_family_conjugate_of_card_le_index (N M Q : Subgroup G)
    (hNM : N ≤ normalizer (M : Set G)) (hQ : Q ∈ elementaryAbelianMaxSubgroups M)
    (hcard : Nat.card {A : Subgroup G // A ∈ elementaryAbelianMaxSubgroups M} ≤
      (normalizer (Q : Set G)).relIndex N) :
    ∀ A ∈ elementaryAbelianMaxSubgroups M,
      ∃ n ∈ N, Q.map (MulAut.conj n).toMonoidHom = A := by
  obtain ⟨f,hf⟩ := exists_coset_family_embedding N M Q hNM hQ
  have hsurj := (f.injective.bijective_of_nat_card_le hcard).2
  intro A hA
  obtain ⟨q,hq⟩ := hsurj ⟨A,hA⟩
  induction q using Quotient.inductionOn with | h n =>
    exact ⟨n,n.property,(hf n).symm.trans (congrArg Subtype.val hq)⟩

end Theory.GroupTheory
