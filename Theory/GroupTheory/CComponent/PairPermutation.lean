module
public import Theory.GroupTheory.CComponent.RelativeQuotientLifting

/-!
# Relative component pairs and their literal commutator supports

Conjugation in an overgroup permutes an exhaustive pair of its C-components.
If their commutator supports in an invariant subgroup differ, preserving one
support is equivalent to normalizing its component. All normalizers are
relative to the specified overgroup; no ambient normality is assumed.

Source application: Aschbacher--Smith 14.6.24(3), pp.1039--1041.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

/-- Conjugation permutes an exhaustive pair of relative C-components. -/
theorem relative_cComponent_pair_permutation
    (H K J : Subgroup G) (hKH : K ≤ H) (hJH : J ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hJ : (J.subgroupOf H).IsCComponent)
    (hall : ∀ D : Subgroup H, D.IsCComponent →
      D = K.subgroupOf H ∨ D = J.subgroupOf H) :
    ∀ x ∈ H,
      (K.map (MulAut.conj x).toMonoidHom = K ∧ J.map (MulAut.conj x).toMonoidHom = J) ∨
      (K.map (MulAut.conj x).toMonoidHom = J ∧ J.map (MulAut.conj x).toMonoidHom = K) := by
  have orbit (A : Subgroup G) (hAH : A ≤ H) (hA : (A.subgroupOf H).IsCComponent)
      (x : G) (hx : x ∈ H) :
      A.map (MulAut.conj x).toMonoidHom = K ∨ A.map (MulAut.conj x).toMonoidHom = J := by
    have hxH : H.map (MulAut.conj x).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer hx)
    have hAH' : A.map (MulAut.conj x).toMonoidHom ≤ H := hxH ▸ map_mono hAH
    have hc := IsCComponent.map_relative_equiv H A hAH hA (MulAut.conj x)
    rw [hxH] at hc
    rcases hall _ hc with he | he
    · exact Or.inl (by simpa only [map_subgroupOf_eq_of_le hAH',
        map_subgroupOf_eq_of_le hKH] using congrArg (map H.subtype) he)
    · exact Or.inr (by simpa only [map_subgroupOf_eq_of_le hAH',
        map_subgroupOf_eq_of_le hJH] using congrArg (map H.subtype) he)
  intro x hx
  rcases orbit K hKH hK x hx with hk | hk <;> rcases orbit J hJH hJ x hx with hj | hj
  · have he : K = J := map_injective (MulAut.conj x).injective (hk.trans hj.symm)
    exact Or.inl ⟨hk,hj.trans he⟩
  · exact Or.inl ⟨hk,hj⟩
  · exact Or.inr ⟨hk,hj⟩
  · have he : K = J := map_injective (MulAut.conj x).injective (hk.trans hj.symm)
    exact Or.inr ⟨hk,hj.trans he.symm⟩

/-- Distinct commutator supports detect the original component normalizers. -/
theorem normalizer_commutator_eq_of_permuted_pair
    (H U K J : Subgroup G) (hU : H ≤ normalizer (U : Set G))
    (hp : ∀ x ∈ H,
      (K.map (MulAut.conj x).toMonoidHom = K ∧ J.map (MulAut.conj x).toMonoidHom = J) ∨
      (K.map (MulAut.conj x).toMonoidHom = J ∧ J.map (MulAut.conj x).toMonoidHom = K))
    (hne : ⁅U,K⁆ ≠ ⁅U,J⁆) :
    (normalizer (K : Set G)).subgroupOf H = (normalizer ((⁅U,K⁆ : Subgroup G) : Set G)).subgroupOf H ∧
    (normalizer (J : Set G)).subgroupOf H = (normalizer ((⁅U,J⁆ : Subgroup G) : Set G)).subgroupOf H := by
  have step (A B : Subgroup G)
      (hp' : ∀ x ∈ H, A.map (MulAut.conj x).toMonoidHom = A ∨
        A.map (MulAut.conj x).toMonoidHom = B)
      (hne' : ⁅U,A⁆ ≠ ⁅U,B⁆) :
      (normalizer (A : Set G)).subgroupOf H = (normalizer ((⁅U,A⁆ : Subgroup G) : Set G)).subgroupOf H := by
    ext x
    change (x:G) ∈ normalizer (A:Set G) ↔ (x:G) ∈ normalizer ((⁅U,A⁆ : Subgroup G) : Set G)
    rw [mem_normalizer_iff_map_conj_eq,mem_normalizer_iff_map_conj_eq,
      map_commutator,mem_normalizer_iff_map_conj_eq.mp (hU x.property)]
    constructor
    · intro he; rw [he]
    · intro he
      rcases hp' x x.property with hx | hx
      · exact hx
      · change ⁅U,A.map (MulAut.conj (x:G)).toMonoidHom⁆ = ⁅U,A⁆ at he
        rw [hx] at he
        exact (hne' he.symm).elim
  exact ⟨step K J (fun x hx => (hp x hx).imp And.left And.left) hne,
    step J K (fun x hx => (hp x hx).imp And.right And.right) hne.symm⟩
end Subgroup
