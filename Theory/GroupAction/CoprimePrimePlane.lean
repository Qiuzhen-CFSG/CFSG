module
public import Theory.GroupAction.HomomorphismFixedKernel
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Nonabelian coprime actions on an elementary prime plane

A proper nontrivial invariant subgroup of a plane and its quotient both
have prime order. Their automorphism groups are abelian. The kernel of the
two actions is a p-group, since it fixes both layers; coprimeness kills that
kernel. Thus a reducible coprime plane action is abelian.

This is the coprime restriction needed when applying the nonabelian-image
argument of Aschbacher--Smith 13.1.12(1), printed p.872.
-/

public section
open Subgroup
namespace PrimePlaneAction
variable {p : ℕ} [Fact p.Prime]
variable {V : Type*} [Group V] [Finite V] [IsElementaryAbelian p V]

/-- A nonabelian prime-to-p group of automorphisms of an elementary plane
has no proper nontrivial invariant subgroup. -/
theorem irreducible_of_coprime_noncommutative
    (hc : Nat.card V = p ^ 2) (H : Subgroup (MulAut V))
    (hcop : Nat.Coprime p (Nat.card H)) (hnc : ¬ IsMulCommutative H)
    (A : Subgroup V) (hA : ∀ g : H, ∀ x ∈ A, (g : MulAut V) x ∈ A) :
    A = ⊥ ∨ A = ⊤ := by
  have hd : Nat.card A ∣ p ^ 2 := hc ▸ A.card_subgroup_dvd_card
  obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hd
  interval_cases k
  · exact Or.inl (A.eq_bot_of_card_eq (by simpa using he))
  · have hcard : Nat.card A = p := by simpa using he
    let : IsCyclic A := isCyclic_of_prime_card hcard
    let φ : H →* MulAut A := {
      toFun := fun g => {
        toFun := fun x => ⟨(g : MulAut V) x,hA g x x.property⟩
        invFun := fun x => ⟨(g⁻¹ : H).val x,hA g⁻¹ x x.property⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun x => Subtype.ext (by simp)
        map_mul' := fun x y => Subtype.ext (map_mul (g : MulAut V) (x : V) (y : V)) }
      map_one' := by ext x; rfl
      map_mul' := by intro g h; ext x; rfl }
    let : A.Normal := inferInstance
    have hmap (g : H) : A.map (g : MulAut V).toMonoidHom = A := by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩; exact hA g x hx
      · intro x hx
        exact ⟨(g⁻¹ : H).val x,hA g⁻¹ x hx,by simp⟩
    let ψ : H →* MulAut (V ⧸ A) := {
      toFun := fun g => QuotientGroup.congr A A (g : MulAut V) (hmap g)
      map_one' := by
        ext q
        obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective A q
        rfl
      map_mul' := by
        intro g h
        ext q
        obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective A q
        rfl }
    have hquot : Nat.card (V ⧸ A) = p := by
      have hh := A.index_mul_card
      change Nat.card (V ⧸ A) * Nat.card A = Nat.card V at hh
      rw [hcard,hc,pow_two] at hh
      exact mul_right_cancel₀ (Fact.out : p.Prime).ne_zero hh
    let : IsCyclic (V ⧸ A) := isCyclic_of_prime_card hquot
    let f := φ.prod ψ
    let α := H.subtype.comp f.ker.subtype
    have hα : Function.Injective α := H.subtype_injective.comp f.ker.subtype_injective
    have hpker : IsPGroup p α.ker := by
      rw [(MonoidHom.ker_eq_bot_iff α).mpr hα]
      exact IsPGroup.of_card (n := 0) (by simp)
    have hK : IsPGroup p f.ker := by
      apply MonoidHom.isPGroup_of_fixes_kernel_and_quotient (QuotientGroup.mk' A)
        (by rw [QuotientGroup.ker_mk']; exact IsPGroup.of_card (n := 1) (by simpa using hcard))
        α hpker
      · intro a x
        have ha : ψ a = 1 := congrArg Prod.snd a.property
        exact congrArg (fun b : MulAut (V ⧸ A) => b (QuotientGroup.mk' A x)) ha
      · intro a x
        have hx : (x : V) ∈ A := by simpa using x.property
        have ha : φ a = 1 := congrArg Prod.fst a.property
        exact congrArg (fun b : MulAut A => (b ⟨x,hx⟩ : V)) ha
    have hKcard : Nat.card f.ker = 1 := by
      obtain ⟨n,hn⟩ := hK.exists_card_eq
      apply Nat.eq_one_of_dvd_coprimes (hcop.pow_left n)
      · exact hn ▸ dvd_refl _
      · exact f.ker.card_subgroup_dvd_card
    have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp
      (f.ker.eq_bot_of_card_eq hKcard)
    exfalso
    apply hnc
    apply IsMulCommutative.of_comm
    intro g h
    apply hf
    apply Prod.ext
    · apply (IsCyclic.mulAutMulEquiv A).injective
      change (IsCyclic.mulAutMulEquiv A) (φ (g*h)) =
        (IsCyclic.mulAutMulEquiv A) (φ (h*g))
      simp only [map_mul]
      exact mul_comm _ _
    · apply (IsCyclic.mulAutMulEquiv (V ⧸ A)).injective
      change (IsCyclic.mulAutMulEquiv (V ⧸ A)) (ψ (g*h)) =
        (IsCyclic.mulAutMulEquiv (V ⧸ A)) (ψ (h*g))
      simp only [map_mul]
      exact mul_comm _ _
  · exact Or.inr (A.eq_top_of_card_eq (he.trans hc.symm))
end PrimePlaneAction
