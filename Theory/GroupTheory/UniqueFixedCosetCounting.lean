module
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Theory.GroupTheory.ConjugacyOrderCensus
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring

/-!
# Fixed cosets from commuting-class incidence counts

Double counting commuting pairs in two conjugacy classes balances the two
centralizer fibers. Separately, a conjugation-invariant set whose members
each fix a coset has unique fixed cosets when its total incidence count
equals its cardinality. These finite counting arguments implement the
orbit comparison in Aschbacher--Smith F.4.42, printed p.295
(`refs/quasithin.pdf`), without choosing orbit representatives.
-/

public noncomputable section
open Subgroup
namespace UniqueFixedCoset
variable {G : Type*} [Group G]

private theorem fixed_iff' (X : Subgroup G) (a g : G) :
    a • (QuotientGroup.mk g : G ⧸ X) = QuotientGroup.mk g ↔ g⁻¹*a*g ∈ X := by
  rw [MulAction.Quotient.smul_mk,QuotientGroup.eq]
  simpa only [smul_eq_mul,mul_inv_rev,inv_inv,mul_assoc] using
    X.inv_mem_iff (x := g⁻¹*a*g)

private def fixedFiberEquiv (X : Subgroup G) (p : G → Prop)
    (hp : ∀ g a, p (g*a*g⁻¹) ↔ p a) (g : G) :
    {a : X // p a.val} ≃ {a : G // p a ∧
      a • (QuotientGroup.mk g : G ⧸ X) = QuotientGroup.mk g} where
  toFun a := ⟨g*a.val.val*g⁻¹,(hp g a.val.val).mpr a.property,
    (fixed_iff' X _ g).mpr (by simp [mul_assoc])⟩
  invFun a := ⟨⟨g⁻¹*a.val*g,(fixed_iff' X _ g).mp a.property.2⟩,
    (hp g⁻¹ a.val).mpr a.property.1 |> fun h => by simpa only [inv_inv] using h⟩
  left_inv a := by
    apply Subtype.ext
    apply Subtype.ext
    simp [mul_assoc]
  right_inv a := by
    apply Subtype.ext
    simp [mul_assoc]

/-- If every member of a conjugation-invariant set fixes a coset and the
total fixed incidence equals the size of that set, each fixes exactly one. -/
theorem unique_of_class_count [Finite G] (X : Subgroup G) (p : G → Prop)
    (hp : ∀ g a, p (g*a*g⁻¹) ↔ p a)
    (hex : ∀ a, p a → ∃ q : G ⧸ X, a • q = q)
    (hcard : Nat.card {a : G // p a} * Nat.card X =
      Nat.card G * Nat.card {a : X // p a.val}) :
    ∀ a, p a → ∃! q : G ⧸ X, a • q = q := by
  classical
  let A := {a : G // p a}
  let I := Σ q : G ⧸ X, {a : G // p a ∧ a • q = q}
  let : Fintype (G ⧸ X) := Fintype.ofFinite _
  have hq (q : G ⧸ X) : Nat.card {a : G // p a ∧ a • q = q} =
      Nat.card {a : X // p a.val} := by
    refine Quotient.inductionOn' q ?_
    intro g
    exact (Nat.card_congr (fixedFiberEquiv X p hp g)).symm
  have hI : Nat.card I = X.index * Nat.card {a : X // p a.val} := by
    rw [Nat.card_sigma]
    simp only [hq,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [←Nat.card_eq_fintype_card]
    rfl
  have hIA : Nat.card I = Nat.card A := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := X))
    rw [hI]
    change _ = Nat.card {a : G // p a} * Nat.card X
    rw [hcard,←X.card_mul_index]
    ring
  let f : I → A := fun s => ⟨s.2.val,s.2.property.1⟩
  have hsurj : Function.Surjective f := by
    intro a
    obtain ⟨q,hq⟩ := hex a.val a.property
    exact ⟨⟨q,⟨a.val,a.property,hq⟩⟩,rfl⟩
  have hinj : Function.Injective f :=
    (Function.Surjective.bijective_of_nat_card_le hsurj hIA.le).1
  intro a ha
  obtain ⟨q,hq⟩ := hex a ha
  refine ⟨q,hq,?_⟩
  intro r hr
  have he : (⟨r,⟨a,ha,hr⟩⟩ : I) = ⟨q,⟨a,ha,hq⟩⟩ := hinj rfl
  exact congrArg Sigma.fst he

end UniqueFixedCoset

namespace CommutingClassIncidence
variable {G : Type*} [Group G]
abbrev Fiber (x y : G) := {a : centralizer ({x} : Set G) // IsConj y a.val}
private abbrev Pairs (x y : G) :=
  {p : G × G // IsConj x p.1 ∧ IsConj y p.2 ∧ Commute p.1 p.2}

private theorem conj_iff (g x a : G) : IsConj x (MulAut.conj g a) ↔ IsConj x a := by
  have h : IsConj a (MulAut.conj g a) := isConj_iff.mpr ⟨g,rfl⟩
  exact ⟨fun h' => h'.trans h.symm,fun h' => h'.trans h⟩

private def fiberConj (x y g : G) : Fiber x y ≃ Fiber (MulAut.conj g x) y where
  toFun a := ⟨⟨MulAut.conj g a.val.val,mem_centralizer_singleton_iff.mpr (by
    have h := congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp a.val.property)
    simpa only [map_mul] using h)⟩,(conj_iff g y _).mpr a.property⟩
  invFun a := ⟨⟨(MulAut.conj g).symm a.val.val,mem_centralizer_singleton_iff.mpr (by
    apply (MulAut.conj g).injective
    simpa only [map_mul,MulEquiv.apply_symm_apply] using
      mem_centralizer_singleton_iff.mp a.val.property)⟩,by
    have h := (conj_iff g y ((MulAut.conj g).symm a.val.val)).mp
      (by simpa only [MulEquiv.apply_symm_apply] using a.property)
    exact h⟩
  left_inv a := by apply Subtype.ext; apply Subtype.ext; exact (MulAut.conj g).symm_apply_apply _
  right_inv a := by apply Subtype.ext; apply Subtype.ext; exact (MulAut.conj g).apply_symm_apply _

private def pairsEquiv (x y : G) :
    (Σ a : {a : G // IsConj x a}, Fiber a.val y) ≃ Pairs x y where
  toFun p := ⟨(p.1.val,p.2.val.val),p.1.property,p.2.property,
    (mem_centralizer_singleton_iff.mp p.2.val.property).symm⟩
  invFun p := ⟨⟨p.val.1,p.property.1⟩,⟨⟨p.val.2,
    mem_centralizer_singleton_iff.mpr p.property.2.2.symm.eq⟩,p.property.2.1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem pairs_card [Finite G] (x y : G) :
    Nat.card (Pairs x y) = Nat.card {a : G // IsConj x a} * Nat.card (Fiber x y) := by
  classical
  let : Fintype {a : G // IsConj x a} := Fintype.ofFinite _
  rw [←Nat.card_congr (pairsEquiv x y),Nat.card_sigma]
  have hf (a : {a : G // IsConj x a}) : Nat.card (Fiber a.val y) = Nat.card (Fiber x y) := by
    obtain ⟨g,hg⟩ := isConj_iff.mp a.property
    rw [←hg]
    exact (Nat.card_congr (fiberConj x y g)).symm
  simp only [hf,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,
    Nat.cast_id]

private def swap (x y : G) : Pairs x y ≃ Pairs y x where
  toFun p := ⟨p.val.swap,p.property.2.1,p.property.1,p.property.2.2.symm⟩
  invFun p := ⟨p.val.swap,p.property.2.1,p.property.1,p.property.2.2.symm⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Double counting commuting conjugate pairs exchanges the two centralizer fibers. -/
theorem balance [Finite G] (x y : G) :
    Nat.card (centralizer ({x} : Set G)) * Nat.card (Fiber y x) =
      Nat.card (centralizer ({y} : Set G)) * Nat.card (Fiber x y) := by
  have he := Nat.card_congr (swap x y)
  rw [pairs_card,pairs_card] at he
  have hx : Nat.card {a : G // IsConj x a} * Nat.card (centralizer ({x} : Set G)) =
      Nat.card G := ConjClasses.nat_card_carrier_mul_card_centralizer x
  have hy : Nat.card {a : G // IsConj y a} * Nat.card (centralizer ({y} : Set G)) =
      Nat.card G := ConjClasses.nat_card_carrier_mul_card_centralizer y
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := G))
  calc
    _ = (Nat.card {a : G // IsConj y a} * Nat.card (Fiber y x)) *
        (Nat.card (centralizer ({x} : Set G)) * Nat.card (centralizer ({y} : Set G))) := by
      rw [←hy]; ring
    _ = (Nat.card {a : G // IsConj x a} * Nat.card (Fiber x y)) *
        (Nat.card (centralizer ({x} : Set G)) * Nat.card (centralizer ({y} : Set G))) := by rw [he]
    _ = _ := by rw [←hx]; ring

end CommutingClassIncidence
