module
public import Theory.GroupTheory.ElementaryFixedQuotientLifting
public import Mathlib.GroupTheory.Index
/-!
# Square-root fixed cardinality through an elementary kernel

A fixed quotient element lifts to a fixed group element when an involution
has a square-root fixed subgroup on its elementary binary kernel. The restricted
quotient map is therefore surjective on fixed subgroups. Its kernel is the
fixed subgroup of the original kernel, so the two square-root counts multiply.
This supplies the literal fixed Thompson-subgroup count in Aschbacher–Smith,
Lemma 2.4.12(2), printed p.532.
-/

public section
namespace Theory.GroupTheory
open Subgroup
variable {R : Type*} [Group R] [Finite R]
theorem fixed_card_square_of_elementary_kernel
    (N : Subgroup R) [N.Normal] [IsElementaryAbelian 2 N]
    (α : R →* R) (hα : Function.Involutive α) (hN : ∀ x ∈ N, α x ∈ N)
    (hcN : Nat.card ((α.restrict hN).eqLocus (MonoidHom.id N)) ^ 2 = Nat.card N)
    (hcQ : Nat.card ((QuotientGroup.map N N α hN).eqLocus (MonoidHom.id (R ⧸ N))) ^ 2 = Nat.card (R ⧸ N)) :
    Nat.card (α.eqLocus (MonoidHom.id R)) ^ 2 = Nat.card R := by
  let A := α.eqLocus (MonoidHom.id R)
  let B := (QuotientGroup.map N N α hN).eqLocus (MonoidHom.id (R ⧸ N))
  let C := (α.restrict hN).eqLocus (MonoidHom.id N)
  let f : A →* B :=
    { toFun := fun a=>⟨QuotientGroup.mk' N a,by
        change QuotientGroup.mk' N (α a)=QuotientGroup.mk' N a
        exact congrArg (QuotientGroup.mk' N) a.property⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b=>Subtype.ext (map_mul (QuotientGroup.mk' N) (a:R) (b:R)) }
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨a,ha,he⟩ := exists_fixed_quotient_lift_of_elementary_kernel N α hα hN hcN b b.property
    exact ⟨⟨a,ha⟩,Subtype.ext he⟩
  let e : f.ker ≃ C :=
    { toFun := fun a=>⟨⟨a.val.val,(QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val a.property)⟩,
        Subtype.ext a.val.property⟩
      invFun := fun a=>⟨⟨a.val.val,congrArg Subtype.val a.property⟩,
        Subtype.ext ((QuotientGroup.eq_one_iff _).mpr a.val.property)⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  have hc : Nat.card A=Nat.card B*Nat.card C := by
    rw [←Nat.card_congr e]
    calc
      Nat.card A = Nat.card f.range * Nat.card f.ker := by
        rw [←Subgroup.index_ker,Subgroup.index_mul_card]
      _ = Nat.card B * Nat.card f.ker := by
        rw [MonoidHom.range_eq_top.mpr hf,card_top]
  change Nat.card A^2=Nat.card R
  rw [hc,mul_pow,hcN,hcQ]
  exact card_eq_card_quotient_mul_card_subgroup N |>.symm
end Theory.GroupTheory
