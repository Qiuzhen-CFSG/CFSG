module
public import Theory.ElementaryAbelian.Basic
/-! # Elementary abelian groups under faithful maps
An injective homomorphism reflects commutativity and the exponent bound.
The subgroup version preserves the literal full preimage under an embedding.
Source application: the elementary lifting step in Aschbacher--Smith 2.5.7.
-/
public section
open scoped IsMulCommutative
theorem IsElementaryAbelian.of_injective {p:ℕ} {G H:Type*} [Group G] [Group H]
    [IsElementaryAbelian p H] (f:G→*H) (hf:Function.Injective f) :
    IsElementaryAbelian p G := by
  refine { toIsMulCommutative := ⟨⟨fun x y=>hf (by rw [map_mul,map_mul,mul_comm])⟩⟩, exponent_dvd_p := ?_ }
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  intro x
  apply hf
  rw [map_pow,map_one]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p p H) (f x)
theorem IsElementaryAbelian.comap_of_injective {p:ℕ} {G H:Type*} [Group G] [Group H]
    (f:G→*H) (hf:Function.Injective f) (A:Subgroup H) [IsElementaryAbelian p A] :
    IsElementaryAbelian p (A.comap f) := by
  let g:(A.comap f)→*A:=(f.comp (A.comap f).subtype).codRestrict A (fun x=>x.property)
  apply IsElementaryAbelian.of_injective g
  intro x y he
  apply Subtype.ext
  exact hf (congrArg Subtype.val he)
