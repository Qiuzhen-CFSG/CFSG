module
public import Theory.GroupTheory.PGroup.ExtraspecialThreeReducibleGenerators
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupAction.QuotientConjugation
/-!
# Small two-subgroups from a stable extraspecial subgroup of order nine

A coprime faithful actor preserving a line in the Frattini quotient of an
extraspecial group of order 27 and exponent three preserves two generating
cubics. Restriction embeds the actor in the product of their automorphism
groups, so it is elementary abelian of order at most four.

A stable subgroup of order nine containing the center gives such a line.
In particular, a normal subgroup meeting a self-centralizing extraspecial
subgroup in order nine forces this bound on every ambient two-subgroup.
All intersections and conjugation actions retain the original inclusions.

Source: Aschbacher–Smith, the coprime reducible action argument in 15.1.2,
printed p.1086. The application here is the order-four chief interval in
the remaining point-central branch of 14.7.20(2), printed p.1049.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace ExtraspecialSylow
variable {A P : Type*} [Group A] [Finite A] [Group P] [Finite P]
  [IsExtraspecial 3 P]

private def restrictAction (α : A →* MulAut P) (K : Subgroup P)
    (hs : ∀ a : A, ∀ x ∈ K, α a x ∈ K) : A →* MulAut K where
  toFun a := {
    toFun x := ⟨α a x,hs a x x.property⟩
    invFun x := ⟨α a⁻¹ x,hs a⁻¹ x x.property⟩
    left_inv x := by
      apply Subtype.ext
      change α a⁻¹ (α a (x : P)) = (x : P)
      rw [map_inv]
      exact (α a).symm_apply_apply x
    right_inv x := by
      apply Subtype.ext
      change α a (α a⁻¹ (x : P)) = (x : P)
      rw [map_inv]
      exact (α a).apply_symm_apply x
    map_mul' x y := by apply Subtype.ext; exact map_mul (α a) (x : P) (y : P) }
  map_one' := by ext x; exact congrArg (fun f : MulAut P => f x) α.map_one
  map_mul' a b := by ext x; exact congrArg (fun f : MulAut P => f x) (α.map_mul a b)

/-- A faithful coprime actor preserving a Frattini line embeds in the product
of the automorphism groups of two generating cubics. -/
theorem small_actor_of_stable_frattini_line
    (α : A →* MulAut P) (hf : Function.Injective α)
    (hcop : Nat.Coprime 3 (Nat.card A))
    (hP : Nat.card P = 27) (hexp : Monoid.exponent P = 3)
    (L : Subgroup (P ⧸ frattini P)) (hL0 : L ≠ ⊥) (hL1 : L ≠ ⊤)
    (hstable : ∀ a : A, ∀ x ∈ L, quotientAut (frattini P) (α a) x ∈ L) :
    IsElementaryAbelian 2 A ∧ Nat.card A ≤ 4 := by
  obtain ⟨K,R,hK,hR,_,_,hKR,hKs,hRs⟩ :=
    exists_normalized_cubic_generators α hcop hP hexp L hL0 hL1 hstable
  let f := (restrictAction α K hKs).prod (restrictAction α R hRs)
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    apply mem_bot.mpr
    apply hf
    rw [map_one]
    apply MulEquiv.ext
    intro x
    have hle : K ⊔ R ≤ (α a).toMonoidHom.eqLocus (MonoidHom.id P) := by
      refine sup_le ?_ ?_
      · intro k hk
        exact congrArg (fun j : MulAut K × MulAut R => ((j.1 ⟨k,hk⟩ : K) : P)) ha
      · intro r hr
        exact congrArg (fun j : MulAut K × MulAut R => ((j.2 ⟨r,hr⟩ : R) : P)) ha
    exact hle (hKR ▸ mem_top x)
  have hkAut : Nat.card (MulAut K) = 2 := by
    let : IsCyclic K := isCyclic_of_prime_card hK
    rw [IsCyclic.card_mulAut,hK]
    decide
  have hrAut : Nat.card (MulAut R) = 2 := by
    let : IsCyclic R := isCyclic_of_prime_card hR
    rw [IsCyclic.card_mulAut,hR]
    decide
  have hkel : IsElementaryAbelian 2 (MulAut K) := by
    let : IsMulCommutative (MulAut K) := (isCyclic_of_prime_card hkAut).isMulCommutative
    exact { exponent_dvd_p := hkAut ▸ Group.exponent_dvd_nat_card }
  have hrel : IsElementaryAbelian 2 (MulAut R) := by
    let : IsMulCommutative (MulAut R) := (isCyclic_of_prime_card hrAut).isMulCommutative
    exact { exponent_dvd_p := hrAut ▸ Group.exponent_dvd_nat_card }
  let := hkel
  let := hrel
  let : IsElementaryAbelian 2 (MulAut K × MulAut R) := {
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a => by
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hkel.exponent_dvd_p a.1
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hrel.exponent_dvd_p a.2 }
  exact ⟨IsElementaryAbelian.of_injective f hfi,
    (Nat.card_le_card_of_injective f hfi).trans_eq (by rw [Nat.card_prod,hkAut,hrAut])⟩

/-- A stable subgroup of order nine contains the center and yields a proper
line on the literal Frattini quotient. -/
theorem small_actor_of_stable_nine
    (α : A →* MulAut P) (hf : Function.Injective α)
    (hcop : Nat.Coprime 3 (Nat.card A))
    (hP : Nat.card P = 27) (hexp : Monoid.exponent P = 3)
    (N : Subgroup P) (hN : Nat.card N = 9) (hZ : center P ≤ N)
    (hstable : ∀ a : A, ∀ x ∈ N, α a x ∈ N) :
    IsElementaryAbelian 2 A ∧ Nat.card A ≤ 4 := by
  let q := QuotientGroup.mk' (frattini P)
  let L := N.map q
  have hφ : frattini P ≤ N := by rwa [IsExtraspecial.frattini_eq_center (p := 3)]
  have hpre : L.comap q = N := by
    change (N.map q).comap q = N
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hφ]
  have hL0 : L ≠ ⊥ := by
    intro he
    have hn := congrArg (Subgroup.comap q) he
    rw [hpre,MonoidHom.comap_bot,QuotientGroup.ker_mk',IsExtraspecial.frattini_eq_center (p := 3)] at hn
    have hh := congrArg (fun B : Subgroup P => Nat.card B) hn
    rw [hN,IsExtraspecial.center_order_p 3 P] at hh
    omega
  have hL1 : L ≠ ⊤ := by
    intro he
    have hn := congrArg (Subgroup.comap q) he
    rw [hpre,comap_top] at hn
    have hh := congrArg (fun B : Subgroup P => Nat.card B) hn
    rw [hN,card_top,hP] at hh
    omega
  apply small_actor_of_stable_frattini_line α hf hcop hP hexp L hL0 hL1
  rintro a _ ⟨x,hx,rfl⟩
  rw [quotientAut_apply_mk]
  exact mem_map_of_mem q (hstable a x hx)
end ExtraspecialSylow

namespace IsExtraspecial
variable {D : Type*} [Group D] [Finite D]
/-- A normal subgroup meeting a self-centralizing extraspecial residual in
order nine forces every two-subgroup to be elementary of order at most four. -/
theorem small_two_subgroup_of_normal_nine_intersection
    (P : Subgroup D) [P.Normal] [IsExtraspecial 3 P]
    (hP : Nat.card P = 27) (hexp : Monoid.exponent P = 3)
    (hC : centralizer (P : Set D) ≤ P)
    (N : Subgroup D) [N.Normal] (hN : Nat.card (N.subgroupOf P) = 9)
    (hZ : center P ≤ N.subgroupOf P) (A : Subgroup D) (hA : IsPGroup 2 A) :
    IsElementaryAbelian 2 A ∧ Nat.card A ≤ 4 := by
  let α : A →* MulAut P := (MulAut.conjNormal : D →* MulAut P).comp A.subtype
  have hf : Function.Injective α := by
    apply (MonoidHom.ker_eq_bot_iff α).mp
    apply bot_unique
    intro a ha
    have hc : (a : D) ∈ centralizer (P : Set D) := by
      rw [←MulAut.conjNormal_ker_eq_centralizer P]
      exact ha
    have hd := hA.disjoint_of_coprime (IsExtraspecial.isPGroup 3 P)
      (by decide : Nat.Coprime 2 3)
    exact Subtype.ext (mem_bot.mp (hd.le_bot ⟨a.property,hC hc⟩))
  have hcop : Nat.Coprime 3 (Nat.card A) := by
    obtain ⟨n,hn⟩ := hA.exists_card_eq
    rw [hn]
    exact (show Nat.Coprime 3 2 from by decide).pow_right n
  apply ExtraspecialSylow.small_actor_of_stable_nine α hf hcop hP hexp
    (N.subgroupOf P) hN hZ
  intro a x hx
  exact (inferInstance : N.Normal).conj_mem x hx a
end IsExtraspecial
