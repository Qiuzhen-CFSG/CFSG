module
public import Theory.Alternating.TripleSevenLocalRank.CentralSix
public import Theory.Representation.ElementaryAbelianAction
public import Theory.Representation.Maschke
public import Mathlib.RepresentationTheory.Subrepresentation
public import Theory.GroupAction.Quotient

/-!
# Invariant cubic lifts in the actual central covers of A₆

The inverse image of a subgroup of order three in a central cubic A₆ cover
has order nine. The checked hexacode cover theorem excludes order nine,
so this inverse image is elementary abelian. Maschke supplies a complement
to the covering kernel invariant under the prescribed coprime action.
The conclusion retains the literal subgroup and its exact projection.
The final consumer handles every quasisimple odd-center A₆ cover, using
the genuine Schur center alternatives, including the trivial-center case.

Source: Aschbacher–Smith C.1.24(c), printed pp.130–131, the invariant
complement in the selected S₃ preimage. Centrality is required only inside
the covered alternating subgroup; outer actors may invert its cubic center.
-/

public section

open Subgroup
open scoped IsMulCommutative Pointwise
namespace Theory.SpecificGroups.AlternatingSix.CubicLift
variable {E A : Type*} [Group E] [Group A] [Finite E] [Finite A]

omit [Finite E] in
private theorem invariant_complement [IsElementaryAbelian 3 E]
    (ρ : A →* MulAut E) (hA : ¬ 3 ∣ Nat.card A)
    (C : Subgroup E) (hC : ∀ a : A, ∀ x ∈ C, ρ a x ∈ C) :
    ∃ M : Subgroup E, C.IsComplement' M ∧
      ∀ a : A, ∀ x ∈ M, ρ a x ∈ M := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : MulDistribMulAction A E := MulDistribMulAction.compHom E ρ
  let σ := Representation.ofElementaryAbelianAction (A := A) (G := E) (p := 3)
  let U : Subrepresentation σ := {
    toSubmodule := AddSubgroup.toZModSubmodule (n := 3) (Subgroup.toAddSubgroup C)
    apply_mem_toSubmodule := fun a x hx => hC a x.toMul hx }
  let : NeZero (Fintype.card A : ZMod 3) := ⟨by
    intro he
    apply hA
    rw [Nat.card_eq_fintype_card]
    exact (ZMod.natCast_eq_zero_iff _ _).mp he⟩
  obtain ⟨Q,hQ⟩ := MonoidAlgebra.Submodule.exists_isCompl' U.asSubmodule
  let W := Subrepresentation.ofSubmodule' Q
  let M : Subgroup E := W.toSubmodule.toAddSubgroup.toSubgroup'
  have hd : Disjoint C M := Subgroup.disjoint_def.mpr fun {x} hx hm => by
    have hz := Submodule.disjoint_def.mp hQ.disjoint (Additive.ofMul x) hx hm
    exact congrArg Additive.toMul hz
  have hp : (C : Set E) * (M : Set E) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : Additive.ofMul x ∈ U.asSubmodule ⊔ Q := by rw [hQ.sup_eq_top]; trivial
    obtain ⟨u,hu,v,hv,huv⟩ := (Submodule.mem_sup (p := U.asSubmodule) (p' := Q)).mp hx
    exact ⟨u.toMul,hu,v.toMul,hv,congrArg Additive.toMul huv⟩
  exact ⟨M,Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hd hp,
    fun a _ hx => W.apply_mem_toSubmodule a hx⟩

omit [Finite E] in
private theorem card_preimage (q : E →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) (P : Subgroup (alternatingGroup (Fin 6))) :
    Nat.card (P.comap q) = Nat.card P * Nat.card q.ker := by
  rw [card_eq_card_quotient_mul_card_subgroup (q.ker.subgroupOf (P.comap q)),
    card_quotient_subgroupOf_comap_eq (f := q) (hf := hq) (H := P)]
  rw [Nat.card_congr (subgroupOfEquivOfLe (ker_le_comap (f := q) (H := P))).toEquiv]

private theorem elementary_preimage (q : E →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) (hc : q.ker ≤ center E) (hk : Nat.card q.ker = 3)
    (P : Subgroup (alternatingGroup (Fin 6))) (hP : Nat.card P = 3) :
    IsElementaryAbelian 3 (P.comap q) := by
  have hcard : Nat.card (P.comap q) = 3^2 := by rw [card_preimage q hq P,hP,hk];norm_num
  refine { toIsMulCommutative := IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
           exponent_dvd_p := ?_ }
  rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
  intro x
  apply Subtype.ext
  apply GLS3.Chapter5.OddCentralCovers.central_six_cube_eq_one_of_ninth q hq hc hk
  exact congrArg Subtype.val (hcard ▸ pow_card_eq_one' (x := x))

private def restrictAction (ρ : A →* MulAut E) (B : Subgroup E)
    (hB : ∀ a : A, ∀ x ∈ B, ρ a x ∈ B) : A →* MulAut B where
  toFun a := {
    toFun x := ⟨ρ a x,hB a x x.property⟩
    invFun x := ⟨ρ a⁻¹ x,hB a⁻¹ x x.property⟩
    left_inv x := Subtype.ext (by
      change (ρ a⁻¹ * ρ a) (x:E)=(x:E)
      rw [←map_mul,inv_mul_cancel,map_one];rfl)
    right_inv x := Subtype.ext (by
      change (ρ a * ρ a⁻¹) (x:E)=(x:E)
      rw [←map_mul,mul_inv_cancel,map_one];rfl)
    map_mul' x y := Subtype.ext (map_mul (ρ a) (x:E) (y:E)) }
  map_one' := by ext x; exact congrArg (fun f : MulAut E => f (x:E)) ρ.map_one
  map_mul' a b := by ext x; exact congrArg (fun f : MulAut E => f (x:E)) (ρ.map_mul a b)

/-- An actual central cubic cover admits an invariant lift of the selected cubic. -/
theorem exists_invariant_lift (q : E →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) (hc : q.ker ≤ center E) (hk : Nat.card q.ker = 3)
    (ρ : A →* MulAut E) (hA : ¬ 3 ∣ Nat.card A)
    (P : Subgroup (alternatingGroup (Fin 6))) (hP : Nat.card P = 3)
    (hstable : ∀ a : A, ∀ x : E, q x ∈ P → q (ρ a x) ∈ P)
    (hker : ∀ a : A, ∀ x : E, q x = 1 → q (ρ a x) = 1) :
    ∃ M : Subgroup E, Nat.card M = 3 ∧ M.map q = P ∧ Disjoint M q.ker ∧
      ∀ a : A, ∀ x ∈ M, ρ a x ∈ M := by
  let B := P.comap q
  let C := q.ker.subgroupOf B
  let σ := restrictAction ρ B hstable
  let : IsElementaryAbelian 3 B := elementary_preimage q hq hc hk P hP
  have hC : ∀ a : A, ∀ x ∈ C, σ a x ∈ C := fun a x hx => hker a x hx
  obtain ⟨D,hD,hDi⟩ := invariant_complement σ hA C hC
  let M := D.map B.subtype
  have hCcard : Nat.card C = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe (ker_le_comap (f := q) (H := P))).toEquiv).trans hk
  have hDcard : Nat.card D = 3 := by
    have hh := hD.card_mul_card
    rw [hCcard,card_preimage q hq P,hP,hk] at hh
    omega
  refine ⟨M,(card_map_of_injective B.subtype_injective).trans hDcard,?_,?_,?_⟩
  · apply le_antisymm
    · rintro p ⟨x,⟨d,hd,rfl⟩,rfl⟩
      exact d.property
    · intro p hp
      obtain ⟨x,hx⟩ := hq p
      let b : B := ⟨x,show q x∈P by rw [hx];exact hp⟩
      have hb : b ∈ (C:Set B)*(D:Set B) := by rw [hD.mul_eq];trivial
      obtain ⟨c,hc,d,hd,hcd⟩ := hb
      refine ⟨d,mem_map_of_mem B.subtype hd,?_⟩
      have he := congrArg (fun z : B => q (z:E)) hcd
      change q ((c:E)*(d:E))=q x at he
      rw [map_mul] at he
      have hqc : q (c:E)=1 := hc
      rwa [hqc,one_mul,hx] at he
  · apply disjoint_def.mpr
    intro x hx hkx
    obtain ⟨d,hd,rfl⟩ := hx
    have he : d = 1 := disjoint_def.mp hD.disjoint hkx hd
    exact congrArg Subtype.val he
  · intro a x hx
    obtain ⟨d,hd,rfl⟩ := hx
    exact mem_map_of_mem B.subtype (hDi a d hd)

/-- Both the ordinary and triple-covered alternating groups retain the chosen cubic image. -/
theorem exists_invariant_lift_of_kernel_card (q : E →* alternatingGroup (Fin 6))
    (hq : Function.Surjective q) (hc : q.ker ≤ center E)
    (hk : Nat.card q.ker = 1 ∨ Nat.card q.ker = 3)
    (ρ : A →* MulAut E) (hA : ¬ 3 ∣ Nat.card A)
    (P : Subgroup (alternatingGroup (Fin 6))) (hP : Nat.card P = 3)
    (hstable : ∀ a : A, ∀ x : E, q x ∈ P → q (ρ a x) ∈ P)
    (hker : ∀ a : A, ∀ x : E, q x = 1 → q (ρ a x) = 1) :
    ∃ M : Subgroup E, Nat.card M = 3 ∧ M.map q = P ∧ Disjoint M q.ker ∧
      ∀ a : A, ∀ x ∈ M, ρ a x ∈ M := by
  rcases hk with hk | hk
  · refine ⟨P.comap q,?_,?_,?_,hstable⟩
    · rw [card_preimage q hq P,hP,hk,mul_one]
    · exact map_comap_eq_self_of_surjective hq P
    · rw [(eq_bot_iff_card _).mpr hk]
      exact disjoint_bot_right
  · exact exists_invariant_lift q hq hc hk ρ hA P hP hstable hker

/-- Original-cover consumer: a prescribed two-group action preserves an actual cubic complement. -/
theorem exists_invariant_lift_of_odd_center [Theory.GroupTheory.IsQuasisimple E]
    (e : E ⧸ center E ≃* alternatingGroup (Fin 6))
    (hodd : Odd (Nat.card (center E))) (ρ : A →* MulAut E) (hA : IsPGroup 2 A)
    (P : Subgroup (alternatingGroup (Fin 6))) (hP : Nat.card P = 3)
    (hstable : ∀ a : A, ∀ x : E, GLS3.Chapter5.alternatingQuotientHom e x ∈ P →
      GLS3.Chapter5.alternatingQuotientHom e (ρ a x) ∈ P) :
    ∃ M : Subgroup E, Nat.card M = 3 ∧
      M.map (GLS3.Chapter5.alternatingQuotientHom e) = P ∧
      Disjoint M (center E) ∧ ∀ a : A, ∀ x ∈ M, ρ a x ∈ M := by
  let q := GLS3.Chapter5.alternatingQuotientHom e
  have hqker : q.ker = center E := GLS3.Chapter5.alternatingQuotientHom_ker e
  have hk : Nat.card q.ker = 1 ∨ Nat.card q.ker = 3 := by
    rw [hqker]
    rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide) e hodd with h | ⟨_,h⟩
    · exact Or.inl h
    · exact Or.inr h
  have ha : ¬3 ∣ Nat.card A := by
    obtain ⟨n,hn⟩ := hA.exists_card_eq
    rw [hn]
    exact fun hd => (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hker : ∀ a : A, ∀ x : E, q x = 1 → q (ρ a x) = 1 := by
    intro a x hx
    have hxc : x ∈ center E := hqker ▸ (show x ∈ q.ker from hx)
    change ρ a x ∈ q.ker
    rw [hqker]
    apply mem_center_iff.mpr
    intro y
    obtain ⟨z,rfl⟩ := (ρ a).surjective y
    simpa only [map_mul] using congrArg (ρ a) (mem_center_iff.mp hxc z)
  obtain ⟨M,hm,hmp,hmd,hmi⟩ := exists_invariant_lift_of_kernel_card q
    (GLS3.Chapter5.alternatingQuotientHom_surjective e) (hqker ▸ le_rfl) hk ρ ha P hP hstable hker
  exact ⟨M,hm,hmp,hqker ▸ hmd,hmi⟩
end Theory.SpecificGroups.AlternatingSix.CubicLift
