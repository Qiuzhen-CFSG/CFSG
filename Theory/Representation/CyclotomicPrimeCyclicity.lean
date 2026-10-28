module

public import Theory.Representation.NonsplitFour
public import Theory.Representation.EndFieldRep
public import Mathlib.RepresentationTheory.Maschke

/-!
# Cyclic prime-power groups in the least possible cross-characteristic degree

Let a finite r-group act faithfully on a vector space over a finite field
of order q. If the dimension is at most the multiplicative order of q modulo
r, and r is nonzero in the field, the group is cyclic. A central subgroup
of order r acts irreducibly: Maschke complements a proper invariant subspace,
and faithfulness on one summand contradicts the general linear group order.
The whole group consequently embeds in the units of the finite endomorphism
field of that central subgroup.

This is the Singer-centralizer argument used in Huppert--Blackburn,
*Finite Groups III*, XI.3.10(a). The concrete six-dimensional G₂ application
is in `G2.MultiplierOrdinary.Nondefining.CyclotomicSylow` and supplies the
twisted cyclotomic branch of Aschbacher--Smith I.1.2--I.1.4.
-/

public section
noncomputable section

namespace Representation.CyclotomicPrimeCyclicity

open scoped MonoidAlgebra

/-- A prime divisor of a general linear group requires at least the
multiplicative order of the field cardinality as its dimension. -/
theorem orderOf_le_of_dvd_card_GL {K : Type*} [Field K] [Fintype K]
    {r d : ℕ} [Fact r.Prime] (hq : ¬ r ∣ Fintype.card K)
    (hdiv : r ∣ Nat.card (GL (Fin d) K)) :
    orderOf (Fintype.card K : ZMod r) ≤ d := by
  classical
  have hr : r.Prime := Fact.out
  rw [Matrix.card_GL_field] at hdiv
  obtain ⟨i, _, hi⟩ := ((Nat.prime_iff.mp hr).dvd_finsetProd_iff _).mp hdiv
  have hle : Fintype.card K ^ (i : ℕ) ≤ Fintype.card K ^ d :=
    Nat.pow_le_pow_right (by have := Fintype.one_lt_card (α := K); omega) i.isLt.le
  have hz : (Fintype.card K : ZMod r) ^ d - (Fintype.card K : ZMod r) ^ (i : ℕ) = 0 := by
    have := (ZMod.natCast_eq_zero_iff _ r).mpr hi
    simpa only [Nat.cast_sub hle, Nat.cast_pow] using this
  have hq0 : (Fintype.card K : ZMod r) ≠ 0 :=
    fun h => hq ((ZMod.natCast_eq_zero_iff _ r).mp h)
  have hpow : (Fintype.card K : ZMod r) ^ (d - i) = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero (i : ℕ) hq0)
    calc
      (Fintype.card K : ZMod r) ^ (i : ℕ) * (Fintype.card K : ZMod r) ^ (d - i) =
          (Fintype.card K : ZMod r) ^ d := by
        rw [← pow_add, Nat.add_sub_of_le i.isLt.le]
      _ = (Fintype.card K : ZMod r) ^ (i : ℕ) * 1 := by
        simpa using sub_eq_zero.mp hz
  exact (orderOf_le_of_pow_eq_one (Nat.sub_pos_of_lt i.isLt) hpow).trans (Nat.sub_le d i)

/-- A faithful prime-order representation in the least possible degree
is irreducible. The coprime-characteristic assumption is explicit. -/
theorem irreducible_of_prime_card
    {A K V : Type*} [Group A] [Finite A] [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {r : ℕ} [Fact r.Prime] (hA : Nat.card A = r) (hrK : (r : K) ≠ 0)
    (hq : ¬ r ∣ Fintype.card K) (ρ : Representation K A V)
    (hρ : Function.Injective ρ)
    (hdim : Module.finrank K V ≤ orderOf (Fintype.card K : ZMod r)) :
    IsIrreducible ρ := by
  classical
  let : NeZero (Nat.card A : K) := ⟨by simpa only [hA] using hrK⟩
  let : Fact (Nat.card A).Prime := ⟨hA.symm ▸ Fact.out⟩
  rcases subsingleton_or_nontrivial V with hV | hV
  · let : Subsingleton A := Function.Injective.subsingleton hρ
    have : Nat.card A = 1 := Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
    have := (Fact.out : r.Prime).two_le
    omega
  refine ⟨fun U => ?_⟩
  by_cases hUbot : U = ⊥
  · exact Or.inl hUbot
  by_cases hUtop : U = ⊤
  · exact Or.inr hUtop
  exfalso
  obtain ⟨W, hUW⟩ := exists_isCompl U
  have hcompl : IsCompl U.toSubmodule W.toSubmodule := by
    rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hUW ⊢
    exact ⟨congrArg Subrepresentation.toSubmodule hUW.1,
      congrArg Subrepresentation.toSubmodule hUW.2⟩
  have hWbot : W.toSubmodule ≠ ⊥ := by
    intro h
    apply hUtop
    apply Subrepresentation.toSubmodule_injective
    change U.toSubmodule = ⊤
    simpa only [h, sup_bot_eq] using codisjoint_iff.mp hcompl.2
  have hUpos : 1 ≤ Module.finrank K U.toSubmodule :=
    Submodule.one_le_finrank_iff.mpr
      (fun h => hUbot (Subrepresentation.toSubmodule_injective h))
  have hWpos : 1 ≤ Module.finrank K W.toSubmodule :=
    Submodule.one_le_finrank_iff.mpr hWbot
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  have hUdim : Module.finrank K U.toSubmodule < orderOf (Fintype.card K : ZMod r) := by
    omega
  have hWdim : Module.finrank K W.toSubmodule < orderOf (Fintype.card K : ZMod r) := by
    omega
  let ρU := U.toRepresentation
  let ρW := W.toRepresentation
  rcases ρU.ker.eq_bot_or_eq_top_of_prime_card with hker | hker
  · have hdiv := Representation.card_dvd_card_GL_of_injective ρU
      ((MonoidHom.ker_eq_bot_iff ρU).mp hker)
    rw [hA] at hdiv
    have := orderOf_le_of_dvd_card_GL hq hdiv
    omega
  · have hfix (a : A) (u : U.toSubmodule) : ρ a (u : V) = (u : V) := by
      have ha : a ∈ ρU.ker := by rw [hker]; trivial
      exact congrArg Subtype.val (LinearMap.congr_fun (MonoidHom.mem_ker.mp ha) u)
    have hinj : Function.Injective ρW := by
      intro a b hab
      apply hρ
      ext v
      have hv : v ∈ U.toSubmodule ⊔ W.toSubmodule := by
        rw [codisjoint_iff.mp hcompl.2]
        trivial
      obtain ⟨u, hu, w, hw, huv⟩ := Submodule.mem_sup.mp hv
      rw [← huv, map_add, map_add, hfix a ⟨u, hu⟩, hfix b ⟨u, hu⟩]
      congr 1
      exact congrArg Subtype.val (LinearMap.congr_fun hab ⟨w, hw⟩)
    have hdiv := Representation.card_dvd_card_GL_of_injective ρW hinj
    rw [hA] at hdiv
    have := orderOf_le_of_dvd_card_GL hq hdiv
    omega

/-- A faithful r-group in the least possible nondefining degree embeds in
the units of the endomorphism field of a central order-r subgroup. -/
theorem isCyclic_of_minimal_degree
    {G K V : Type*} [Group G] [Finite G] [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {r : ℕ} [Fact r.Prime] (hG : IsPGroup r G) (hrK : (r : K) ≠ 0)
    (hq : ¬ r ∣ Fintype.card K) (ρ : Representation K G V)
    (hρ : Function.Injective ρ)
    (hdim : Module.finrank K V ≤ orderOf (Fintype.card K : ZMod r)) :
    IsCyclic G := by
  classical
  rcases subsingleton_or_nontrivial G with hGtriv | hGnontriv
  · infer_instance
  let := hG.center_nontrivial
  have hZp : IsPGroup r (Subgroup.center G) := hG.to_subgroup _
  have hrZ : r ∣ Nat.card (Subgroup.center G) := by
    obtain ⟨n, hn⟩ := hZp.exists_card_eq
    have hpos : 0 < n := by
      have := Finite.one_lt_card (α := Subgroup.center G)
      by_contra h
      have : n = 0 := by omega
      simp_all
    rw [hn]
    exact dvd_pow_self r hpos.ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) r hrZ
  let C : Subgroup G := Subgroup.zpowers (z : G)
  have hC : Nat.card C = r := by
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
  have hcentral : C ≤ Subgroup.center G := Subgroup.zpowers_le.mpr z.property
  let τ : Representation K C V := ρ.comp C.subtype
  let : IsIrreducible τ := irreducible_of_prime_card hC hrK hq τ
    (hρ.comp C.subtype_injective) hdim
  let φ : G →* Module.End K[C] τ.asModule :=
    (IntertwiningMap.equivAlgEnd τ).toMonoidHom.comp
      { toFun := fun g =>
          { toLinearMap := ρ g
            isIntertwining' := fun c => by
              change ρ g * ρ c.val = ρ c.val * ρ g
              rw [← map_mul, ← map_mul]
              exact congrArg ρ (Subgroup.mem_center_iff.mp (hcentral c.property) g) }
        map_one' := by
          apply IntertwiningMap.toLinearMap_injective τ τ
          exact ρ.map_one
        map_mul' := by
          intro g h
          apply IntertwiningMap.toLinearMap_injective τ τ
          exact ρ.map_mul g h }
  have hφ : Function.Injective φ := by
    intro g h he
    apply hρ
    ext v
    exact LinearMap.congr_fun he (τ.asModuleEquiv.symm v)
  exact isCyclic_of_injective φ.toHomUnits
    (fun g h he => hφ (congrArg Units.val he))

end Representation.CyclotomicPrimeCyclicity
