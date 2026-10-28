module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.Target

/-!
# Separating the cyclic-three coordinates of B.1.12

The compatible internal product makes the conjugate closure abelian. The
literal map from M to M/O₂(M) is injective on that three-group. A nonidentity
involution in one SL₂(2) factor therefore lifts to an element of M which
inverts its marked conjugate of K and fixes each prescribed distinct one.
The lift is asserted to lie in M; membership in the component is established
separately by the commutator calculation in `CyclicIntersection`.

The final lemma identifies every H-conjugate of K with a T-conjugate, using
H = K₀T and the commutativity of K₀.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.1.12–B.1.13, printed pp. 73–74 (PDF pp. 84–85).
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.ThreeConjugates
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K T : Subgroup G}

private abbrev SL := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
private theorem inverting_involution : ∃ s : SL, s ≠ 1 ∧ s ^ 2 = 1 ∧
    ∀ a : SL, a ^ 3 = 1 → s * a * s⁻¹ = a⁻¹ := by decide

namespace ThreeConjugatesConclusion
variable (d : ThreeConjugatesConclusion ρ K T)

omit [Finite G] in
include d in
private theorem closure_commutative (hcard : Nat.card K = 3) :
    IsMulCommutative (conjugateClosure K T) := by
  have (i : conjugateFamily K T) : IsMulCommutative (i : Subgroup G) := by
    obtain ⟨t, ht⟩ := i.property
    have hc : Nat.card (i : Subgroup G) = 3 := by
      rw [← ht, card_map_of_injective (MulAut.conj (t : G)).injective]
      exact hcard
    let : IsCyclic (i : Subgroup G) := isCyclic_of_prime_card hc
    infer_instance
  apply IsMulCommutative.of_comm
  intro a b
  obtain ⟨a, rfl⟩ := d.groupProduct.surjective a
  obtain ⟨b, rfl⟩ := d.groupProduct.surjective b
  rw [← map_mul, ← map_mul, mul_comm']

private theorem quotient_injective_on_closure
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3) :
    Set.InjOn (QuotientGroup.mk' (pCore 2 (mixedSubgroup ρ K T)))
      {m : mixedSubgroup ρ K T | (m : G) ∈ conjugateClosure K T} := by
  let C := conjugateClosure K T
  let M := mixedSubgroup ρ K T
  let q := QuotientGroup.mk' (pCore 2 M)
  have hi : Function.Injective (q.comp (inclusion (show C ≤ M from le_sup_right))) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro a ha
    have hd : Disjoint (C.subgroupOf M) (pCore 2 M) :=
      (conjugateClosure_isThreeGroup K T hK hcard).comap_subtype.disjoint_of_coprime
        pCore_isPGroup (by decide : Nat.Coprime 3 2)
    have hm : inclusion (show C ≤ M from le_sup_right) a ∈
        C.subgroupOf M ⊓ pCore 2 M :=
      ⟨a.property, (QuotientGroup.eq_one_iff _).mp ha⟩
    rw [hd.eq_bot] at hm
    exact Subtype.ext (congrArg (fun x : M => (x : G)) (mem_bot.mp hm))
  intro a ha b hb he
  exact Subtype.ext (congrArg (fun x : C => (x : G)) (hi (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) he))

omit [Finite G] in
private theorem quotient_factors_commute {i j : conjugateFamily K T} (hij : i ≠ j)
    (a : d.quotientFactor i) (b : d.quotientFactor j) :
    Commute (a : mixedSubgroup ρ K T ⧸ pCore 2 (mixedSubgroup ρ K T)) (b : _) := by
  classical
  let : DecidableEq (conjugateFamily K T) := Classical.decEq _
  rw [← d.quotientProduct_single i a, ← d.quotientProduct_single j b]
  simpa only [MulEquiv.coe_toMonoidHom] using (Pi.mulSingle_commute (f := fun i => d.quotientFactor i) hij a b).map
    d.quotientProduct.toMonoidHom

omit [Finite G] in
private theorem quotient_mem_factor (i : conjugateFamily K T) (k : mixedSubgroup ρ K T)
    (hk : (k : G) ∈ (i : Subgroup G)) :
    QuotientGroup.mk' (pCore 2 (mixedSubgroup ρ K T)) k ∈ d.quotientFactor i := by
  have hm : QuotientGroup.mk' (pCore 2 (mixedSubgroup ρ K T)) k ∈
      quotientConjugate ρ K T i := mem_map_of_mem _ hk
  rw [← d.oddCore i] at hm
  obtain ⟨a, _, he⟩ := hm
  exact he ▸ a.property

/-- A single quotient involution inverts one marked order-three factor and
fixes a distinct one. Its representative is required to lie only in M. -/
theorem separating_involution_lift
    (hK : (K.subgroupOf (K ⊔ T)).IsSubnormal) (hcard : Nat.card K = 3)
    (i j : conjugateFamily K T) (hij : i ≠ j) :
    ∃ m : mixedSubgroup ρ K T,
      QuotientGroup.mk' (pCore 2 (mixedSubgroup ρ K T)) m ∈ d.quotientFactor i ∧
      QuotientGroup.mk' (pCore 2 (mixedSubgroup ρ K T)) m ≠ 1 ∧
      (QuotientGroup.mk' (pCore 2 (mixedSubgroup ρ K T)) m) ^ 2 = 1 ∧
      (∀ k ∈ (i : Subgroup G), (m : G) * k * (m : G)⁻¹ = k⁻¹) ∧
      (∀ k ∈ (j : Subgroup G), (m : G) * k * (m : G)⁻¹ = k) := by
  obtain ⟨s, hsne, hs2, hs⟩ := inverting_involution
  let a : d.quotientFactor i := (d.factorModel i).symm s
  obtain ⟨m, hm⟩ := QuotientGroup.mk'_surjective (pCore 2 (mixedSubgroup ρ K T)) (a : _)
  have hnorm : K ⊔ T ≤ normalizer (conjugateClosure K T : Set G) :=
    sup_le ((le_conjugateClosure K T).trans (conjugateClosure K T).le_normalizer)
      (le_normalizer_conjugateClosure K T)
  have hmnorm := hnorm (mixedSubgroup_le ρ K T m.property)
  have hinj := quotient_injective_on_closure (ρ := ρ) hK hcard
  have hq (k : mixedSubgroup ρ K T) :
      QuotientGroup.mk' (pCore 2 (mixedSubgroup ρ K T)) (m * k * m⁻¹) =
        (a : mixedSubgroup ρ K T ⧸ pCore 2 (mixedSubgroup ρ K T)) * QuotientGroup.mk' (pCore 2 (mixedSubgroup ρ K T)) k * (a : _)⁻¹ := by
    simp only [map_mul, map_inv, hm, Subgroup.coe_inv]
  refine ⟨m, hm.symm ▸ a.property, ?_, ?_, ?_, ?_⟩
  · intro he
    apply hsne
    have ha1 : a = 1 := Subtype.ext (hm.symm.trans he)
    have := congrArg (d.factorModel i) ha1
    simpa [a] using this
  · rw [hm]
    have ha2 : a ^ 2 = 1 := (d.factorModel i).injective (by simp [a, hs2])
    exact congrArg (fun z : d.quotientFactor i =>
      (z : mixedSubgroup ρ K T ⧸ pCore 2 (mixedSubgroup ρ K T))) ha2
  · intro k hk
    let kM : mixedSubgroup ρ K T := ⟨k, (show conjugateClosure K T ≤ mixedSubgroup ρ K T
      from le_sup_right) (conjugate_le_closure K T i hk)⟩
    let b : d.quotientFactor i := ⟨_, d.quotient_mem_factor i kM hk⟩
    have hk3 : k ^ 3 = 1 := by
      obtain ⟨t, ht⟩ := i.property
      have hc : Nat.card (i : Subgroup G) = 3 := by
        rw [← ht, card_map_of_injective (MulAut.conj (t : G)).injective]
        exact hcard
      exact congrArg Subtype.val (show (⟨k, hk⟩ : (i : Subgroup G)) ^ 3 = 1 by
        rw [← hc]; exact pow_card_eq_one')
    have hb3 : b ^ 3 = 1 := by
      apply Subtype.ext
      change (QuotientGroup.mk' (pCore 2 (mixedSubgroup ρ K T)) kM) ^ 3 = 1
      rw [← map_pow]
      have : kM ^ 3 = 1 := Subtype.ext hk3
      rw [this, map_one]
    have he : a * b * a⁻¹ = b⁻¹ := (d.factorModel i).injective (by
      simpa [a] using hs (d.factorModel i b) (by rw [← map_pow, hb3, map_one]))
    have heq : m * kM * m⁻¹ = kM⁻¹ := hinj
      ((mem_normalizer_iff.mp hmnorm k).mp (conjugate_le_closure K T i hk))
      ((conjugateClosure K T).inv_mem (conjugate_le_closure K T i hk))
      (by rw [hq, map_inv]; exact congrArg Subtype.val he)
    exact congrArg Subtype.val heq
  · intro k hk
    let kM : mixedSubgroup ρ K T := ⟨k, (show conjugateClosure K T ≤ mixedSubgroup ρ K T
      from le_sup_right) (conjugate_le_closure K T j hk)⟩
    let b : d.quotientFactor j := ⟨_, d.quotient_mem_factor j kM hk⟩
    have hc := d.quotient_factors_commute hij a b
    have heq : m * kM * m⁻¹ = kM := hinj
      ((mem_normalizer_iff.mp hmnorm k).mp (conjugate_le_closure K T j hk))
      (conjugate_le_closure K T j hk)
      (by rw [hq]; exact mul_inv_eq_iff_eq_mul.mpr hc.eq)
    exact congrArg Subtype.val heq
end ThreeConjugatesConclusion
end CFSG.Quasithin.ChapterB.ThreeConjugates

namespace CFSG.Quasithin.ChapterB.ThreeConjugates.ThreeConjugatesConclusion
open Subgroup
open scoped Pointwise
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {K T : Subgroup G}
  (d : ThreeConjugatesConclusion ρ K T)
include d in
/-- The abelian conjugate closure shows that H introduces no new conjugates
beyond the actual T-orbit used to index B.1.12. -/
theorem conjugate_mem_family_of_mem_sup (hcard : Nat.card K = 3) {x : G}
    (hx : x ∈ K ⊔ T) : K.map (MulAut.conj x).toMonoidHom ∈ conjugateFamily K T := by
  let := d.closure_commutative hcard
  change x ∈ (↑(K ⊔ T) : Set G) at hx
  rw [sup_product K T] at hx
  obtain ⟨c, hc, t, ht, rfl⟩ := hx
  refine ⟨⟨t, ht⟩, ?_⟩
  have he (k : G) (hk : k ∈ K) :
      (c * t) * k * (c * t)⁻¹ = t * k * t⁻¹ := by
    have hkt : t * k * t⁻¹ ∈ conjugateClosure K T :=
      conjugate_le_closure K T ⟨_, ⟨⟨t, ht⟩, rfl⟩⟩ (mem_map_of_mem _ hk)
    have hct : c * (t * k * t⁻¹) = (t * k * t⁻¹) * c :=
      congrArg Subtype.val (mul_comm' (⟨c, hc⟩ : conjugateClosure K T) ⟨_, hkt⟩)
    calc
      (c * t) * k * (c * t)⁻¹ = c * (t * k * t⁻¹) * c⁻¹ := by group
      _ = t * k * t⁻¹ := mul_inv_eq_iff_eq_mul.mpr hct
  apply le_antisymm
  · rintro y ⟨k, hk, rfl⟩
    exact ⟨k, hk, he k hk⟩
  · rintro y ⟨k, hk, rfl⟩
    exact ⟨k, hk, (he k hk).symm⟩
end CFSG.Quasithin.ChapterB.ThreeConjugates.ThreeConjugatesConclusion
