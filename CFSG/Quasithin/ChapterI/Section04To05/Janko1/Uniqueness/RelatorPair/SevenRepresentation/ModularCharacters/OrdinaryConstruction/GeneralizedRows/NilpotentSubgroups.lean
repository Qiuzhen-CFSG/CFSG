module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Local
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.Contracts
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import Mathlib.Data.Nat.Squarefree

/-!
# Nilpotent subgroups needed for the ordinary J₁ rows

Every nilpotent subgroup of the source group is cyclic or has exponent dividing
two and order dividing eight. Odd ambient Sylow subgroups have prime order or
are trivial, while the Sylow two-subgroups are elementary abelian. The actual
Sylow direct-product theorem therefore makes every nilpotent subgroup abelian.
If such a subgroup contains an element whose square is not the identity, the
supplied class enumeration places it in a squarefree-order centralizer, forcing
cyclicity. Otherwise it embeds in an ambient Sylow two-subgroup.

Centralizer orders are transported by conjugation of the actual representatives.
The result uses the explicit `OrdinaryClassData`, without compatible power labels
or character assumptions. Simplicity and involution fusion are not needed once
this enumeration and the ambient order are supplied. The separate application
in `NilpotentSubgroups.RestrictionAssembly` discharges exactly `htypes` in
`ordinaryGeneralizedRows_of_local_restrictions`.

Source: Janko, J. Algebra 3 (1966), 147–186, ordinary-character calculation;
Gorenstein, *Finite Groups*, §16.6, printed p.482. This is a local reduction
for that calculation, not a construction of its remaining character inputs.
-/

open scoped IsMulCommutative

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
variable {G : Type*} [Group G] [Finite G]

private theorem odd_sylow_cyclic (horder : Nat.card G = 175560)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (P : Sylow p G) : IsCyclic P := by
  apply isCyclic_of_card_dvd_prime (p := p)
  rw [P.card_eq_multiplicity, horder]
  by_cases hd : p ∣ 175560
  · have hm := Nat.mem_primeFactors.mpr ⟨Fact.out, hd, (by decide : (175560 : ℕ) ≠ 0)⟩
    have hf : (175560 : ℕ).primeFactors = {2, 3, 5, 7, 11, 19} := by decide +kernel
    rw [hf] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hp2 rfl).elim
    all_goals decide +kernel
  · rw [Nat.factorization_eq_zero_of_not_dvd hd, pow_zero]
    exact one_dvd _

private theorem sylow_commutative (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    IsMulCommutative P := by
  by_cases hp : p = 2
  · subst p
    exact (h.any_sylow_elementaryAbelian P).toIsMulCommutative
  · let := odd_sylow_cyclic horder hp P
    infer_instance

private theorem nilpotent_commutative (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) (H : Subgroup G) (hn : Group.IsNilpotent H) :
    IsMulCommutative H := by
  have hP (p : ℕ) [Fact p.Prime] (P : Sylow p H) : IsMulCommutative P := by
    obtain ⟨Q, hQ⟩ := P.exists_comap_subtype_eq
    let := sylow_commutative h horder Q
    apply IsMulCommutative.of_comm
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    exact setLike_mul_comm (s := (Q : Subgroup G))
      (show (x : H) ∈ Q.comap H.subtype from hQ.symm ▸ x.property)
      (show (y : H) ∈ Q.comap H.subtype from hQ.symm ▸ y.property)
  have hp (p : (Nat.card H).primeFactors) : Fact p.val.Prime :=
    ⟨Nat.prime_of_mem_primeFactors p.property⟩
  let (p : (Nat.card H).primeFactors) (P : Sylow p H) : IsMulCommutative P := hP p P
  obtain ⟨e⟩ := ((Group.isNilpotent_of_finite_tfae (G := H)).out 0 4).mp hn
  apply IsMulCommutative.of_comm
  intro x y
  apply e.symm.injective
  simp only [map_mul, mul_comm]

private theorem table_squarefree (i : Fin 15) (hi : ¬ classOrder i ∣ 2) :
    Squarefree (centralizerOrder i) := by
  have h : ∀ i : Fin 15, ¬ classOrder i ∣ 2 → Squarefree (centralizerOrder i) := by
    decide +kernel
  exact h i hi

private theorem centralizer_squarefree (c : OrdinaryClassData G) (x : G)
    (hx : x ^ 2 ≠ 1) : Squarefree (Nat.card (Subgroup.centralizer ({x} : Set G))) := by
  let i := c.classes.symm (ConjClasses.mk x)
  have hc : IsConj (c.representatives i) x := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    rw [← c.classes_eq]
    exact c.classes.apply_symm_apply _
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  let e := MulAut.conj g
  have he : e (c.representatives i) = x := hg
  have ho : classOrder i = orderOf x := by
    rw [← c.orders, ← he]
    exact (e.orderOf_eq _).symm
  have hc' : Nat.card (Subgroup.centralizer ({c.representatives i} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv e.toEquiv ?_
    intro y
    simp only [Subgroup.mem_centralizer_singleton_iff]
    change y * c.representatives i = c.representatives i * y ↔
      e y * x = x * e y
    rw [← he, ← map_mul, ← map_mul]
    exact e.injective.eq_iff.symm
  rw [← hc', c.centralizers]
  exact table_squarefree i (by rw [ho, orderOf_dvd_iff_pow_eq_one]; exact hx)

private theorem two_group_bounds (h : Janko1CentralizerData G)
    (H : Subgroup G) (hsq : ∀ x : H, x ^ 2 = 1) : Nat.card H ∣ 8 := by
  have hp : IsPGroup 2 H := fun x => ⟨1, by simpa using hsq x⟩
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  rw [← h.any_sylow_card P]
  exact Subgroup.card_dvd_of_le hP

/-- The nilpotent-subgroup alternatives consumed by the ordinary-row restriction
criterion. The class enumeration remains explicit; no power-map or character
premise is required. -/
public theorem ordinary_nilpotent_subgroup_types (h : Janko1CentralizerData G)
    (horder : Nat.card G = 175560) (c : OrdinaryClassData G) :
    ∀ H : Subgroup G, Group.IsNilpotent H →
      IsCyclic H ∨ ((∀ x : H, x ^ 2 = 1) ∧ Nat.card H ∣ 8) := by
  classical
  intro H hn
  let : Group.IsNilpotent H := hn
  let : IsMulCommutative H := nilpotent_commutative h horder H hn
  by_cases hsq : ∀ x : H, x ^ 2 = 1
  · exact Or.inr ⟨hsq, two_group_bounds h H hsq⟩
  · obtain ⟨x, hx⟩ := not_forall.mp hsq
    have hcent : H ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (setLike_mul_comm hy x.property)
    have hsf : Squarefree (Nat.card H) :=
      (centralizer_squarefree c (x : G) (fun he => hx (Subtype.ext he))).squarefree_of_dvd
        (Subgroup.card_dvd_of_le hcent)
    let : IsZGroup H := IsZGroup.of_squarefree hsf
    exact Or.inl inferInstance

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
