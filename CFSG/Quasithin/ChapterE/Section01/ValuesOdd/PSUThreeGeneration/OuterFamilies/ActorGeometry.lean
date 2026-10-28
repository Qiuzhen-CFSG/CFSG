module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.Obstruction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.ModelInputs
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure
public import Theory.SpecificGroups.OddThreeRank.Automorphisms
public import Theory.SpecificGroups.SU3.OddInvolutionFixed

/-!
# Actual outer actors in odd-prime PSU₃ extensions

The simple generalized Fitting subgroup acts faithfully by conjugation.
The concrete unitary automorphism theorems therefore bound the ambient
two-rank by three and the two-rank of the literal quotient G/F*(G) by one.
A nontrivial large family member consequently has order four or eight;
if it is outer, its intersection with F*(G) has order two or four respectively.
No closure of the family under intersections or subgroups is used.

Every outer involution has its actual intrinsic centralizer in F*(G)
isomorphic to the split ternary special orthogonal group over the original
Hermitian fixed field. The inner intersection of its elementary actor embeds
in this fixed group. The family consumer also retains the chosen involution,
the actual ambient tau, and its centralizer containment. These statements
include p = 3 and arbitrary nondegenerate Gram matrices.

These are inputs to the local E-member construction. They do not assert
that a centralizer is an E-member, that an arbitrary Sylow intersection is
Sylow, or that its actor image in the local radical quotient has rank one.

Source: Aschbacher--Smith, E.1.1--2 and E.1.14(7), printed pp.209--210, 214;
A.2.3(2), p.33; GLS3, §§2.7 and 4.3 for the outer fixed-group calculation.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies
variable {G : Type*} [Group G] [Finite G]

/-- The faithful ambient action bounds the rank of actors outside the socle as well. -/
theorem ambient_primeRank_two_le_three [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p) :
    primeRank 2 G ≤ 3 := by
  have hC := SimpleSocle.centralizer_eq_bot (nonabelian_of_model hp ho hmodel)
  obtain ⟨F, _, _, J, hcard, hc, ⟨e⟩⟩ := hmodel
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv (generalizedFitting G) e.toEquiv
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  calc
    primeRank 2 G ≤ primeRank 2 (MulAut (generalizedFitting G)) :=
      primeRank_le_of_injective 2 MulAut.conjNormal
        (MulAut.conjNormal_injective_of_centralizer_eq_bot _ hC)
    _ = primeRank 2 (MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) :=
      primeRank_equiv 2 (MulAut.congr e)
    _ ≤ 3 := Theory.SpecificGroups.OddThreeRank.psu3_automorphism_two_rank_le_three
      J hp ho hcard hc

/-- The literal outer quotient has elementary two-rank at most one. -/
theorem socle_quotient_primeRank_two_le_one [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p) :
    primeRank 2 (G ⧸ generalizedFitting G) ≤ 1 := by
  have hC := SimpleSocle.centralizer_eq_bot (nonabelian_of_model hp ho hmodel)
  obtain ⟨F, _, _, J, hcard, hc, ⟨e⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa only [pow_one] using
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hcard)
        (by simpa only [pow_one] using hc))
  obtain ⟨es⟩ := exists_projectiveEquiv J p hcard hfixed
  let e₀ := e.trans es
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) :=
    Finite.of_equiv (generalizedFitting G) e₀.toEquiv
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) :=
    e₀.symm.isSimpleGroup
  have hcoverage :=
    HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.semilinear_coverage_odd
      (standardForm J) rfl hp ho hcard hfixed
  calc
    primeRank 2 (G ⧸ generalizedFitting G) ≤
        primeRank 2 (MulAut.Outer (generalizedFitting G)) :=
      primeRank_le_of_injective 2 (MulAut.outerAction _)
        (MulAut.outerAction_injective _ hC)
    _ = primeRank 2 (MulAut.Outer (ProjectiveSpecialUnitaryMatrixGroup (standardForm J))) :=
      primeRank_equiv 2 (MulAut.outerCongr e₀)
    _ ≤ 1 := HermitianForm.EvenTwoRank.outer_two_rank_le_of_coverage
      (standardForm J) rfl hcoverage

/-- Large family actors have order four or eight; no inner-actor bound is substituted. -/
theorem large_member_card [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (d : LargeFamilyObstruction T)
    {A : Subgroup G} (hA : A ∈ d.family) (hAT : A ≤ (T : Subgroup G))
    (hne : A ≠ ⊥) : Nat.card A = 4 ∨ Nat.card A = 8 := by
  let := d.elementary.1 A hA
  have hc : Nat.card A ≤ 2 ^ 3 :=
    (primeRank_le_iff_elementary_card_le G).mp
      (ambient_primeRank_two_le_three hp ho hmodel) A inferInstance
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hnle : n ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hn ▸ hc)
  have hnlo : 2 ≤ n := by
    by_contra h
    have hn1 : n ≤ 1 := by omega
    have hc1 : Nat.card A ≤ 2 ^ 1 := by
      rw [hn]
      exact pow_le_pow_right' (by decide) hn1
    have hr := IsElementaryAbelian.rank_le_of_card_le A hc1
    have := d.large A hA hAT hne
    omega
  have hncase : n = 2 ∨ n = 3 := by omega
  rcases hncase with rfl | rfl
  · exact Or.inl hn
  · exact Or.inr hn

/-- An outer elementary actor has index two over its actual intersection with the socle. -/
theorem outer_member_intersection_card [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hout : ¬ A ≤ generalizedFitting G) :
    Nat.card (A ⊓ generalizedFitting G : Subgroup G) * 2 = Nat.card A := by
  let L := generalizedFitting G
  let q := QuotientGroup.mk' L
  let f : A →* G ⧸ L := q.comp A.subtype
  have hmapne : A.map q ≠ ⊥ := by
    intro h
    apply hout
    intro x hx
    have he : q x = 1 := mem_bot.mp (h ▸ mem_map_of_mem q hx)
    exact (QuotientGroup.eq_one_iff _).mp he
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  let : Nontrivial (A.map q) := (Subgroup.nontrivial_iff_ne_bot _).mpr hmapne
  have hmap : Nat.card (A.map q) = 2 := by
    have hlo : 2 ≤ Nat.card (A.map q) := Finite.one_lt_card
    have hhi : Nat.card (A.map q) ≤ 2 ^ 1 :=
      (primeRank_le_iff_elementary_card_le (G ⧸ L)).mp
        (socle_quotient_primeRank_two_le_one hp ho hmodel) (A.map q) inferInstance
    omega
  let e : f.ker ≃* (A ⊓ L : Subgroup G) := {
    toFun := fun x => ⟨x.1.1, x.1.2, (QuotientGroup.eq_one_iff (N := L) _).mp x.2⟩
    invFun := fun x => ⟨⟨x.1, x.2.1⟩, (QuotientGroup.eq_one_iff (N := L) _).mpr x.2.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have h := f.ker.card_mul_index
  rw [index_ker, Nat.card_congr e.toEquiv] at h
  simpa only [f, MonoidHom.range_comp, range_subtype, hmap] using h

/-- The full intrinsic centralizer of an outer involution is the orthogonal fixed group. -/
theorem outer_fixed_equiv [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (e : generalizedFitting G ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (t : G) (ht : t ∉ generalizedFitting G) (ht2 : t ^ 2 = 1) :
    Nonempty ((centralizer ({t} : Set G)).subgroupOf (generalizedFitting G) ≃*
      (HermitianForm.OddPrimeSylow.splitOrthogonalForm (FixedBy.subfield F J.conj)).specialSubgroup) := by
  let L := generalizedFitting G
  have hC := SimpleSocle.centralizer_eq_bot (nonabelian_of_model hp ho hmodel)
  let a : MulAut L := MulAut.conjNormal t
  have ha2 : a ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hao : ¬ ∃ x : L, a = MulAut.conj x := by
    rintro ⟨x, hx⟩
    have he : t = (x : G) := MulAut.conjNormal_injective_of_centralizer_eq_bot L hC
      (hx.trans MulAut.conjNormal_val.symm)
    exact ht (by simpa only [he] using x.property)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : F // J.conj x = x} = p := by
    simpa only [pow_one] using
      (FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
        (by simpa only [pow_one] using hcard)
        (by simpa only [pow_one] using hc))
  obtain ⟨ef⟩ := HermitianForm.OddInvolutionNormalization.fixed_equiv_orthogonal
    J hp ho hcard hfixed (MulAut.congr e a)
    (by rw [← map_pow, ha2, map_one])
    (fun h => hao ((MulAut.congr_inner_iff e a).mp h))
  have hfix : a.fixedSubgroup = (centralizer ({t} : Set G)).subgroupOf L := by
    ext x
    rw [MulAut.mem_fixedSubgroup, mem_subgroupOf, mem_centralizer_singleton_iff,
      Subtype.ext_iff]
    change t * (x : G) * t⁻¹ = (x : G) ↔ (x : G) * t = t * x
    rw [mul_inv_eq_iff_eq_mul, eq_comm]
  exact ⟨(MulEquiv.subgroupCongr hfix).symm.trans
    ((MulAut.fixedSubgroupCongr e a).trans ef)⟩

open scoped IsMulCommutative commutatorElement

/-- Consumer of the rank calculations: select an actual family actor and an outer
involution, retaining its inner intersection and ambient tau containment. -/
theorem exists_large_outer_actor [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {T : Sylow 2 G} (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (d : LargeFamilyObstruction T)
    (houter : ∀ A ∈ d.family, A ≤ (T : Subgroup G) → A ≠ ⊥ →
      ¬ A ≤ generalizedFitting G) :
    ∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧
      ((Nat.card A = 4 ∧ Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 2) ∨
       (Nat.card A = 8 ∧ Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 4)) ∧
      ∃ t : G, t ∈ A ∧ t ∉ generalizedFitting G ∧ orderOf t = 2 ∧
        A ≤ centralizer ({t} : Set G) ∧
        tau (T : Subgroup G) A ≤ centralizer ({t} : Set G) := by
  classical
  obtain ⟨A, hA, hAT, hne⟩ := d.nontrivial_member
  let := d.elementary.1 A hA
  have hout := houter A hA hAT hne
  have hdouble := outer_member_intersection_card hp ho hmodel A hout
  have hcard := large_member_card hp ho hmodel d hA hAT hne
  have hcases :
      (Nat.card A = 4 ∧ Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 2) ∨
      (Nat.card A = 8 ∧ Nat.card (A ⊓ generalizedFitting G : Subgroup G) = 4) := by
    omega
  have hex : ∃ t : G, t ∈ A ∧ t ∉ generalizedFitting G := by
    simpa only [SetLike.le_def, not_forall, exists_prop] using hout
  obtain ⟨t, htA, htL⟩ := hex
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t htA
  have htne : t ≠ 1 := fun h => htL (h ▸ (generalizedFitting G).one_mem)
  have hO := (SimpleSocle.structure_of_sylow_supplement
    (nonabelian_of_model hp ho hmodel) T hLT).2.2.1
  refine ⟨A, hA, hAT, hne, hcases, t, htA, htL, orderOf_eq_prime ht2 htne, ?_, ?_⟩
  · intro a ha
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) (⟨t, htA⟩ : A)))
  · intro x hx
    have hc := (mem_centralizerModulo_iff.mp hx).2 t htA
    rw [hO, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact mem_centralizer_singleton_iff.mpr hc.symm

/-- The actor's inner intersection embeds in the actual orthogonal fixed group. -/
theorem outer_actor_fixed_embedding [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    {F : Type} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (e : generalizedFitting G ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (A : Subgroup G) [IsElementaryAbelian 2 A]
    (t : G) (htA : t ∈ A) (htL : t ∉ generalizedFitting G) :
    ∃ f : (A ⊓ generalizedFitting G : Subgroup G) →*
      (HermitianForm.OddPrimeSylow.splitOrthogonalForm (FixedBy.subfield F J.conj)).specialSubgroup,
      Function.Injective f := by
  obtain ⟨ef⟩ := outer_fixed_equiv hp ho hmodel J hcard hc e t htL
    (elemPow_eq_one_of_isElementaryAbelian t htA)
  let f : (A ⊓ generalizedFitting G : Subgroup G) →*
      (centralizer ({t} : Set G)).subgroupOf (generalizedFitting G) := {
    toFun := fun x => ⟨⟨x, x.2.2⟩, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨x, x.2.1⟩ : A) (⟨t, htA⟩ : A)))⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  refine ⟨ef.toMonoidHom.comp f, ?_⟩
  intro x y h
  have hxy : f x = f y := ef.injective h
  apply Subtype.ext
  exact congrArg (fun z : (centralizer ({t} : Set G)).subgroupOf (generalizedFitting G) => z.1.1) hxy

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies
