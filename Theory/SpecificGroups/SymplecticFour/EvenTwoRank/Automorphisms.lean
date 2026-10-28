module

public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.InvolutionNormalForms
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Descent
public import Theory.SpecificGroups.Suzuki.StandardSubgroups
public import Theory.GroupAction.AutomorphismFixedResidualTransport
public import Theory.GroupTheory.PrimeRankHom

/-!
# Automorphism two-rank from symplectic involution descent

An elementary abelian subgroup contained in the inner automorphisms has rank
at most 3n. Otherwise, choose a noninner involution. The inner part embeds
faithfully in its fixed subgroup, while the cyclic outer quotient contributes
at most one further generator. The field fixed group has rank 3(n/2); the
Suzuki fixed group's Sylow order q² bounds its rank by 2n. Thus the whole
elementary subgroup has rank at most 2n+1 ≤ 3n.

This proves the numerical calculation with four explicit geometric inputs:
diagram-preserving semilinear coverage, the field and exceptional-graph
cocycle descents, and the actual Suzuki fixed-group equivalence. Their
construction remains with the existing automorphism and fixed-matrix owners.
No rank estimate is assumed, and this conditional module does not claim the
unconditional full-automorphism theorem. The equivalences from `EvenTwoRank`
transport the bound to both genuine derived carriers, retaining the literal
projective central quotient.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, printed
p.356 and 16.3.9 on p.1180, using the involution types of 16.1.4 on p.1171.
-/

public section

open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymplecticFour.EvenTwoRank
open DiagramAutomorphisms DiagramAutomorphisms.InvolutionNormalForms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private noncomputable def innerEquiv : Sp F ≃* MulAut.innerSubgroup (Sp F) :=
  MonoidHom.ofInjective inner_injective

omit [Finite F] in
private theorem fixes_of_commutes (a : MulAut (Sp F)) (g : Sp F)
    (h : a * MulAut.conj g = MulAut.conj g * a) : a g = g := by
  apply inner_injective
  have he : a * MulAut.conj g * a⁻¹ = MulAut.conj (a g) := by
    ext x
    simp
  rw [← he, h, mul_assoc, mul_inv_cancel, mul_one]

private theorem aut_rank_le_of_fixed {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    [IsCyclic (MulAut.Outer (Sp F))]
    (hfixed : ∀ a : MulAut (Sp F), orderOf a = 2 → a ∉ MulAut.innerSubgroup (Sp F) →
      primeRank 2 a.fixedSubgroup ≤ 2 * n) :
    primeRank 2 (MulAut (Sp F)) ≤ 3 * n := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let := hE
  let : CommGroup E := IsMulCommutative.instCommGroup
  have hout : primeRank 2 (MulAut.Outer (Sp F)) ≤ 1 := by
    let P := Classical.choice (inferInstance : Nonempty (Sylow 2 (MulAut.Outer (Sp F))))
    exact P.primeRank_le_one_of_isCyclic inferInstance
  have hEbound : primeRank 2 E ≤ 3 * n := by
    by_cases hi : E ≤ MulAut.innerSubgroup (Sp F)
    · let f : E →* Sp F := innerEquiv.symm.toMonoidHom.comp (Subgroup.inclusion hi)
      have hf : Function.Injective f := innerEquiv.symm.injective.comp
        (Subgroup.inclusion_injective hi)
      exact (primeRank_le_of_injective 2 f hf).trans (rank hF (by omega)).le
    · obtain ⟨a, haE, ha⟩ := SetLike.not_le_iff_exists.mp hi
      have hao : orderOf a = 2 := by
        have hs : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (A := E) a haE
        have hne : a ≠ 1 := fun h => ha (h ▸ (MulAut.innerSubgroup (Sp F)).one_mem)
        exact orderOf_eq_prime_iff.mpr ⟨hs, hne⟩
      let π : E →* MulAut.Outer (Sp F) :=
        (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))).comp E.subtype
      let j : π.ker →* MulAut.innerSubgroup (Sp F) := {
        toFun x := ⟨x.val.val, (QuotientGroup.eq_one_iff _).mp x.property⟩
        map_one' := rfl
        map_mul' _ _ := rfl }
      let k : π.ker →* Sp F := innerEquiv.symm.toMonoidHom.comp j
      have hk (x : π.ker) : MulAut.conj (k x) = x.val.val := by
        exact congrArg Subtype.val (innerEquiv.apply_symm_apply (j x))
      let f : π.ker →* a.fixedSubgroup := k.codRestrict _ (fun x => by
        rw [MulAut.mem_fixedSubgroup]
        apply fixes_of_commutes
        rw [hk]
        exact congrArg Subtype.val (mul_comm (⟨a, haE⟩ : E) x.val))
      have hf : Function.Injective f := by
        intro x y h
        have hxy := congrArg (fun z : a.fixedSubgroup => MulAut.conj z.val) h
        change MulAut.conj (k x) = MulAut.conj (k y) at hxy
        rw [hk, hk] at hxy
        exact Subtype.ext (Subtype.ext hxy)
      have hker := (primeRank_le_of_injective 2 f hf).trans (hfixed a hao ha)
      have hb := primeRank_le_ker_add (p := 2) π
      omega
  have htop : IsElementaryAbelian 2 (⊤ : Subgroup E) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) x.val)) }
  have hc := (primeRank_le_iff_elementary_card_le E).mp hEbound ⊤ htop
  simpa only [Nat.card_congr Subgroup.topEquiv.toEquiv] using hc


omit [CharP F 2] in
private theorem fixed_rank_eq_of_isConj {a b : MulAut (Sp F)} (h : IsConj a b) :
    primeRank 2 a.fixedSubgroup = primeRank 2 b.fixedSubgroup := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have he : ∀ x, c (a x) = b (c x) := by
    intro x
    exact congrArg (fun d : MulAut (Sp F) => d x) (mul_inv_eq_iff_eq_mul.mp hc)
  exact primeRank_equiv 2 (MulAut.fixedSubgroupEquivOfCompatible c a b he)

open BenderSuzuki.MatrixGroups in
private theorem suzuki_rank_le (m : ℕ) (hm : 0 < m) :
    primeRank 2 (SuzukiMatrixGroup m) ≤ 2 * (2 * m + 1) := by
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  rw [P.primeRank_eq]
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E _
  calc
    Nat.card E ≤ Nat.card P := E.card_le_card_group
    _ = 2 ^ (2 * (2 * m + 1)) := by
      rw [hP, suzukiRootSubgroup_card m hm, ← pow_mul, Nat.mul_comm (2 * m + 1) 2]

/-- The fixed subgroups of the two standard outer involutions have rank at
most 2n. The Suzuki input is an actual fixed-group equivalence, not a rank premise. -/
theorem outer_fixed_rank_le_of_models {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (hSuzuki : ∀ m : ℕ, n = 2 * m + 1 →
      Nonempty ((ExceptionalGraph.graphAut (F := F) ^ n).fixedSubgroup ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
    (a : MulAut (Sp F))
    (ha : (Even n ∧ IsConj a (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)))) ∨
      (Odd n ∧ IsConj a (ExceptionalGraph.graphAut ^ n))) :
    primeRank 2 a.fixedSubgroup ≤ 2 * n := by
  rcases ha with ⟨heven, ha⟩ | ⟨hodd, ha⟩
  · rw [fixed_rank_eq_of_isConj ha,
      primeRank_equiv 2 (FieldFixedResidual.fixedEquiv _)]
    have heq : n = 2 * (n / 2) := by
      obtain ⟨m, hm⟩ := heven
      omega
    have hc := FieldFixedResidual.card_halfField (F := F)
      (by omega : 1 ≤ n / 2) (heq ▸ hF)
    rw [rank hc (by omega)]
    omega
  · obtain ⟨m, hm⟩ := hodd
    obtain ⟨e⟩ := hSuzuki m hm
    rw [fixed_rank_eq_of_isConj ha, primeRank_equiv 2 e, hm]
    exact suzuki_rank_le m (by omega)

section Descent

variable {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (hfield : Even n → ∀ g : Sp F,
      g * fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) g = 1 →
      ∃ h : Sp F, g = h * (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) h)⁻¹)
    (hgraph : Odd n → ∀ g : Sp F,
      g * (ExceptionalGraph.graphAut ^ n) g = 1 →
      ∃ h : Sp F, g = h * ((ExceptionalGraph.graphAut ^ n) h)⁻¹)
    (hSuzuki : ∀ m : ℕ, n = 2 * m + 1 →
      Nonempty ((ExceptionalGraph.graphAut (F := F) ^ n).fixedSubgroup ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))

include hF hn hclass hfield hgraph hSuzuki

/-- The full automorphism-rank bound after the explicit geometric classification
and the two cocycle descents. All remaining inputs concern actual maps or fixed
group equivalences; none assumes a rank estimate. -/
theorem automorphism_rank_le_of_descent :
    primeRank 2 (MulAut (Sp F)) ≤ 3 * n := by
  let := ExceptionalGraph.outer_isCyclic_of_card hF (by omega) hclass
  apply aut_rank_le_of_fixed hF hn
  intro a ha hi
  rcases involution_normalForms_of_coboundaries hF (by omega) hclass hfield hgraph a ha
    with hinner | houter
  · obtain ⟨g, _, rfl⟩ := hinner
    exact False.elim (hi ⟨g, rfl⟩)
  · exact outer_fixed_rank_le_of_models hF hn hSuzuki a houter

/-- The same bound on the full automorphism group of the genuine derived
matrix carrier, using the proved derived-to-whole equivalence. -/
theorem derived_automorphism_rank_le_of_descent :
    primeRank 2 (MulAut (commutator (Sp F))) ≤ 3 * n := by
  rw [primeRank_equiv 2 (MulAut.congr (derivedEquiv hF hn))]
  exact automorphism_rank_le_of_descent hF hn hclass hfield hgraph hSuzuki

/-- The bound for the full automorphism group of the derived projective
carrier retains the literal quotient by the symplectic center. -/
theorem projective_derived_automorphism_rank_le_of_descent :
    primeRank 2 (MulAut (commutator (Sp F ⧸ center (Sp F)))) ≤ 3 * n := by
  let e := (projectiveDerivedEquiv hF hn).trans EvenProjective.equiv.symm
  rw [primeRank_equiv 2 (MulAut.congr e)]
  exact automorphism_rank_le_of_descent hF hn hclass hfield hgraph hSuzuki

end Descent

end Theory.SpecificGroups.SymplecticFour.EvenTwoRank
