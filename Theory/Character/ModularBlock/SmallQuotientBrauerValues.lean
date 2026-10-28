module

public import Theory.Character.ModularBlock.SmallQuotientCartan

/-!
# Genuine Brauer values through small quotients

Completeness identifies two principal Brauer families with the same distinct
module degrees, through actual representation isomorphisms. We apply this to
the inflated two-group and S₄ models. Thus the values are determined for every
supplied family, retaining their eigenvalue-defined meaning and the prescribed
modular place. A central two-extension of S₄ has values `(1,2)` above the
identity and `(1,-1)` above a three-cycle, on odd-order elements. Odd normal
inflation preserves these descriptions.

Source: Fong, *Some Sylow subgroups of order 32*, J. Algebra 6 (1967),
printed pp. 71, 73–74.
-/

public section
noncomputable section
namespace ModularBlock.Cartan
open PrincipalBlockConstruction CompatibleLocalBlock
variable {G : Type*} [Group G] [Finite G]

/-- Matching distinct degrees identify the actual simple modules and their values. -/
theorem PrincipalBrauerFamily.value_eq_of_degree_injective
    {d : PrincipalCongruenceBlockData G} {n : ℕ}
    (a b : PrincipalBrauerFamily d n) (hb : Function.Injective b.degree)
    (hd : a.degree = b.degree) (j : Fin n) (g : G) :
    BrauerCharacter.value d (a.rep j) g = BrauerCharacter.value d (b.rep j) g := by
  obtain ⟨k, ⟨e⟩⟩ := b.complete _ (a.rep j) (a.irreducible j) (a.inBlock j)
  have hk : a.degree j = b.degree k := by simpa using e.toLinearEquiv.finrank_eq
  have hkj : k = j := hb (hk.symm.trans (congrFun hd j))
  subst k
  exact BrauerCharacter.value_equiv d e g

/-- The singleton character is one on odd elements when the odd quotient is a two-group. -/
theorem brauerValue_eq_one_of_oddNormal_twoGroup (d : PrincipalCongruenceBlockData G)
    (b : PrincipalBrauerFamily d 1) (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) (hQ : IsPGroup 2 (G ⧸ N))
    (hd : b.degree 0 = 1) (g : G) (hg : Odd (orderOf g)) :
    BrauerCharacter.value d (b.rep 0) g = 1 := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  let aQ := PGroupCartan.family q hQ
  let a := aQ.ofOddQuotient d N hN
  have hdegree : b.degree = a.degree := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    exact hd
  rw [b.value_eq_of_degree_injective a (fun _ _ _ => Subsingleton.elim _ _) hdegree]
  change BrauerCharacter.value d (inflateQuotientRepresentation d N (aQ.rep 0)) g = 1
  rw [inflateQuotientRepresentation_brauerValue d N _ g hg]
  have hodd : Odd (orderOf (QuotientGroup.mk' N g)) := hg.of_dvd_nat (orderOf_map_dvd _ _)
  have hone : QuotientGroup.mk' N g = 1 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (hQ.dvd_orderOf hne))
  rw [hone, BrauerCharacter.value_one]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  norm_num [aQ, PGroupCartan.family]

private theorem degree_injective_two {b : Fin 2 → ℕ} (h0 : b 0 = 1) (h1 : b 1 = 2) :
    Function.Injective b := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- Completeness and distinct degrees recover the S₄ table without unfolding its models. -/
theorem brauerValues_of_symmetricFour
    (d : PrincipalCongruenceBlockData (Equiv.Perm (Fin 4)))
    (b : PrincipalBrauerFamily d 2) (hd0 : b.degree 0 = 1) (hd1 : b.degree 1 = 2)
    (g : Equiv.Perm (Fin 4)) (hg : Odd (orderOf g)) :
    BrauerCharacter.value d (b.rep 0) g = 1 ∧
      BrauerCharacter.value d (b.rep 1) g = if g = 1 then 2 else -1 := by
  let s := SymmetricFourCartan.simpleModuleData d
  have hv (j : Fin 2) : BrauerCharacter.value d (b.rep j) g =
      BrauerCharacter.value d (s.rep j) g := by
    obtain ⟨k, ⟨e⟩⟩ := s.complete _ (b.rep j) (b.irreducible j)
    have hk : b.degree j = SymmetricFourCartan.modularDegree k := by
      simpa using e.toLinearEquiv.finrank_eq
    have hd : b.degree j = SymmetricFourCartan.modularDegree j := by
      fin_cases j
      · exact hd0
      · exact hd1
    have hkj : k = j := degree_injective_two (b := SymmetricFourCartan.modularDegree)
      rfl rfl (hk.symm.trans hd)
    subst k
    exact BrauerCharacter.value_equiv d e g
  rw [hv 0, hv 1]
  exact ⟨s.value_zero g hg, s.value_one g hg⟩

/-- Values of any degree-ordered principal family on a central two-extension of S₄. -/
theorem brauerValues_of_centralTwo_symmetricFour (d : PrincipalCongruenceBlockData G)
    (b : PrincipalBrauerFamily d 2) (Z : Subgroup G) [Z.Normal]
    (hc : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z)
    (e : (G ⧸ Z) ≃* Equiv.Perm (Fin 4))
    (hd0 : b.degree 0 = 1) (hd1 : b.degree 1 = 2)
    (g : G) (hg : Odd (orderOf g)) :
    BrauerCharacter.value d (b.rep 0) g = 1 ∧
      BrauerCharacter.value d (b.rep 1) g =
        if e (QuotientGroup.mk' Z g) = 1 then 2 else -1 := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d Z
  let s := q.transport e
  let aS := (SymmetricFourCartan.principalDecompositionData s).family
  let aQ := aS.transportBack e
  let a := aQ.ofCentralTwoQuotient d Z hc hZ
  have ha0 : a.degree 0 = 1 := SymmetricFourCartan.principalDecompositionData_degree_zero s
  have ha1 : a.degree 1 = 2 := SymmetricFourCartan.principalDecompositionData_degree_one s
  have hdegree : b.degree = a.degree := by
    funext j
    fin_cases j
    · exact hd0.trans ha0.symm
    · exact hd1.trans ha1.symm
  have hv (j : Fin 2) : BrauerCharacter.value d (b.rep j) g =
      BrauerCharacter.value s (aS.rep j) (e (QuotientGroup.mk' Z g)) := by
    rw [b.value_eq_of_degree_injective a (degree_injective_two ha0 ha1) hdegree]
    rw [show a = aQ.ofCentralTwoQuotient d Z hc hZ from rfl,
      PrincipalBrauerFamily.ofCentralTwoQuotient_value d Z hc hZ aQ j g hg]
    exact (brauerValue_transport q e (aS.rep j) _
      (hg.of_dvd_nat (orderOf_map_dvd _ _))).symm
  have hodd : Odd (orderOf (e (QuotientGroup.mk' Z g))) := by
    rw [e.orderOf_eq]
    exact hg.of_dvd_nat (orderOf_map_dvd _ _)
  rw [hv 0, hv 1]
  exact brauerValues_of_symmetricFour s aS
    (SymmetricFourCartan.principalDecompositionData_degree_zero s)
    (SymmetricFourCartan.principalDecompositionData_degree_one s) _ hodd

/-- Odd normal inflation of the genuine two-character S₄ value table. -/
theorem brauerValues_of_oddNormal_centralFour_symmetricFour (d : PrincipalCongruenceBlockData G)
    (b : PrincipalBrauerFamily d 2) (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) (Z : Subgroup (G ⧸ N)) [Z.Normal]
    (hc : Z ≤ Subgroup.center (G ⧸ N)) (hcard : Nat.card Z = 4)
    (e : ((G ⧸ N) ⧸ Z) ≃* Equiv.Perm (Fin 4))
    (hd0 : b.degree 0 = 1) (hd1 : b.degree 1 = 2)
    (g : G) (hg : Odd (orderOf g)) :
    BrauerCharacter.value d (b.rep 0) g = 1 ∧
      BrauerCharacter.value d (b.rep 1) g =
        if e (QuotientGroup.mk' Z (QuotientGroup.mk' N g)) = 1 then 2 else -1 := by
  let q := compatibleQuotientPrincipalCongruenceBlockData d N
  obtain ⟨aQ, ha0, ha1, _⟩ := exists_centralFour_symmetricFour_cartan q Z hc hcard e
  let a := aQ.family.ofOddQuotient d N hN
  have hdegree : b.degree = a.degree := by
    funext j
    fin_cases j
    · exact hd0.trans ha0.symm
    · exact hd1.trans ha1.symm
  have hv (j : Fin 2) : BrauerCharacter.value d (b.rep j) g =
      BrauerCharacter.value q (aQ.family.rep j) (QuotientGroup.mk' N g) := by
    rw [b.value_eq_of_degree_injective a (degree_injective_two ha0 ha1) hdegree]
    exact inflateQuotientRepresentation_brauerValue d N (aQ.family.rep j) g hg
  rw [hv 0, hv 1]
  exact brauerValues_of_centralTwo_symmetricFour q aQ.family Z hc
    (IsPGroup.of_card (n := 2) (by simpa using hcard)) e ha0 ha1 _
    (hg.of_dvd_nat (orderOf_map_dvd _ _))

end ModularBlock.Cartan
