module
public import ABG.Recognition.ThreeQuotientSections
public import ABG.Recognition.ThreeCyclicCharacterTable

/-!
# Ambient cyclic sections above the GL₂(3) odd-core quotient

The two-power part of a lift of the concrete rotation has order eight and
fourth power equal to the distinguished involution. The centralizers of its
noncentral powers in GL₂(3) have order eight, so commuting odd parts map to
one. The root restriction theorem and the concrete cyclic table therefore
give the exact signed order-four/eight section formulas. Neither the generator
nor the primitive root is assumed: both witnesses are constructed here.

Source: Alperin--Brauer--Gorenstein III.2 Proposition 2 and III.5--6;
Wong (1964), Table 1 and the root restriction argument.
-/

open scoped BigOperators
open BenderGlauberman Matrix Matrix.GeneralLinearGroup
open ModularBlock.PrincipalBlockConstruction
namespace ABG
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
variable {G : Type*} [Group G] [Finite G] (x : G)
local notation "C" => Subgroup.centralizer (Set.singleton x)
local notation "L" => GL (Fin 2) (ZMod 3)

private theorem table_odd_centralizer (a r : L)
    (ha : orderOf a = 4 ∨ orderOf a = 8) (hr : Odd (orderOf r))
    (har : Commute a r) : r = 1 := by
  obtain ⟨k, hk, _⟩ := three_conjugacy_data.1 a
  obtain ⟨g, hg⟩ := isConj_iff.mp hk
  let e := MulAut.conj g
  have he : e a = threeClassRepr k := hg
  have ho : (![1,2,4,3,6,2,8,8] k : ℕ) = 4 ∨
      (![1,2,4,3,6,2,8,8] k : ℕ) = 8 := by
    rw [← three_conjugacy_data.2.1, ← he, e.orderOf_eq]
    exact ha
  have hm : e r ∈ Subgroup.centralizer ({threeClassRepr k} : Set L) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← he]
    exact (har.map e.toMonoidHom).symm.eq
  let rr : Subgroup.centralizer ({threeClassRepr k} : Set L) := ⟨e r, hm⟩
  have hc : Nat.card (Subgroup.centralizer ({threeClassRepr k} : Set L)) = 8 := by
    rw [three_conjugacy_data.2.2.1]
    fin_cases k <;> norm_num at ho <;> rfl
  have hd : orderOf r ∣ 8 := by
    have h := orderOf_dvd_natCard rr
    rw [hc, ← Subgroup.orderOf_coe, e.orderOf_eq] at h
    exact h
  have h1 : orderOf r = 1 := Nat.eq_one_of_dvd_coprimes
    ((Nat.coprime_two_left.mpr hr).pow_left 3) hd dvd_rfl
  exact orderOf_eq_one_iff.mp h1

omit [Finite G] in
private theorem quotient_ker
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) :
    (threeOddCoreQuotientMap e).ker = pPrimeCore 2 C := by
  rw [threeOddCoreQuotientMap,
    MonoidHom.ker_comp_of_injective _ _ (e.trans glTwoThreeFieldEquiv).injective,
    QuotientGroup.ker_mk']

private theorem quotient_order
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (a : C) (ha : orderOf a = 4 ∨ orderOf a = 8) :
    orderOf (threeOddCoreQuotientMap e a) = orderOf a := by
  apply MonoidHom.orderOf_eq_of_prime_power_of_coprime_ker
    (p := 2) (threeOddCoreQuotientMap e)
    (by rw [quotient_ker]; exact pPrimeCore_coprime_card)
  rcases ha with ha | ha
  · exact ⟨2, by simpa only [show 2^2 = 4 from rfl, ← ha] using pow_orderOf_eq_one a⟩
  · exact ⟨3, by simpa only [show 2^3 = 8 from rfl, ← ha] using pow_orderOf_eq_one a⟩

omit [Finite G] in
private theorem root_mul_odd (a r : C)
    (ha : orderOf a = 4 ∨ orderOf a = 8) (hr : Odd (orderOf r))
    (har : Commute a r) (hxa : x ∈ Subgroup.zpowers (a : G)) :
    x ∈ Subgroup.zpowers ((a * r : C) : G) := by
  have hcop : (orderOf r).Coprime (orderOf a) := by
    have h2 := (Nat.coprime_two_left.mpr hr).symm
    rcases ha with ha | ha <;> rw [ha]
    · exact h2.pow_right 2
    · exact h2.pow_right 3
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime (x := a) hcop
  have ha' : (a : G) ∈ Subgroup.zpowers ((a * r : C) : G) := by
    have hp : ((a * r) ^ orderOf r) ^ n = a := by
      rw [har.mul_pow, pow_orderOf_eq_one, mul_one]
      exact hn
    exact ⟨((orderOf r * n : ℕ) : ℤ), by
      simp only [zpow_natCast, pow_mul]
      exact congrArg Subtype.val hp⟩
  exact (Subgroup.zpowers_le.mpr ha') hxa

/-- The sections of order-four and order-eight roots have constant values
on their commuting odd parts, despite a possibly nontrivial local odd core. -/
public theorem threeQuotient_principalCandidate_cyclic_section_table
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (b : PrincipalCongruenceBlockData G) (hx : orderOf x = 2)
    (a r : C) (ha : orderOf a = 4 ∨ orderOf a = 8)
    (hr : Odd (orderOf r)) (har : Commute a r)
    (hxa : x ∈ Subgroup.zpowers (a : G)) (j : Fin 8) :
    d.principalCandidate j ((a * r : C) : G) =
      (![1,d.sign 0,-d.sign 3,d.sign 1,-d.sign 2,d.sign 0,d.sign 0,d.sign 0] j : ℤ) *
        glTwoThreeCharacter (![0,4,3,1,5,2,6,7] j) (threeOddCoreQuotientMap e a) := by
  rw [threeQuotient_principalCandidate_root_restriction x e d b hx _
    (root_mul_odd x a r ha hr har hxa) j, map_mul]
  have hqr : threeOddCoreQuotientMap e r = 1 := table_odd_centralizer _ _
    (by rw [quotient_order x e a ha]; exact ha)
    (hr.of_dvd_nat (orderOf_map_dvd _ r)) (har.map _)
  rw [hqr, mul_one]

/-- Choose a lift of the concrete rotation, preserving its order through the
odd kernel and identifying its fourth power with the given involution. -/
public theorem threeQuotient_exists_section_generator
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1) (hx : orderOf x = 2) :
    ∃ u : C, orderOf u = 8 ∧ (u : G)^4 = x ∧
      threeOddCoreQuotientMap e u = threeRotation := by
  let f := threeOddCoreQuotientMap e
  obtain ⟨g, hg⟩ := threeOddCoreQuotientMap_surjective e threeRotation
  obtain ⟨u, v, hu, hv, huv, he, _, hvg⟩ := exists_prime_power_decomposition 2 Nat.prime_two g
  have hvdiv : orderOf (f v) ∣ 8 := by
    have hvm : f v ∈ Subgroup.zpowers (f g) := by
      obtain ⟨n, hn⟩ := hvg
      exact ⟨n, (map_zpow f g n).symm.trans (congrArg f hn)⟩
    have hd := orderOf_dvd_of_mem_zpowers hvm
    rw [show f g = threeRotation from hg, show orderOf threeRotation = 8 from
      three_conjugacy_data.2.1 6] at hd
    exact hd
  have hvone : f v = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((hv.of_dvd_right (orderOf_map_dvd f v)).pow_left 3) hvdiv dvd_rfl)
  have hfu : f u = threeRotation := by
    rw [← he, map_mul, hvone, mul_one] at hg
    exact hg
  have huo : orderOf u = 8 := by
    have hker : Nat.Coprime 2 (Nat.card f.ker) := by
      rw [show f.ker = pPrimeCore 2 C from quotient_ker x e]
      exact pPrimeCore_coprime_card
    have hh := f.orderOf_eq_of_prime_power_of_coprime_ker (p := 2) hker u hu
    rw [hfu] at hh
    exact hh.symm.trans (three_conjugacy_data.2.1 6)
  have hxu : x ∈ Subgroup.zpowers (u : G) :=
    (threeOddCoreQuotientMap_root_iff x hx e u).mp (by
      change f u ∈ glTwoThreeRootSupport
      rw [hfu]
      exact (glTwoThreeRootSupport_class 6).mpr (by decide))
  have hu4 : orderOf ((u : G)^4) = 2 := by
    rw [orderOf_pow, Subgroup.orderOf_coe, huo]
    norm_num
  have hfour : (u : G)^4 = x := congrArg Subtype.val
    (IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨(u : G)^4, (Subgroup.zpowers (u : G)).pow_mem (Subgroup.mem_zpowers _) 4⟩ :
        Subgroup.zpowers (u : G)))
      (y := (⟨x, hxu⟩ : Subgroup.zpowers (u : G)))
      (by simpa only [← Subgroup.orderOf_coe] using hu4)
      (by simpa only [← Subgroup.orderOf_coe] using hx))
  exact ⟨u, huo, hfour, hfu⟩

private theorem cyclic_power_root (u : G) (hu : orderOf u = 8)
    (hfour : u^4 = x) (h : ℤ) (hh : ¬ 4 ∣ h) :
    (orderOf (u^h) = 4 ∨ orderOf (u^h) = 8) ∧ x ∈ Subgroup.zpowers (u^h) := by
  have hmod : h % 8 = 1 ∨ h % 8 = 2 ∨ h % 8 = 3 ∨
      h % 8 = 5 ∨ h % 8 = 6 ∨ h % 8 = 7 := by omega
  have hp : u ^ h = u ^ (h%8) := by
    simpa only [hu, Nat.cast_ofNat] using (zpow_mod_orderOf u h).symm
  have hc (n : ℤ) (hn : (h%8*n)%8 = 4) : x ∈ Subgroup.zpowers (u^(h%8)) := by
    refine ⟨n, ?_⟩
    change (u^(h%8))^n = x
    rw [← zpow_mul, ← zpow_mod_orderOf u (h%8*n), hu]
    norm_num only [Nat.cast_ofNat, hn, zpow_ofNat]
    exact hfour
  rw [hp]
  constructor
  · rcases hmod with hm | hm | hm | hm | hm | hm <;> rw [hm]
    all_goals simp only [zpow_ofNat]
    all_goals rw [orderOf_pow, hu]
    all_goals norm_num
  · rcases hmod with hm | hm | hm | hm | hm | hm
    · exact hc 4 (by omega)
    · exact hc 2 (by omega)
    · exact hc 4 (by omega)
    · exact hc 4 (by omega)
    · exact hc 2 (by omega)
    · exact hc 4 (by omega)

/-- The exact ABG order-four/eight section formula for a compatible rotation
lift, whose existence follows from the preceding generator theorem. -/
public theorem threeQuotient_principalCandidate_cyclic_section
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (b : PrincipalCongruenceBlockData G) (hx : orderOf x = 2)
    (u : C) (hu : orderOf u = 8) (hfour : (u : G)^4 = x)
    (hqu : threeOddCoreQuotientMap e u = threeRotation)
    (h : ℤ) (hh : ¬ 4 ∣ h)
    (r : Subgroup.centralizer ({(u : G)^h} : Set G)) (hr : Odd (orderOf r)) (j : Fin 8) :
    d.principalCandidate j ((u : G)^h * (r : G)) =
      threeSignedPrincipalCyclicSection ![-d.sign 0,-d.sign 3,-d.sign 1]
        glTwoThreeSectionRoot h j := by
  have hroot := cyclic_power_root x (u : G) ((Subgroup.orderOf_coe u).trans hu) hfour h hh
  have hrc : (r : G) ∈ C := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    obtain ⟨n, hn⟩ := hroot.2
    have hc : Commute (r : G) ((u : G)^h) :=
      Subgroup.mem_centralizer_singleton_iff.mp r.property
    have hcn := (hc.zpow_right n).eq
    simpa only [hn] using hcn
  let rr : C := ⟨r, hrc⟩
  have hcomm : Commute (u^h) rr := Subtype.ext
    (Subgroup.mem_centralizer_singleton_iff.mp r.property).symm
  have horder : orderOf (u^h) = 4 ∨ orderOf (u^h) = 8 := by
    simpa only [← Subgroup.orderOf_coe, Subgroup.coe_zpow] using hroot.1
  have hodd : Odd (orderOf rr) := by
    simpa only [← Subgroup.orderOf_coe] using hr
  have hv := threeQuotient_principalCandidate_cyclic_section_table x e d b hx
    (u^h) rr horder hodd hcomm hroot.2 j
  rw [map_zpow, hqu, glTwoThree_cyclic_section h hh j] at hv
  change d.principalCandidate j ((u : G)^h * (r : G)) = _ at hv
  rw [hv]
  fin_cases j <;> simp [threeSignedPrincipalCyclicSection, Matrix.cons_val, Fin.reduceFinMk] <;> ring

/-- Unconditional cyclic-section witnesses from the odd-core quotient. -/
public theorem threeQuotient_principalCandidate_exists_cyclic_sections
    (e : (C ⧸ pPrimeCore 2 C) ≃* GL2 3 1)
    (d : ThreeCharacterDecomposition (threeQuotientInducedGenerator x e))
    (b : PrincipalCongruenceBlockData G) (hx : orderOf x = 2) :
    ∃ u : G, orderOf u = 8 ∧ u^4 = x ∧
      ∃ ζ : ℂ, IsPrimitiveRoot ζ 8 ∧
        ∀ (h : ℤ), ¬ 4 ∣ h →
          ∀ (r : Subgroup.centralizer ({u^h} : Set G)), Odd (orderOf r) →
            ∀ j : Fin 8, d.principalCandidate j (u^h * (r : G)) =
              threeSignedPrincipalCyclicSection ![-d.sign 0,-d.sign 3,-d.sign 1] ζ h j := by
  obtain ⟨u, hu, hfour, hqu⟩ := threeQuotient_exists_section_generator x e hx
  exact ⟨u, (Subgroup.orderOf_coe u).trans hu, hfour, glTwoThreeSectionRoot,
    glTwoThreeSectionRoot_primitive,
    threeQuotient_principalCandidate_cyclic_section x e d b hx u hu hfour hqu⟩

end
end ABG
