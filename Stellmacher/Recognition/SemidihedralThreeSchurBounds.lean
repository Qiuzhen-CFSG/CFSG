module

public import Stellmacher.Recognition.SemidihedralThreePrincipalCharacters
public import Stellmacher.Recognition.SemidihedralThreeSchurFromPrincipalData

/-!
# Schur bounds in the semidihedral characteristic-three case

The principal-character existence theorem supplies the actual rational
irreducible rows and their local section identities. The negative eigenspace
of the central involution in the first row (degree eleven), or the fourth row
(degree twelve in the degree-thirteen alternative), gives a faithful local
character of degree four. The supplied-data theorem proves faithfulness using
the odd core and the principal local row. Schur's rational-trace bounds then
give the local divisor 720 and the two global divisors, without assuming a
rational realization of any character.

The final assembly retains the elementary-four subgroup and its actual
odd-core centralizer parameters. Its alternatives pair each global bound with
the corresponding group-order formula, so consumers need no character data
as an additional hypothesis.

Source: Alperin–Brauer–Gorenstein, III.8 Lemmas 1–2, pp.114–115, and
Proposition 5, p.117. The degree estimate used upstream is the weak inequality
`2 * f* ≤ fi - 3` in the printed source.
-/

namespace Stellmacher.Recognition

/-- The actual principal characters supply a faithful complex local character
of degree four, rational on odd-order elements. -/
public theorem exists_semidihedral_three_local_degree_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2) :
    ∃ ρ : Representation ℂ (Subgroup.centralizer ({x} : Set G)) (Fin 4 → ℂ),
      Function.Injective ρ ∧
      ∀ r, Odd (orderOf r) → ∃ q : ℚ, ρ.character r = (q : ℂ) := by
  obtain ⟨c⟩ := exists_threePrincipalData S hS hN x hx
  obtain ⟨d, ρ, hf, hr, hd, hfour, hcases⟩ :=
    semidihedral_three_exists_local_schur_character S hS x hx c
  have hd4 : d = 4 := by
    rcases hcases with ⟨hdegree, hbound, _⟩ | ⟨hdegree, hbound, _⟩
    · exact semidihedral_local_constituent_degree_eq_four hd hfour hbound (Or.inl hdegree)
    · exact semidihedral_local_constituent_degree_eq_four hd hfour hbound (Or.inr hdegree)
  subst d
  exact ⟨ρ, hf, hr⟩

/-- ABG III.8 Lemma 2 for the original elementary-four configuration. -/
public theorem semidihedral_three_local_schur
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T) :
    let N := Subgroup.centralizer ({x} : Set G)
    let K := (pPrimeCore 2 N).map N.subtype
    let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
    A.index ≠ 1 → Nat.card N ∣ 720 := by
  obtain ⟨c⟩ := exists_semidihedralThreePrincipalCharacters S hS hN x hx T hT hxT
  dsimp only
  intro hb
  exact (semidihedral_three_schur_bounds_from_principalData
    S hS hN x hx T hT hxT c.toThreePrincipalData hb).1

/-- The local bound and both global bounds, paired with the corresponding
order alternatives. All character-theoretic witnesses are constructed from
the original group hypotheses. -/
public theorem semidihedral_three_schur_bounds
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (S : Sylow 2 G) (hS : IsSemidihedralGroup S) (hN : IsNTwoGroup G)
    (x : G) (hx : orderOf x = 2)
    (T : Subgroup G) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4) (hxT : x ∈ T) :
    let N := Subgroup.centralizer ({x} : Set G)
    let K := (pPrimeCore 2 N).map N.subtype
    let A := (Subgroup.centralizer (T : Set G)).subgroupOf K
    let a := Nat.card A
    let b := A.index
    b ≠ 1 → Nat.card N ∣ 720 ∧
      ((Nat.card G = 7920 * (a * b^3) ∧
          Nat.card G ∣ 16 * 3^6 * 5^2 * 7 * 11) ∨
       (Nat.card G = 5616 * (a * b^3) ∧
          Nat.card G ∣ 16 * 3^8 * 5^3 * 7^2 * 11 * 13)) := by
  obtain ⟨c⟩ := exists_semidihedralThreePrincipalCharacters S hS hN x hx T hT hxT
  dsimp only
  intro hb
  obtain ⟨hlocal, heleven, hthirteen⟩ := semidihedral_three_schur_bounds_from_principalData
    S hS hN x hx T hT hxT c.toThreePrincipalData hb
  refine ⟨hlocal, ?_⟩
  rcases c.alternatives with h | h
  · exact Or.inl ⟨h.2.2.2.2.2, heleven h.1⟩
  · exact Or.inr ⟨h.2.2.2.2.2, hthirteen h.2.1⟩

end Stellmacher.Recognition
