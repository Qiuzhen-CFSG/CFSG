module
public import CFSG.Quasithin.Chapter2.Section05.PrimeSource.Reduction
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Persistence

/-!
# The terminal original prime branch for a normal component

Component normality in H is the remaining earlier source premise.
The exact quotient and core exclusions select its nonabelian dihedral core
and marked crossing. The preceding component persistence theorem then gives
normality in every core-involution centralizer. The proved prime reduction
supplies fixed generation and the complete crossing-pair contradiction.

Source: Aschbacher--Smith 2.5.19--21, printed pp.560--567.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement Overcomponents
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The original prime component contradiction once its earlier normality
is supplied. All quotient, crossing and overcomponent premises are discharged. -/
theorem MathieuSourceSetup.prime_source_false_of_normal_component
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hfm : IsFermatOrMersennePrime p)
    (eK : K ≃* PSL(2,ZMod p)) : False := by
  have hQ := MathieuSourceSetup.normal_prime_core_quotient c hG hempty hgen hp eK
  have hne : Nat.card (twoCore H) ≠ 2 := by
    rcases hQ with hQ | hQ
    · obtain ⟨eQ⟩ := hQ
      exact MathieuSourceSetup.prime_psl_twoCore_card_ne_two c hG hempty hgen hb hstar eK eQ
    · obtain ⟨eQ⟩ := hQ
      exact MathieuSourceSetup.prime_pgl_twoCore_card_ne_two c hG hempty hgen hb hstar hp eK eQ
  have hlarge := MathieuSourceSetup.two_lt_core_card_of_ne_two c hG hempty hgen hb hne
  obtain ⟨k,hk,⟨eC⟩⟩ := MathieuSourceSetup.prime_source_twoCore_model c hG hempty hgen hb
    hp hfm eK hQ hlarge
  obtain ⟨t,w,_x,ht,hw,htC,hwK,_hxT,_hxS,_hxN,_hx2,_htx,hz,hne,_hnf,hHt,_hP⟩ :
      ∃ t zK x : G, orderOf t = 2 ∧ orderOf zK = 2 ∧ t ∈ twoCore H ∧
      zK ∈ K ∧ x ∈ c.T ∧ x ∉ (S : Subgroup H).map H.subtype ∧
      x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      x ^ 2 ∈ (S : Subgroup H).map H.subtype ∧
      x⁻¹ * t * x = zK ∧ z = t * zK ∧ z ≠ zK ∧ ¬ IsConj t z ∧
      H ≤ centralizer ({t} : Set G) ∧
      ∃ P : Sylow 2 (centralizer ({t} : Set G)),
        (P : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype =
          (S : Subgroup H).map H.subtype := by
    rcases hQ with hQ | hQ
    · obtain ⟨eQ⟩ := hQ
      exact MathieuSourceSetup.prime_psl_large_core_crossing
        c hG hempty hgen hb hp hfm eK eQ hlarge
    · obtain ⟨eQ⟩ := hQ
      exact MathieuSourceSetup.prime_pgl_large_core_crossing
        c hG hempty hgen hb hp hfm eK eQ hlarge
  have htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype) := by
    have hc := MathieuSourceSetup.core_eq_sylow_centralizer c hgen
    refine ⟨(show twoCore H ≤ (S : Subgroup H).map H.subtype from hc ▸ inf_le_left) htC,?_⟩
    intro s hs
    exact mem_centralizer_singleton_iff.mp (hHt (map_subtype_le _ hs))
  have hnormal := source_prime_core_normalization c hG hempty hgen hb hstar hp hfm eK
    ⟨k,hk,⟨eC⟩⟩ t w ht hw htC htZ hwK hz hne
  exact MathieuSourceSetup.prime_source_false_of_component_centralizer_normality
    c hG hempty hgen hb hstar hp hfm eK hnormal

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
