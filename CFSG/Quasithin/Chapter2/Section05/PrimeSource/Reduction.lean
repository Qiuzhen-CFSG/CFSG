module
public import Theory.SpecificGroups.PSL2.PrimeInvolutionFixedGeneration
public import CFSG.Quasithin.Chapter2.Section05.PrimeSource.Incoming
public import CFSG.Quasithin.Chapter2.Section05.PrimeSource.CrossingGeneration
public import CFSG.Quasithin.Chapter2.Section05.PrimeSource.Quotient
public import CFSG.Quasithin.Chapter2.Section05.PrimeSource.CoreModel
public import CFSG.Quasithin.Chapter2.Section05.OrderTwoCore.PrimePSLSource
public import CFSG.Quasithin.Chapter2.Section05.OrderTwoCore.PrimePGLSource

/-!
# Reducing the original prime branch to component-centralizer normality

The original conjugation action supplies the PSL₂/PGL₂ quotient alternatives.
The source order-two-core exclusions give a large nonabelian dihedral core
and its marked crossing. Fixed groups of its faithful conjugate action
generate the component, so normalization in the original core-involution
centralizers makes the crossed components commute. Their literal incoming
pair contradicts native ZD. Only the genuine preceding source component
normality statements remain as hypotheses for final assembly.

Source: Aschbacher--Smith 2.5.20--21, printed pp.565--567.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- All original prime-pair inputs follow from the source involution-centralizer
normality conclusion. The quotient alternatives, core shape, crossing, faithful
fixed generation, component commutation, and native ZD contradiction are derived. -/
theorem MathieuSourceSetup.prime_source_false_of_component_centralizer_normality
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hfm : IsFermatOrMersennePrime p)
    (eK : K ≃* PSL(2,ZMod p))
    (hnormal : ∀ i ∈ twoCore H, orderOf i = 2 →
      centralizer ({i} : Set G) ≤ normalizer (K : Set G)) : False := by
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
  obtain ⟨t,w,x,ht,_hw,htC,hwK,hxT,hxS,hxN,hx2,htx,hz,_hne,_hnf,hHt,_hP⟩ :
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
  have hpower : ∃ m, p-1=2^m ∨ p+1=2^m := by
    rcases hfm.2 with ⟨m,hm⟩ | ⟨m,hm⟩
    · exact ⟨2^m,Or.inl (by omega)⟩
    · exact ⟨m,Or.inr hm⟩
  let eD : (twoCore H).conjBy x⁻¹ ≃* DihedralGroup (2^k) :=
    ((MulAut.conj x⁻¹).subgroupMap (twoCore H)).symm.trans eC
  have hgener := MathieuSourceSetup.crossing_centralizer_generation_of_model
    c hgen eK x hxT hxS hxN hx2 (fun f hf N hfixed =>
      Theory.PSL2.prime_dihedral_involution_fixed_generation hp hpower hk eD f hf N hfixed)
  have hKN := normalizes_crossing_of_centralizer_generation K (twoCore H) x hnormal hgener
  have hC : twoCore H ≠ ⊥ := by
    intro he
    have ht1 : t=1 := mem_bot.mp (he ▸ htC)
    simp [ht1] at ht
  have hcomm := MathieuSourceSetup.crossing_commutes_of_normalizes
    c hgen hC x hxT hxS hxN hx2 hKN
  exact MathieuSourceSetup.prime_crossing_false_of_commuting
    c hG hempty hgen hb hstar hp hfm eK t x ht htC htZ hxT hxS hxN hx2
    (htx.symm ▸ hwK) (by rw [htx];exact hz) hcomm

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
