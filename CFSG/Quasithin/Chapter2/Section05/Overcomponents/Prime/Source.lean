module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Census
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.ExchangedModels
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.Exchanged
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.InvariantKernel
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.RankNormality
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.FixedRanks
/-!
# Prime-source bad orbits and their exact centralizer kernels

The marked ordinary pumpup supplies the literal component orbit. The invariant census and cubic-rank bound make its containing component normal; the exchanged census identifies two centerless copies of the original component. Their fixed-component uniqueness and pointwise-fixer calculations then prove Sylow-centralizer normalization and the exact index-two kernel. This discharges both local row premises of the original maximal bad-involution dichotomy.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
open ComponentRefinement ComponentSelection OvercomponentsSource PrimeRows
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The actual prime-source bad orbit is either a normal component with the
retained quotient mark and two-primary center, or two exchanged simple
copies of the original component. -/
theorem source_bad_prime_rows
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (eK : K ≃* PSL(2,ZMod p))
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hi : BadInvolution ((S : Subgroup H).map H.subtype) K i) :
    ∃ htI : t ∈ centralizer ({i} : Set G),
      let Gi := centralizer ({i} : Set G)
      let tI : Gi := ⟨t,htI⟩
      let D := K.subgroupOf Gi
      let X := componentOrbit D (oddELayer Gi)
      (IsComponent Gi X ∧ X.Normal ∧ IsPGroup 2 (center X) ∧
        ∃ a : MulAut X, orderOf a = 2 ∧
          (∀ x : X, ((a x : Gi) : G) = t * ((x : Gi) : G) * t⁻¹) ∧
          IsComponentIn (D.subgroupOf X) a.fixedSubgroup ∧
          Nonempty (K ≃* ((D.subgroupOf X).subgroupOf a.fixedSubgroup)) ∧
          PrimeFixedQuotientModels (X ⧸ center X) (quotientAut (center X) a)) ∨
      ∃ J : Subgroup Gi, IsComponent Gi J ∧
        J ≠ J.map (MulAut.conj tI).toMonoidHom ∧
        X = J ⊔ J.map (MulAut.conj tI).toMonoidHom ∧
        center J = ⊥ ∧ Nonempty (J ≃* K) := by
  obtain ⟨htI,hrows⟩ := source_marked_ordinary_pumpup c hG hempty hgen hb hstar
    t i ht htC htZ hi.2.1 hi.1.1 hi.1.2 hi.2.2
  refine ⟨htI,?_⟩
  rcases hrows with ⟨hX,a,ha,hact,hB,⟨eKB⟩⟩ | ⟨J,hJ,hm,hpair,⟨e⟩⟩
  · obtain ⟨hmodel,hZ⟩ := source_prime_overcomponent_quotient c hG hempty hgen hb
      hp hp7 eK i hi.2.1 _ hX a ha _ hB.2 eKB
    have hnormal := component_normal_of_central_quotient_rank_two
      (hG.involution_centralizer_sqtk hi.2.1) _ hX
      (prime_fixed_quotient_three_rank_ge_two _ hmodel)
    exact Or.inl ⟨hX,hnormal,hZ,a,ha,hact,hB,⟨eKB⟩,hmodel⟩
  · obtain ⟨hZ,he⟩ := source_exchanged_component_equiv c hG hempty hgen hb
      hp.1 hp7 eK i hi.2.1 J hJ e
    exact Or.inr ⟨J,hJ,hm,hpair,hZ,he⟩

/-- Both prime-source orbit rows discharge the actual normalizer and index-two
kernel premises in the source maximal-bad-involution argument. -/
theorem source_bad_prime_kernel
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (eK : K ≃* PSL(2,ZMod p))
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hi : BadInvolution ((S : Subgroup H).map H.subtype) K i) :
    ((S : Subgroup H).map H.subtype ⊓ centralizer ({i} : Set G) ≤ normalizer (K : Set G)) ∧
    (let Gi := centralizer ({i} : Set G)
     let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
     let R := ((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓ Gi
     ((R ⊓ centralizer (X.map Gi.subtype : Set G)).subgroupOf R).index = 2) := by
  obtain ⟨htI,hrows⟩ := source_bad_prime_rows c hG hempty hgen hb hstar
    hp hp7 eK t i ht htC htZ hi
  rcases hrows with ⟨hX,hN,_,a,ha,hact,hB,_,hm⟩ | ⟨J,hJ,hm,hpair,_⟩
  · let := hN
    have hKi : K ≤ centralizer ({i} : Set G) :=
      fun k hk => mem_centralizer_singleton_iff.mpr (hi.1.2 k hk)
    exact source_invariant_kernel c hG hempty hgen hb t i htZ hKi htI _ hX
      (le_componentOrbit _ _) a ha hact hB hm
  · exact source_exchanged_kernel c hG hempty hgen hb hstar t i ht htC htZ hi
      htI J hJ hm hpair

/-- The maximal bad-involution dichotomy on the original source groups,
with every local prime-row kernel premise discharged. -/
theorem source_maximal_prime_dichotomy
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (eK : K ≃* PSL(2,ZMod p))
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hi : MaximalBadInvolution ((S : Subgroup H).map H.subtype) K i) :
    Nat.card ((((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G)) : Subgroup G) ≤ 4 ∨
      (¬ (K.subgroupOf H).Normal ∧
        i ∈ centerIn ((S : Subgroup H).map H.subtype ⊓ normalizer (K : Set G))) := by
  obtain ⟨hN,hidx⟩ := source_bad_prime_kernel c hG hempty hgen hb hstar
    hp hp7 eK t i ht htC htZ hi.1
  exact source_maximal_kernel_dichotomy c hG hempty hgen hb hstar i hi hN hidx
end CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
