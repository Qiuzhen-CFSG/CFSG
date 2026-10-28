module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.EndpointThree
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.SmallThree.Factors
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.Preparation

/-!
# Exactly two canonical cubic supports in the cyclic source branch

The original full support premise supplies the canonical internal product.
A starred involution has displacement rank two. The cyclic three-core
centralizer bounds the number of factors by three, and the involution
rank-nullity bound excludes zero or one. If there are three, the
transposition obstruction makes every starred generator normalize them;
Jhat generation makes all factors invariant, contradicting the three-plane
endpoint. Thus the original canonical subgroup has order nine and its
two support planes span the original four-dimensional module.

Source: Aschbacher--Smith, D.2.25, printed p.190. The full canonical support
is supplied by the preceding indecomposability argument; the two-support
local-generation theorem consumes the actual factors exported here.
-/

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.ChapterD.CyclicSource.SmallThree
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- Once the original canonical cubic supports span V, exactly two occur. -/
public theorem canonical_count_eq_two (h : CoreHypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hc : ∀ t : G, orderOf t = 2 →
      IsCyclic (pCore 3 G ⊓ centralizer ({t} : Set G) : Subgroup G))
    (hm : let := BinaryGroupAction.action ρ
      subspaceCommutator ρ ⊤ (smallSupportGroup G (Multiplicative V) 1) = ⊤) :
    let := BinaryGroupAction.action ρ
    Nat.card (smallSupportFactors G (Multiplicative V) 1) = 2 := by
  classical
  let := BinaryGroupAction.action ρ
  let := BinaryGroupAction.elementary (V := V)
  let := BinaryGroupAction.faithful ρ h.faithful
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let Y := smallSupportGroup G (Multiplicative V) 1
  let : IsElementaryAbelian 3 Y := canonical_elementary ρ h.faithful
  have hYC (t : G) (ht : orderOf t = 2) :
      IsCyclic (Y ⊓ centralizer ({t} : Set G) : Subgroup G) := by
    let := hc t ht
    exact Subgroup.isCyclic_of_le (inf_le_inf_right _ (canonical_le_threeCore ρ))
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr h.ratio_le
  obtain ⟨t,ht,hT⟩ := starred_generator ρ hA (h.rank_one A hA)
  have hti : IsInvolution t := ⟨by intro he; simp [he] at ht,ht ▸ pow_orderOf_eq_one t⟩
  have htR : fixedCodim ρ (zpowers t) = 2 := by
    have he := (starred_codimension ρ hA (h.rank_one A hA)).trans hq
    rw [← hT] at he
    exact_mod_cast he
  have htSmall : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 2 := by
    rw [← fixedCodim_zpowers_eq_displacement_rank,htR]
  obtain ⟨d,hdf,hcard⟩ := canonical_supportFactors ρ h.faithful hm
  let s := Nat.card (smallSupportFactors G (Multiplicative V) 1)
  change s = 2
  have hup : s ≤ 3 := supportFactors_size_le_three ρ h.faithful Y d t hti htSmall (hYC t ht)
  have hlo : 2 ≤ s := by
    have hh := (involution_actor_rank_and_fixedCodim ρ t ht).2.2.2
    rw [htR,d.finrank_eq ρ] at hh
    omega
  suffices s ≠ 3 by omega
  intro he
  have he' : Nat.card (smallSupportFactors G (Multiplicative V) 1) = 3 := he
  have hex := canonical_supportFactors ρ h.faithful hm
  dsimp only at hex
  rw [he'] at hex
  obtain ⟨d3,hdf3,_⟩ := hex
  have hnorm (g : G) (i : Fin 3) : g ∈ normalizer (d3.ambient i : Set G) := by
    have hj : Jhat ρ ≤ normalizer (d3.ambient i : Set G) := by
      apply sSup_le
      intro B hB
      obtain ⟨u,hu,hU⟩ := starred_generator ρ hB (h.rank_one B hB)
      rw [← hU]
      apply zpowers_le.mpr
      have hu2 : IsInvolution u := ⟨by intro he; simp [he] at hu,hu ▸ pow_orderOf_eq_one u⟩
      have huR : fixedCodim ρ (zpowers u) = 2 := by
        have hh := (starred_codimension ρ hB (h.rank_one B hB)).trans hq
        rw [← hU] at hh
        exact_mod_cast hh
      have huCard : Nat.card (commutatorAction (zpowers u) (Multiplicative V)) = 4 := by
        rw [BinaryGroupAction.commutator_card,CyclicFixedRank.commutator_eq_range,
          ← fixedCodim_zpowers_eq_displacement_rank,huR]
        rfl
      exact factors_normalized_of_three_le (V := Multiplicative V) Y le_rfl u hu2 huCard
        (hYC u hu) (by rw [he']) (d3.ambient i) (hdf3 i)
    exact hj (h.generated.symm ▸ mem_top g)
  exact not_three_invariant_supports ρ h.faithful d3 hnorm h.generated hq t hti htSmall

/-- The original canonical subgroup and two actual factors, ready for the
order-eighteen local-generation endpoint. -/
public theorem canonical_two_supportFactors (h : CoreHypotheses ρ)
    (hq : cubicRatio ρ = 2)
    (hc : ∀ t : G, orderOf t = 2 →
      IsCyclic (pCore 3 G ⊓ centralizer ({t} : Set G) : Subgroup G))
    (hm : let := BinaryGroupAction.action ρ
      subspaceCommutator ρ ⊤ (smallSupportGroup G (Multiplicative V) 1) = ⊤) :
    let := BinaryGroupAction.action ρ
    let Y := smallSupportGroup G (Multiplicative V) 1
    ∃ d : FittingConfigurations.SupportFactors ρ Y 2,
      (∀ i, d.ambient i ∈ smallSupportFactors G (Multiplicative V) 1) ∧
      Nat.card Y = 9 ∧ Module.finrank (ZMod 2) V = 4 := by
  let := BinaryGroupAction.action ρ
  have hs := canonical_count_eq_two ρ h hq hc hm
  have hd := canonical_supportFactors ρ h.faithful hm
  dsimp only at hs hd ⊢
  rw [hs] at hd
  obtain ⟨d,hdf,hcard⟩ := hd
  exact ⟨d,hdf,hcard,d.finrank_eq ρ⟩

end CFSG.Quasithin.ChapterD.CyclicSource.SmallThree
