module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.NonadjacentInvolutions.CosetAction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveTypes
public import Theory.GroupTheory.IndexTwoIntersection
public import Theory.SpecificGroups.SL2.CubicPairCentralizer
public import Theory.SpecificGroups.Alternating.CubicPairCentralizer

/-!
# The two literal nonneighbor centralizers

Let L = C_G(X). For an SL₂(3) join, 47.5 gives a pair stabilizer of order
sixteen in M = N_G(X). Since L has index two in M and order 1080, its
intersection with that stabilizer has order eight. The small SL₂(3) pair
calculation shows that an element of L normalizing U centralizes U; thus
the intersection is exactly C_L(U), and is a Sylow two-subgroup of L.

For an A₅ join the order-twenty pair stabilizer has a normal subgroup of
order five. It centralizes the join and puts its whole centralizer inside
one of the two five-normalizers from 47.2. The actual A₅ join excludes the
D₁₀ × D₁₀ alternative and fills the A₅ factor of D₁₀ × A₅, identifying
C_L(U) with the dihedral factor by a multiplicative equivalence.

`centralizerTypes_of_representatives` constructs both fields of the record
consumed by the six-coset argument. Its additional input `FiveNormalizerTypes`
is precisely the two order-five normalizer alternatives of 47.2(1)–(3).
It does not assume a centralizer type, a fixed point, or a common involution.
The final application constructs the ambient witness using the existing coset
action and genuine earlier-source conclusions.

Source: Aschbacher, *Sporadic Groups* (1994), 47.5 and the final paragraph
of the proof of 47.6, printed pp.263–264; the five-local input is p.261.
All intersections and normality statements use the literal ambient
inclusions. No semidihedral assertion is used.
-/

public section

open Subgroup MulAction
open Theory.GroupTheory.GraphUniquenessSystem
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.NonadjacentInvolutions
variable {G : Type*} [Group G] [Finite G]

/-- Intersecting the order-sixteen pair stabilizer with L has order eight;
the SL₂(3) pair calculation identifies this intersection with C_L(U). -/
theorem sl_centralizer_card (D : Seed G) (R : ThreePairRepresentatives D)
    (hG : Nat.card G = 604800) (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    (hL : Nat.card (localCentralizer D) = 1080)
    (U : D.Vertex) (hU : sl2Join D D.base U) :
    Nat.card (nonneighborCentralizer D U) = 8 := by
  let M := normalizer (D.X : Set G)
  let K := (localCentralizer D).subgroupOf M
  let E := stabilizer M U
  have hK : Nat.card K = 1080 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (centralizer_le_normalizer (D.X : Set G))).toEquiv]
    exact hL
  have hiK : K.index = 2 := by
    have hh := K.card_mul_index
    rw [hK, hM] at hh
    omega
  have hE : Nat.card E = 16 := by
    obtain ⟨P, hP⟩ := R.sl_stabilizer_sylow hG hM hU
    change Nat.card (stabilizer M U) = 16
    rw [← hP, P.card_eq_multiplicity, hM]
    decide +kernel
  have hn : ¬ E ≤ K := by
    intro hn
    have hd := card_dvd_of_le hn
    rw [hE, hK] at hd
    norm_num at hd
  have hi := subgroupOf_index_eq_two K E hiK hn
  have hc : Nat.card (K.subgroupOf E) = 8 := by
    have hh := (K.subgroupOf E).card_mul_index
    rw [hi, hE] at hh
    omega
  have hfix (g : M) : g ∈ E ↔ (g : G) ∈ normalizer (U.val : Set G) := by
    change g ∈ stabilizer M U ↔ _
    rw [mem_stabilizer_iff]
    change (g : G) • U = U ↔ _
    rw [← mem_stabilizer_iff, D.stabilizer_eq_normalizer]
  have hcent := Theory.SpecificGroups.SL2.CubicPairCentralizer.pair_centralizes
    D.X U.val D.card_X (D.vertex_card U) hU.some
  let f : K.subgroupOf E ≃* nonneighborCentralizer D U := {
    toFun := fun g => ⟨⟨g.val.val.val, g.property⟩,
      hcent ⟨g.property, (hfix g.val.val).mp g.val.property⟩⟩
    invFun := fun t => ⟨⟨⟨t.val.val, centralizer_le_normalizer _ t.val.property⟩,
      (hfix _).mpr (centralizer_le_normalizer _ t.property)⟩, t.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  exact (Nat.card_congr f.toEquiv).symm.trans hc

/-- The literal C_L(U) is Sylow two when the endpoint join is SL₂(3). -/
theorem sl_centralizer_sylow (D : Seed G) (R : ThreePairRepresentatives D)
    (hG : Nat.card G = 604800) (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    (hZ : center (localCentralizer D) = D.X.subgroupOf (localCentralizer D))
    (e : (localCentralizer D ⧸ center (localCentralizer D)) ≃* alternatingGroup (Fin 6))
    (U : D.Vertex) (hU : sl2Join D D.base U) :
    ∃ P : Sylow 2 (localCentralizer D),
      (P : Subgroup (localCentralizer D)) = nonneighborCentralizer D U := by
  have hL := localCentralizer_card D hZ e
  refine ⟨Sylow.ofCard (nonneighborCentralizer D U) ?_, rfl⟩
  rw [sl_centralizer_card D R hG hM hL U hU, hL]
  decide +kernel

/-- Application to the source six-coset action; the SL₂(3) branch no longer
needs a centralizer-type premise. -/
theorem commonInvolution_of_sl2Join (D : Seed G) (R : ThreePairRepresentatives D)
    (hG : Nat.card G = 604800) (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    (Y : D.Vertex) (hY : D.graph.Adj D.base Y)
    (hclass : ∀ t ∈ edgeFixer G D.base Y, orderOf t = 2 → IsConj D.z t)
    (hZ : center (localCentralizer D) = D.X.subgroupOf (localCentralizer D))
    (e : (localCentralizer D ⧸ center (localCentralizer D)) ≃* alternatingGroup (Fin 6))
    (U : D.Vertex) (hU : sl2Join D D.base U) :
    ∃ t : G, IsConj D.z t ∧ D.X ⊔ Y.val ⊔ U.val ≤ involutionCentralizer t := by
  have hL := localCentralizer_card D hZ e
  exact commonInvolution_of_card_eight D Y U (R.edgeFixer_equiv hG hM hY)
    hclass hL (sl_centralizer_card D R hG hM hL U hU)


private noncomputable def nonneighborCentralizerEquivJoin (D : Seed G) (U : D.Vertex) :
    nonneighborCentralizer D U ≃*
      centralizer ((D.X ⊔ U.val : Subgroup G) : Set G) := by
  have hm : (nonneighborCentralizer D U).map (localCentralizer D).subtype =
      centralizer ((D.X ⊔ U.val : Subgroup G) : Set G) := by
    rw [nonneighborCentralizer, subgroupOf_map_subtype]
    apply le_antisymm
    · apply le_centralizer_iff.mpr
      exact sup_le (le_centralizer_iff.mp (show
        centralizer (U.val : Set G) ⊓ localCentralizer D ≤ centralizer (D.X : Set G)
          from inf_le_right)) (le_centralizer_iff.mp inf_le_left)
    · exact le_inf (centralizer_le (show U.val ≤ D.X ⊔ U.val from le_sup_right))
        (centralizer_le (show D.X ≤ D.X ⊔ U.val from le_sup_left))
  exact ((nonneighborCentralizer D U).equivMapOfInjective (localCentralizer D).subtype
    (localCentralizer D).subtype_injective).trans (MulEquiv.subgroupCongr hm)

/-- The literal A₅ nonneighbor centralizer is D₁₀, using the two normalizer
alternatives of source 47.2. -/
theorem five_centralizer_dihedral (D : Seed G) (R : ThreePairRepresentatives D)
    (hG : Nat.card G = 604800) (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    (h₅ : PrimeNormalizers.FiveNormalizerTypes G)
    (U : D.Vertex) (hU : a5Join D D.base U) :
    Nonempty (nonneighborCentralizer D U ≃* DihedralGroup 5) := by
  have hN : Nat.card (normalizer (D.X : Set G) ⊓ normalizer (U.val : Set G) : Subgroup G) = 20 := by
    have he : edgeFixer G D.base U = normalizer (D.X : Set G) ⊓
        normalizer (U.val : Set G) := by
      rw [edgeFixer, D.stabilizer_eq_normalizer, D.stabilizer_eq_normalizer]
      rfl
    rw [← he, Nat.card_congr (R.five_edgeFixer_equiv hG hM hU).some.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, DihedralGroup.card]
  obtain ⟨e⟩ := Theory.SpecificGroups.Alternating.CubicPairCentralizer.pair_centralizer_equiv D.X U.val D.card_X
    (D.vertex_card U) hN hU.some h₅
  exact ⟨(nonneighborCentralizerEquivJoin D U).trans e⟩

/-- Both source centralizer types, using only the representative stabilizers,
source orders, central quotient, and the earlier five-normalizer alternatives. -/
theorem centralizerTypes_of_representatives (D : Seed G) (R : ThreePairRepresentatives D)
    (hG : Nat.card G = 604800) (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    (hZ : center (localCentralizer D) = D.X.subgroupOf (localCentralizer D))
    (e : (localCentralizer D ⧸ center (localCentralizer D)) ≃* alternatingGroup (Fin 6))
    (h₅ : PrimeNormalizers.FiveNormalizerTypes G) : CentralizerTypes D :=
  ⟨sl_centralizer_sylow D R hG hM hZ e, five_centralizer_dihedral D R hG hM h₅⟩

/-- The complete nonneighbor application of the constructed record to the
literal six-coset action. Only genuine earlier-source conclusions remain. -/
theorem commonInvolution_of_representatives_and_fiveNormalizerTypes (D : Seed G)
    [Theory.GroupTheory.IsQuasisimple (localCentralizer D)]
    (R : ThreePairRepresentatives D)
    (hG : Nat.card G = 604800) (hM : Nat.card (normalizer (D.X : Set G)) = 2160)
    (Y : D.Vertex) (hY : D.graph.Adj D.base Y)
    (hclass : ∀ t ∈ edgeFixer G D.base Y, orderOf t = 2 → IsConj D.z t)
    (hZ : center (localCentralizer D) = D.X.subgroupOf (localCentralizer D))
    (e : (localCentralizer D ⧸ center (localCentralizer D)) ≃* alternatingGroup (Fin 6))
    (h₅ : PrimeNormalizers.FiveNormalizerTypes G) (U : D.Vertex)
    (hU : sl2Join D D.base U ∨ a5Join D D.base U) :
    ∃ t : G, IsConj D.z t ∧ D.X ⊔ Y.val ⊔ U.val ≤ involutionCentralizer t :=
  commonInvolution_of_centralizerTypes D Y (R.edgeFixer_equiv hG hM hY)
    hclass hZ e (centralizerTypes_of_representatives D R hG hM hZ e h₅) U hU

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.NonadjacentInvolutions
