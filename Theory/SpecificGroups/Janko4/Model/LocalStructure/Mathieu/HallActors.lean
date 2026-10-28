module
public import Theory.Mathieu.M24.Properties.SolvableOddActors
public import Theory.Mathieu.M24.LocalGeometry.PairOvergroups.Placement.TransitiveCoverage
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu
public import Theory.SpecificGroups.Janko4.Model.GeneratorCertificates
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.OddCyclicThreeNormalizer
public import Theory.GroupTheory.PermutingSupCard

/-!
# Hall cubics in the actual J₄ Mathieu local subgroup

The literal max1 quotient has elementary two-kernel and image M₂₄.
Its solvable Sylow overgroups therefore have cyclic odd actors of order
at most three, including after the specified ambient conjugation. If the
original normalizing cubic does not contain the actor, they are distinct
commuting cubics and generate an elementary nine. Their two permuting
Sylow products give the whole actor order 9·|S|.

The SAME quotient image has order 9,216 and lies in an actual octad or
translated trio stabilizer. This geometric alternative does not identify
its action on any external local A₅ section.

Source: Aschbacher--Smith 5.1.13, printed p.637; GLS3 Table 5.3e/i.
All carrier maps and ATLAS word certificates are those of the imports.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Janko4.LocalStructure.MathieuHallActors
open Janko4 Janko4.Cardinality
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
local notation "M" => max1Subgroup matrixA_mul_self matrixB_pow_four


/-- The literal max1 quotient map to the native Mathieu carrier. -/
@[expose] def projection : M →* Sporadic.Mathieu.M24 :=
  (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).toMonoidHom.comp
    (QuotientGroup.mk' (localKernel matrixA_mul_self matrixB_pow_four))

/-- The native Mathieu quotient map is surjective. -/
theorem projection_surjective : Function.Surjective projection :=
  (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).surjective.comp
    (QuotientGroup.mk'_surjective _)

/-- Its kernel is exactly the certified elementary local kernel. -/
theorem projection_ker : projection.ker = localKernel matrixA_mul_self matrixB_pow_four := by
  ext x
  change localQuotientEquivM24 matrixA_mul_self matrixB_pow_four
    (QuotientGroup.mk' _ x) = 1 ↔ _
  rw [map_eq_one_iff _ (localQuotientEquivM24 matrixA_mul_self matrixB_pow_four).injective]
  exact QuotientGroup.eq_one_iff x

/-- A cyclic odd actor in a solvable full-Sylow overgroup in max1 has order at most three. -/
theorem cyclic_odd_card_dvd_three (S : Sylow 2 Model) (K D : Subgroup Model)
    (hSK : (S : Subgroup Model) ≤ K) (hs : Group.IsSolvable K)
    (hDK : D ≤ K) (hodd : Odd (Nat.card D)) (hcyc : IsCyclic D)
    (hKM : K ≤ M) : Nat.card D ∣ 3 := by
  let f := projection
  have hf := projection_surjective
  have hk := projection_ker
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    exact IsPGroup.of_card (n := 11) (localKernel_card _ _)
  let eK := subgroupOfEquivOfLe hKM
  let eD := subgroupOfEquivOfLe (hDK.trans hKM)
  let := hs
  let := hcyc
  have hs' : Group.IsSolvable (K.subgroupOf M) :=
    Group.isSolvable_of_isSolvable_injective (f := eK.toMonoidHom) eK.injective
  have hc' : IsCyclic (D.subgroupOf M) := isCyclic_of_injective eD.toMonoidHom eD.injective
  have hh := Sporadic.Mathieu.M24SolvableActors.cyclic_odd_card_dvd_three_of_two_kernel
    f hf hp (S.subtype (hSK.trans hKM)) (K.subgroupOf M) (D.subgroupOf M)
    (comap_mono hSK) hs' (comap_mono hDK)
    (by rwa [Nat.card_congr eD.toEquiv]) hc'
  rwa [Nat.card_congr eD.toEquiv] at hh


/-- The actor order bound is preserved under the specified ambient conjugation. -/
theorem cyclic_odd_card_dvd_three_of_map (S : Sylow 2 Model) (K D : Subgroup Model)
    (hSK : (S : Subgroup Model) ≤ K) (hs : Group.IsSolvable K)
    (hDK : D ≤ K) (hodd : Odd (Nat.card D)) (hcyc : IsCyclic D)
    (a : MulAut Model) (hKM : K.map a.toMonoidHom ≤ M) : Nat.card D ∣ 3 := by
  let := hs
  let := hcyc
  have hs' : Group.IsSolvable (K.map a.toMonoidHom) := Group.isSolvable_of_surjective
    (f := a.toMonoidHom.subgroupMap K) (a.toMonoidHom.subgroupMap_surjective K)
  have hc' : IsCyclic (D.map a.toMonoidHom) := isCyclic_of_surjective
    (a.toMonoidHom.subgroupMap D) (a.toMonoidHom.subgroupMap_surjective D)
  have hh := cyclic_odd_card_dvd_three (S.mapSurjective (f := a.toMonoidHom) a.surjective)
    (K.map a.toMonoidHom) (D.map a.toMonoidHom) (map_mono hSK) hs' (map_mono hDK)
    (by rwa [card_map_of_injective a.injective]) hc' hKM
  rwa [card_map_of_injective a.injective] at hh

/-- Distinct original odd actors form an elementary nine with the exact whole-actor order. -/
theorem cubic_pair (S : Sylow 2 Model) (D E : Subgroup Model)
    (hs : Group.IsSolvable ((D ⊔ (S : Subgroup Model)) ⊔ E : Subgroup Model))
    (hodd : Odd (Nat.card D)) (hcyc : IsCyclic D) (hE : Nat.card E = 3)
    (hED : E ≤ normalizer (D : Set Model)) (hne : ¬ D ≤ E)
    (hDS : (D : Set Model) * (S : Set Model) = (S : Set Model) * (D : Set Model))
    (hES : (E : Set Model) * (S : Set Model) = (S : Set Model) * (E : Set Model))
    (a : MulAut Model)
    (hKM : ((D ⊔ (S : Subgroup Model)) ⊔ E).map a.toMonoidHom ≤ M) :
    Nat.card D = 3 ∧ ⁅D,E⁆ = ⊥ ∧ Disjoint D E ∧
      Nat.card (D ⊔ E : Subgroup Model) = 9 ∧
      IsElementaryAbelian 3 (D ⊔ E : Subgroup Model) ∧
      Nat.card ((D ⊔ (S : Subgroup Model)) ⊔ E : Subgroup Model) = 9 * Nat.card S := by
  have hd := cyclic_odd_card_dvd_three_of_map S _ D (le_sup_right.trans le_sup_left)
    hs (le_sup_left.trans le_sup_left) hodd hcyc a hKM
  have hD : Nat.card D = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with hd | hd
    · exact (hne ((card_eq_one.mp hd).trans_le bot_le)).elim
    · exact hd
  have hcomm := commutator_eq_bot_of_odd_normalizes_card_three D E hD
    (by rw [hE]; decide) hED
  have hdis : Disjoint D E := by
    apply disjoint_iff.mpr
    have hi : Nat.card (D ⊓ E : Subgroup Model) ∣ 3 := hD ▸ card_dvd_of_le
      (show D ⊓ E ≤ D from inf_le_left)
    rcases (Nat.dvd_prime Nat.prime_three).mp hi with hi | hi
    · exact card_eq_one.mp hi
    · have heq : D ⊓ E = D := eq_of_le_of_card_ge inf_le_left (by rw [hD,hi])
      exact (hne (heq.symm.trans_le inf_le_right)).elim
  have hcard : Nat.card (D ⊔ E : Subgroup Model) = 9 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint D E hED hdis,hD,hE]
  have hp : ((D ⊔ E : Subgroup Model) : Set Model) * (S : Set Model) =
      (S : Set Model) * ((D ⊔ E : Subgroup Model) : Set Model) := by
    rw [coe_mul_of_right_le_normalizer_left D E hED,mul_assoc,hES,←mul_assoc,hDS,mul_assoc]
  have hKS : Disjoint (D ⊔ E) (S : Subgroup Model) := by
    obtain ⟨n,hn⟩ := S.isPGroup'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hcard,hn]
    exact (by decide : Nat.Coprime 9 2).pow_right n
  have elem (F : Subgroup Model) (hF : Nat.card F = 3) : IsElementaryAbelian 3 F := by
    let : IsCyclic F := isCyclic_of_prime_card hF
    exact { exponent_dvd_p := hF ▸ Group.exponent_dvd_nat_card }
  let := elem D hD
  let := elem E hE
  have hel : IsElementaryAbelian 3 (D ⊔ E : Subgroup Model) :=
    IsElementaryAbelian.sup_of_le_centralizer
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm))
  refine ⟨hD,hcomm,hdis,hcard,hel,?_⟩
  rw [sup_right_comm D (S : Subgroup Model) E,
    card_sup_eq_mul_of_permutes_of_disjoint _ _ hp hKS,hcard]


/-- The same whole actor has image of order 9,216 under the literal Mathieu projection. -/
theorem whole_actor_image_card (S : Sylow 2 Model) (K : Subgroup Model)
    (hSK : (S : Subgroup Model) ≤ K) (hKM : K ≤ M)
    (hK : Nat.card K = 9 * Nat.card S) :
    Nat.card ((K.subgroupOf M).map projection) = 9216 := by
  have hSM := hSK.trans hKM
  let P := S.subtype hSM
  have hS : Nat.card S = 2^21 := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe hSM).toEquiv]
    change Nat.card P = _
    rw [Sylow.card_eq_multiplicity,max1Subgroup_card]
    decide +kernel
  have hk : IsPGroup 2 projection.ker := by
    rw [projection_ker]
    exact IsPGroup.of_card (n := 11) (localKernel_card _ _)
  have hle : projection.ker ≤ K.subgroupOf M :=
    (hk.le_sylow_of_normal P).trans (comap_mono hSK)
  have hh := (projection.ker.subgroupOf (K.subgroupOf M)).card_mul_index
  change Nat.card (projection.ker.subgroupOf (K.subgroupOf M)) *
    projection.ker.relIndex (K.subgroupOf M) = _ at hh
  rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,relIndex_ker,
    projection_ker,localKernel_card,Nat.card_congr (subgroupOfEquivOfLe hKM).toEquiv,hK,hS] at hh
  omega

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups

/-- The same Mathieu image lies in an actual octad or translated trio stabilizer. -/
theorem whole_actor_image_geometry (S : Sylow 2 Model) (K : Subgroup Model)
    (hSK : (S : Subgroup Model) ≤ K) (hKM : K ≤ M)
    (hs : Group.IsSolvable K) (hK : Nat.card K = 9 * Nat.card S) :
    (∃ O : Octad, (K.subgroupOf M).map projection ≤ octadStabilizer O) ∨
      ∃ g : M24, (K.subgroupOf M).map projection ≤ conjugateTrioStabilizer g := by
  let := hs
  let eK := subgroupOfEquivOfLe hKM
  let : Group.IsSolvable (K.subgroupOf M) :=
    Group.isSolvable_of_isSolvable_injective (f := eK.toMonoidHom) eK.injective
  have hs' : Group.IsSolvable ((K.subgroupOf M).map projection) :=
    Group.isSolvable_of_surjective (f := projection.subgroupMap (K.subgroupOf M))
      (projection.subgroupMap_surjective _)
  exact Placement.small_sylow_overgroup_geometry Placement.transitiveSmallSylowPlacement
    ((S.subtype (hSK.trans hKM)).mapSurjective projection_surjective)
    ((K.subgroupOf M).map projection) (map_mono (comap_mono hSK)) hs'
    (Or.inl (whole_actor_image_card S K hSK hKM hK))

end Janko4.LocalStructure.MathieuHallActors
