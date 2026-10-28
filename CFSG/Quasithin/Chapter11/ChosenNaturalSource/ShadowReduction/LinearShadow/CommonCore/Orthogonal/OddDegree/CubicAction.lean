module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Source
public import Theory.SpecificGroups.SL2.CubicFixedVectors
public import Theory.GroupTheory.PrimeOrderLift
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Hall.Geometry

/-!
# Fixed points of the actual cubic subgroup on the common core

An order-three element survives the two-core quotient. On each of the
marked natural SL₂ summands it fixes only zero, so its fixed subgroup in P
is trivial. The calculation uses the independent coefficient field of P;
no compatibility with the field of V is assumed. Applied to a cubic
subgroup of the original D₀, it discharges the common-core fixed-point
premise in the source coprime-action contradiction.

Source: Aschbacher--Smith, printed p.774, the even-degree paragraph.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] [Finite G] {V H : Subgroup G} {h : G} {F : BinaryField}

/-- Cubic fixed-point freeness on the literal marked P, over its own field. -/
theorem PairNaturalMarking.cubic_fixed_eq_bot (c : PairNaturalMarking V H h F)
    (C : Subgroup G) (hC : Nat.card C = 3) (hCK : C ≤ outsideResidual H) :
    pairCore V H h ⊓ centralizer (C : Set G) = ⊥ := by
  let : Nontrivial C := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x,hx⟩ := exists_ne (1 : C)
  let k : outsideResidual H := inclusion hCK x
  have hx3 : x ^ 3 = 1 := by simpa only [hC] using pow_card_eq_one' (x := x)
  have hk3 : orderOf k = 3 := by
    apply orderOf_eq_prime
    · exact (map_pow (inclusion hCK) x 3).symm.trans (by rw [hx3,map_one])
    · intro he
      exact hx ((inclusion_injective hCK) (he.trans (map_one _).symm))
  let q := c.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (outsideResidual H)))
  have hkq : q.ker = pCore 2 (outsideResidual H) := by
    ext z
    change c.quotientEquiv (QuotientGroup.mk' _ z) = 1 ↔ _
    rw [c.quotientEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff z
  have hq3 : orderOf (q k) = 3 := by
    rw [q.orderOf_map_eq_of_coprime_of_isPGroup_ker
      (hkq ▸ pCore_isPGroup) k (by rw [hk3]; decide),hk3]
  apply bot_unique
  rintro v ⟨hv,hcv⟩
  have hfix : pairResidualAction V H h c.normalizes k ⟨v,hv⟩ = ⟨v,hv⟩ := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hcv x x.property)
  have hz : c.coordinates ⟨v,hv⟩ = 1 := by
    change (c.coordinates ⟨v,hv⟩).toAdd = 0
    funext i
    have hi := c.intertwines k ⟨v,hv⟩ i
    rw [hfix] at hi
    exact Matrix.SL2.cubic_fixed_eq_zero (q k) hq3 _ hi.symm
  have hv1 : (⟨v,hv⟩ : pairCore V H h) = 1 :=
    c.coordinates.injective (hz.trans c.coordinates.map_one.symm)
  exact congrArg Subtype.val hv1

variable {T : Sylow 2 G} {L X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)}
    (d : OrthogonalInput D S m f H X A h)

include d

/-- Only cubic existence and the scalar conclusion remain in this source branch. -/
theorem source_cubic_contradiction_of_scalar (C : Subgroup G) (hC : Nat.card C = 3)
    (hCA : C ≤ oddCartanPart A) (hscalar : ⁅L,C⁆ ≤ V) : False := by
  have hCK := hCA.trans (oddCartanPart_le_residual_of_hall
    (normalizer (L : Set G)) A d.hall_le d.hall)
  exact source_cubic_contradiction d C hC (hCK.trans d.pair_natural.normalizes)
    (d.pair_natural.cubic_fixed_eq_bot C hC hCK) hscalar


/-- The lifted Borel forces a cubic divisor in the actual Hall group. -/
theorem source_three_dvd_hall (heven : Even S.field.degree) : 3 ∣ Nat.card A := by
  have hmod : 2 ^ S.field.degree % 3 = 1 := by
    obtain ⟨k,hk⟩ := heven
    rw [hk,← two_mul,pow_mul,Nat.pow_mod]
    norm_num
  have h3units : 3 ∣ Nat.card S.field.Carrierˣ := by
    rw [Nat.card_units,S.field.card_eq]
    have hp := pow_pos (by decide : 0 < (2 : ℕ)) S.field.degree
    omega
  let K := outsideResidual H
  let R := Hall.residualSylow d.source
  let N := normalizer (R : Set K)
  let J := H ⊓ normalizer (L : Set G)
  let j : N →* J :=
    { toFun x := ⟨x.val.val,outsideResidual_le H x.val.property,
        (Hall.source_residual_borel d.source d.closure_natural).ge x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : J => (z : G)) he
  obtain ⟨q,hq,_⟩ := Matrix.SpecialLinearGroup.exists_sylowNormalizer_diagonal
    (Hall.quotientMap d.closure_natural) (Hall.quotientMap_surjective d.closure_natural) R
    (by rw [Hall.quotientMap_ker]; exact pCore_isPGroup.le_sylow_of_normal _)
  have h3J : 3 ∣ Nat.card J :=
    (h3units.trans (card_dvd_of_surjective q hq)).trans (card_dvd_of_injective j hj)
  have hindex : ¬ 3 ∣ (A.subgroupOf J).index := by
    intro hi
    exact d.hall.p_in_pi_of_p_dvd_index ⟨3,Nat.prime_three⟩ hi (by change (3 : ℕ) ≠ 2; decide)
  rw [← (A.subgroupOf J).card_mul_index] at h3J
  have h3A := (Nat.prime_three.dvd_mul.mp h3J).resolve_right hindex
  rwa [Nat.card_congr (subgroupOfEquivOfLe d.hall_le).toEquiv] at h3A

/-- Construct the source D₃ inside D₀, with its actual fixed subgroup on P. -/
theorem source_cubic_subgroup (heven : Even S.field.degree) :
    ∃ C : Subgroup G, Nat.card C = 3 ∧ C ≤ oddCartanPart A ∧
      C ≤ X ∧ C ≤ normalizer (pairCore V H h : Set G) ∧
      pairCore V H h ⊓ centralizer (C : Set G) = ⊥ := by
  have ho : Odd (Nat.card A) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe d.hall_le).toEquiv]
    exact OddHall.odd_hall_odd d.hall
  obtain ⟨j,hj⟩ := Hall.source_units_embedding d.source d.closure_natural A d.hall_le ho
  let : IsCyclic A := isCyclic_of_injective j hj
  obtain ⟨C,hC⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) 3 (n := 1)
    (by simpa using source_three_dvd_hall d heven)
  have hC3 : Nat.card C = 3 := by simpa using hC
  have hCC : C ≤ pCore 3 A :=
    le_sSup ⟨inferInstance,IsPGroup.of_card (p := 3) (n := 1) hC⟩
  let B := C.map A.subtype
  have hB3 : Nat.card B = 3 :=
    (Nat.card_congr (C.equivMapOfInjective A.subtype A.subtype_injective).symm.toEquiv).trans hC3
  have hBA : B ≤ oddCartanPart A := by
    rintro _ ⟨a,ha,rfl⟩
    refine ⟨a,mem_sup_right ⟨⟨a,hCC ha⟩,?_,rfl⟩,rfl⟩
    apply Subgroup.subset_closure
    change (⟨a,hCC ha⟩ : pCore 3 A) ^ (3^1) = 1
    apply Subtype.ext
    change a ^ (3^1) = 1
    have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨a,ha⟩ : C)))
    change a ^ Nat.card C = 1 at hh
    simpa only [hC3,pow_one] using hh
  have hBK := hBA.trans (oddCartanPart_le_residual_of_hall
    (normalizer (L : Set G)) A d.hall_le d.hall)
  exact ⟨B,hB3,hBA,hBA.trans d.oddCartan_le,hBK.trans d.pair_natural.normalizes,
    d.pair_natural.cubic_fixed_eq_bot B hB3 hBK⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
