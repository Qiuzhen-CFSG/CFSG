module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.Reduction
public import Theory.SpecificGroups.Suzuki.FieldTorus
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The cubic field-action contradiction on the lifted Borel

Every element of the first split torus lifts to O²(B): lift it first to
B, then use its odd order in the image and surjective residual transport.
If [Lᵥ,O²(B)] lies in O₂(Lᵥ), its image under the literal central quotient
has two-power order. For a field actor on the first Suzuki factor these
images are exactly the torus displacements. The intrinsic matrix calculation
forces that field automorphism to be identity, contradicting order three.

No central kernel is discarded, and no field action is inferred from an
unconnected family label. The source owner supplies the actual conjugation
identity for its chosen actor and quotient marking.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]
variable {T K L : Subgroup G} {v : G}

namespace Marking

/-- The first-factor map on the entire lifted Borel. -/
def firstBorelMap (d : Marking T K v) : d.borel →* SuzukiMatrixGroup d.parameter :=
  (MonoidHom.fst _ _).comp (d.quotientMap.comp (inclusion d.borel_le_orbit))

theorem exists_residual_torus_lift (d : Marking T K v)
    (t : SuzukiMatrixGroup d.parameter) (ht : t ∈ SuzukiSplitTorus d.parameter) :
    ∃ b : d.borel, b ∈ pResidual 2 d.borel ∧ d.firstBorelMap b = t := by
  have htB : t ∈ SuzukiBorelSubgroup d.parameter := by
    rw [suzukiBorelSubgroup_eq_sup]
    exact mem_sup_right ht
  have hp : (t, 1) ∈ d.borelInOrbit.map d.quotientMap := by
    rw [d.borel_image]
    exact ⟨htB, one_mem _⟩
  obtain ⟨x, hx, he⟩ := hp
  have hr : t ∈ d.firstBorelMap.range := by
    refine ⟨⟨x, ⟨x, hx, rfl⟩⟩, ?_⟩
    exact congrArg Prod.fst he
  let y : d.firstBorelMap.range := ⟨t, hr⟩
  have htord : orderOf t ∣ Nat.card (SuzukiSplitTorus d.parameter) := by
    simpa only [orderOf_mk] using orderOf_dvd_natCard (⟨t, ht⟩ : SuzukiSplitTorus d.parameter)
  have hy : y ∈ pResidual 2 d.firstBorelMap.range :=
    mem_pResidual_of_orderOf_coprime (by
      rw [show orderOf y = orderOf t from orderOf_mk t hr]
      exact (Nat.prime_two.coprime_iff_not_dvd.mpr
        (splitTorus_card_odd d.parameter d.positive).not_two_dvd_nat).of_dvd_right htord)
  rw [← map_pResidual_of_surjective 2 d.firstBorelMap.rangeRestrict
    d.firstBorelMap.rangeRestrict_surjective] at hy
  obtain ⟨b, hb, hyb⟩ := hy
  exact ⟨b, hb, congrArg Subtype.val hyb⟩

end Marking

/-- A literal nontrivial field action on a Suzuki factor is incompatible
with the source commutator bound, including for a nontrivial central cover. -/
theorem field_trivial_of_commutator_bound (d : Marking T K v)
    (c : G) (hc : c ∈ Lv L v) (hcN : c ∈ normalizer (orbit T K v : Set G))
    (σ : BinaryGaloisField (2 * d.parameter + 1) ≃ₐ[ZMod 2]
      BinaryGaloisField (2 * d.parameter + 1))
    (hfield : ∀ x : orbit T K v,
      (d.quotientMap ((orbit T K v).normalizerMonoidHom ⟨c, hcN⟩ x)).1 =
        suzukiFieldAut d.parameter σ (d.quotientMap x).1)
    (hcomm : ⁅Lv L v, (pResidual 2 d.borel).map d.borel.subtype⁆ ≤
      (pCore 2 (Lv L v)).map (Lv L v).subtype) : σ = 1 := by
  apply field_eq_one_of_torus_two_power d.parameter d.positive σ
  intro u
  obtain ⟨b, hb, hbt⟩ := d.exists_residual_torus_lift
    (splitTorusElement d.parameter u) (splitTorusElement_mem _ _)
  have hw : ⁅c, (b : G)⁆ ∈ (pCore 2 (Lv L v)).map (Lv L v).subtype :=
    hcomm (commutator_mem_commutator hc (mem_map_of_mem _ hb))
  have htwo : IsPGroup 2 ((pCore 2 (Lv L v)).map (Lv L v).subtype) :=
    pCore_isPGroup.map _
  obtain ⟨n, hn⟩ := htwo ⟨⁅c, (b : G)⁆, hw⟩
  have hnG : ⁅c, (b : G)⁆ ^ (2 ^ n) = 1 := congrArg Subtype.val hn
  let x : orbit T K v := inclusion d.borel_le_orbit b
  let a := (orbit T K v).normalizerMonoidHom ⟨c, hcN⟩
  have hx : (a x * x⁻¹) ^ (2 ^ n) = 1 := Subtype.ext hnG
  have hm := congrArg (fun z : orbit T K v => (d.quotientMap z).1) hx
  have hxt : (d.quotientMap x).1 = splitTorusElement d.parameter u := hbt
  have haf : (d.quotientMap (a x)).1 =
      suzukiFieldAut d.parameter σ (d.quotientMap x).1 := hfield x
  refine ⟨n, ?_⟩
  simpa only [map_pow, map_mul, map_inv, map_one, Prod.pow_fst, Prod.fst_mul,
    Prod.fst_inv, Prod.fst_one, haf, hxt] using hm

/-- The source order-three action gives the terminal contradiction. -/
theorem cubic_field_contradiction (d : Marking T K v)
    (c : G) (hc : c ∈ Lv L v) (hcN : c ∈ normalizer (orbit T K v : Set G))
    (σ : BinaryGaloisField (2 * d.parameter + 1) ≃ₐ[ZMod 2]
      BinaryGaloisField (2 * d.parameter + 1)) (hσ : orderOf σ = 3)
    (hfield : ∀ x : orbit T K v,
      (d.quotientMap ((orbit T K v).normalizerMonoidHom ⟨c, hcN⟩ x)).1 =
        suzukiFieldAut d.parameter σ (d.quotientMap x).1)
    (hcomm : ⁅Lv L v, (pResidual 2 d.borel).map d.borel.subtype⁆ ≤
      (pCore 2 (Lv L v)).map (Lv L v).subtype) : False := by
  have he := field_trivial_of_commutator_bound d c hc hcN σ hfield hcomm
  simp [he] at hσ

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
