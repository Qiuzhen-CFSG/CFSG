module

public import Theory.Representation.HexacodeAction.NoTransvections
public import Theory.Representation.AlternatingSixStrictOffender
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.CubicRatio

/-!
# The secondary-module equality budget for the hexacode

Retain the full six-space actor and its literal coordinate image in S6.
A faithful scalar-trivial secondary action, together with the whole product
budget two, forces one of two equality cases. An even actor has rank two
and costs two dimensions on each summand. An odd actor has rank three and
costs four dimensions on the hexacode and two on the secondary summand.
The latter image is a strong offender; the former is an equality offender.

This is the numerical reduction in Aschbacher--Smith, 12.7.20, printed
p.846. It does not identify the secondary module or change its S6 marking.
-/

public section
open Atlas.Codes Subgroup Representation.BinaryOffender
namespace Representation.Hexacode.SecondaryEquality

private theorem image_facts (A : Subgroup HexAutomorphisms)
    (hA : IsElementaryTwo A) :
    IsElementaryTwo (A.map hexCoordinateSixHom) ∧
      Nat.card (A.map hexCoordinateSixHom) = Nat.card A ∧
      rank (A.map hexCoordinateSixHom) = rank A ∧ rank A ≤ 3 := by
  let E := A.map hexCoordinateSixHom
  let : IsElementaryAbelian 2 A := hA.2
  have hi := coordinate_injective_on_two_subgroup A hA.2.isPGroup
  have hc : Nat.card E = Nat.card A := by
    change Nat.card (A.map hexCoordinateSixHom) = _
    conv_lhs => rw [← A.range_subtype, ← MonoidHom.range_comp]
    exact (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm
  have hn : E ≠ ⊥ := by
    intro hb
    apply hA.1
    apply le_bot_iff.mp
    intro a ha
    have he : hexCoordinateSixHom a = 1 := by
      have := Subgroup.mem_map_of_mem hexCoordinateSixHom ha
      rw [show A.map hexCoordinateSixHom = ⊥ from hb] at this
      exact this
    exact congrArg Subtype.val (hi (show
      (hexCoordinateSixHom.comp A.subtype) ⟨a,ha⟩ =
        (hexCoordinateSixHom.comp A.subtype) 1 by simpa using he))
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.map hexCoordinateSixHom
  let f : Equiv.Perm (Fin 6) →* Equiv.Perm (Fin 7) :=
    Equiv.Perm.viaEmbeddingHom Fin.castSuccEmb
  have hf : Function.Injective f := Equiv.Perm.viaEmbeddingHom_injective Fin.castSuccEmb
  have hb : Nat.card (E.map f) ≤ 8 :=
    AlternatingSevenConjugatePair.ElementaryGeometry.elementary_card_le
      (@IsElementaryAbelian.map 2 (by infer_instance) (Equiv.Perm (Fin 6))
        (Equiv.Perm (Fin 7)) inferInstance inferInstance E hE f)
  rw [Subgroup.card_map_of_injective hf,hc,hA.card_eq_two_pow_rank] at hb
  exact ⟨⟨hn,hE⟩,hc,congrArg (Nat.log 2) hc,
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb⟩

private theorem full_no_strong : ¬ IsStrongFFModule action := by
  rintro ⟨A,hA⟩
  obtain ⟨B,_,hB,hs⟩ := hA.exists_bestOffender action
  have hc := ThompsonOffenders.full_bestOffender_card B hB
  have hd := ThompsonOffenders.full_bestOffender_fixedSpace_finrank B hB
  have hr : rank B = 2 := by rw [rank,hc]; decide
  have he := fixedCodim_add_finrank action B
  rw [hexacode_finrank,hd] at he
  have := hs.2
  omega

private theorem full_fixedCodim_ge_two (A : Subgroup HexAutomorphisms)
    (hA : A ≠ ⊥) : 2 ≤ fixedCodim action A := by
  have hex : ∃ a ∈ A, a ≠ 1 := by
    by_contra! hn
    apply hA
    exact le_bot_iff.mp (fun a ha => hn a ha)
  obtain ⟨a,ha,ha1⟩ := hex
  have hn : zpowers a ≠ ⊥ := by
    intro he
    have hh := mem_zpowers a
    rw [he] at hh
    exact ha1 hh
  have hp := fixedCodim_pos_of_faithful action action_injective hn
  have ht := no_transvections a
  have hd := Submodule.finrank_mono
    (fixedSpace_antitone action (zpowers_le.mpr ha))
  have h1 := fixedCodim_add_finrank action (zpowers a)
  have h2 := fixedCodim_add_finrank action A
  omega

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The original actor is retained, including its equality case and exact
coordinate image. No natural-module or point-stabilizer marking is inferred. -/
theorem product_budget_cases
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (hσ : Function.Injective σ) (A : Subgroup HexAutomorphisms)
    (hA : IsElementaryTwo A)
    (hb : fixedCodim (action.prod (σ.comp hexCoordinateSixHom)) A ≤ 2 * rank A) :
    (A ≤ hexSign.ker ∧ rank A = 2 ∧ fixedCodim action A = 2 ∧
      fixedCodim σ (A.map hexCoordinateSixHom) = 2 ∧
      IsOffender σ (A.map hexCoordinateSixHom)) ∨
    (¬ A ≤ hexSign.ker ∧ rank A = 3 ∧ fixedCodim action A = 4 ∧
      fixedCodim σ (A.map hexCoordinateSixHom) = 2 ∧
      IsStrongOffender σ (A.map hexCoordinateSixHom)) := by
  classical
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨hE,hcard,hrank,hthree⟩ := image_facts A hA
  have hc : fixedCodim (σ.comp hexCoordinateSixHom) A =
      fixedCodim σ (A.map hexCoordinateSixHom) := by
    unfold fixedCodim
    rw [fixedSpace_comp_map]
  rw [fixedCodim_prod,hc] at hb
  have hhex := full_fixedCodim_ge_two A hA.1
  have hpos := fixedCodim_pos_of_faithful σ hσ hE.1
  have htwo : 2 ≤ rank A := by omega
  have hfour : 2 < Nat.card (A.map hexCoordinateSixHom) := by
    rw [hcard,hA.card_eq_two_pow_rank]
    have : 2^2 ≤ 2 ^ rank A := Nat.pow_le_pow_right (by decide) htwo
    omega
  obtain ⟨b,hbE,hbe,hb1⟩ :=
    AlternatingSixInvolutionDisplacement.even_element_of_card_gt_two _ hfour
  have : IsElementaryAbelian 2 (A.map hexCoordinateSixHom) := hE.2
  have hbo : orderOf b = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian b hbE) hb1
  have hnon : ∃ g : alternatingGroup (Fin 6), σ g ≠ 1 := by
    refine ⟨⟨b,hbe⟩,?_⟩
    intro he
    exact hb1 (hσ (he.trans (map_one σ).symm))
  have hsecondary := AlternatingSixInvolutionDisplacement.fixedCodim_lower_of_even_involution_mem
    σ hnon b hbo hbe hbE
  by_cases he : A ≤ hexSign.ker
  · let Ae := A.subgroupOf hexSign.ker
    have hmap : Ae.map hexSign.ker.subtype = A := map_subgroupOf_eq_of_le he
    have hAe : IsElementaryTwo Ae := by
      refine ⟨?_,IsElementaryAbelian.subgroupOf he⟩
      intro hn
      apply hA.1
      rw [←hmap,hn,Subgroup.map_bot]
    have hr : rank Ae = rank A := by
      rw [←hmap,rank_map_injective _ Subtype.val_injective]
    have hle := ThompsonOffenders.elementary_rank_le_two Ae hAe
    rw [hr] at hle
    have ha : rank A = 2 := by omega
    have hd : fixedCodim action A = 2 := by omega
    have hs : fixedCodim σ (A.map hexCoordinateSixHom) = 2 := by omega
    exact Or.inl ⟨he,ha,hd,hs,hE,by omega⟩
  · have hn : ¬ fixedCodim action A ≤ rank A := by
      intro hle
      have hbest := (show IsOffender action A from ⟨hA,hle⟩).isBest_of_not_strong
        action full_no_strong
      exact he (ThompsonOffenders.bestOffender_le_even A hbest)
    have ha : rank A = 3 := by omega
    have hd : fixedCodim action A = 4 := by omega
    have hs : fixedCodim σ (A.map hexCoordinateSixHom) = 2 := by omega
    exact Or.inr ⟨he,ha,hd,hs,hE,by omega⟩

/-- A cubic ratio bound on the whole product supplies a literal cubic actor
in one of the two equality cases, with the secondary offender retained. -/
theorem cubic_product_cases
    (σ : Representation (ZMod 2) (Equiv.Perm (Fin 6)) V)
    (hσ : Function.Injective σ)
    (hb : cubicRatio (action.prod (σ.comp hexCoordinateSixHom)) ≤ 2) :
    ∃ A : Subgroup HexAutomorphisms, IsElementaryTwo A ∧
      IsCubic (action.prod (σ.comp hexCoordinateSixHom)) A ∧
      ((A ≤ hexSign.ker ∧ rank A = 2 ∧ fixedCodim action A = 2 ∧
        fixedCodim σ (A.map hexCoordinateSixHom) = 2 ∧
        IsOffender σ (A.map hexCoordinateSixHom)) ∨
      (¬ A ≤ hexSign.ker ∧ rank A = 3 ∧ fixedCodim action A = 4 ∧
        fixedCodim σ (A.map hexCoordinateSixHom) = 2 ∧
        IsStrongOffender σ (A.map hexCoordinateSixHom))) := by
  obtain ⟨A,hA,hc,hd⟩ := (cubicRatio_le_nat_iff _ 2).mp hb
  exact ⟨A,hA,hc,product_budget_cases σ hσ A hA hd⟩

end Representation.Hexacode.SecondaryEquality
