module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InnerInvolutionCores.Noncentral
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# The literal rank-four actor in the noncentral J₂ centralizer

The checked isomorphism of the entire centralizer of `GeneratorPair.a` with
E₄ × A₅ embeds the product of E₄ and the usual four-letter Klein subgroup.
Its image has order sixteen, is elementary abelian, and contains the specified
involution. The central E₄ is exactly the image of the centralizer's center.
An elementary actor of rank at least three containing this involution has
nontrivial projection to the actual A₅ factor.

These are the group inputs to the natural-module calculation in K.4.5,
Aschbacher–Smith, printed p.460/PDF p.471. Cubic action and fixed codimension
are separate representation obligations; no such conclusion is assumed here.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.InnerInvolutionCores

/-- The full centralizer in the retained degree-100 carrier. -/
abbrev involutionCentralizer := centralizer ({a} : Set Carrier)

/-- The checked product isomorphism followed by the actual subgroup inclusion. -/
def centralizerEmbedding : E4 × A5 →* Carrier :=
  involutionCentralizer.subtype.comp a_centralizer_equiv.symm.toMonoidHom

theorem centralizerEmbedding_injective : Function.Injective centralizerEmbedding :=
  involutionCentralizer.subtype_injective.comp a_centralizer_equiv.symm.injective

def centralFour : Subgroup Carrier :=
  ((⊤ : Subgroup E4).prod (⊥ : Subgroup A5)).map centralizerEmbedding

def fourLetters : Finset (Fin 5) := Finset.univ.erase 4

private theorem fourLetters_card : Nat.card fourLetters = 4 := by
  simp [fourLetters]

/-- The Klein four on the first four of the five alternating-group letters. -/
def alternatingFour : Subgroup A5 :=
  (alternatingGroup.kleinFour fourLetters).map (alternatingGroup.ofSubtype fourLetters)

theorem alternatingFour_card : Nat.card alternatingFour = 4 := by
  rw [alternatingFour, Subgroup.card_map_of_injective alternatingGroup.ofSubtype_injective]
  exact alternatingGroup.kleinFour_card_of_card_eq_four fourLetters_card

theorem alternatingFour_elementary : IsElementaryAbelian 2 alternatingFour := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsKleinFour (alternatingGroup.kleinFour fourLetters) :=
    alternatingGroup.kleinFour_isKleinFour fourLetters_card
  let : IsElementaryAbelian 2 (alternatingGroup.kleinFour fourLetters) :=
    { toIsMulCommutative := IsKleinFour.isMulCommutative
      exponent_dvd_p := by simp }
  exact IsElementaryAbelian.map _

/-- The proposed attaining actor, as a concrete subgroup of the actual J₂ carrier. -/
def actor : Subgroup Carrier :=
  ((⊤ : Subgroup E4).prod alternatingFour).map centralizerEmbedding

theorem centralFour_card : Nat.card centralFour = 4 := by
  rw [centralFour, Subgroup.card_map_of_injective centralizerEmbedding_injective,
    Nat.card_congr ((⊤ : Subgroup E4).prodEquiv (⊥ : Subgroup A5)).toEquiv,
    Nat.card_prod]
  simp [E4, C2, Nat.card_eq_fintype_card]

theorem actor_card : Nat.card actor = 16 := by
  rw [actor, Subgroup.card_map_of_injective centralizerEmbedding_injective,
    Nat.card_congr ((⊤ : Subgroup E4).prodEquiv alternatingFour).toEquiv,
    Nat.card_prod, alternatingFour_card]
  simp [E4, C2, Nat.card_eq_fintype_card]

theorem actor_rank : rank actor = 4 := by
  rw [rank, actor_card]
  exact Nat.log_pow (by decide) 4

theorem actor_elementary : IsElementaryTwo actor := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 alternatingFour := alternatingFour_elementary
  let : IsElementaryAbelian 2 ((⊤ : Subgroup E4).prod alternatingFour) := {
    toIsMulCommutative := ⟨⟨fun x y => by
      apply Subtype.ext
      apply Prod.ext
      · exact mul_comm x.val.1 y.val.1
      · exact congrArg Subtype.val
          (mul_comm (⟨x.val.2, x.property.2⟩ : alternatingFour)
            (⟨y.val.2, y.property.2⟩ : alternatingFour))⟩⟩
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      apply Subtype.ext
      apply Prod.ext
      · change x.val.1 ^ 2 = 1
        have hs : ∀ y : E4, y ^ 2 = 1 := by decide +kernel
        exact hs _
      · exact elemPow_eq_one_of_isElementaryAbelian x.val.2 x.property.2 }
  refine ⟨?_, IsElementaryAbelian.map _⟩
  intro h
  have hc := actor_card
  rw [h, Subgroup.card_bot] at hc
  omega

theorem centralFour_le_actor : centralFour ≤ actor :=
  Subgroup.map_mono (Subgroup.prod_mono le_rfl bot_le)

theorem actor_le_centralizer : actor ≤ involutionCentralizer := by
  rintro _ ⟨x, _, rfl⟩
  exact (a_centralizer_equiv.symm x).property

theorem a_mem_centralFour : a ∈ centralFour := by
  let t : involutionCentralizer := ⟨a, mem_centralizer_singleton_iff.mpr rfl⟩
  have ht (x : involutionCentralizer) : x * t = t * x := by
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp x.property
  have he : (a_centralizer_equiv t).2 ∈ center A5 := by
    apply mem_center_iff.mpr
    intro x
    have h := congrArg (fun y : involutionCentralizer => (a_centralizer_equiv y).2)
      (ht (a_centralizer_equiv.symm (1, x)))
    simpa only [map_mul, MulEquiv.apply_symm_apply, Prod.snd_mul] using h
  have hbot : center A5 = ⊥ := alternatingGroup.center_eq_bot (by simp)
  rw [hbot, mem_bot] at he
  refine ⟨a_centralizer_equiv t, ⟨mem_top _, he⟩, ?_⟩
  change (a_centralizer_equiv.symm (a_centralizer_equiv t)).val = a
  rw [MulEquiv.symm_apply_apply]

theorem a_mem_actor : a ∈ actor := centralFour_le_actor a_mem_centralFour

theorem rank_three_not_le_centralFour (A : Subgroup Carrier) (hA : 3 ≤ rank A) :
    ¬ A ≤ centralFour := by
  intro h
  have hc := Nat.card_le_card_of_injective (Subgroup.inclusion h)
    (Subgroup.inclusion_injective h)
  rw [centralFour_card] at hc
  have hr : 2 ^ 3 ≤ Nat.card A :=
    (Nat.le_log_iff_pow_le (by decide) Nat.card_pos.ne').mp hA
  omega

/-- The central four-group is the literal image of the full centralizer's center. -/
theorem centralFour_eq_center :
    centralFour = (center involutionCentralizer).map involutionCentralizer.subtype := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨a_centralizer_equiv.symm x, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply a_centralizer_equiv.injective
    simp only [map_mul, MulEquiv.apply_symm_apply]
    apply Prod.ext
    · exact mul_comm _ _
    · have hx2 : x.2 = 1 := hx.2
      simp only [Prod.snd_mul, hx2, mul_one, one_mul]
  · rintro _ ⟨x, hx, rfl⟩
    have he : (a_centralizer_equiv x).2 ∈ center A5 := by
      apply mem_center_iff.mpr
      intro y
      have h := congrArg (fun z : involutionCentralizer => (a_centralizer_equiv z).2)
        (mem_center_iff.mp hx (a_centralizer_equiv.symm (1, y)))
      simpa only [map_mul, MulEquiv.apply_symm_apply, Prod.snd_mul] using h
    have hbot : center A5 = ⊥ := alternatingGroup.center_eq_bot (by simp)
    rw [hbot, mem_bot] at he
    refine ⟨a_centralizer_equiv x, ⟨mem_top _, he⟩, ?_⟩
    change (a_centralizer_equiv.symm (a_centralizer_equiv x)).val = x.val
    rw [MulEquiv.symm_apply_apply]

/-- Elementary actors containing the specified involution lie in its full centralizer. -/
theorem le_centralizer_of_elementary (A : Subgroup Carrier)
    (hA : IsElementaryTwo A) (ha : a ∈ A) : A ≤ involutionCentralizer := by
  let : IsElementaryAbelian 2 A := hA.2
  intro x hx
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : A) (⟨a, ha⟩ : A))

/-- The nontrivial A₅ coordinate is forced by the actual actor's rank.
This supplies the group premise of the local fixed-space calculation. -/
theorem exists_nontrivial_simple_coordinate (A : Subgroup Carrier)
    (hA : IsElementaryTwo A) (ha : a ∈ A) (hr : 3 ≤ rank A) :
    ∃ x : E4 × A5, centralizerEmbedding x ∈ A ∧ x.2 ≠ 1 := by
  classical
  obtain ⟨g, hgA, hgC⟩ := Set.not_subset.mp (rank_three_not_le_centralFour A hr)
  let c : involutionCentralizer := ⟨g, le_centralizer_of_elementary A hA ha hgA⟩
  have hval : centralizerEmbedding (a_centralizer_equiv c) = g := by
    change (a_centralizer_equiv.symm (a_centralizer_equiv c)).val = g
    rw [MulEquiv.symm_apply_apply]
  refine ⟨a_centralizer_equiv c, hval.symm ▸ hgA, ?_⟩
  intro h
  exact hgC ⟨a_centralizer_equiv c, ⟨mem_top _, h⟩, hval⟩

end CFSG.Quasithin.ChapterK.JankoTwo.NaturalLocalAction
