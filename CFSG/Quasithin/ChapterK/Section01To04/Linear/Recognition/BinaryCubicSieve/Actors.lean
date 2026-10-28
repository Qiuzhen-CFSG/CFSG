module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.Setup
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.Transport
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.Representation.CharacteristicTwoIrreducibleRank
public import Theory.Representation.Quotient
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Models
public import Theory.SpecificGroups.BinaryLinear.AutomorphismTwoRank

/-!
# The original cubic actors in the binary linear models

An actual component equivalence marks a representation of SL₄(2) or SL₅(2).
The ambient representation embeds in its full linear normalizer, preserving
the action of every element, the rank of every elementary actor and its fixed
codimension. Thus actors outside the component are retained. The intrinsic
automorphism two-ranks bound actor rank by four and six, respectively.

These bounds concern fixed codimension, not the dimension of the whole module.
The multiple-support displacement estimates needed for the latter are separate.
Source: Aschbacher–Smith, K.3.2, printed pp.451,454–455; GM04, Table 7.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve

open Representation Representation.BinaryOffender Theory.GroupTheory

variable {G D V : Type*} [Group G] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) {L : Subgroup G}

/-- The component action marked by the supplied group equivalence. -/
abbrev modelAction (e : L ≃* D) : Representation (ZMod 2) D V :=
  (ρ.comp L.subtype).comp e.symm.toMonoidHom

/-- Changing the marking and then inflating gives the original marked action.
In particular this applies to the canonical binary SL-to-PSL equivalences. -/
theorem modelAction_trans_comp {E : Type*} [Group E]
    (e : L ≃* D) (f : D ≃* E) :
    (modelAction ρ (e.trans f)).comp f.toMonoidHom = modelAction ρ e := by
  ext g v
  simp [modelAction]

/-- Faithfulness is preserved by the actual component marking. -/
theorem modelAction_injective (hf : Function.Injective ρ) (e : L ≃* D) :
    Function.Injective (modelAction ρ e) :=
  (hf.comp L.subtype_injective).comp e.symm.injective

/-- Irreducibility is transported through the supplied equivalence. -/
theorem modelAction_irreducible
    (hi : IsIrreducible (ρ.comp L.subtype)) (e : L ≃* D) :
    IsIrreducible (modelAction ρ e) :=
  (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
    (ρ.comp L.subtype)).mpr hi

/-- The marking changes neither the component image nor its normalizer. -/
theorem modelAction_image (e : L ≃* D) :
    actionImage (modelAction ρ e) = actionImage (ρ.comp L.subtype) := by
  ext x
  constructor
  · rintro ⟨d, rfl⟩
    exact ⟨e.symm d, Units.ext rfl⟩
  · rintro ⟨l, rfl⟩
    refine ⟨e l, Units.ext ?_⟩
    change ρ ((e.symm (e l) : L) : G) = ρ l
    rw [e.symm_apply_apply]

/-- The literal ambient action map into the marked component normalizer. -/
def ambientToNormalizer [L.Normal] (e : L ≃* D) :
    G →* linearNormalizer (modelAction ρ e) :=
  ρ.asGroupHom.codRestrict _ (by
    intro g
    have hg := actionImage_le_linearNormalizer ρ L ⟨g, rfl⟩
    change ρ.asGroupHom g ∈ Subgroup.normalizer
      (actionImage (modelAction ρ e) : Set _)
    rwa [modelAction_image])

/-- No ambient elements are discarded when the source action is faithful. -/
theorem ambientToNormalizer_injective [L.Normal]
    (hf : Function.Injective ρ) (e : L ≃* D) :
    Function.Injective (ambientToNormalizer ρ e) := by
  intro x y h
  apply hf
  exact congrArg (fun z : linearNormalizer (modelAction ρ e) => z.val.val) h

/-- The inclusion preserves the literal action on the original binary space. -/
@[simp] theorem ambientToNormalizer_apply [L.Normal] (e : L ≃* D) (g : G) (v : V) :
    normalizerRepresentation (modelAction ρ e) (ambientToNormalizer ρ e g) v = ρ g v := rfl

variable {ρ}

/-- Automorphism rank bounds apply to the original ambient group. -/
theorem source_twoRank_le {K : GroupClass} (h : SourceHypothesis K ρ L)
    (e : L ≃* D) {r : ℕ} (hr : primeRank 2 (MulAut D) ≤ r) :
    primeRank 2 G ≤ r := by
  let : Finite G := h.finite_group
  let : Finite D := Finite.of_surjective e e.surjective
  let : L.Normal := h.fitting ▸ inferInstance
  let : IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hb := CharacteristicTwoIrreducible.primeRank_le_automorphisms ρ L h.faithful
  rw [primeRank_equiv 2 (MulAut.congr e)] at hb
  exact hb.trans hr

/-- A bounded cubic actor in the full marked normalizer, constructed as the
image of an original ambient actor. No SQTK premise on the normalizer is used. -/
theorem source_model_actor {K : GroupClass} (h : SourceHypothesis K ρ L)
    (e : L ≃* D) {r : ℕ} (hr : primeRank 2 G ≤ r) :
    ∃ A : Subgroup (linearNormalizer (modelAction ρ e)),
      IsElementaryTwo A ∧ IsCubic (normalizerRepresentation (modelAction ρ e)) A ∧
      rank A ≤ r ∧
      fixedCodim (normalizerRepresentation (modelAction ρ e)) A ≤ 2 * rank A ∧
      fixedCodim (normalizerRepresentation (modelAction ρ e)) A ≤ 2 * r := by
  let : Finite G := h.finite_group
  let : L.Normal := h.fitting ▸ inferInstance
  obtain ⟨B, hB, hc, hd⟩ := (cubicRatio_le_nat_iff ρ 2).mp h.cubic_le_two
  have hcard := (primeRank_le_iff_elementary_card_le G).mp hr B hB.2
  have hb : rank B ≤ r := by
    have hh := Nat.log_mono_right (b := 2) hcard
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hh
  let f := ambientToNormalizer ρ e
  have hf := ambientToNormalizer_injective ρ h.faithful e
  obtain ⟨he, hc', hd'⟩ := Exceptional.cubic_actor_map_equivariant ρ
    (normalizerRepresentation (modelAction ρ e)) f hf
    (LinearEquiv.refl _ _) (fun _ _ => rfl) hB hc hd
  have hr' : rank (B.map f) ≤ r := by rwa [rank_map_injective f hf]
  exact ⟨B.map f, he, hc', hr', hd', hd'.trans (Nat.mul_le_mul_left 2 hr')⟩

/-- Rank four is an ambient bound, including graph actors. -/
theorem source_four_twoRank_le {K : GroupClass} (h : SourceHypothesis K ρ L)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    primeRank 2 G ≤ 4 :=
  source_twoRank_le h (e.trans Atlas.Order20160A8.sl4TwoEquivPSL)
    BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le

/-- The degree-five rank bound uses the literal canonical SL-to-PSL map. -/
theorem source_five_twoRank_le {K : GroupClass} (h : SourceHypothesis K ρ L)
    (e : L ≃* SL5TenDimensional.Group) : primeRank 2 G ≤ 6 :=
  source_twoRank_le h (e.trans SL5TenDimensional.projectiveEquiv)
    BinaryLinear.AutomorphismTwoRank.psl5_two_rank_le

/-- The four-dimensional group supplies an actor of codimension at most eight.
This is not a bound on the dimension of V. -/
theorem source_four_actor {K : GroupClass} (h : SourceHypothesis K ρ L)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    ∃ A : Subgroup (linearNormalizer (modelAction ρ e)),
      IsElementaryTwo A ∧ IsCubic (normalizerRepresentation (modelAction ρ e)) A ∧
      rank A ≤ 4 ∧
      fixedCodim (normalizerRepresentation (modelAction ρ e)) A ≤ 2 * rank A ∧
      fixedCodim (normalizerRepresentation (modelAction ρ e)) A ≤ 8 :=
  source_model_actor h e (source_four_twoRank_le h e)

/-- The five-dimensional group supplies an actor of codimension at most twelve.
This is not a bound on the dimension of V. -/
theorem source_five_actor {K : GroupClass} (h : SourceHypothesis K ρ L)
    (e : L ≃* SL5TenDimensional.Group) :
    ∃ A : Subgroup (linearNormalizer (modelAction ρ e)),
      IsElementaryTwo A ∧ IsCubic (normalizerRepresentation (modelAction ρ e)) A ∧
      rank A ≤ 6 ∧
      fixedCodim (normalizerRepresentation (modelAction ρ e)) A ≤ 2 * rank A ∧
      fixedCodim (normalizerRepresentation (modelAction ρ e)) A ≤ 12 :=
  source_model_actor h e (source_five_twoRank_le h e)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve
