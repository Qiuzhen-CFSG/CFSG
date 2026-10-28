module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.AlternatingFiveActions.QuotientTransport
public import CFSG.Quasithin.Chapter1.Section03.Terminal.AlternatingFiveActions.ForcedOuter
public import CFSG.Quasithin.Chapter1.Section03.Terminal.AlternatingFiveActions.JankoOneStabilizer
public import CFSG.Quasithin.Chapter1.Section03.Terminal.AlternatingFiveActions.LinearTwoStabilizer
public import Theory.SpecificGroups.AlternatingFiveCore

/-!
# The A₅ action contradiction in the terminal lemma

An actual A₅ image of B in Y/O₂(Y) has trivial two-core. Consequently
B ∩ O₂(Y) = O₂(B), and the restricted quotient map identifies B/O₂(B)
with that image. The imported transport intertwines the normalizer actions
and lifts intrinsic inner-stabilizer conclusions back to the ambient group.

The imported forced-action theorem derives an outer actor in N_T(B) from
the genuine swapped-component source input. The intrinsic J₁ and prime-field
PSL₂ stabilizer theorems imply that a subgroup normalizing both B and Y acts
innerly on B/O₂(B), when the actual image of B is A₅ and Y/O₂(Y) is one of
these models. Thus N_T(B) cannot normalize such an overgroup Y. This closes
the action contradiction; the selection of the overgroup by 1.2.8 and 1.3.4
and the resulting source maximality remain with the terminal lemma's owner.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, final paragraph of Lemma 1.3.9, printed p.514.
The relevant prime-field case of A.3.12(8) also requires q ≡ ±3 modulo 8.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Terminal
variable {G : Type*} [Group G]

/-- An actual A₅ quotient image has trivial two-core. -/
theorem image_twoCore_eq_bot_of_alternatingFive {B Y : Subgroup G}
    (hA : Nonempty (twoQuotientImage B Y ≃* alternatingGroup (Fin 5))) :
    pCore 2 (twoQuotientImage B Y) = ⊥ := by
  obtain ⟨e⟩ := hA
  apply (map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp
  rw [pCore_map_iso, alternatingGroup.five_twoCore_eq_bot]

/-- The A₅ embedding proves the exact intersection of the two intrinsic cores. -/
theorem core_eq_intersection_of_alternatingFive_image [Finite G]
    {B Y : Subgroup G} (hBY : B ≤ Y)
    (hA : Nonempty (twoQuotientImage B Y ≃* alternatingGroup (Fin 5))) :
    B.pCoreIn 2 = B ⊓ Y.pCoreIn 2 :=
  core_eq_intersection_of_image_core_eq_bot hBY (image_twoCore_eq_bot_of_alternatingFive hA)

/-- The A₅ image identifies the smaller quotient via its actual projection. -/
noncomputable def alternatingFiveImageEquiv [Finite G]
    {B Y : Subgroup G} (hBY : B ≤ Y)
    (hA : Nonempty (twoQuotientImage B Y ≃* alternatingGroup (Fin 5))) :
    XiQuotient B ≃* twoQuotientImage B Y :=
  twoQuotientImageEquiv hBY (image_twoCore_eq_bot_of_alternatingFive hA)

/-- The A₅-specialized equivalence retains its defining quotient map. -/
theorem alternatingFiveImageEquiv_mk [Finite G]
    {B Y : Subgroup G} (hBY : B ≤ Y)
    (hA : Nonempty (twoQuotientImage B Y ≃* alternatingGroup (Fin 5))) (b : B) :
    alternatingFiveImageEquiv hBY hA (QuotientGroup.mk' (pCore 2 B) b) =
      twoQuotientProjection hBY b := rfl

/-- The A₅ identification intertwines the actions of an element normalizing both groups. -/
theorem alternatingFiveImageEquiv_action [Finite G]
    {B Y : Subgroup G} (hBY : B ≤ Y)
    (hA : Nonempty (twoQuotientImage B Y ≃* alternatingGroup (Fin 5)))
    (s : G) (hsB : s ∈ normalizer (B : Set G)) (hsY : s ∈ normalizer (Y : Set G))
    (x : XiQuotient B) :
    (alternatingFiveImageEquiv hBY hA (twoQuotientNormalizerAction B ⟨s, hsB⟩ x) :
        XiQuotient Y) =
      twoQuotientNormalizerAction Y ⟨s, hsY⟩ (alternatingFiveImageEquiv hBY hA x) :=
  twoQuotientImageEquiv_action hBY (image_twoCore_eq_bot_of_alternatingFive hA) s hsB hsY x

/-- The actual J₁ quotient embedding makes every common normalizer act innerly on B/O₂(B). -/
theorem le_innerTwoQuotientNormalizer_of_janko_one_image
    {B Y S : Subgroup G} (hBY : B ≤ Y)
    (hSB : S ≤ normalizer (B : Set G)) (hSY : S ≤ normalizer (Y : Set G))
    (hA : Nonempty (twoQuotientImage B Y ≃* alternatingGroup (Fin 5)))
    (hY : Nonempty (XiQuotient Y ≃* Janko1.Model)) :
    S ≤ innerTwoQuotientNormalizer B := by
  obtain ⟨e⟩ := hY
  obtain ⟨a⟩ := hA
  apply le_innerTwoQuotientNormalizer_of_model_stabilizer hBY hSB hSY e
  exact janko_one_alternatingFive_hasInnerStabilizerAction _
    ⟨((e.subgroupMap (twoQuotientImage B Y)).symm.trans a)⟩

/-- The A.3.12(8) quotient embedding makes every common normalizer act innerly on B/O₂(B).
All prime and congruence restrictions of that source case are retained. -/
theorem le_innerTwoQuotientNormalizer_of_linear_two_image
    {B Y S : Subgroup G} (hBY : B ≤ Y)
    (hSB : S ≤ normalizer (B : Set G)) (hSY : S ≤ normalizer (Y : Set G))
    (hA : Nonempty (twoQuotientImage B Y ≃* alternatingGroup (Fin 5)))
    {q : ℕ} (hq : Section02.A312ExceptionalPrime q)
    (hY : ClassicalGroup.IsPSL (XiQuotient Y) 2 q) :
    S ≤ innerTwoQuotientNormalizer B := by
  obtain ⟨a⟩ := hA
  exact le_innerTwoQuotientNormalizer_of_image_stabilizer hBY hSB hSY
    (LinearTwoStabilizer.hasInnerStabilizerAction_of_isPSL hq hY _ a)

/-- Both source overgroup models exclude outer action on the actual A₅ image.
In particular this applies to any two-group S normalizing both B and Y. -/
theorem le_innerTwoQuotientNormalizer_of_alternatingFive_image
    {B Y S : Subgroup G} (hBY : B ≤ Y)
    (hSB : S ≤ normalizer (B : Set G)) (hSY : S ≤ normalizer (Y : Set G))
    (hA : Nonempty (twoQuotientImage B Y ≃* alternatingGroup (Fin 5)))
    (hY : Nonempty (XiQuotient Y ≃* Janko1.Model) ∨
      ∃ q : ℕ, Section02.A312ExceptionalPrime q ∧
        ClassicalGroup.IsPSL (XiQuotient Y) 2 q) :
    S ≤ innerTwoQuotientNormalizer B := by
  rcases hY with hJ | ⟨q, hq, hL⟩
  · exact le_innerTwoQuotientNormalizer_of_janko_one_image hBY hSB hSY hA hJ
  · exact le_innerTwoQuotientNormalizer_of_linear_two_image hBY hSB hSY hA hq hL

/-- The final A₅ action contradiction in 1.3.9(1): the actual component
normalizer cannot normalize an overgroup with either source quotient embedding.
The image identification supplies B/O₂(B) ≃ A₅, and the local input supplies
the outer actor; neither action assertion is an additional hypothesis. -/
theorem not_normalizes_overgroup_of_swapped_alternatingFive [Finite G]
    {𝒦 : GroupClass} {p : ℕ} {T X P H B Y : Subgroup G}
    (hSQTK : IsSQTK 𝒦 H) (hchar : HasCharacteristicTwo H) (hH : H = B ⊔ T)
    (hT : IsSylowIn 2 T H) (hB : B ∈ cComponentsIn H) (hX : X ∈ Xi G T)
    (hXB : X ≤ componentOrbit B T) (h : XiEmbedding.LocalInput p T X P H)
    (hswap : XiEmbedding.SwappedFactors T P B) (hBY : B ≤ Y)
    (hA : Nonempty (twoQuotientImage B Y ≃* alternatingGroup (Fin 5)))
    (hY : Nonempty (XiQuotient Y ≃* Janko1.Model) ∨
      ∃ q : ℕ, Section02.A312ExceptionalPrime q ∧
        ClassicalGroup.IsPSL (XiQuotient Y) 2 q) :
    ¬ T ⊓ normalizer B ≤ normalizer Y := by
  intro hNY
  have hquot : Nonempty (XiQuotient B ≃* alternatingGroup (Fin 5)) :=
    ⟨(alternatingFiveImageEquiv hBY hA).trans hA.some⟩
  exact ForcedOuter.forced_outer_of_swapped_alternatingFive
    hSQTK hchar hH hT hB hX hXB h hswap hquot
    (le_innerTwoQuotientNormalizer_of_alternatingFive_image hBY inf_le_right hNY hA hY)

end CFSG.Quasithin.Chapter1.Terminal
