module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.JankoTwoAction.Transport
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.Seed

/-!+# The marked local calculation needed in Aut(J₂)

The fixed radical is the inner image of the actual ATLAS `Seed.q₂`.
Its normalizer is formed in the full automorphism group. `LocalMarking`
asks for a single conjugation carrying the source pair Y₊ ≤ Y₊S to
the two-residual of this normalizer and the normalizer itself.

The reductions below transport the center bound and centralizer calculation
through that marking. Existence of the marking and both concrete calculations
are separate proof obligations; neither is asserted here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.42,
printed p.1138; GLS3 Table 5.3g. The underlying ATLAS words and their
attribution are retained by `ExceptionalParabolics.Seed`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.JankoTwoAction

abbrev Model := MulAut Sporadic.LeechRelated.J2.Carrier

/-- The fixed inner radical, embedded by the literal conjugation action. -/
def secondRadical : Subgroup Model :=
  Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.q₂.map MulAut.conj

/-- The normalizer in all automorphisms, including the outer automorphisms. -/
def secondNormalizer : Subgroup Model := normalizer (secondRadical : Set Model)

/-- The literal two-residual of the fixed normalizer, embedded in Aut(J₂). -/
noncomputable def secondResidual : Subgroup Model :=
  Stellmacher.twoResidualAmbient secondNormalizer

variable {G : Type*} [Group G]
variable {I L M Y S V V₁ V₂ Yplus : Subgroup G} [(L.subgroupOf I).Normal]

/-- A compatible conjugation of the two actual subgroup images.
This contains no commutator-order or centralizer conclusion. -/
structure LocalMarking (j : JankoTwoIdentification I L) (Yplus S : Subgroup G) where
  conjugator : Model
  join_eq : (modelImage j (Yplus ⊔ S)).map (MulAut.conj conjugator).toMonoidHom =
    secondNormalizer
  yplus_eq : (modelImage j Yplus).map (MulAut.conj conjugator).toMonoidHom =
    secondResidual

/-- Inherit simplicity from the source component through its specified equivalence. -/
theorem carrier_simple (d : ComponentSetup I L M Yplus S)
    (j : JankoTwoIdentification I L) : IsSimpleGroup Sporadic.LeechRelated.J2.Carrier :=
  (MulEquiv.isSimpleGroup_congr j.component).mp d.simple_image

/-- The inner-compatibility clause identifies the whole component image. -/
theorem modelImage_component (j : JankoTwoIdentification I L) :
    modelImage j L = (MulAut.conj : Sporadic.LeechRelated.J2.Carrier →* Model).range := by
  rw [modelImage_eq]
  ext f
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨j.component ⟨x, hx⟩, (j.inner_compatible ⟨x, hx⟩).symm⟩
  · rintro ⟨g, rfl⟩
    obtain ⟨x, hx⟩ := j.component.surjective g
    exact ⟨x, x.property, (j.inner_compatible x).trans (congrArg MulAut.conj hx)⟩

/-- The local core-center order is invariant under the specified conjugation. -/
theorem LocalMarking.radical_center_card
    {j : JankoTwoIdentification I L} (m : LocalMarking j Yplus S) :
    Nat.card (center ((modelImage j (Yplus ⊔ S)).pCoreIn 2)) =
      Nat.card (center (secondNormalizer.pCoreIn 2)) := by
  let e := MulAut.conj m.conjugator
  have hcore : (((modelImage j (Yplus ⊔ S)).pCoreIn 2).map e.toMonoidHom) =
      secondNormalizer.pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 _ e.toMonoidHom e.injective, m.join_eq]
  let c := ((modelImage j (Yplus ⊔ S)).pCoreIn 2).equivMapOfInjective
    e.toMonoidHom e.injective
  exact Nat.card_congr (centerCongr (c.trans (MulEquiv.subgroupCongr hcore))).toEquiv

/-- Transport a trivial fixed normalizer-residual centralizer to the actual image. -/
theorem LocalMarking.centralizer_eq_bot
    {j : JankoTwoIdentification I L} (m : LocalMarking j Yplus S)
    (hc : centralizer (secondResidual : Set Model) = ⊥) :
    centralizer (modelImage j Yplus : Set Model) = ⊥ := by
  apply centralizer_eq_bot_of_model _ (MulAut.conj m.conjugator)
  rwa [m.yplus_eq]

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.JankoTwoAction
