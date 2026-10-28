module

public import Theory.SpecificGroups.G2Five.AtlasPresentation
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Mathlib.Algebra.Field.ZMod

/-!
# Identifying the fixed ATLAS presentation of G₂(5)

The order formula for octonion automorphisms reduces identification to two
independent certificates: a surjection from the literal presentation and a
finite upper bound for that presentation. A generating pair satisfying the
relators supplies the surjection by the universal property. The upper bound
then makes this map injective.

The results here are conditional assembly lemmas, not a certificate that the
22 relators are sufficient. In particular, finiteness is an explicit premise:
a bound on `Nat.card` alone would also hold for an infinite group.

Sources: the retained presentation data in `AtlasPresentationSource/`, and the
octonion order formula in `Theory.AtlasPort.LinearGroups.G2.Order`.
-/

namespace G2Five.AtlasPresentation

public instance presentationFivePrime : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Relations on a generating pair give a surjection from the fixed presentation. -/
public theorem hom_surjective {G : Type*} [Group G] (g : Bool → G)
    (hrel : ∀ i, FreeGroup.lift g (relator i) = 1)
    (hgen : Subgroup.closure ({g false, g true} : Set G) = ⊤) :
    Function.Surjective (hom g hrel) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro x hx
  rcases hx with rfl | hx
  · exact ⟨generator false, hom_generator g hrel false⟩
  · obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨generator true, hom_generator g hrel true⟩

/-- The order of the actual split-octonion automorphism group over `ZMod 5`. -/
public theorem card_octonionModel :
    Nat.card (Atlas.G2.Model (ZMod 5)) = 5859000000 := by
  rw [Atlas.G2.card_Model]
  norm_num [Nat.card_eq_fintype_card]

/-- A surjection is faithful once the presentation has the required finite bound. -/
public theorem bijective_of_surjective_of_card_le [Finite Model]
    (f : Model →* Atlas.G2.Model (ZMod 5)) (hf : Function.Surjective f)
    (hcard : Nat.card Model ≤ 5859000000) : Function.Bijective f :=
  hf.bijective_of_nat_card_le (card_octonionModel ▸ hcard)

/-- Assemble the desired equivalence from an independently certified quotient
and finite cardinality bound. -/
public noncomputable def g2EquivOfSurjectiveOfCardLE [Finite Model]
    (f : Model →* Atlas.G2.Model (ZMod 5)) (hf : Function.Surjective f)
    (hcard : Nat.card Model ≤ 5859000000) : Model ≃* Atlas.G2.Model (ZMod 5) :=
  MulEquiv.ofBijective f (bijective_of_surjective_of_card_le f hf hcard)

/-- A version of assembly accepting the generating pair and its literal relations. -/
public noncomputable def g2EquivOfGeneratorsOfCardLE [Finite Model]
    (g : Bool → Atlas.G2.Model (ZMod 5))
    (hrel : ∀ i, FreeGroup.lift g (relator i) = 1)
    (hgen : Subgroup.closure ({g false, g true} : Set (Atlas.G2.Model (ZMod 5))) = ⊤)
    (hcard : Nat.card Model ≤ 5859000000) : Model ≃* Atlas.G2.Model (ZMod 5) :=
  g2EquivOfSurjectiveOfCardLE (hom g hrel) (hom_surjective g hrel hgen) hcard

end G2Five.AtlasPresentation
