module

public import Theory.Representation.HexacodeAction.Cover
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient

/-!
# The generalized Fitting subgroup above the even hexacode cover

An injective homomorphism into the full hexacode automorphism group whose
image contains the even cover identifies its even preimage with the actual
perfect triple cover of A₆. The quotient embeds in the sign group, so is a
two-group. If the original group has trivial two-core, the normal
quasisimple two-quotient theorem identifies this preimage with F*.

The isomorphism retains the original embedding, rather than identifying
carriers by their orders. The cover and its perfectness are the checked
ATLAS construction imported through `HexacodeAction.Cover`.

Source: Aschbacher–Smith, B.5.6 and the terminal comparison in the proof of
15.3.1, printed pp.105 and 1155; the cover convention is A.3.5, p.43.
-/

@[expose] public section
open Subgroup Atlas.Codes Theory.GroupTheory

namespace Representation.Hexacode
variable {D : Type*} [Group D]

/-- The literal preimage of the even cover under the given embedding. -/
abbrev evenPreimage (f : D →* HexAutomorphisms) : Subgroup D := (hexSign.comp f).ker

/-- Restrict the original embedding to an equivalence with the even cover. -/
noncomputable def evenPreimageEquiv (f : D →* HexAutomorphisms)
    (hf : Function.Injective f) (hE : hexSign.ker ≤ f.range) :
    evenPreimage f ≃* HexEvenAutomorphisms := by
  let g : evenPreimage f →* HexEvenAutomorphisms :=
    { toFun x := ⟨f x, x.property⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' x y := Subtype.ext (map_mul f x.val y.val) }
  apply MulEquiv.ofBijective g
  constructor
  · intro x y h
    exact Subtype.ext (hf (congrArg Subtype.val h))
  · intro x
    obtain ⟨y, hy⟩ := hE x.property
    refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
    change hexSign (f y) = 1
    rw [hy]
    exact x.property

/-- The sign map embeds the quotient over the even preimage in a two-group. -/
theorem quotient_evenPreimage_isTwoGroup (f : D →* HexAutomorphisms) :
    IsPGroup 2 (D ⧸ evenPreimage f) := by
  have hu : IsPGroup 2 ℤˣ := by
    intro x
    refine ⟨1, ?_⟩
    rcases Int.units_eq_one_or x with rfl | rfl <;> norm_num
  exact hu.of_injective (QuotientGroup.kerLift (hexSign.comp f))
    (QuotientGroup.kerLift_injective _)

variable [Finite D]

/-- With trivial two-core, the even preimage is exactly F*. -/
theorem generalizedFitting_eq_evenPreimage (f : D →* HexAutomorphisms)
    (hf : Function.Injective f) (hE : hexSign.ker ≤ f.range)
    (hcore : pCore 2 D = ⊥) : generalizedFitting D = evenPreimage f := by
  let : (evenPreimage f).Normal := inferInstanceAs (hexSign.comp f).ker.Normal
  let : IsQuasisimple HexEvenAutomorphisms := even_isQuasisimple
  let : IsQuasisimple (evenPreimage f) :=
    IsQuasisimple.of_mulEquiv (evenPreimageEquiv f hf hE).symm
  exact generalizedFitting_eq_of_quasisimple_two_quotient _
    (quotient_evenPreimage_isTwoGroup f) hcore

/-- The image of F* under the original embedding is the even cover. -/
theorem generalizedFitting_map_eq_even (f : D →* HexAutomorphisms)
    (hf : Function.Injective f) (hE : hexSign.ker ≤ f.range)
    (hcore : pCore 2 D = ⊥) : (generalizedFitting D).map f = hexSign.ker := by
  rw [generalizedFitting_eq_evenPreimage f hf hE hcore]
  exact map_comap_eq_self hE

/-- F* is the actual perfect triple cover, through the given embedding. -/
noncomputable def generalizedFittingEquivEven (f : D →* HexAutomorphisms)
    (hf : Function.Injective f) (hE : hexSign.ker ≤ f.range)
    (hcore : pCore 2 D = ⊥) : generalizedFitting D ≃* HexEvenAutomorphisms :=
  (MulEquiv.subgroupCongr (generalizedFitting_eq_evenPreimage f hf hE hcore)).trans
    (evenPreimageEquiv f hf hE)

/-- The equivalence is the restriction of the specified embedding. -/
theorem generalizedFittingEquivEven_apply (f : D →* HexAutomorphisms)
    (hf : Function.Injective f) (hE : hexSign.ker ≤ f.range)
    (hcore : pCore 2 D = ⊥) (x : generalizedFitting D) :
    (generalizedFittingEquivEven f hf hE hcore x : HexAutomorphisms) = f x := rfl

end Representation.Hexacode
