module

public import Theory.SpecificGroups.ReeF4.Model
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.BinaryAutomorphisms.TitsTower

/-!
# Comparing the full binary Ree group through its derived subgroup

Conjugation gives a concrete homomorphism from `Model 0` to the automorphism
group of its derived subgroup. If this homomorphism is bijective, an actual
identification of the derived subgroup with Parrott's group constructs the
required comparison `Model 0 ≃* Aut(ParrottGroup)`.

The two inputs are independent: the derived-group comparison identifies the
simple carrier; bijectivity of the conjugation action proves faithfulness
and automorphism coverage for its full extension. Both must be discharged
to use the identification of `Aut(²F₄(2)')` with `²F₄(2)` in
Aschbacher–Smith F.1.12, printed p.263 of `refs/quasithin.pdf`.
-/

public section
noncomputable section

namespace ReeF4.Parabolics.OuterLocal

/-- The full fixed group's actual conjugation action on its derived subgroup. -/
abbrev binaryDerivedAction : Model 0 →* MulAut (commutator (Model 0)) :=
  MulAut.conjNormal

/-- The action is conjugation inside the actual binary Ree carrier. -/
@[simp] theorem binaryDerivedAction_apply (g : Model 0) (x : commutator (Model 0)) :
    (binaryDerivedAction g x : Model 0) = g * (x : Model 0) * g⁻¹ := by rfl

/-- A derived-group identification and bijective conjugation action construct
the full comparison, with no change of the fixed-point carrier. -/
def binaryTitsAutEquiv
    (e : commutator (Model 0) ≃* Tits.ParrottGroup)
    (h : Function.Bijective binaryDerivedAction) : Model 0 ≃* MulAut Tits.ParrottGroup :=
  (MulEquiv.ofBijective binaryDerivedAction h).trans (MulAut.congr e)

/-- The comparison sends each element to its transported conjugation action. -/
@[simp] theorem binaryTitsAutEquiv_apply
    (e : commutator (Model 0) ≃* Tits.ParrottGroup)
    (h : Function.Bijective binaryDerivedAction) (g : Model 0) :
    binaryTitsAutEquiv e h g = MulAut.congr e (binaryDerivedAction g) := by rfl

end ReeF4.Parabolics.OuterLocal
