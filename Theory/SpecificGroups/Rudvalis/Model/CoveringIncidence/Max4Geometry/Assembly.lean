module
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Steinberg
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Involutions
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Transport

/-!
# The two module factors of the Rudvalis max4 core

The literal core P is special of order 2048, with Z(P) the original marked
E8 and P/Z(P) elementary abelian of order 256. The independent word and
commutator calculations discharge every structural premise of the natural
and Steinberg intertwiners. Both actions factor through the literal
max4/O₂(max4), and both use the same actor equivalence and quotient projection.

The checked outside-core fusion also discharges the involution-marking premise
in the transport to a max4 conjugate containing any prescribed ambient Sylow.
Thus none of the center, generation, elementary-quotient, full-image or fusion
premises remain in the module-factor and marking conclusions below.

Source: Aschbacher--Smith I.2.2(7), printed pp.412--413, and J.2.6(2),
printed pp.434--435; GLS3 Table 5.3r and its justification on pp.291--292.
The later central-cover conclusions belong to the covering-incidence consumer.
-/

open Subgroup Rudvalis Rudvalis.SylowOvergroups
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
namespace Rudvalis.CoveringIncidence.Max4Geometry

public noncomputable def naturalCoordinates :
    center max4Core ≃* Multiplicative BinaryLinearThree.Vector :=
  max4CenterCoordinates max4CoreCenter_eq_marked

public noncomputable def steinbergCoordinates :
    Max4CentralQuotient ≃* Multiplicative BinaryLinearThree.Steinberg :=
  max4SteinbergEquiv max4CoreCenter_eq_marked max4Core_generated_by_words

private theorem core_le_centerAction_ker : pCore 2 max4 ≤ max4CenterAction.ker := by
  intro g hg
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  let p : max4Core := ⟨g, mem_map_of_mem max4.subtype hg⟩
  have h : (max4CenterAction g x : max4Core) = p * (x : max4Core) * p⁻¹ := by
    apply Subtype.ext
    exact max4CenterAction_apply g x
  rw [h, mem_center_iff.mp x.property p]
  simp

/-- The natural action of the literal quotient max4/O₂(max4) on Z(P). -/
public def naturalAction : (max4 ⧸ pCore 2 max4) →* MulAut (center max4Core) :=
  QuotientGroup.lift (pCore 2 max4) max4CenterAction core_le_centerAction_ker

@[simp] public theorem naturalAction_mk (g : max4) :
    naturalAction (QuotientGroup.mk' (pCore 2 max4) g) = max4CenterAction g := by rfl

/-- The action of the same quotient on the literal central quotient P/Z(P). -/
public def steinbergAction : (max4 ⧸ pCore 2 max4) →* MulAut Max4CentralQuotient :=
  max4FactorAction max4Core_commutator_eq_center.le

@[simp] public theorem steinbergAction_mk (g : max4) :
    steinbergAction (QuotientGroup.mk' (pCore 2 max4) g) = max4CentralQuotientAction g :=
  max4FactorAction_mk max4Core_commutator_eq_center.le g

public theorem natural_intertwines (q : max4 ⧸ pCore 2 max4) (x : center max4Core) :
    (naturalCoordinates (naturalAction q x)).toAdd =
      BinaryLinearThree.W (max4NaturalActor q) (naturalCoordinates x).toAdd := by
  induction q using Quotient.inductionOn with
  | h g => exact max4_center_natural max4CoreCenter_eq_marked g x

public theorem steinberg_intertwines (q : max4 ⧸ pCore 2 max4)
    (x : Max4CentralQuotient) :
    (steinbergCoordinates (steinbergAction q x)).toAdd =
      BinaryLinearThree.S (max4NaturalActor q) (steinbergCoordinates x).toAdd := by
  induction q using Quotient.inductionOn with
  | h g =>
    change (steinbergCoordinates (steinbergAction (QuotientGroup.mk' (pCore 2 max4) g) x)).toAdd = _
    rw [steinbergAction_mk]
    exact max4_steinberg max4CoreCenter_eq_marked max4Core_generated_by_words g x

public theorem steinberg_intertwines_mk (g : max4) (x : max4Core) :
    (steinbergCoordinates
      (QuotientGroup.mk' (center max4Core) (max4CoreAction g x))).toAdd =
      BinaryLinearThree.S (max4NaturalActor (QuotientGroup.mk' (pCore 2 max4) g))
        (steinbergCoordinates (QuotientGroup.mk' (center max4Core) x)).toAdd :=
  max4_steinberg_mk max4CoreCenter_eq_marked max4Core_generated_by_words g x

public theorem conjugate_center_eq_marked (g : Model) :
    conjugateMax4CoreCenter g = (elementary 2).map (MulAut.conj g).toMonoidHom :=
  CoveringIncidence.conjugate_center_eq_marked g max4CoreCenter_eq_marked

public theorem outside_core_twoCentral_conjugate (g : Model) (x : Model)
    (hx : x ∈ conjugateMax4 g) (hxP : x ∉ conjugateMax4Core g)
    (horder : orderOf x = 2) :
    Theory.GroupTheory.DoubleCoverCentralizer.TwoCentral x :=
  CoveringIncidence.outside_core_twoCentral_conjugate outside_core_twoCentral g x hx hxP horder

public theorem exists_marked_conjugateMax4_over_sylow (S : Sylow 2 Model) :
    ∃ g : Model, (S : Subgroup Model) ≤ conjugateMax4 g ∧
      ∀ x : Model, x ∈ conjugateMax4 g → x ∉ conjugateMax4Core g → orderOf x = 2 →
        ∃ T : Sylow 2 Model, ∃ hxT : x ∈ T, (⟨x, hxT⟩ : T) ∈ center T :=
  CoveringIncidence.exists_marked_conjugateMax4_over_sylow outside_core_twoCentral S

end Rudvalis.CoveringIncidence.Max4Geometry
