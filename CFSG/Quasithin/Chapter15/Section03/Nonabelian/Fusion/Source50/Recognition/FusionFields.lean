module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.Assembly
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.Coset
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.Square
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.DihedralCube
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.Centers
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Assembly

/-!
# Literal recognition fields of the final 15.3.50 fusion consumer

The record below retains exactly the action, plus-type, square, singularity
and all-outer-elements swap fields of `Fusion.Assembly.EarlierData`. Each
is constructed from the earlier source inputs and the proved natural pair.
The surrounding local geometry and simultaneous partner transvections remain
with the source 15.3.51–56 producer; no recognition field is assumed there.
Source: Aschbacher–Smith 15.3.58, printed p.1149.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction Core.ResidualGeneration
universe u
variable {G : Type u} [Group G] [Finite G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {C : GroupClass.{u}} {v : ActorQuotient Z} {s : ℕ}

/-- The dependent recognition fields used literally by `Assembly.EarlierData`. -/
structure FusionRecognition (T : Subgroup G) (Z ZS V : Subgroup G) (t : G)
    [(Z.subgroupOf (closureU Z ZS)).Normal] where
  recognized : RecognizedAction T Z ZS V t
  U_card : Nat.card (closureU Z ZS) = 2 ^ 7
  extraspecial : IsExtraspecial 2 (closureU Z ZS)
  plusType : closureU Z ZS ≃* Cubic.HLocal.DihedralCube
  plusElementary : ∃ A : Subgroup (closureU Z ZS), IsElementaryAbelian 2 A ∧ Nat.card A = 16
  natural_singular : ∀ x : G, x ∈ ResidualOrbits.Extraspecial.naturalPreimage recognized → x ^ 2 = 1
  square : ∀ z : G, orderOf z = 2 → zpowers z = Z →
    ResidualOrbits.Extraspecial.SquareForm recognized z
  displacement_centers : ∃ c : BinaryLinearThree.Vector, c ≠ 0 ∧
    ∃ f : Module.Dual (ZMod 2) BinaryLinearThree.Vector, f ≠ 0 ∧
      ∀ x : closureU Z ZS, (x : G) ∈ V →
        (recognized.coordinates (QuotientGroup.mk' _ x)).toAdd.1 ∈ ({0, c} : Set _) ∧
        (recognized.coordinates (QuotientGroup.mk' _ x)).toAdd.2 ∈ ({0, f} : Set _)
  swap : ∀ (h : centralizerH Z), (h : G) ∈ T →
    (h : G) ∉ closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G)) →
    (∀ w : BinaryLinearThree.Vector,
      (recognized.coordinates (quotientAction Z ZS h
        (recognized.coordinates.symm (Multiplicative.ofAdd (w, 0))))).toAdd.1 = 0) ∧
    (∀ f : Module.Dual (ZMod 2) BinaryLinearThree.Vector,
      (recognized.coordinates (quotientAction Z ZS h
        (recognized.coordinates.symm (Multiplicative.ofAdd (0, f))))).toAdd.2 = 0)

/-- Construct every recognition-dependent consumer field on the literal maps. -/
noncomputable def fusionRecognition
    {d : EarlierSourceInputs Z ZS V M C v s} {a : EarlierActionInputs d}
    (p : NaturalPair d a) (b : EarlierPowerInputs d a)
    (hUQ : closureU Z ZS ≤ coreQ Z)
    (hUT : closureU Z ZS ≤ (d.T : Subgroup G))
    (hcomm : ⁅closureU Z ZS, V⁆ ≤ V)
    (hindex : (closureU Z ZS ⊔ ((d.T : Subgroup G) ⊓ centralizer (V : Set G))).relIndex
      (d.T : Subgroup G) = 2)
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hout : t ∉ closureU Z ZS ⊔ ((d.T : Subgroup G) ⊓ centralizer (V : Set G))) :
    FusionRecognition (d.T : Subgroup G) Z ZS V t where
  recognized := p.sourceRecognizedAction hUQ hUT hcomm hindex t ht hout
  U_card := p.card_U
  extraspecial := b.extraspecial
  plusType := (Classical.choice (p.plusType b)).trans dihedralCubeEquiv
  plusElementary := by
    obtain ⟨A, hA, hc, _⟩ := p.elementary_preimage b
    exact ⟨A, hA, hc⟩
  natural_singular := p.natural_preimage_squares b
  square z hz hgen := p.squareForm b z (hgen ▸ mem_zpowers z)
    (by intro he; rw [he, orderOf_one] at hz; omega)
  displacement_centers := p.displacement_centers
  swap h hh hout := by
    have ho := p.outside_mem_outer hUQ hUT hcomm hindex h hh hout
    exact p.outer_swaps (QuotientGroup.mk' _ h) ho

/-- Source models and source geometry together supply the final action fields;
the sole later branch premise is the actual minimal-normal G.9.3 application. -/
theorem fusionRecognition_of_earlier_source
    (d : EarlierSourceInputs Z ZS V M KnownSimple.IsKnownSimple v s)
    (a : EarlierActionInputs d) (b : EarlierPowerInputs d a)
    (hG93 : LocalIrreducibleExclusion d a)
    (hUQ : closureU Z ZS ≤ coreQ Z)
    (hUT : closureU Z ZS ≤ (d.T : Subgroup G))
    (hcomm : ⁅closureU Z ZS, V⁆ ≤ V)
    (hindex : (closureU Z ZS ⊔ ((d.T : Subgroup G) ⊓ centralizer (V : Set G))).relIndex
      (d.T : Subgroup G) = 2)
    (t : G) (ht : t ∈ (d.T : Subgroup G))
    (hout : t ∉ closureU Z ZS ⊔ ((d.T : Subgroup G) ⊓ centralizer (V : Set G))) :
    s = 1 ∧ Nonempty (FusionRecognition (d.T : Subgroup G) Z ZS V t) := by
  obtain ⟨p⟩ := naturalPair_of_local_exclusion d a hG93
  exact ⟨p.s_eq_one, ⟨fusionRecognition p b hUQ hUT hcomm hindex t ht hout⟩⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition
