module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic.Radical
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic.Reverse

/-!
# The even symplectic critical-pair argument

The point-radical calculation gives the two literal source alternatives
after left correction by L₁. Pulling back their common point reduces the
reverse field-line assertion to the small-displacement criterion. Actual
field-line transitivity then gives the right correction and contradicts
abelianness of W, retaining noncommutation throughout.

The final interfaces construct the radical coordinates from the actual
natural normalizer, discharge the small-displacement criterion, and prove
odd distance. Only the preceding compatible flag coordinates and fixed-space
vanishing remain explicit. The K=L₁ assembly stays with
qt-d-1222-natural-closure-amalgam.
The flag identities are produced by qt-d-1222-natural-flag-cartan; fixed-space
vanishing belongs to qt-d-1222-shadow-components.
Source: Aschbacher--Smith, 11.5.8, refs/quasithin.pdf, printed p.784.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic
open Closure.Symplectic Closure.Symplectic.Terminal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D) (m : MarkedFlag E)

include m in
/-- The existing marked flag matches the original three closure subspaces. -/
theorem flagMatch : FlagMatch E m.flag :=
  ⟨m.point_eq.symm,m.plane_eq.symm,m.threeSpace_eq.symm⟩

/-- Assemble the source alternatives from the action coordinates and the
small-displacement criterion, both constructed by the final source adapter. -/
theorem alternatives_of_action_inputs (p : PointCoordinates E m)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) (hs : SmallCommutatorLines E m)
    (g : G) (hB : V.map (MulAut.conj g).toMonoidHom ≤ E.R₁)
    (hn : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hi : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    ∃ a ∈ E.L₁, V.map (MulAut.conj (a*g)).toMonoidHom ≤ E.R₁ ∧
      ⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ ≠ ⊥ ∧
      (⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ = E.V₁ ∨
        (⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ = E.V₂ ∧
          ⁅E.V₃,V.map (MulAut.conj (a*g)).toMonoidHom⁆ = E.V₁)) ∧
      IsFieldLine E (.sp4 m.action) (E.V₁.map (MulAut.conj (a*g)⁻¹).toMonoidHom) := by
  obtain ⟨a,ha,hR,hn',hi',halt⟩ := forward_alternatives m p hc g hB hn hi
  exact ⟨a,ha,hR,hn',halt,reverse_line_of_alternatives E m hc hs (a*g) hi' halt⟩

/-- The actual critical pair contradicts abelianness once the two action
prerequisites have been supplied; no alignment is assumed. -/
theorem false_of_action_inputs (p : PointCoordinates E m)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) (hs : SmallCommutatorLines E m)
    (hab : IsMulCommutative E.W) (g : G)
    (hB : V.map (MulAut.conj g).toMonoidHom ≤ E.R₁)
    (hn : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hi : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) : False := by
  obtain ⟨a,_,_,hn',_,hline⟩ := alternatives_of_action_inputs E m p hc hs g hB hn hi
  exact false_of_common_fieldLine E m.action m.flag (flagMatch E m) hab (a*g) hn' hline

/-- Application to the literal F.7 critical pair at the action-coordinate
interface. The final adapter below supplies both action inputs. -/
theorem not_even_of_action_inputs (p : PointCoordinates E m)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) (hs : SmallCommutatorLines E m)
    (hab : IsMulCommutative E.W) (h : LocalInputs E) (hout : ¬ E.K ≤ E.M) :
    ¬ Even (distance E h hout) := by
  intro he
  obtain ⟨g,hB,hn,hi⟩ := exists_critical_conjugate_in_R₁ E h hout he
  exact false_of_action_inputs E m p hc hs hab g hB hn hi

open Theory.SpecificGroups.SymplecticFour in
/-- The literal alternatives and reverse line from the two independent action
inputs. The earlier flag coordinates retain the original marking and subgroups;
the direct source adapter below constructs the radical action in the
actual natural normalizer. -/
theorem alternatives_of_radical_image (s : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear s⁻¹).toLinearMap)
    (hplane : ∀ x : V, (x : G) ∈ E.V₂ ↔
      (markedProjection E m s x).toAdd ∈ plane E.input.field.Carrier)
    (hthree : ∀ x : V, (x : G) ∈ E.V₃ ↔
      (markedProjection E m s x).toAdd (.inr 0) = 0)
    (hr : actionImage (V := V) E.R₁ ≤ actionImage (V := V) (E.L₁.pCoreIn 2))
    (hc : V ⊓ centralizer (L : Set G) = ⊥) (hs : SmallCommutatorLines E m)
    (g : G) (hB : V.map (MulAut.conj g).toMonoidHom ≤ E.R₁)
    (hn : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hi : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    ∃ a ∈ E.L₁, V.map (MulAut.conj (a*g)).toMonoidHom ≤ E.R₁ ∧
      ⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ ≠ ⊥ ∧
      (⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ = E.V₁ ∨
        (⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ = E.V₂ ∧
          ⁅E.V₃,V.map (MulAut.conj (a*g)).toMonoidHom⁆ = E.V₁)) ∧
      IsFieldLine E (.sp4 m.action) (E.V₁.map (MulAut.conj (a*g)⁻¹).toMonoidHom) :=
  alternatives_of_action_inputs E m (pointCoordinates_of_radical_image m s hp hplane hthree hr)
    hc hs g hB hn hi

/-- The complete pair calculation once the original radical coordinates are
supplied. The small-displacement and reciprocal-line premises are discharged. -/
theorem alternatives_of_pointCoordinates (p : PointCoordinates E m)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (g : G) (hB : V.map (MulAut.conj g).toMonoidHom ≤ E.R₁)
    (hn : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hi : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    ∃ a ∈ E.L₁, V.map (MulAut.conj (a*g)).toMonoidHom ≤ E.R₁ ∧
      ⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ ≠ ⊥ ∧
      (⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ = E.V₁ ∨
        (⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ = E.V₂ ∧
          ⁅E.V₃,V.map (MulAut.conj (a*g)).toMonoidHom⁆ = E.V₁)) ∧
      IsFieldLine E (.sp4 m.action) (E.V₁.map (MulAut.conj (a*g)⁻¹).toMonoidHom) :=
  alternatives_of_action_inputs E m p hc (smallCommutatorLines E m) g hB hn hi

/-- F.7 and the constructed field-line alignment exclude even distance.
The final adapter supplies these coordinates from the original radical;
the K=L₁ assembly belongs to qt-d-1222-natural-closure-amalgam. -/
theorem odd_distance_of_pointCoordinates (p : PointCoordinates E m)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hab : IsMulCommutative E.W) (h : LocalInputs E) (hout : ¬ E.K ≤ E.M) :
    Odd (distance E h hout) :=
  Nat.not_even_iff_odd.mp
    (not_even_of_action_inputs E m p hc (smallCommutatorLines E m) hab h hout)

open Theory.SpecificGroups.SymplecticFour

/-- Both source alternatives and the genuine field line on the conjugate module.
Only the preceding compatible flag coordinates and C_V(L)=1 remain explicit. -/
theorem critical_pair_geometry (s : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear s⁻¹).toLinearMap)
    (hplane : ∀ x : V, (x : G) ∈ E.V₂ ↔
      (markedProjection E m s x).toAdd ∈ plane E.input.field.Carrier)
    (hthree : ∀ x : V, (x : G) ∈ E.V₃ ↔
      (markedProjection E m s x).toAdd (.inr 0) = 0)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (g : G) (hB : V.map (MulAut.conj g).toMonoidHom ≤ E.R₁)
    (hn : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hi : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    ∃ a ∈ E.L₁, V.map (MulAut.conj (a*g)).toMonoidHom ≤ E.R₁ ∧
      ⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ ≠ ⊥ ∧
      (⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ = E.V₁ ∨
        (⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ = E.V₂ ∧
          ⁅E.V₃,V.map (MulAut.conj (a*g)).toMonoidHom⁆ = E.V₁)) ∧
      IsFieldLine E (.sp4 m.action) (E.V₁.map (MulAut.conj (a*g)⁻¹).toMonoidHom) :=
  alternatives_of_pointCoordinates E m (pointCoordinates m s hp hplane hthree) hc g hB hn hi

/-- The actual F.7 critical distance is odd in the Sp₄ branch. The normalizer,
radical, quadratic-subgroup and reciprocal field-line calculations are discharged. -/
theorem odd_distance (s : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear s⁻¹).toLinearMap)
    (hplane : ∀ x : V, (x : G) ∈ E.V₂ ↔
      (markedProjection E m s x).toAdd ∈ plane E.input.field.Carrier)
    (hthree : ∀ x : V, (x : G) ∈ E.V₃ ↔
      (markedProjection E m s x).toAdd (.inr 0) = 0)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hab : IsMulCommutative E.W) (h : LocalInputs E) (hout : ¬ E.K ≤ E.M) :
    Odd (distance E h hout) :=
  odd_distance_of_pointCoordinates E m (pointCoordinates m s hp hplane hthree) hc hab h hout
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic

