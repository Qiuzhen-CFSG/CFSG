module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action.SymplecticPair
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Joint

/-!
# The conditional source 11.5.8 implication for Sp₄

The preceding marked flag and Cartan facts construct the actual generated-group
F.7 setup. Under L₁<K, relative component comparability gives escape from M.
The genuine point-or-plane geometry excludes even distance. At the odd endpoint,
the two index bounds and the hyperplane-to-point argument give the complete
OddPair. The chief-section transvection contradiction then proves K=L₁.

Only the displayed source conclusions through 11.5.6 and abelianness of W
remain explicit. The actual radical action, odd pair, axis and surviving
chief section are constructed. The exceptional-case premise is the surviving
list after triangle elimination, not an assertion that its partial definition
is exhaustive. Its producer is qt-d-1222-shadow-component-triangle.

Together with Linear.lean this completes qt-d-1222-natural-closure-amalgam.
Parent qt-d-1222-natural-closure retains the terminal closure contradiction;
qt-d-1222-nonbinary-natural discharges the earlier source premises.
Source: Aschbacher--Smith, 11.5.8, printed p.784.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam
open Chapter12.Section02 LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- Source 11.5.8 in the Sp₄ branch, conditional only on the displayed earlier
flag, Cartan, relative-component, point-comparison, corank and parameter facts.
Every amalgam, parity, odd-pair and chief-section premise is discharged here. -/
theorem symplectic_eq_of_abelian
    (m : Closure.Symplectic.MarkedFlag E) (s : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear s⁻¹).toLinearMap)
    (hplane : ∀ x : V, (x : G) ∈ E.V₂ ↔
      (Closure.Symplectic.Terminal.markedProjection E m s x).toAdd ∈ plane E.input.field.Carrier)
    (hthree : ∀ x : V, (x : G) ∈ E.V₃ ↔
      (Closure.Symplectic.Terminal.markedProjection E m s x).toAdd (.inr 0) = 0)
    (hfix : E.L₁ ≤ centralizer (E.V₁ : Set G))
    (hsplit : L ⊓ E.G₁ = (E.L₁ ⊔ L.pCoreIn 2) ⊔ E.X)
    (hcartan : LocalGeometry.IsCartan T L E.X)
    (hker : E.X ⊓ centralizer (E.V₁ : Set G) ≤ E.L₁ ⊔ L.pCoreIn 2)
    (hLi : Source.ComponentIn E.M₁ E.L₁)
    (hK : Source.NormalComponentIn E.G₁ E.K)
    (hlocal : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree))
    (hcase : Source.ClassicalRefinementCase L E.L₁ E.K 1 E.input.field.degree)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hc : E.L₁ < E.K → OddGeometry.RadicalCorank E)
    (hres : pointResidual L E.z = E.L₁) (hcomp : E.Kz = E.K)
    (horbit : ∀ u ∈ E.V₁, u ≠ 1 → ∃ x ∈ L ⊓ E.G₁, (MulAut.conj x) E.z = u)
    (ht : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 → ∃ l ∈ L, (MulAut.conj l) u = v)
    (hs : letI := D.elementary; ChapterE.globalS V = (E.input.field.degree : ℕ∞))
    (hab : IsMulCommutative E.W) : E.K = E.L₁ := by
  apply le_antisymm ?_ (le_conjugateSpanBy E.L₁ E.G₁)
  by_contra hle
  have hlt : E.L₁ < E.K := lt_of_le_of_ne (le_conjugateSpanBy E.L₁ E.G₁) (fun he => hle he.ge)
  have h := Even.localInputs_of_flag E m.flag (Even.Symplectic.flagMatch E m) hfix hsplit hcartan hker
  have hout := Even.strict_component_escapes E hLi hK.1 hlt
  have ho := Even.Symplectic.odd_distance E m s hp hplane hthree hfixed hab h hout
  obtain ⟨g,p⟩ := OddGeometry.symplectic_oddPair E h hout hab ho m
    (Even.Symplectic.pointCoordinates m s hp hplane hthree) hfixed (hc hlt)
    hres hcomp horbit ht hK hlt hlocal
  exact Chief.false_of_odd_pair_of_flag E g h hab hs (.sp4 m.action) m.flag m.point_eq p
    hK hlt hlocal hcase

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam
