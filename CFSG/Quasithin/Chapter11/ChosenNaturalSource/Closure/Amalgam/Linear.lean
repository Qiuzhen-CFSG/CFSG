module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.OddGeometry.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Joint

/-!
# The conditional source 11.5.8 implication for SL₃

On the original chosen natural module, the earlier flag and Cartan facts
construct every local F.7 input. A strict enlargement L₁<K escapes M by
relative component comparability. The actual SL₃ geometry excludes even
critical distance. The odd endpoint construction gives both intersection
bounds, disjoint field lines, the core commutator and nontrivial motion.
The genuine chief-section contradiction excludes that pair, proving K=L₁.

Only source conclusions through 11.5.6 and abelianness of W remain explicit.
In particular the surviving exceptional list is an input from the preceding
triangle-elimination branch, not treated as an exhaustive definition.
The corank input is required only in the strict branch, where 11.5.6(6)
applies with H₁=KT. No parity, alignment, odd-pair, action-kernel or chief
section conclusion remains as an extra premise.

The final owner qt-d-1222-natural-closure-amalgam retains the Sp₄ branch.
Its parent qt-d-1222-natural-closure supplies abelianness and assembles the
terminal contradiction; qt-d-1222-nonbinary-natural discharges earlier inputs.
Source: Aschbacher--Smith, 11.5.8, printed p.784.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam
open Chapter12.Section02 LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)

/-- Source 11.5.8 in the SL₃ branch, conditional only on the displayed earlier
flag, Cartan, relative-component, point-comparison, corank and parameter facts.
Every amalgam, parity, odd-pair and chief-section premise is discharged here. -/
theorem linear_eq_of_abelian
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))
    (f : InvariantFlag (.sl3 m)) (hm : Even.FlagMatch E f)
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
  have h := Even.localInputs_of_flag E f hm hfix hsplit hcartan hker
  have hout := Even.strict_component_escapes E hLi hK.1 hlt
  have ho := Even.Linear.odd_distance m f hm hfixed hab h hout
  obtain ⟨g,p⟩ := OddGeometry.linear_oddPair E h hout hab ho m f hm (hc hlt)
    hres hcomp horbit ht hK hlt hlocal
  exact Chief.false_of_odd_pair_of_flag E g h hab hs (.sl3 m) f hm.point.symm p
    hK hlt hlocal hcase

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam
