module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Application
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.RadicalLifts
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Geometry.Escape

/-!
# Apply the common-plane calculation to the original flag

This discharges the radical-representative and escape inputs of the existing
reselection application. The outstanding geometric premises are the triangle
generation identity and compatible plane marking. The complete preceding
11.3.2 implication and the source weak-closure bounds remain explicit.
This conditional theorem does not assert the paired-flag construction or
11.4.1(2).

Source: Aschbacher--Smith, 11.1.2(3), pp.762--764, and 11.4.1(2), p.776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin Chapter11.ChosenNaturalSource ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)

/-- Common plane placement supplies the literal R₂ action and the source
mutually-normalizing conjugate, with no assumed radical representatives. -/
theorem ofFlag_conjugate_of_plane_residual
    (X : Subgroup G) (z : G) (H₀ K K₀ U : Subgroup G)
    (hgen : K = f.Li 0 ⊔ K₀)
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hlocal : f.Li 0 ∈ Chapter1.L G T) (hlt : f.Li 0 < K)
    (ho : LocalGeometry.Components.TriangleOrientation L (K₀ ⊔ f.Li 1))
    (D_I : Chapter12.Section02.ChosenModule T (K₀ ⊔ f.Li 1) U)
    (S_I : D_I.NonbinaryNaturalInput) (hdegree : S_I.field.degree = 2)
    (U₁ : Submodule (ZMod 2) D_I.chosenCentralQuotient)
    (hlinear : Source.IsSL ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G))
      3 (2 ^ S_I.field.degree) → U ⊓ centralizer ((K₀ ⊔ f.Li 1 : Subgroup G) : Set G) = ⊥)
    (h1132 : ∀ H, Hypothesis1131At D_I S_I U₁ H → Proposition1132At D_I S_I U₁ H)
    (m : ActionEquiv D_I.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S_I.field.Carrier) 2)))
    (hplane : ((f.Li 1).subgroupOf (K₀ ⊔ f.Li 1)).map
      (m.groupEquiv.toMonoidHom.comp
        (QuotientGroup.mk' (pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G)))) = planeLocal)
    (hN : normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
      normalizer (L : Set G))
    (hW : indexedWeakClosure V (T : Subgroup G) 0 ≤ (ofFlag S f X z H₀).R₂)
    (hs : (4 : ℕ∞) ≤ @globalS G _ V D.elementary) (hr : (4 : ℕ∞) < globalR V) :
    U ⊓ centralizer ((K₀ ⊔ f.Li 1 : Subgroup G) : Set G) = ⊥ ∧
    ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) =
      ((K₀ ⊔ f.Li 1) ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    ∃ (e : U ≃* Multiplicative (Vector S_I.field.Carrier))
      (α : (ofFlag S f X z H₀).R₂ →* Sp S_I.field.Carrier),
      (∀ (a : (ofFlag S f X z H₀).R₂) (u : U),
        (e ⟨a.val * u.val * a.val⁻¹,
          (mem_normalizer_iff.mp
            (S_I.sylow_normalizes (LocalGeometry.localRadical_le_sylow _ a.property))
            u.val).mp u.property⟩).toAdd = α a • (e u).toAdd) ∧
      α.range ≤ Plane.radical.map planeLocal.subtype ∧
      ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (ofFlag S f X z H₀).R₂ ∧
        V.map (MulAut.conj g).toMonoidHom ≤ T ∧
        V.map (MulAut.conj g).toMonoidHom ≤ normalizer (U : Set G) ∧
        U ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) ∧
        inducedAutomizer U (V.map (MulAut.conj g).toMonoidHom) ≠ ⊥ ∧
        4 ≤ Representation.BinaryOffender.rank
          (inducedAutomizer U (V.map (MulAut.conj g).toMonoidHom)) := by
  have hn : 1 < S_I.field.degree := by rw [hdegree]; decide
  have hlift := ofFlag_planeRadicalLifts D_I D S f X z H₀ m hn le_sup_right hplane
  exact ofFlag_conjugate_of_classified_choice D S f X z H₀ K K₀ U hgen
    (proper_flag_component_escapes D S f K hK hlocal hlt)
    ho D_I S_I hdegree U₁ hlinear h1132 m hlift hN hW hs hr

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
