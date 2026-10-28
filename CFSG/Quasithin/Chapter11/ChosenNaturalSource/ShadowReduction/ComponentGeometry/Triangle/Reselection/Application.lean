module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Choice
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Action

/-!
# The original flag consumer of the swapped module construction

The complete preceding 11.3.2 implication kills the new fixed space. The
whole-module marking and the literal old R₂ action are then constructed,
and its image bound follows from geometric representatives. The actual
centralizer kernel and the triangle generation identity supply the remaining
inputs of the published mutually-normalizing-conjugate theorem.

The two outstanding construction inputs are the earlier FF classification
of the newly selected module and the compatible paired-flag geometry.
This conditional application does not prove 11.4.1(2) or discard the
orientation in which the original L is symplectic.
Source: Aschbacher--Smith 11.1.2(3), pp.762--764, and 11.4.1(2), p.776.
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

/-- Apply the constructed action to E=ofFlag, preserving both the original
second residual and its radical. The explicit remaining inputs belong to
the earlier classification and compatible-flag construction. -/
theorem ofFlag_conjugate_of_classified_choice
    (X : Subgroup G) (z : G) (H₀ K K₀ U : Subgroup G)
    (hgen : K = f.Li 0 ⊔ K₀) (hKout : ¬ K ≤ normalizer (L : Set G))
    (ho : LocalGeometry.Components.TriangleOrientation L (K₀ ⊔ f.Li 1))
    (D_I : Chapter12.Section02.ChosenModule T (K₀ ⊔ f.Li 1) U)
    (S_I : D_I.NonbinaryNaturalInput) (hdegree : S_I.field.degree = 2)
    (U₁ : Submodule (ZMod 2) D_I.chosenCentralQuotient)
    (hlinear : Source.IsSL ((K₀ ⊔ f.Li 1 : Subgroup G) ⧸ pCore 2 (K₀ ⊔ f.Li 1 : Subgroup G))
      3 (2 ^ S_I.field.degree) → U ⊓ centralizer ((K₀ ⊔ f.Li 1 : Subgroup G) : Set G) = ⊥)
    (h1132 : ∀ H, Hypothesis1131At D_I S_I U₁ H → Proposition1132At D_I S_I U₁ H)
    (m : ActionEquiv D_I.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S_I.field.Carrier) 2)))
    (hlift : HasPlaneRadicalLifts D_I m (ofFlag S f X z H₀).R₂)
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
  have hc := fixed_trivial D_I S_I U₁ hlinear h1132
  have hker := centralizer_join_eq_core D_I S_I.sylow_normalizes (orientation_simple ho)
  obtain ⟨_, α, hα, him⟩ := exists_plane_radical_action D_I hc m _ hlift
  let e := symplecticEquiv D_I hc m
  have hact : ∀ (a : (ofFlag S f X z H₀).R₂) (u : U),
      (e ⟨a.val * u.val * a.val⁻¹,
        (mem_normalizer_iff.mp
          (S_I.sylow_normalizes (LocalGeometry.localRadical_le_sylow _ a.property))
          u.val).mp u.property⟩).toAdd = α a • (e u).toAdd := hα
  refine ⟨hc, hker, e, α, hact, him, ?_⟩
  have hF : Nat.card S_I.field.Carrier = 4 := by
    simpa [hdegree] using S_I.field.card_eq
  exact ofFlag_exists_mutually_normalizing_conjugate D S f X z H₀ hF
    (K₀ ⊔ f.Li 1) U (third_vertex_escapes D S f K K₀ hgen hKout)
    hN hker (@IsElementaryAbelian.isPGroup 2 _ _ D_I.elementary)
    S_I.sylow_normalizes hW hs hr α e hact him

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
