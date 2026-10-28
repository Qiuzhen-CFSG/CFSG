module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison.Marking
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.RankComparison.Actor

/-!
# The original G₂ flag produces the inner comparison actor

Use the same G₂ marking and invariant flag as the chosen geometry. The literal
weak closure selects A=V^g inside R₂. The symplectic calculation gives both its
commutator and reverse automizer rank four. Fixed-space vanishing lifts the
original L/O₂(L) marking to V, and the source normalizer inclusion transports
that action to this same A. Field and scalar factors are removed from the
U-action, producing an elementary subgroup of the actual G₂(4) model with
rank four and moved-space dimension four. Its normalizer image is literally
the U-conjugation image, retained in the conclusion.

The independent swapped-module construction supplies α and e. The two earlier
source inputs hfix and hchosen have the producers documented in Marking.lean.
The native long-root placement of the resulting small-moved subgroup remains
the final geometric step; this theorem does not assert triangle exclusion.

Source: Aschbacher--Smith, 11.4.1(2), printed p.776.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle
variable {G F : Type*} [Group G] [Field F] [Algebra (ZMod 2) F]
variable [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : letI : Algebra (ZMod 2) S.field.Carrier := S.field.binaryAlgebra
      ActionEquiv D.centralQuotientAction
        (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : LocalGeometry.InvariantFlag (LocalGeometry.Coordinates.g2 m))

attribute [local instance 2000] ZMod.algebra

-- The source BinaryField retains its algebra structure. The normalizer API
-- uses the canonical ZMod algebra; additive coordinates identify their actions.
private def canonicalMarking : ActionEquiv D.centralQuotientAction
    (Atlas.G2.Natural.Normalizer.binary S.field.Carrier) := by
  let em : D.chosenCentralQuotient ≃+ Atlas.G2.Natural.Space S.field.Carrier := by
    letI : Algebra (ZMod 2) S.field.Carrier := S.field.binaryAlgebra
    exact m.linearEquiv.toAddEquiv
  let gm : (L ⧸ pCore 2 L) ≃* Atlas.G2.Model S.field.Carrier := by
    letI : Algebra (ZMod 2) S.field.Carrier := S.field.binaryAlgebra
    exact m.groupEquiv
  have hmark (a : L ⧸ pCore 2 L) (v : D.chosenCentralQuotient) :
      em (D.centralQuotientAction a v) = Atlas.G2.Natural.action S.field.Carrier (gm a) (em v) := by
    let : Algebra (ZMod 2) S.field.Carrier := S.field.binaryAlgebra
    exact m.intertwines a v
  exact {
    groupEquiv := gm
    linearEquiv := em.toLinearEquiv (ZMod.map_smul em)
    intertwines := by
      intro a v
      change em (D.centralQuotientAction a v) = _
      rw [Atlas.G2.Natural.Normalizer.binary_apply]
      exact hmark a v }

/-- The exact selected conjugate supplies an inner G₂ actor of rank and moved dimension four. -/
theorem ofFlag_exists_inner_four_actor [Finite F]
    (X : Subgroup G) (z : G) (H₀ : Subgroup G)
    (hF : Nat.card F = 4) (hG2 : Nat.card S.field.Carrier = 4)
    (hfix : V ⊓ centralizer (L : Set G) = ⊥)
    (hchosen : normalizer (V : Set G) ≤ normalizer (L : Set G)) (I U : Subgroup G)
    (hout : ¬ I ≤ normalizer (L : Set G))
    (hN : normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
      normalizer (L : Set G))
    (hC : (I ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) =
      (I ⊔ (T : Subgroup G)).pCoreIn 2)
    (hU : IsPGroup 2 U) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hW : indexedWeakClosure V (T : Subgroup G) 0 ≤ (ofFlag S f X z H₀).R₂)
    (hs : (4 : ℕ∞) ≤ @globalS G _ V D.elementary)
    (hr : (4 : ℕ∞) < globalR V)
    (α : (ofFlag S f X z H₀).R₂ →* Sp F) (e : U ≃* Multiplicative (Vector F))
    (hact : ∀ (a : (ofFlag S f X z H₀).R₂) (u : U),
      (e ⟨a.val * u.val * a.val⁻¹,
        (mem_normalizer_iff.mp (hTU (LocalGeometry.localRadical_le_sylow _ a.property))
          u.val).mp u.property⟩).toAdd = α a • (e u).toAdd)
    (himage : α.range ≤ Plane.radical.map planeLocal.subtype) :
    ∃ (g : G) (hUg : U ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
      (eA : V.map (MulAut.conj g).toMonoidHom ≃*
        Multiplicative (Atlas.G2.Natural.Space S.field.Carrier))
      (β : normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) →*
        linearNormalizer (Atlas.G2.Natural.Normalizer.binary S.field.Carrier))
      (C : Subgroup (Atlas.G2.Model S.field.Carrier)),
      V.map (MulAut.conj g).toMonoidHom ≤ (ofFlag S f X z H₀).R₂ ∧
      (∀ (n : normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
          (a : V.map (MulAut.conj g).toMonoidHom),
        (eA ⟨n.val * a.val * n.val⁻¹,
          (mem_normalizer_iff.mp n.property a.val).mp a.property⟩).toAdd =
          normalizerRepresentation (Atlas.G2.Natural.Normalizer.binary S.field.Carrier)
            (β n) (eA a).toAdd) ∧
      C.map (normalizerEmbedding (Atlas.G2.Natural.Normalizer.binary S.field.Carrier)) =
        (β.comp (inclusion hUg)).range ∧
      IsElementaryAbelian 2 C ∧
      Module.finrank (ZMod 2)
        (subspaceCommutator (Atlas.G2.Natural.Normalizer.binary S.field.Carrier) ⊤ C) = 4 ∧
      rank C = 4 := by
  obtain ⟨g,hgR,_,_,hUg,_,_,_,hc,hrank⟩ :=
    ofFlag_exists_mutual_rank_four D S f X z H₀ hF I U hout hN hC hU hTU hW hs hr α e hact himage
  obtain ⟨eA,β,hβ⟩ := RankComparison.chosen_conjugate_normalizer D _ (canonicalMarking D S m) hfix hchosen g
  let : IsElementaryAbelian 2 (Multiplicative (Vector F)) := BinaryGroupAction.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  obtain ⟨C,hCe,hCmap,hCm,hCr⟩ := RankComparison.exists_inner_actor hG2
    (V.map (MulAut.conj g).toMonoidHom) U hUg eA β hβ hc hrank
  exact ⟨g,hUg,eA,β,C,hgR,hβ,hCmap,hCe,hCm,hCr⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle
