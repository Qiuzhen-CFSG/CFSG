module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.TorusConjugacy
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.Transfer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.SourceSupplement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Generation

/-!
# The opposite pair and containment of the original symplectic core

Choose the Cartan-compatible opposite pair in the original group. The
literal Q/((W∩Wʸ)V) action has natural coordinates, so the constructed
Cartan diagonal bounds C_Q(X₁) by the denominator. Conjugacy of X₁ under
the full opposite stabilizer and concrete point-radical transitivity give
the Frattini supplement. The original 11.5.6 commutator conclusions then
put Q in O₂(G₁). Three L₁-conjugates of the same pair and the genuine
symplectic multiplier theorem give O₂(L)≤O₂(G₁), including q=4.

The remaining inputs precede this branch: TI geometry from 11.0.3.3.4,
G₁=KY M₁ from 11.4.3.2, the Cartan and 11.5.6(4--5), and the radical
image, displacement and Frattini bounds. Their discharge, including the
full-cover identity [V,O₂(L₁)]=V₃, belongs to the final assembly owner
qt-d-1222-natural-closure-sp4. No opposite-pair, quotient-recognition,
diagonal, stabilizer-conjugacy or orbit-transitivity premise remains.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

open Subgroup Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
open CFSG.Quasithin.Chapter12.Section02 OppositeGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

private theorem opposite_not_le_threeSpace (m : MarkedFlag E) (y : G)
    (hjoin : E.V₃ ⊔ E.V₁.map (MulAut.conj y).toMonoidHom = V) :
    ¬ E.V₁.map (MulAut.conj y).toMonoidHom ≤ E.V₃ := by
  intro hle
  have he : E.V₃ = V := by simpa only [sup_eq_left.mpr hle] using hjoin
  rw [m.threeSpace_preimage] at he
  have hh : m.flag.space 2 = ⊤ := (LocalGeometry.Coordinates.sp4 m.action).preimage_injective
    (he.trans (LocalGeometry.Coordinates.sp4 m.action).preimage_top.symm)
  have hd := m.flag.dimension 2
  rw [hh,finrank_top] at hd
  change Module.finrank E.input.field.Carrier (Theory.SpecificGroups.SymplecticFour.Vector E.input.field.Carrier) = 3 at hd
  norm_num [Theory.SpecificGroups.SymplecticFour.Vector] at hd

/-- Construct the opposite pair and complete its transfer to O₂(G₁).
Only preceding flag/orbit geometry, 11.5.6, and radical-action outputs remain
as inputs; the quotient recognition, Cartan diagonal and stabilizer conjugacy
are all discharged for this same y. -/
theorem exists_cartan_opposite_core (m : MarkedFlag E)
    (hX : LocalGeometry.IsCartan T L E.X)
    (hV : V ≤ E.G₁.pCoreIn 2) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hroot : actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hmove : ⁅V,auxiliaryW E⁆ = E.V₁)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (hfour : ∀ P : Subgroup G, ⁅P,E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤ (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hM3 : E.M₁ ≤ normalizer (E.V₃ : Set G))
    (hG : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁) :
    ∃ (g : Sp E.input.field.Carrier) (y : L),
      (∀ i : Fin 3, m.flag.space i = LocalGeometry.Sp4.ModelFlag.movedStage g i.succ) ∧
      PointModel.quotientMap m y = g * TwoConjugate.opposition * g⁻¹ ∧
      actionImage (V := V) (oppositeJoin (auxiliaryW E) (y:G)) =
        (OppositeLongRootPair.pair.map (MulAut.conj g).toMonoidHom).map (FullAction.modelHom m) ∧
      cartanKernel E ≤ oppositeJoin (auxiliaryW E) (y:G) ∧
      E.X ≤ normalizer (E.V₁.map (MulAut.conj (y:G)).toMonoidHom : Set G) ∧
      (oppositeJoin (auxiliaryW E) (y:G)).pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      corePair (auxiliaryW E) (y:G) ≤ E.G₁.pCoreIn 2 ∧
      L.pCoreIn 2 ≤ E.G₁.pCoreIn 2 := by
  obtain ⟨g,y,hflag,hlocal,hy,hi,hXI,hXp,_hXQ,_hc,hjoin,_hmeet,hcore,_hN,hgen⟩ :=
    exists_cartan_opposite_with_kernel E m hX hW hroot hPhi
  have hXL : E.X ≤ L := hX.1.trans inf_le_left
  have hXG : E.X ≤ E.G₁ := by
    change E.X ≤ normalizer (E.V₁ : Set G)
    rw [m.point_preimage]
    exact cartan_normalizes_marked_flag E m hX 0
  have ho : Odd (Nat.card (cartanKernel E)) := hX.odd.of_dvd_nat
    (card_dvd_of_le (show cartanKernel E ≤ E.X from inf_le_left))
  have hr := hroot.trans (FullAction.center_eq_marked_root m g hlocal)
  have hf := centralizer_le_of_cartan_opposite E m hX hW hPhi g hflag y hy hXp hi hr hmove hjoin.symm hcore hXI
  have hconj := opposite_stabilizer_cartan_conjugacy E m hX hW g hflag y hy hXp hi hXI
  have hQ := corePair_le_point_core_of_cartan E m y.property hV hW hcore hXI ho hf hG
    (marked_point_stabilizer_supplement E m g hflag y hy
      (opposite_not_le_threeSpace E m y hjoin) hM3)
    (stabilizer_normalizes_commutator_of_core_conjugacy E m y.property hcore hXI ho hconj)
    (cartan_commutator_KY_le_core E m y.property hV hW hPhi hcore hXI ho
      hXL hXG hXp hfour hfive)
  obtain ⟨l,hl,hgen⟩ := hgen
  exact ⟨g,y,hflag,hy,hi,hXI,hXp,hcore,hQ,
    core_le_point_core_of_three_opposites E m y.property hW hcore hQ l hl hgen⟩

/-- The original symplectic two-core lies in the original point-normalizer
core, using the genuine multiplier theorem also at q=4. The full source
11.5.7 assembly is owned by qt-d-1222-natural-closure-sp4. -/
theorem core_le_point_core (m : MarkedFlag E)
    (hX : LocalGeometry.IsCartan T L E.X)
    (hV : V ≤ E.G₁.pCoreIn 2) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hroot : actionImage (V := V) (auxiliaryW E) =
      (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype)
    (hmove : ⁅V,auxiliaryW E⁆ = E.V₁)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (hfour : ∀ P : Subgroup G, ⁅P,E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤ (E.K ⊔ (T : Subgroup G)).pCoreIn 2)
    (hti : ∀ g ∈ E.M, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hthree : ⁅V,E.L₁.pCoreIn 2⁆ = E.V₃)
    (hG : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁) : L.pCoreIn 2 ≤ E.G₁.pCoreIn 2 := by
  obtain ⟨g,y,_hf,_hy,_hi,_hXI,_hXp,_hcore,_hQ,hL⟩ :=
    exists_cartan_opposite_core E m hX hV hW hroot hmove hPhi hfour hfive (M₁_normalizes_threeSpace_of_radical_displacement E m hti hthree) hG
  exact hL

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
