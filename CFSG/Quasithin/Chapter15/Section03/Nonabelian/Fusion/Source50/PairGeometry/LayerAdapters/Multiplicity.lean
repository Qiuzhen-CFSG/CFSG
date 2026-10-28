module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters.Literal

/-!
# Arbitrary-multiplicity coordinates on the literal pair quotient

The binary augmentation core is a two-dimensional plane. Applying that
coordinate equivalence in every summand identifies the canonical pair
quotient with two families of s binary planes, retaining the multiplicity
of the original source module witness. No multiplicity-one conclusion is
needed by the source57 normal reduction.

Source: Aschbacher–Smith, 15.3.54(4) and 15.3.57, pp.1146–1148.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters
open Subgroup
open scoped IsMulCommutative
open ChapterG.Section02 OrthogonalPlusFour OrthogonalPlusFour.Chapter15Collapse

def commonPlaneCoordinates (s : ℕ) :
    Multiplicative (Fin 2 → Fin s → ThreeCore) ≃*
      (Fin 2 → Fin s → Multiplicative (Fin 2 → ZMod 2)) where
  toFun v i j := coreCoordinates.toAddEquiv.toMultiplicative (Multiplicative.ofAdd (v.toAdd i j))
  invFun v := Multiplicative.ofAdd fun i j =>
    (coreCoordinates.toAddEquiv.toMultiplicative.symm (v i j)).toAdd
  left_inv v := by
    apply Multiplicative.toAdd.injective
    funext i j
    simp
  right_inv v := by
    funext i j
    simp
  map_mul' v w := by
    funext i j
    exact coreCoordinates.toAddEquiv.toMultiplicative.map_mul _ _

variable {G : Type*} [Group G] [Finite G]
  {Z ZS Zperp V Y T : Subgroup G} {g : G}
  [((OrthogonalPlusFour.S₂ (Chapter15.setup Z Zperp Y T) g).subgroupOf
    ((Chapter15.setup Z Zperp Y T).S g)).Normal]
  [IsElementaryAbelian 2 (OrthogonalPlusFour.Quotient (Chapter15.setup Z Zperp Y T) g)]
  [(V.subgroupOf (pairP Z ZS g)).Normal]

omit [Finite G] in
private theorem quotient_equiv_cast
    {P B P' B' : Subgroup G} [(B.subgroupOf P).Normal] [(B'.subgroupOf P').Normal]
    {A : Type*} [Group A] (hP : P = P') (hB : B = B')
    (he : Nonempty ((P ⧸ B.subgroupOf P) ≃* A)) :
    Nonempty ((P' ⧸ B'.subgroupOf P') ≃* A) := by
  subst P' B'
  exact he

/-- The normal-reduction quotient, with the same source multiplicity. -/
theorem literal_common_quotient
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS)
    (hspan : localSpan Z Y = V)
    (d : Hypothesis (Chapter15.setup Z Zperp Y T) g) (f : SourceModuleData d)
    (hΩ : omegaCenter T = Z)
    (hsame : f.decomposition.leftMultiplicity = f.decomposition.rightMultiplicity) :
    Nonempty ((pairP Z ZS g ⧸ V.subgroupOf (pairP Z ZS g)) ≃*
      (Fin 2 → Fin f.decomposition.leftMultiplicity → Multiplicative (Fin 2 → ZMod 2))) := by
  let D := Chapter15.setup Z Zperp Y T
  have hP : D.S g = pairP Z ZS g := Chapter15.S_eq g hZS hperp
  have hV : D.VL = V := Chapter15.VL_eq hspan
  have : (D.VL.subgroupOf (D.S g)).Normal := by
    rw [hP,hV]
    infer_instance
  have hΩD : omegaCenter D.T ≤ D.VL := by
    change omegaCenter T ≤ D.VL
    rw [hΩ]
    exact point_le_VL D
  let e : (D.S g ⧸ D.VL.subgroupOf (D.S g)) ≃*
      (Fin 2 → Fin f.decomposition.leftMultiplicity → Multiplicative (Fin 2 → ZMod 2)) :=
    (commonQuotientEquiv (σ := f.representation)
      (canonicalFactorData d f hΩD).conjugation f.decomposition hsame).trans
        (commonPlaneCoordinates _)
  exact quotient_equiv_cast hP hV ⟨e⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters
