module

public import Submission.FeitThompson.Wielandt.HomocyclicLift

/-!
# Standard homocyclic quotient-cover packages for Wielandt

This file contains the standard homocyclic Frattini quotient-cover data
records and checked adapters used by the Wielandt fixed-point
infrastructure. The source-existence theorems that construct these packages
remain in `FeitThompson.Wielandt`.
-/

noncomputable section

namespace Wielandt

universe u

/-- Prime-exponent base case of the homocyclic Frattini quotient-cover
construction.

When `e = 1`, the elementary-abelian group itself is a valid cover: its
Frattini subgroup is trivial, the quotient by the Frattini subgroup is just
`V`, and a `ZMod p` basis supplies the required coordinates. -/
public theorem exists_homocyclic_frattini_quotient_cover_e_one
    {G V : Type u} [Group G] [Finite G] [Group V] [Finite V]
    [MulDistribMulAction G V] [Fintype G] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V] :
    Nonempty (HomocyclicFrattiniQuotientCover (G := G) (V := V) (p := p) 1) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : DecidableEq V := Classical.decEq V
  haveI : Fact (IsPGroup p V) := ⟨IsElementaryAbelian.isPGroup p V⟩
  have hExp : Monoid.exponent V = p := IsElementaryAbelian.exponent_eq_prime (G := V) (p := p)
  let matrixIndex : Type u := ULift (Fin (Module.finrank (ZMod p) (Additive V)))
  let b : Module.Basis (Fin (Module.finrank (ZMod p) (Additive V))) (ZMod p) (Additive V) :=
    Module.finBasis (ZMod p) (Additive V)
  let reindexEquiv :
      (matrixIndex → ZMod (p ^ 1)) ≃+ (Fin (Module.finrank (ZMod p) (Additive V)) → ZMod (p ^ 1)) := {
    toFun := fun f i => f (ULift.up i)
    invFun := fun f i => f i.down
    left_inv := by
      intro f
      ext i
      cases i
      rfl
    right_inv := by
      intro f
      ext i
      rfl
    map_add' := by
      intro f g
      ext i
      rfl }
  let coordinateEquiv : (matrixIndex → ZMod (p ^ 1)) ≃+ Additive V :=
    (reindexEquiv.trans (AddEquiv.piCongrRight fun _ => ZMod.ringEquivCongr (pow_one p))).trans
      b.equivFun.symm.toAddEquiv
  let frattiniQuotientEquiv : V ⧸ frattini V ≃* V :=
    frattiniQuotientEquivOfIsElementaryAbelian (R := V) (p := p)
  let coverAction : G →* MulAut V := MulDistribMulAction.toMulAut G V
  exact ⟨{
    cover := V
    instGroupCover := inferInstance
    instFiniteCover := inferInstance
    instFintypeCover := inferInstance
    instDecidableEqCover := inferInstance
    cover_isPGroup := IsElementaryAbelian.isPGroup p V
    cover_commutative := inferInstance
    cover_exponent := by simpa using hExp
    matrixIndex := matrixIndex
    instFintypeMatrixIndex := inferInstance
    instDecidableEqMatrixIndex := inferInstance
    coordinateEquiv := coordinateEquiv
    frattiniQuotientEquiv := frattiniQuotientEquiv
    coverAction := coverAction
    quotientEquiv_action := by
      intro g w
      dsimp [frattiniQuotientEquiv, coverAction]
      rw [frattiniQuotientEquivOfIsElementaryAbelian_coe,
        frattiniQuotientEquivOfIsElementaryAbelian_coe]
    card_matrixIndex := by
      simp [matrixIndex] }⟩


public structure StandardHomocyclicFrattiniQuotientCoverData
    (G V : Type u) [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) : Type (u + 1) where
  matrixIndex : Type u
  [instFintypeMatrixIndex : Fintype matrixIndex]
  [instDecidableEqMatrixIndex : DecidableEq matrixIndex]
  [instNonemptyMatrixIndex : Nonempty matrixIndex]
  frattiniQuotientEquiv :
    StandardHomocyclicCover matrixIndex (p ^ e) ⧸
      frattini (StandardHomocyclicCover matrixIndex (p ^ e)) ≃* V
  coverAction : G →* MulAut (StandardHomocyclicCover matrixIndex (p ^ e))
  quotientEquiv_action :
    ∀ (g : G) (w : StandardHomocyclicCover matrixIndex (p ^ e)),
      frattiniQuotientEquiv
          (QuotientGroup.mk' (frattini (StandardHomocyclicCover matrixIndex (p ^ e)))
            (coverAction g w)) =
        g • frattiniQuotientEquiv
          (QuotientGroup.mk' (frattini (StandardHomocyclicCover matrixIndex (p ^ e))) w)
  card_matrixIndex :
    Fintype.card matrixIndex = Module.finrank (ZMod p) (Additive V)


public structure StandardHomocyclicFrattiniQuotientCoverActionData
    (G V : Type u) [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) : Type (u + 1) where
  matrixIndex : Type u
  [instFintypeMatrixIndex : Fintype matrixIndex]
  [instDecidableEqMatrixIndex : DecidableEq matrixIndex]
  [instNonemptyMatrixIndex : Nonempty matrixIndex]
  height_pos : 1 ≤ e
  quotientToV : StandardHomocyclicCover matrixIndex p ≃* V
  coverAction : G →* MulAut (StandardHomocyclicCover matrixIndex (p ^ e))
  quotientEquiv_action :
    ∀ (g : G) (w : StandardHomocyclicCover matrixIndex (p ^ e)),
      quotientToV (standardHomocyclicCoverReduction matrixIndex p e height_pos
          (coverAction g w)) =
        g • quotientToV (standardHomocyclicCoverReduction matrixIndex p e height_pos w)
  card_matrixIndex :
    Fintype.card matrixIndex = Module.finrank (ZMod p) (Additive V)

/-- Source-hard standard cover data at the coordinate-linear interface.

This is the part of the higher-exponent standard cover construction before
turning the linear automorphisms of the free `ZMod (p ^ e)` coordinates into
multiplicative automorphisms of `StandardHomocyclicCover`. -/
public structure StandardHomocyclicFrattiniQuotientCoverLinearData
    (G V : Type u) [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) : Type (u + 1) where
  matrixIndex : Type u
  [instFintypeMatrixIndex : Fintype matrixIndex]
  [instDecidableEqMatrixIndex : DecidableEq matrixIndex]
  [instNonemptyMatrixIndex : Nonempty matrixIndex]
  height_pos : 1 ≤ e
  quotientToV : StandardHomocyclicCover matrixIndex p ≃* V
  linearLift : G →* (Module.End (ZMod (p ^ e)) (matrixIndex → ZMod (p ^ e)))ˣ
  quotientEquiv_linear :
    ∀ (g : G) (w : StandardHomocyclicCover matrixIndex (p ^ e)),
      quotientToV (standardHomocyclicCoverReduction matrixIndex p e height_pos
          (Multiplicative.ofAdd
            (((linearLift g :
                (Module.End (ZMod (p ^ e)) (matrixIndex → ZMod (p ^ e)))ˣ) :
              Module.End (ZMod (p ^ e)) (matrixIndex → ZMod (p ^ e)))
              (Multiplicative.toAdd w)))) =
        g • quotientToV (standardHomocyclicCoverReduction matrixIndex p e height_pos w)
  card_matrixIndex :
    Fintype.card matrixIndex = Module.finrank (ZMod p) (Additive V)

/-- Source-hard standard cover data reduced to a matrix lifting condition, with
the cover height supplied by the checked wrapper.

The mod-`p` action is defined and checked by transport through the
source-chosen quotient map. The remaining source-hard datum is a matrix
representation over `ZMod (p ^ e)` whose coordinatewise additive reduction is
that transported mod-`p` linear action. -/
public structure StandardHomocyclicFrattiniQuotientCoverMatrixReductionCoreData
    (G V : Type u) [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) (height_pos : 1 ≤ e) : Type (u + 1) where
  matrixIndex : Type u
  [instFintypeMatrixIndex : Fintype matrixIndex]
  quotientToV : StandardHomocyclicCover matrixIndex p ≃* V
  matrixLift : G → Matrix matrixIndex matrixIndex (ZMod (p ^ e))
  matrixLift_one :
    letI : DecidableEq matrixIndex := Classical.decEq matrixIndex
    matrixLift 1 = 1
  matrixLift_mul :
    letI : DecidableEq matrixIndex := Classical.decEq matrixIndex
    ∀ g h : G, matrixLift (g * h) = matrixLift g * matrixLift h
  reduction_matrix :
    letI : DecidableEq matrixIndex := Classical.decEq matrixIndex
    ∀ (g : G) (x : matrixIndex → ZMod (p ^ e)),
      standardHomocyclicCoverAddReduction matrixIndex p e height_pos
          (Matrix.toLin' (matrixLift g) x) =
        (((standardHomocyclicCoverModPLinearActionOfEquiv
            (G := G) (V := V) (p := p) quotientToV g :
            (Module.End (ZMod p) (matrixIndex → ZMod p))ˣ) :
          Module.End (ZMod p) (matrixIndex → ZMod p))
          (standardHomocyclicCoverAddReduction matrixIndex p e height_pos x))

/-- Source-hard standard cover data at the reduction-compatible matrix
interface, with the positive height reattached as checked data. -/
public structure StandardHomocyclicFrattiniQuotientCoverMatrixReductionData
    (G V : Type u) [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) : Type (u + 1) where
  height_pos : 1 ≤ e
  core :
    StandardHomocyclicFrattiniQuotientCoverMatrixReductionCoreData
      (G := G) (V := V) (p := p) e height_pos


public structure StandardHomocyclicFrattiniQuotientCoverMatrixData
    (G V : Type u) [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) : Type (u + 1) where
  matrixIndex : Type u
  [instFintypeMatrixIndex : Fintype matrixIndex]
  [instDecidableEqMatrixIndex : DecidableEq matrixIndex]
  [instNonemptyMatrixIndex : Nonempty matrixIndex]
  height_pos : 1 ≤ e
  quotientToV : StandardHomocyclicCover matrixIndex p ≃* V
  matrixLift : G → Matrix matrixIndex matrixIndex (ZMod (p ^ e))
  matrixLift_one : matrixLift 1 = 1
  matrixLift_mul : ∀ g h : G, matrixLift (g * h) = matrixLift g * matrixLift h
  quotientEquiv_matrix :
    ∀ (g : G) (w : StandardHomocyclicCover matrixIndex (p ^ e)),
      quotientToV (standardHomocyclicCoverReduction matrixIndex p e height_pos
          (Multiplicative.ofAdd
            (Matrix.toLin' (matrixLift g) (Multiplicative.toAdd w)))) =
        g • quotientToV (standardHomocyclicCoverReduction matrixIndex p e height_pos w)
  card_matrixIndex :
    Fintype.card matrixIndex = Module.finrank (ZMod p) (Additive V)

/-- Pass from a reduction-compatible matrix lift to the source-shaped matrix
package whose quotient/action compatibility is stated directly on `V`. -/
public noncomputable def
    StandardHomocyclicFrattiniQuotientCoverMatrixReductionData.toStandardHomocyclicFrattiniQuotientCoverMatrixData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V] [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (D : StandardHomocyclicFrattiniQuotientCoverMatrixReductionData
      (G := G) (V := V) (p := p) e) :
    StandardHomocyclicFrattiniQuotientCoverMatrixData
      (G := G) (V := V) (p := p) e := by
  classical
  letI : Fintype D.core.matrixIndex := D.core.instFintypeMatrixIndex
  letI : DecidableEq D.core.matrixIndex := Classical.decEq D.core.matrixIndex
  letI : Nonempty D.core.matrixIndex :=
    standardHomocyclicCoverQuotientEquiv_nonempty_matrixIndex
      (V := V) (p := p) D.core.quotientToV
  exact {
    matrixIndex := D.core.matrixIndex
    instFintypeMatrixIndex := D.core.instFintypeMatrixIndex
    instDecidableEqMatrixIndex := inferInstance
    instNonemptyMatrixIndex := inferInstance
    height_pos := D.height_pos
    quotientToV := D.core.quotientToV
    matrixLift := D.core.matrixLift
    matrixLift_one := D.core.matrixLift_one
    matrixLift_mul := D.core.matrixLift_mul
    quotientEquiv_matrix := by
      intro g w
      let y :=
        standardHomocyclicCoverAddReduction D.core.matrixIndex p e D.height_pos
          (Multiplicative.toAdd w)
      have hright :
          standardHomocyclicCoverReduction D.core.matrixIndex p e D.height_pos w =
            Multiplicative.ofAdd y := by
        apply Multiplicative.toAdd.injective
        simp [y, standardHomocyclicCoverReduction_toAdd]
      have hleft :
          standardHomocyclicCoverReduction D.core.matrixIndex p e D.height_pos
              (Multiplicative.ofAdd
                (Matrix.toLin' (D.core.matrixLift g) (Multiplicative.toAdd w))) =
            Multiplicative.ofAdd
              (standardHomocyclicCoverAddReduction D.core.matrixIndex p e D.height_pos
                (Matrix.toLin' (D.core.matrixLift g) (Multiplicative.toAdd w))) := by
        apply Multiplicative.toAdd.injective
        simp [standardHomocyclicCoverReduction_toAdd]
      rw [hleft, D.core.reduction_matrix g (Multiplicative.toAdd w),
        standardHomocyclicCoverModPLinearActionOfEquiv_coordinate
          (G := G) (V := V) (p := p) D.core.quotientToV g y,
        hright]
      exact standardHomocyclicCoverModPActionOfEquiv_quotientToV
        (G := G) (V := V) (p := p) D.core.quotientToV g _
    card_matrixIndex :=
      standardHomocyclicCoverQuotientEquiv_card_matrixIndex
        (V := V) (p := p) D.core.quotientToV }

/-- A matrix representation of the source-chosen standard cover gives the
coordinate-linear source package, using inverse matrices supplied by the group
law. -/
public noncomputable def
    StandardHomocyclicFrattiniQuotientCoverMatrixData.toStandardHomocyclicFrattiniQuotientCoverLinearData
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (D : StandardHomocyclicFrattiniQuotientCoverMatrixData
      (G := G) (V := V) (p := p) e) :
    StandardHomocyclicFrattiniQuotientCoverLinearData
      (G := G) (V := V) (p := p) e := by
  classical
  letI : Fintype D.matrixIndex := D.instFintypeMatrixIndex
  letI : DecidableEq D.matrixIndex := D.instDecidableEqMatrixIndex
  letI : Nonempty D.matrixIndex := D.instNonemptyMatrixIndex
  let linearLift :
      G →*
        (Module.End (ZMod (p ^ e)) (D.matrixIndex → ZMod (p ^ e)))ˣ := by
    let toUnit : G →
        (Module.End (ZMod (p ^ e)) (D.matrixIndex → ZMod (p ^ e)))ˣ := fun g => {
      val := Matrix.toLin' (D.matrixLift g)
      inv := Matrix.toLin' (D.matrixLift g⁻¹)
      val_inv := by
        rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← D.matrixLift_mul, mul_inv_cancel,
          D.matrixLift_one, Matrix.toLin'_one]
        rfl
      inv_val := by
        rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← D.matrixLift_mul, inv_mul_cancel,
          D.matrixLift_one, Matrix.toLin'_one]
        rfl }
    exact {
      toFun := toUnit
      map_one' := by
        apply Units.ext
        change Matrix.toLin' (D.matrixLift 1) =
          (1 : Module.End (ZMod (p ^ e)) (D.matrixIndex → ZMod (p ^ e)))
        rw [D.matrixLift_one, Matrix.toLin'_one]
        rfl
      map_mul' := by
        intro g h
        apply Units.ext
        change Matrix.toLin' (D.matrixLift (g * h)) =
          Matrix.toLin' (D.matrixLift g) * Matrix.toLin' (D.matrixLift h)
        rw [D.matrixLift_mul, Module.End.mul_eq_comp, ← Matrix.toLin'_mul] }
  exact {
    matrixIndex := D.matrixIndex
    instFintypeMatrixIndex := D.instFintypeMatrixIndex
    instDecidableEqMatrixIndex := D.instDecidableEqMatrixIndex
    instNonemptyMatrixIndex := D.instNonemptyMatrixIndex
    height_pos := D.height_pos
    quotientToV := D.quotientToV
    linearLift := linearLift
    quotientEquiv_linear := by
      intro g w
      simpa [linearLift] using D.quotientEquiv_matrix g w
    card_matrixIndex := D.card_matrixIndex }

/-- Canonical-index source data for the higher-exponent standard cover.

The index and quotient equivalence are fixed by a basis of `Additive V` over
`ZMod p`; the remaining source-hard datum is the lifted linear action and its
compatibility with coordinatewise reduction. -/
public structure StandardHomocyclicFrattiniQuotientCoverCanonicalLinearData
    (G V : Type u) [Group G] [Group V] [Finite V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) (he : 1 ≤ e) : Type (u + 1) where
  linearLift :
    G →*
      (Module.End (ZMod (p ^ e))
        (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)))ˣ
  quotientEquiv_linear :
    ∀ (g : G)
      (w : StandardHomocyclicCover
        (StandardHomocyclicCanonicalIndex (p := p) V) (p ^ e)),
      standardHomocyclicCoverToElementaryAbelianEquiv (p := p) V
          (standardHomocyclicCoverReduction
            (StandardHomocyclicCanonicalIndex (p := p) V) p e he
            (Multiplicative.ofAdd
              (((linearLift g :
                  (Module.End (ZMod (p ^ e))
                    (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)))ˣ) :
                Module.End (ZMod (p ^ e))
                  (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)))
                (Multiplicative.toAdd w)))) =
        g • standardHomocyclicCoverToElementaryAbelianEquiv (p := p) V
          (standardHomocyclicCoverReduction
            (StandardHomocyclicCanonicalIndex (p := p) V) p e he w)

/-- Canonical-index source data reduced to an additive linear lifting condition.

This is the direct linear form of the source construction: a
`ZMod (p ^ e)` representation whose coordinatewise additive reduction is the
checked mod-`p` linear action. -/
public structure StandardHomocyclicFrattiniQuotientCoverCanonicalAdditiveLinearReductionData
    (G V : Type u) [Group G] [Group V] [Finite V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) (he : 1 ≤ e) : Type (u + 1) where
  linearLift :
    G →*
      (Module.End (ZMod (p ^ e))
        (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)))ˣ
  reduction_linear :
    ∀ (g : G)
      (x : StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)),
      standardHomocyclicCoverAddReduction
          (StandardHomocyclicCanonicalIndex (p := p) V) p e he
          (((linearLift g :
              (Module.End (ZMod (p ^ e))
                (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)))ˣ) :
            Module.End (ZMod (p ^ e))
              (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e))) x) =
        (((standardHomocyclicCoverModPLinearAction G V (p := p) g :
            (Module.End (ZMod p)
              (StandardHomocyclicCanonicalIndex (p := p) V → ZMod p))ˣ) :
          Module.End (ZMod p)
            (StandardHomocyclicCanonicalIndex (p := p) V → ZMod p))
          (standardHomocyclicCoverAddReduction
            (StandardHomocyclicCanonicalIndex (p := p) V) p e he x))

/-- Canonical quotient-action linear data implies additive linear reduction
compatibility through the checked canonical mod-`p` action. -/
public noncomputable def
    StandardHomocyclicFrattiniQuotientCoverCanonicalLinearData.toStandardHomocyclicFrattiniQuotientCoverCanonicalAdditiveLinearReductionData
    {G V : Type u} [Group G] [Group V] [Finite V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ} {he : 1 ≤ e}
    (L : StandardHomocyclicFrattiniQuotientCoverCanonicalLinearData
      (G := G) (V := V) (p := p) e he) :
    StandardHomocyclicFrattiniQuotientCoverCanonicalAdditiveLinearReductionData
      (G := G) (V := V) (p := p) e he := by
  classical
  refine {
    linearLift := L.linearLift
    reduction_linear := ?_ }
  intro g x
  let quotientToV := standardHomocyclicCoverToElementaryAbelianEquiv (p := p) V
  apply Multiplicative.ofAdd.injective
  apply quotientToV.injective
  calc
    quotientToV
        (Multiplicative.ofAdd
          (standardHomocyclicCoverAddReduction
            (StandardHomocyclicCanonicalIndex (p := p) V) p e he
            (((L.linearLift g :
                (Module.End (ZMod (p ^ e))
                  (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)))ˣ) :
              Module.End (ZMod (p ^ e))
                (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e))) x))) =
      quotientToV
        (standardHomocyclicCoverReduction
          (StandardHomocyclicCanonicalIndex (p := p) V) p e he
          (Multiplicative.ofAdd
            (((L.linearLift g :
                (Module.End (ZMod (p ^ e))
                  (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)))ˣ) :
              Module.End (ZMod (p ^ e))
                (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e))) x))) := by
        congr 1
    _ = g • quotientToV
        (standardHomocyclicCoverReduction
          (StandardHomocyclicCanonicalIndex (p := p) V) p e he
          (Multiplicative.ofAdd x)) := by
        simpa using L.quotientEquiv_linear g (Multiplicative.ofAdd x)
    _ = quotientToV
        (standardHomocyclicCoverModPAction G V (p := p) g
          (standardHomocyclicCoverReduction
            (StandardHomocyclicCanonicalIndex (p := p) V) p e he
            (Multiplicative.ofAdd x))) := by
        exact (standardHomocyclicCoverModPAction_quotientToV
          (G := G) (V := V) (p := p) g
          (standardHomocyclicCoverReduction
            (StandardHomocyclicCanonicalIndex (p := p) V) p e he
            (Multiplicative.ofAdd x))).symm
    _ = quotientToV
        (standardHomocyclicCoverModPAction G V (p := p) g
          (Multiplicative.ofAdd
            (standardHomocyclicCoverAddReduction
              (StandardHomocyclicCanonicalIndex (p := p) V) p e he x))) := by
        congr 2
    _ = quotientToV
        (Multiplicative.ofAdd
          (((standardHomocyclicCoverModPLinearAction G V (p := p) g :
              (Module.End (ZMod p)
                (StandardHomocyclicCanonicalIndex (p := p) V → ZMod p))ˣ) :
            Module.End (ZMod p)
              (StandardHomocyclicCanonicalIndex (p := p) V → ZMod p))
            (standardHomocyclicCoverAddReduction
              (StandardHomocyclicCanonicalIndex (p := p) V) p e he x))) := by
        rw [standardHomocyclicCoverModPLinearAction_coordinate]


public structure StandardHomocyclicFrattiniQuotientCoverCanonicalMatrixReductionData
    (G V : Type u) [Group G] [Group V] [Finite V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) (he : 1 ≤ e) : Type (u + 1) where
  matrixLift :
    G → Matrix (StandardHomocyclicCanonicalIndex (p := p) V)
      (StandardHomocyclicCanonicalIndex (p := p) V) (ZMod (p ^ e))
  matrixLift_one : matrixLift 1 = 1
  matrixLift_mul : ∀ g h : G, matrixLift (g * h) = matrixLift g * matrixLift h
  reduction_matrix :
    ∀ (g : G)
      (x : StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)),
      standardHomocyclicCoverAddReduction
          (StandardHomocyclicCanonicalIndex (p := p) V) p e he
          (Matrix.toLin' (matrixLift g) x) =
        (((standardHomocyclicCoverModPLinearAction G V (p := p) g :
            (Module.End (ZMod p)
              (StandardHomocyclicCanonicalIndex (p := p) V → ZMod p))ˣ) :
          Module.End (ZMod p)
            (StandardHomocyclicCanonicalIndex (p := p) V → ZMod p))
          (standardHomocyclicCoverAddReduction
            (StandardHomocyclicCanonicalIndex (p := p) V) p e he x))

/-- Canonical-index matrix-reduction data is a source-chosen matrix-reduction
core with the index and quotient equivalence fixed by the checked canonical
coordinate equivalence. -/
public noncomputable def
    StandardHomocyclicFrattiniQuotientCoverCanonicalMatrixReductionData.toStandardHomocyclicFrattiniQuotientCoverMatrixReductionCoreData
    {G V : Type u} [Group G] [Group V] [Finite V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ} {he : 1 ≤ e}
    (D : StandardHomocyclicFrattiniQuotientCoverCanonicalMatrixReductionData
      (G := G) (V := V) (p := p) e he) :
    StandardHomocyclicFrattiniQuotientCoverMatrixReductionCoreData
      (G := G) (V := V) (p := p) e he := by
  classical
  exact {
    matrixIndex := StandardHomocyclicCanonicalIndex (p := p) V
    instFintypeMatrixIndex := inferInstance
    quotientToV := standardHomocyclicCoverToElementaryAbelianEquiv (p := p) V
    matrixLift := D.matrixLift
    matrixLift_one := by
      ext i j
      have h := congrFun (congrFun D.matrixLift_one i) j
      by_cases hij : i = j
      · subst j
        simpa [Matrix.one] using h
      · simpa [Matrix.one, hij] using h
    matrixLift_mul := by
      intro g h
      ext i j
      have hm := congrFun (congrFun (D.matrixLift_mul g h) i) j
      simp [Matrix.mul_apply] at hm ⊢
      exact hm
    reduction_matrix := by
      intro g x
      simpa [standardHomocyclicCoverModPLinearAction,
        standardHomocyclicCoverModPAction] using D.reduction_matrix g x }

/-- A matrix representation of the canonical standard cover gives units of the
endomorphism ring, using inverse matrices supplied by the group law. -/
public noncomputable def
    StandardHomocyclicFrattiniQuotientCoverCanonicalMatrixReductionData.toLinearLift
    {G V : Type u} [Group G] [Group V] [Finite V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ} {he : 1 ≤ e}
    (D : StandardHomocyclicFrattiniQuotientCoverCanonicalMatrixReductionData
      (G := G) (V := V) (p := p) e he) :
    G →*
      (Module.End (ZMod (p ^ e))
        (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)))ˣ := by
  classical
  let toUnit : G →
      (Module.End (ZMod (p ^ e))
        (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)))ˣ := fun g => {
    val := Matrix.toLin' (D.matrixLift g)
    inv := Matrix.toLin' (D.matrixLift g⁻¹)
    val_inv := by
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← D.matrixLift_mul, mul_inv_cancel,
        D.matrixLift_one, Matrix.toLin'_one]
      rfl
    inv_val := by
      rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← D.matrixLift_mul, inv_mul_cancel,
        D.matrixLift_one, Matrix.toLin'_one]
      rfl }
  exact {
    toFun := toUnit
    map_one' := by
      apply Units.ext
      change Matrix.toLin' (D.matrixLift 1) =
        (1 : Module.End (ZMod (p ^ e))
          (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)))
      rw [D.matrixLift_one, Matrix.toLin'_one]
      rfl
    map_mul' := by
      intro g h
      apply Units.ext
      change Matrix.toLin' (D.matrixLift (g * h)) =
        Matrix.toLin' (D.matrixLift g) * Matrix.toLin' (D.matrixLift h)
      rw [D.matrixLift_mul, Module.End.mul_eq_comp, ← Matrix.toLin'_mul] }

/-- Pass from matrix reduction compatibility to additive linear reduction
compatibility. -/
public noncomputable def
    StandardHomocyclicFrattiniQuotientCoverCanonicalMatrixReductionData.toStandardHomocyclicFrattiniQuotientCoverCanonicalAdditiveLinearReductionData
    {G V : Type u} [Group G] [Group V] [Finite V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ} {he : 1 ≤ e}
    (D : StandardHomocyclicFrattiniQuotientCoverCanonicalMatrixReductionData
      (G := G) (V := V) (p := p) e he) :
    StandardHomocyclicFrattiniQuotientCoverCanonicalAdditiveLinearReductionData
      (G := G) (V := V) (p := p) e he where
  linearLift := D.toLinearLift
  reduction_linear := D.reduction_matrix

/-- Pass from additive linear reduction data to canonical matrix reduction data
by taking matrices in the standard coordinate basis. -/
public noncomputable def
    StandardHomocyclicFrattiniQuotientCoverCanonicalAdditiveLinearReductionData.toStandardHomocyclicFrattiniQuotientCoverCanonicalMatrixReductionData
    {G V : Type u} [Group G] [Group V] [Finite V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ} {he : 1 ≤ e}
    (L : StandardHomocyclicFrattiniQuotientCoverCanonicalAdditiveLinearReductionData
      (G := G) (V := V) (p := p) e he) :
    StandardHomocyclicFrattiniQuotientCoverCanonicalMatrixReductionData
      (G := G) (V := V) (p := p) e he := by
  classical
  exact {
    matrixLift := fun g =>
      LinearMap.toMatrix'
        ((L.linearLift g :
            (Module.End (ZMod (p ^ e))
              (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)))ˣ) :
          Module.End (ZMod (p ^ e))
            (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)))
    matrixLift_one := by
      simp
    matrixLift_mul := by
      intro g h
      simp [map_mul, LinearMap.toMatrix'_mul]
    reduction_matrix := by
      intro g x
      simpa using L.reduction_linear g x }

/-- Canonical-index source data reduced to the genuine lifting condition.

The mod-`p` action is already checked by
`standardHomocyclicCoverModPAction`; the source-hard datum is a linear action
over `ZMod (p ^ e)` whose coordinatewise reduction is that mod-`p` action. -/
public structure StandardHomocyclicFrattiniQuotientCoverCanonicalLinearReductionData
    (G V : Type u) [Group G] [Group V] [Finite V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (e : ℕ) (he : 1 ≤ e) : Type (u + 1) where
  linearLift :
    G →*
      (Module.End (ZMod (p ^ e))
        (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)))ˣ
  reduction_compat :
    ∀ (g : G)
      (w : StandardHomocyclicCover (StandardHomocyclicCanonicalIndex (p := p) V) (p ^ e)),
      standardHomocyclicCoverReduction
          (StandardHomocyclicCanonicalIndex (p := p) V) p e he
          (Multiplicative.ofAdd
            (((linearLift g :
                (Module.End (ZMod (p ^ e))
                  (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)))ˣ) :
              Module.End (ZMod (p ^ e))
                (StandardHomocyclicCanonicalIndex (p := p) V → ZMod (p ^ e)))
              (Multiplicative.toAdd w))) =
        standardHomocyclicCoverModPAction G V (p := p) g
          (standardHomocyclicCoverReduction
            (StandardHomocyclicCanonicalIndex (p := p) V) p e he w)

/-- Pass from additive linear reduction compatibility to the multiplicative
standard-cover compatibility used by the quotient-cover adapter. -/
public noncomputable def
    StandardHomocyclicFrattiniQuotientCoverCanonicalAdditiveLinearReductionData.toStandardHomocyclicFrattiniQuotientCoverCanonicalLinearReductionData
    {G V : Type u} [Group G] [Group V] [Finite V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ} {he : 1 ≤ e}
    (L : StandardHomocyclicFrattiniQuotientCoverCanonicalAdditiveLinearReductionData
      (G := G) (V := V) (p := p) e he) :
    StandardHomocyclicFrattiniQuotientCoverCanonicalLinearReductionData
      (G := G) (V := V) (p := p) e he := by
  classical
  refine {
    linearLift := L.linearLift
    reduction_compat := ?_ }
  intro g w
  apply Multiplicative.toAdd.injective
  rw [standardHomocyclicCoverReduction_toAdd]
  let y :=
    standardHomocyclicCoverAddReduction
      (StandardHomocyclicCanonicalIndex (p := p) V) p e he (Multiplicative.toAdd w)
  have hred :
      standardHomocyclicCoverReduction
          (StandardHomocyclicCanonicalIndex (p := p) V) p e he w =
        Multiplicative.ofAdd y := by
    apply Multiplicative.toAdd.injective
    simp [y, standardHomocyclicCoverReduction_toAdd]
  rw [hred]
  have hcoord := congrArg Multiplicative.toAdd
    (standardHomocyclicCoverModPLinearAction_coordinate
      (G := G) (V := V) (p := p) g y)
  rw [← hcoord]
  simpa using L.reduction_linear g (Multiplicative.toAdd w)

/-- Assemble reduction-compatible canonical linear data into the previous
canonical linear-data interface. -/
public noncomputable def
    StandardHomocyclicFrattiniQuotientCoverCanonicalLinearReductionData.toStandardHomocyclicFrattiniQuotientCoverCanonicalLinearData
    {G V : Type u} [Group G] [Group V] [Finite V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ} {he : 1 ≤ e}
    (L : StandardHomocyclicFrattiniQuotientCoverCanonicalLinearReductionData
      (G := G) (V := V) (p := p) e he) :
    StandardHomocyclicFrattiniQuotientCoverCanonicalLinearData
      (G := G) (V := V) (p := p) e he := by
  classical
  refine {
    linearLift := L.linearLift
    quotientEquiv_linear := ?_ }
  intro g w
  rw [L.reduction_compat]
  exact standardHomocyclicCoverModPAction_quotientToV
    (G := G) (V := V) (p := p) g _

/-- Assemble canonical-index source data into the general coordinate-linear
standard source package. -/
public noncomputable def
    StandardHomocyclicFrattiniQuotientCoverCanonicalLinearData.toStandardHomocyclicFrattiniQuotientCoverLinearData
    {G V : Type u} [Group G] [Finite V] [Group V] [MulDistribMulAction G V]
    [Nontrivial V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ} {he : 1 ≤ e}
    (L : StandardHomocyclicFrattiniQuotientCoverCanonicalLinearData
      (G := G) (V := V) (p := p) e he) :
    StandardHomocyclicFrattiniQuotientCoverLinearData
      (G := G) (V := V) (p := p) e := by
  classical
  exact {
    matrixIndex := StandardHomocyclicCanonicalIndex (p := p) V
    instFintypeMatrixIndex := inferInstance
    instDecidableEqMatrixIndex := inferInstance
    instNonemptyMatrixIndex := standardHomocyclicCanonicalIndex_nonempty (p := p) V
    height_pos := he
    quotientToV := standardHomocyclicCoverToElementaryAbelianEquiv (p := p) V
    linearLift := L.linearLift
    quotientEquiv_linear := L.quotientEquiv_linear
    card_matrixIndex := standardHomocyclicCanonicalIndex_card (p := p) V }

/-- Assemble coordinate-linear standard source data into the action-only
standard cover package. -/
public noncomputable def
    StandardHomocyclicFrattiniQuotientCoverLinearData.toStandardHomocyclicFrattiniQuotientCoverActionData
    {G V : Type u} [Group G] [Finite V] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (L : StandardHomocyclicFrattiniQuotientCoverLinearData
      (G := G) (V := V) (p := p) e) :
    StandardHomocyclicFrattiniQuotientCoverActionData
      (G := G) (V := V) (p := p) e := by
  classical
  letI : Fintype L.matrixIndex := L.instFintypeMatrixIndex
  letI : DecidableEq L.matrixIndex := L.instDecidableEqMatrixIndex
  letI : Nonempty L.matrixIndex := L.instNonemptyMatrixIndex
  let coverAction : G →* MulAut (StandardHomocyclicCover L.matrixIndex (p ^ e)) := {
    toFun := fun g =>
      AddEquiv.toMultiplicative
        ((LinearMap.GeneralLinearGroup.toLinearEquiv (L.linearLift g)).toAddEquiv)
    map_one' := by
      ext w i
      simp
    map_mul' := by
      intro g h
      ext w i
      simp [LinearMap.GeneralLinearGroup.toLinearEquiv_mul] }
  exact {
    matrixIndex := L.matrixIndex
    instFintypeMatrixIndex := L.instFintypeMatrixIndex
    instDecidableEqMatrixIndex := L.instDecidableEqMatrixIndex
    instNonemptyMatrixIndex := L.instNonemptyMatrixIndex
    height_pos := L.height_pos
    quotientToV := L.quotientToV
    coverAction := coverAction
    quotientEquiv_action := by
      intro g w
      dsimp [coverAction]
      exact L.quotientEquiv_linear g w
    card_matrixIndex := L.card_matrixIndex }

/-- Assemble action-only standard source data into the older standard
quotient-cover package. -/
public noncomputable def
    StandardHomocyclicFrattiniQuotientCoverActionData.toStandardHomocyclicFrattiniQuotientCoverData
    {G V : Type u} [Group G] [Finite V] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (D : StandardHomocyclicFrattiniQuotientCoverActionData
      (G := G) (V := V) (p := p) e) :
    StandardHomocyclicFrattiniQuotientCoverData
      (G := G) (V := V) (p := p) e := by
  classical
  letI : Fintype D.matrixIndex := D.instFintypeMatrixIndex
  letI : DecidableEq D.matrixIndex := D.instDecidableEqMatrixIndex
  letI : Nonempty D.matrixIndex := D.instNonemptyMatrixIndex
  exact {
    matrixIndex := D.matrixIndex
    instFintypeMatrixIndex := D.instFintypeMatrixIndex
    instDecidableEqMatrixIndex := D.instDecidableEqMatrixIndex
    instNonemptyMatrixIndex := D.instNonemptyMatrixIndex
    frattiniQuotientEquiv :=
      (standardHomocyclicCoverFrattiniQuotientEquiv D.matrixIndex p e D.height_pos).trans
        D.quotientToV
    coverAction := D.coverAction
    quotientEquiv_action := by
      intro g w
      dsimp [MulEquiv.trans]
      simpa only [standardHomocyclicCoverFrattiniQuotientEquiv_mk'] using
        D.quotientEquiv_action g w
    card_matrixIndex := D.card_matrixIndex }

/-- Assemble standard homocyclic quotient-cover source data into the cover
package used downstream. -/
public noncomputable def
    StandardHomocyclicFrattiniQuotientCoverData.toHomocyclicFrattiniQuotientCover
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    {e : ℕ}
    (D : StandardHomocyclicFrattiniQuotientCoverData
      (G := G) (V := V) (p := p) e) :
    HomocyclicFrattiniQuotientCover (G := G) (V := V) (p := p) e := by
  classical
  letI : Fintype D.matrixIndex := D.instFintypeMatrixIndex
  letI : DecidableEq D.matrixIndex := D.instDecidableEqMatrixIndex
  letI : Nonempty D.matrixIndex := D.instNonemptyMatrixIndex
  exact {
    cover := StandardHomocyclicCover D.matrixIndex (p ^ e)
    instGroupCover := inferInstance
    instFiniteCover := inferInstance
    instFintypeCover := inferInstance
    instDecidableEqCover := inferInstance
    cover_isPGroup := standardHomocyclicCover_isPGroup D.matrixIndex p e
    cover_commutative := standardHomocyclicCover_commutative D.matrixIndex (p ^ e)
    cover_exponent := standardHomocyclicCover_exponent D.matrixIndex (p ^ e)
    matrixIndex := D.matrixIndex
    instFintypeMatrixIndex := D.instFintypeMatrixIndex
    instDecidableEqMatrixIndex := D.instDecidableEqMatrixIndex
    coordinateEquiv := standardHomocyclicCoverCoordinateEquiv D.matrixIndex (p ^ e)
    frattiniQuotientEquiv := D.frattiniQuotientEquiv
    coverAction := D.coverAction
    quotientEquiv_action := D.quotientEquiv_action
    card_matrixIndex := D.card_matrixIndex }


end Wielandt
