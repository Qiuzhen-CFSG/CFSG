module
public import Glauberman.PushingUpSL2DegreeCovering
public import Glauberman.FixedNormalPairDegreeCovering

/-!
# Full original-degree Niles intersection lattice

The original SL₂ quotient supplies both full center covering and center
index q. The shifted-center commutator estimate then forces index q at
depth 3v. Monotonicity of the rectangle indices reconstructs every
intervening adjacent join. The conjugator remains in the original
residual, and all centers are literal full centers.

Source: Niles, *Pushing-up in finite groups* (1979), Proposition 4.6,
printed pp.46--47. Elementwise covering and the nonabelian structure
argument in Sections 5--6 are subsequent steps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.SubgroupTransport
namespace Glauberman
variable {G : Type*} [Group G] [Finite G]

@[expose] def NilesFullIntersectionDiagram (q : ℕ) (S : Subgroup G) (α : MulAut S) : Prop :=
  ∃ x : G, x ∈ pResidual 2 G ∧
  let T := S.map (MulAut.conj x).toMonoidHom
  let φ := twistedConjugacy S α x
  S ⊔ T = ⊤ ∧ S ⊓ T = pCore 2 G ∧ NumericalPairAt q S T φ ∧
  ∃ v : ℕ, 0 < v ∧
    IsElementaryAbelian 2 (intervalCell φ 1 v) ∧
    intervalCell φ 1 v ∈ thompsonAbelianSubgroups S ∧
    intervalCell φ 1 v ∈ thompsonAbelianSubgroups T ∧
    (∀ i j : ℕ, 1 ≤ i+j → i+j < 3*v →
      intervalCell φ i (j+1) ⊔ intervalCell φ (i+1) j = intervalCell φ i j) ∧
    centerIn S = intervalCell φ v (v+1) ∧
    centerIn T = intervalCell φ (v+1) v ∧
    centerIn (pCore 2 G) = intervalCell φ v v ∧
    center G = intervalCell φ (v+1) (v+1) ∧
    ⁅intervalCell φ 0 (2*v),intervalCell φ v v⁆ ≤ intervalCell φ v (2*v)

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem original_sl2_full_intersection_lattice
    (e : (G ⧸ pCore 2 G) ≃* Matrix.SpecialLinearGroup (Fin 2) F) {n : ℕ}
    (hn : 1 < n) (hF : Nat.card F = 2^n)
    (S : Sylow 2 G) (α : MulAut S)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : NoInvariantNormal (S : Subgroup G) α) :
    NilesFullIntersectionDiagram (Nat.card F) (S : Subgroup G) α ∧
    ⁅centerIn (pCore 2 G),(S : Subgroup G)⁆ ⊔ center G = centerIn (S : Subgroup G) ∧
    (center G).relIndex (centerIn (pCore 2 G)) = Nat.card F ^ 2 ∧
    (center G).relIndex (centerIn (S : Subgroup G)) = Nat.card F := by
  obtain ⟨x,hx,hgen,hinter,hnum⟩ := original_sl2_numerical_pair e hn hF S α hfit hno
  let P : IntersectionPair G :=
    ⟨S,(S : Subgroup G).map (MulAut.conj x).toMonoidHom,twistedConjugacy (S : Subgroup G) α x⟩
  obtain ⟨v,hv,hE,hAS,hAT,hj,hzS,hzT,hzQ⟩ := P.exists_double_lattice_center_cells_at hnum
  have hnormS := normalizes_centerIn (S := P.left ⊓ P.right) (A := P.left) hnum.normal_left
  have hnormT := normalizes_centerIn (S := P.left ⊓ P.right) (A := P.right) hnum.normal_right
  rw [hzQ] at hnormS hnormT
  have hcomm := intervalCell_center_commutator_bound P.equiv v hv hnormS hnormT
  have hzHle : center G ≤ P.left ⊓ P.right := by
    change _ ≤ (S : Subgroup G) ⊓ (S : Subgroup G).map (MulAut.conj x).toMonoidHom
    rw [hinter]
    have hQc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G := by
      rw [←hfit]
      exact centralizer_generalizedFitting_le G
    exact (center_le_centralizer _).trans hQc
  have hzH : center G = intervalCell P.equiv (v+1) (v+1) := by
    rw [center_eq_inf_centers_of_generating hgen hzHle,hzS,hzT,intervalCell_inf,
      max_eq_right (Nat.le_succ v),max_eq_left (Nat.le_succ v)]
  obtain ⟨hcover,hiQ,hiS⟩ := original_sl2_full_center_covering e hn hF S α hfit hno
  have hcover' : ⁅centerIn (P.left ⊓ P.right),P.left⁆ ⊔ center G = centerIn P.left := by
    change ⁅centerIn ((S : Subgroup G) ⊓
      (S : Subgroup G).map (MulAut.conj x).toMonoidHom),(S : Subgroup G)⁆ ⊔ center G = _
    rw [hinter]
    exact hcover
  have htriple := P.rectangleStepIndex_triple_eq_index (Nat.card F) v hv hnum.normal_left
    hj hzS hzQ hzH hcomm hcover' hiS
  have hfull : ∀ i j : ℕ, 1 ≤ i+j → i+j < 3*v →
      intervalCell P.equiv i (j+1) ⊔ intervalCell P.equiv (i+1) j = intervalCell P.equiv i j := by
    intro i j hij hb
    apply intervalCell_sup_of_stepIndex_lower P.equiv hij (show i+j+1 ≤ 3*v by omega)
    rw [P.rectangleStepIndex_eq_index 0 hnum,htriple]
  have hzcore : centerIn (pCore 2 G) = intervalCell P.equiv v v := by
    calc
      _ = centerIn (P.left ⊓ P.right) := congrArg centerIn hinter.symm
      _ = _ := hzQ
  exact ⟨⟨x,hx,hgen,hinter,hnum,v,hv,hE,hAS,hAT,hfull,hzS,hzT,hzcore,hzH,hcomm⟩,
    hcover,hiQ,hiS⟩
end Glauberman
