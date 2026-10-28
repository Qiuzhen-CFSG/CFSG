module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.Frattini
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.Residual
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.ResidualAlternatives.Duality
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Mathlib.Algebra.Module.ZMod

/-!
# Fixed-or-moving alternatives for the actual three-layer residual

Conjugation on the genuine quotient Q/Z(Q) is transported through its marked
identification with two dual natural modules. The displacement [Y_C,L] ≤ Q
makes this action commute with the marked L-action. The dual multiplicity
calculation gives either trivial action or full quotient displacement.

In the trivial case, fixation of Z(Q) makes inverse displacement at each
q ∈ Q a homomorphism Y_C → Z(Q); two-perfectness kills these maps. In the
moving case, [Q,Y_C]Z(Q) = Q and the established center–Frattini containment
lifts this to [Q,Y_C] = Q. No odd-order hypothesis on Y_C is used.

The final theorem retains both layers under their common marking, and assumes
only the center fixation supplied by `ThreeLayer.YC_fixes_center` in the
parent argument. It discharges the fixed-or-moving premise of
`ThreeLayer.YC_fixes_core_of_action_alternatives` without importing that umbrella.

Source: Aschbacher–Smith, C.1.34(3), printed pp.136–137, and the three-layer
paragraph of 15.3.23, printed p.1129 (1 March 2004 manuscript).
-/

public section

open Subgroup Representation
open scoped commutatorElement
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.ResidualAlternatives
variable {G : Type*} [Group G]
local notation "SL" => Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
local notation "D" => Fin 2 → Module.Dual (ZMod 2) (Fin 3 → ZMod 2)

variable {L : Subgroup G} {e : (L ⧸ pCore 2 L) ≃* SL}
variable (n : LayerModel L (commutatorCore L) (coreCenter L) e (DualCopies (ZMod 2) 2))

/-- The genuine quotient map followed by the supplied dual-layer marking. -/
noncomputable def coordinates : commutatorCore L →* Multiplicative D :=
  let _ := n.lower_normal
  n.quotientIso.toMonoidHom.comp (QuotientGroup.mk' _)

/-- Every vector represents an element of the actual commutator core. -/
theorem coordinates_surjective : Function.Surjective (coordinates n) :=
  let _ := n.lower_normal
  n.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The coordinate kernel is precisely the actual center. -/
theorem coordinates_eq_one (q : commutatorCore L) :
    coordinates n q = 1 ↔ (q : G) ∈ coreCenter L := by
  let _ := n.lower_normal
  change n.quotientIso (QuotientGroup.mk' _ q) = 1 ↔ _
  rw [← n.quotientIso.map_one, n.quotientIso.injective.eq_iff]
  exact QuotientGroup.eq_one_iff q

private theorem normalizer_center : normalizer (commutatorCore L : Set G) ≤
    normalizer (coreCenter L : Set G) :=
  normalizer_le_normalizer_characteristic_image _ (center (commutatorCore L))

/-- The normalizer acts on the genuine central quotient by ambient conjugation. -/
noncomputable def quotientConjugation :
    let _ := n.lower_normal
    normalizer (commutatorCore L : Set G) →*
      MulAut (commutatorCore L ⧸ (coreCenter L).subgroupOf (commutatorCore L)) :=
  Classical.choose (exists_quotient_conjugation_action _ _ _ le_rfl
    normalizer_center n.lower_normal)

/-- Conjugation on the central quotient, transported to the marked dual copies. -/
noncomputable def quotientAut :
    normalizer (commutatorCore L : Set G) →* MulAut (Multiplicative D) :=
  let _ := n.lower_normal
  (MulAut.congr n.quotientIso).toMonoidHom.comp (quotientConjugation n)

/-- The transported automorphism agrees with conjugation on every representative. -/
theorem quotientAut_apply (x : normalizer (commutatorCore L : Set G))
    (q : commutatorCore L) :
    quotientAut n x (coordinates n q) =
      coordinates n (layerConjugate _ _ le_rfl x q) := by
  let _ := n.lower_normal
  change n.quotientIso (quotientConjugation n x
    (n.quotientIso.symm (n.quotientIso (QuotientGroup.mk' _ q)))) = _
  rw [n.quotientIso.symm_apply_apply]
  exact congrArg n.quotientIso
    (Classical.choose_spec (exists_quotient_conjugation_action _ _ _ le_rfl
      normalizer_center n.lower_normal) x q)

private theorem quotientAut_core (x : normalizer (commutatorCore L : Set G))
    (hx : (x : G) ∈ commutatorCore L) : quotientAut n x = 1 := by
  apply MulEquiv.ext
  intro v
  obtain ⟨q, rfl⟩ := coordinates_surjective n v
  rw [quotientAut_apply]
  let xQ : commutatorCore L := ⟨x, hx⟩
  change coordinates n (xQ * q * xQ⁻¹) = coordinates n q
  simp only [map_mul, map_inv, mul_comm, mul_inv_cancel_right]

/-- Displacement in Q makes the two automorphisms commute on Q/Z(Q). -/
theorem quotientAut_commute (x y : normalizer (commutatorCore L : Set G))
    (hxy : ⁅(x : G), (y : G)⁆ ∈ commutatorCore L) :
    Commute (quotientAut n x) (quotientAut n y) := by
  apply commutatorElement_eq_one_iff_commute.mp
  rw [← map_commutatorElement]
  exact quotientAut_core n ⁅x,y⁆ hxy

variable {d : LocalData G} {I : Subgroup G} (c : ComponentWitness d I)
variable {e : (c.L ⧸ pCore 2 c.L) ≃* SL}
variable (n : LayerModel c.L (commutatorCore c.L) (coreCenter c.L) e (DualCopies (ZMod 2) 2))

/-- The actual section residual normalizes the commutator core. -/
theorem residual_normalizes : YC d c.L ≤ normalizer (commutatorCore c.L : Set G) :=
  (YC_section_action d c.L).1.trans (normalizer_le_normalizer_commutatorCore c.L)

/-- The binary linear action of the actual residual on the marked quotient. -/
noncomputable def residualAction : Representation (ZMod 2) (YC d c.L) D where
  toFun y := (AddMonoidHom.toMultiplicative.symm
    (quotientAut n (inclusion (residual_normalizes c) y)).toMonoidHom).toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change quotientAut n (inclusion (residual_normalizes c) 1) (Multiplicative.ofAdd v) = _
    rw [map_one, map_one]
    rfl
  map_mul' y z := by
    apply LinearMap.ext
    intro v
    change quotientAut n (inclusion (residual_normalizes c) (y*z)) (Multiplicative.ofAdd v) = _
    rw [map_mul, map_mul]
    rfl

/-- The linear action is the genuine quotient conjugation action. -/
theorem residualAction_apply (y : YC d c.L) (q : commutatorCore c.L) :
    residualAction c n y (coordinates n q).toAdd =
      (coordinates n (layerConjugate _ _ (residual_normalizes c) y q)).toAdd := by
  exact congrArg Multiplicative.toAdd (quotientAut_apply n (inclusion (residual_normalizes c) y) q)

/-- The residual action commutes with the full SL₃(2) action under the given marking. -/
theorem residualAction_commutes (y : YC d c.L) (g : SL) (v : D) :
    residualAction c n y (DualCopies (ZMod 2) 2 g v) =
      DualCopies (ZMod 2) 2 g (residualAction c n y v) := by
  obtain ⟨l, hl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 c.L))) g
  change e (QuotientGroup.mk' (pCore 2 c.L) l) = g at hl
  let ny : normalizer (commutatorCore c.L : Set G) := inclusion (residual_normalizes c) y
  let nl : normalizer (commutatorCore c.L : Set G) := ⟨l, n.normalized l.property⟩
  have hh := quotientAut_commute n ny nl
    (YC_commutator_le d c (commutator_mem_commutator y.property l.property))
  have ht (w : D) : quotientAut n nl (Multiplicative.ofAdd w) =
      Multiplicative.ofAdd (DualCopies (ZMod 2) 2 g w) := by
    obtain ⟨q, hq⟩ := coordinates_surjective n (Multiplicative.ofAdd w)
    have hq' : (coordinates n q).toAdd = w := congrArg Multiplicative.toAdd hq
    calc
      _ = coordinates n (layerConjugate _ _ le_rfl nl q) := by
        rw [← hq]
        exact quotientAut_apply n nl q
      _ = _ := by
        have hi := n.intertwining l q
        change (coordinates n (layerConjugate _ _ n.normalized l q)).toAdd =
          DualCopies (ZMod 2) 2 (e (QuotientGroup.mk' _ l)) (coordinates n q).toAdd at hi
        rw [hl, hq'] at hi
        exact congrArg Multiplicative.ofAdd hi
  have h := congrArg (fun f : MulAut (Multiplicative D) => f (Multiplicative.ofAdd v)) hh.eq
  change quotientAut n ny (quotientAut n nl (Multiplicative.ofAdd v)) =
    quotientAut n nl (quotientAut n ny (Multiplicative.ofAdd v)) at h
  rw [ht v] at h
  change quotientAut n ny (Multiplicative.ofAdd (DualCopies (ZMod 2) 2 g v)) =
    quotientAut n nl (Multiplicative.ofAdd (residualAction c n y v)) at h
  rw [ht] at h
  exact congrArg Multiplicative.toAdd h

/-- Trivial marked quotient action puts the actual displacement in the center. -/
theorem displacement_le_center_of_trivial
    (htriv : ∀ y, residualAction c n y = 1) :
    ⁅YC d c.L, commutatorCore c.L⁆ ≤ coreCenter c.L := by
  apply commutator_le.mpr
  intro y hy q hq
  let yY : YC d c.L := ⟨y, hy⟩
  let qQ : commutatorCore c.L := ⟨q, hq⟩
  let q' := layerConjugate _ _ (residual_normalizes c) yY qQ
  have he := LinearMap.congr_fun (htriv yY) (coordinates n qQ).toAdd
  rw [residualAction_apply] at he
  have he' : coordinates n q' = coordinates n qQ := congrArg Multiplicative.ofAdd he
  have hk : coordinates n (q' * qQ⁻¹) = 1 := by
    rw [map_mul, map_inv, he', mul_inv_cancel]
  exact (coordinates_eq_one n (q' * qQ⁻¹)).mp hk

/-- Fixing the center and its quotient fixes Q: the inverse displacement maps
into the two-group Z(Q) are homomorphisms killed by two-perfectness. -/
theorem core_fixed_of_displacement_le_center [Finite G]
    (hfix : YC d c.L ≤ centralizer (coreCenter c.L : Set G))
    (hcomm : ⁅YC d c.L, commutatorCore c.L⁆ ≤ coreCenter c.L) :
    YC d c.L ≤ centralizer (commutatorCore c.L : Set G) := by
  have hZ : IsPGroup 2 (coreCenter c.L) :=
    ((c.L.isPGroup_pCoreIn 2).to_le (commutatorCore_le c.L)).to_le (map_subtype_le _)
  have hp := ComponentIntersection.centralizerResidual_isPPerfect d.Yplus c.L
  intro y hy q hq
  let f : YC d c.L →* coreCenter c.L :=
    { toFun x := ⟨⁅(x : G), q⁆⁻¹,
        (coreCenter c.L).inv_mem (hcomm (commutator_mem_commutator x.property hq))⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' x z := by
        apply Subtype.ext
        change ⁅(x : G) * (z : G), q⁆⁻¹ = ⁅(x : G), q⁆⁻¹ * ⁅(z : G), q⁆⁻¹
        have hc := hfix x.property _ (hcomm (commutator_mem_commutator z.property hq))
        rw [commutatorElement_mul_left_eq_conj_mul, ← hc, mul_inv_cancel_right, mul_inv_rev] }
  have hf := hp.hom_eq_one_of_isPGroup hZ f
  have he := congrArg (fun k : YC d c.L →* coreCenter c.L => (k ⟨y, hy⟩ : G)) hf
  change ⁅y, q⁆⁻¹ = 1 at he
  exact (commutatorElement_eq_one_iff_mul_comm.mp (inv_eq_one.mp he)).symm

/-- Full linear displacement gives generation of Q modulo its actual center. -/
theorem sup_center_of_moving
    (hfull : Coinvariants.ker (residualAction c n) = ⊤) :
    ⁅commutatorCore c.L, YC d c.L⁆ ⊔ coreCenter c.L = commutatorCore c.L := by
  let Q := commutatorCore c.L
  let H := ⁅YC d c.L, Q⁆
  have hH : H ≤ Q := le_normalizer_iff_commutator_le_right.mp (residual_normalizes c)
  let U : Submodule (ZMod 2) D := AddSubgroup.toZModSubmodule 2
    ((H.subgroupOf Q).map (coordinates n)).toAddSubgroup
  have hU : Coinvariants.ker (residualAction c n) ≤ U := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨y, v⟩, rfl⟩
    obtain ⟨q, hq⟩ := coordinates_surjective n (Multiplicative.ofAdd v)
    have hq' : (coordinates n q).toAdd = v := congrArg Multiplicative.toAdd hq
    let q' : Q := layerConjugate _ _ (residual_normalizes c) y q * q⁻¹
    refine ⟨q', ?_, ?_⟩
    · exact commutator_mem_commutator y.property q.property
    · change coordinates n (layerConjugate _ _ (residual_normalizes c) y q * q⁻¹) =
        Multiplicative.ofAdd (residualAction c n y v - v)
      rw [map_mul, map_inv]
      have ha := residualAction_apply c n y q
      rw [hq'] at ha
      have ha' : Multiplicative.ofAdd (residualAction c n y v) =
          coordinates n (layerConjugate _ _ (residual_normalizes c) y q) :=
        congrArg Multiplicative.ofAdd ha
      rw [← ha', hq]
      change residualAction c n y v + -v = residualAction c n y v - v
      rw [sub_eq_add_neg]
  have htop : U = ⊤ := top_unique (hfull ▸ hU)
  rw [commutator_comm]
  apply le_antisymm (sup_le hH (map_subtype_le _))
  intro q hq
  have hu : (coordinates n ⟨q, hq⟩).toAdd ∈ U := by rw [htop]; trivial
  obtain ⟨a, ha, he⟩ := hu
  change coordinates n a = coordinates n ⟨q, hq⟩ at he
  have hZ : (a⁻¹ * ⟨q, hq⟩ : Q).val ∈ coreCenter c.L := by
    apply (coordinates_eq_one n _).mp
    rw [map_mul, map_inv, he, inv_mul_cancel]
  have hm := (H ⊔ coreCenter c.L).mul_mem
    ((le_sup_left : H ≤ H ⊔ coreCenter c.L) ha)
    ((le_sup_right : coreCenter c.L ≤ H ⊔ coreCenter c.L) hZ)
  change (a : G) * ((a : G)⁻¹ * q) ∈ H ⊔ coreCenter c.L at hm
  rwa [mul_inv_cancel_left] at hm

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer.ResidualAlternatives

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer
variable {G : Type*} [Group G] [Finite G]

/-- Under the common C.1.34(3) marking, a center-fixing actual residual
centralizes Q or generates all of Q by displacement. This supplies the
alternative used by `YC_fixes_core_of_action_alternatives`. -/
theorem YC_fixed_or_moving (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I)
    {e : (c.L ⧸ pCore 2 c.L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)}
    (m : LayerModel c.L (coreCenter c.L) ⊥ e (NaturalCopies (ZMod 2) 1))
    (n : LayerModel c.L (commutatorCore c.L) (coreCenter c.L) e (DualCopies (ZMod 2) 2))
    (hfix : YC d c.L ≤ centralizer (coreCenter c.L : Set G)) :
    YC d c.L ≤ centralizer (commutatorCore c.L : Set G) ∨
      ⁅commutatorCore c.L, YC d c.L⁆ = commutatorCore c.L := by
  rcases ResidualAlternatives.dual_copies_fixed_or_moving
    (ResidualAlternatives.residualAction c n)
    (ComponentIntersection.centralizerResidual_isPPerfect d.Yplus c.L)
    (ResidualAlternatives.residualAction_commutes c n) with htriv | hfull
  · exact Or.inl (ResidualAlternatives.core_fixed_of_displacement_le_center c hfix
      (ResidualAlternatives.displacement_le_center_of_trivial c n htriv))
  · refine Or.inr (eq_core_of_sup_center c.L _ m n ?_
      (ResidualAlternatives.sup_center_of_moving c n hfull))
    exact le_normalizer_iff_commutator_le_left.mp (ResidualAlternatives.residual_normalizes c)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearThree.CoreActions.ThreeLayer
end
