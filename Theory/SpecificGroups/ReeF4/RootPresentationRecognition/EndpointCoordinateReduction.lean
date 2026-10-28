module
public import Theory.SpecificGroups.ReeF4.RootPresentationRecognition.AngularPresentation


/-!
# Extracting endpoint coefficients from native ordered words

Canceling the common first root reduces the comparison to six interior roots.
Uniqueness of their ordered coordinates then fixes the two linear/main labels
and the remaining relation between the central labels. The comparison is
factored through a concrete six-coordinate product before field coordinates
are substituted.

Source: Fong--Seitz II (1974), Section 10, (10.27)--(10.41), interpreted in
the literal native triangular Suzuki charts.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup ReeF4
namespace ReeF4.RootPresentationRecognition.EndpointCoordinateReduction
open CentralCovers.TwoPrimary Theory.GroupTheory.OrderedRootPresentation
variable (m : ℕ)
local notation "L" i:max a:max => (PositiveTables.pair m i a : Model m)
local notation "S" i:max a:max b:max => (PositiveTables.quartet m i a b : Model m)

private theorem pair_coe (i : Fin 4) (a : CoefficientField m) :
    (PositiveTables.rootChartEquiv m (.inl i) a : Model m) = L i a := rfl
private theorem quartet_coe (i : Fin 4) (a b : CoefficientField m) :
    (PositiveTables.rootChartEquiv m (.inr i) (a,b) : Model m) = S i a b := rfl

private abbrev Coordinates :=
  AngularPresentation.Parameter m (.inl 1) × AngularPresentation.Parameter m (.inr 3) ×
  AngularPresentation.Parameter m (.inl 3) × AngularPresentation.Parameter m (.inr 1) ×
  AngularPresentation.Parameter m (.inl 2) × AngularPresentation.Parameter m (.inr 2)

private def product (p : Coordinates m) : Model m :=
  (p.1 : Model m) * p.2.1 * p.2.2.1 * p.2.2.2.1 * p.2.2.2.2.1 * p.2.2.2.2.2

private theorem product_injective : Function.Injective (product m) := by
  intro p q he
  let a : Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inr 0)) :=
    (p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2,1,PUnit.unit)
  let b : Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inr 0)) :=
    (q.1,q.2.1,q.2.2.1,q.2.2.2.1,q.2.2.2.2.1,q.2.2.2.2.2,1,PUnit.unit)
  have hw : word (AngularPresentation.Parameter m) (fun i => AngularPresentation.nativeRoot m i)
      (tail sourceOrder (.inr 0)) a =
    word (AngularPresentation.Parameter m) (fun i => AngularPresentation.nativeRoot m i)
      (tail sourceOrder (.inr 0)) b := by
    change (p.1 : Model m) * (p.2.1 * (p.2.2.1 * (p.2.2.2.1 *
      (p.2.2.2.2.1 * (p.2.2.2.2.2 * (1*1)))))) =
      (q.1 : Model m) * (q.2.1 * (q.2.2.1 * (q.2.2.2.1 *
      (q.2.2.2.2.1 * (q.2.2.2.2.2 * (1*1))))))
    simpa only [product,mul_one,mul_assoc] using he
  have hab : a = b := AngularPresentation.native_tail_injective m (.inr 0) hw
  exact congrArg (fun z : Tuple (AngularPresentation.Parameter m) (tail sourceOrder (.inr 0)) =>
    (z.1,z.2.1,z.2.2.1,z.2.2.2.1,z.2.2.2.2.1,z.2.2.2.2.2.1)) hab

theorem collected_endpoint_coefficients (s e t v w : CoefficientField m)
    (hc : S 0 1 0 * L 1 1 * S 3 1 (w+1) * L 3 v *
      S 1 e (t+titsEnd m e*e) * L 2 s * S 2 1 0 =
      S 0 1 0 * L 1 (s+e) * S 3 (e+1) (titsEnd m s+titsEnd m e*e+titsEnd m e+e+t+v) *
      L 3 (s+e+v+1) * S 1 0 (s+v+w+1) * L 2 1 * S 2 1 0) :
    s = 1 ∧ e = 0 ∧ t = v+w := by
  let p : Coordinates m :=
    (PositiveTables.rootChartEquiv m (.inl 1) 1,
      PositiveTables.rootChartEquiv m (.inr 3) (1,w+1),
      PositiveTables.rootChartEquiv m (.inl 3) v,
      PositiveTables.rootChartEquiv m (.inr 1) (e,t+titsEnd m e*e),
      PositiveTables.rootChartEquiv m (.inl 2) s,
      PositiveTables.rootChartEquiv m (.inr 2) (1,0))
  let q : Coordinates m :=
    (PositiveTables.rootChartEquiv m (.inl 1) (s+e),
      PositiveTables.rootChartEquiv m (.inr 3)
        (e+1,titsEnd m s+titsEnd m e*e+titsEnd m e+e+t+v),
      PositiveTables.rootChartEquiv m (.inl 3) (s+e+v+1),
      PositiveTables.rootChartEquiv m (.inr 1) (0,s+v+w+1),
      PositiveTables.rootChartEquiv m (.inl 2) 1,
      PositiveTables.rootChartEquiv m (.inr 2) (1,0))
  have hpq : p = q := by
    apply product_injective m
    apply mul_left_cancel (a := S 0 1 0)
    dsimp only [p,q,product]
    simpa only [pair_coe m 1 1,quartet_coe m 3 1 (w+1),pair_coe m 3 v,
      quartet_coe m 1 e (t+titsEnd m e*e),pair_coe m 2 s,quartet_coe m 2 1 0,
      pair_coe m 1 (s+e),
      quartet_coe m 3 (e+1) (titsEnd m s+titsEnd m e*e+titsEnd m e+e+t+v),
      pair_coe m 3 (s+e+v+1),quartet_coe m 1 0 (s+v+w+1),pair_coe m 2 1,
      mul_assoc] using hc
  have hs : s=1 := (PositiveTables.rootChartEquiv m (.inl 2)).injective
    (congrArg (fun z : Coordinates m => z.2.2.2.2.1) hpq)
  have he : e=0 := congrArg Prod.fst ((PositiveTables.rootChartEquiv m (.inr 1)).injective
    (congrArg (fun z : Coordinates m => z.2.2.2.1) hpq))
  have hz := congrArg Prod.snd ((PositiveTables.rootChartEquiv m (.inr 3)).injective
    (congrArg (fun z : Coordinates m => z.2.1) hpq))
  refine ⟨hs,he,?_⟩
  change w+1 = titsEnd m s+titsEnd m e*e+titsEnd m e+e+t+v at hz
  rw [hs,he] at hz
  simp only [map_one,map_zero,mul_zero,add_zero] at hz
  have hw : w = t+v := add_right_cancel (show w+1 = (t+v)+1 by
    simpa only [add_assoc,add_comm,add_left_comm] using hz)
  calc t = t+(v+v) := by rw [CharTwo.add_self_eq_zero,add_zero]
       _ = v+(t+v) := add_left_comm t v v
       _ = v+w := by rw [hw]

end ReeF4.RootPresentationRecognition.EndpointCoordinateReduction
