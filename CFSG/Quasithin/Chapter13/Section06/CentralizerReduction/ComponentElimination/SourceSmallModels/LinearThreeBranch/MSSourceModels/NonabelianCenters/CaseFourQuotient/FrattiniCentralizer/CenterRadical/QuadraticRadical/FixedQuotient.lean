module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical.QuadraticRadical.Extension

/-!
# Killing the fixed component of squares

Squares modulo the moved center form an additive invariant map on the literal
doubled-dual quotient. The dual has no trivial quotient, so this map vanishes.
This is the projection to the fixed summand in C.1.34(4)'s Z = C ⊕ U.
-/

@[expose] public section
open Subgroup Matrix
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical.QuadraticRadical
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Linear
open BinaryLinearThree.AutomorphismAction
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

private theorem invariant_additive_zero {E : Type*} [AddCommGroup E]
    (f : W →+ E) (hf : ∀ g v, f (dual g v) = f v) : ∀ v, f v = 0 := by
  let a : W := Pi.single 0 1
  let b : W := Pi.single 1 1
  have ha : a ≠ 0 := by decide
  have hb : b ≠ 0 := by decide
  have hab : a+b ≠ 0 := by decide
  have same {v w : W} (hv : v ≠ 0) (hw : w ≠ 0) : f w = f v := by
    obtain ⟨g, hg⟩ := dual_orbit hv hw
    rw [← hg, hf]
  have hz : f a = 0 := by
    have hh := same ha hab
    rw [map_add, same ha hb] at hh
    exact add_eq_left.mp hh
  intro v
  by_cases hv : v = 0
  · simp [hv]
  · exact (same ha hv).trans hz

/-- The doubled dual has no invariant additive map to a trivial module. -/
theorem invariant_doubled_additive_zero {E : Type*} [AddCommGroup E]
    (f : (W × W) →+ E)
    (hf : ∀ g v, f (dual g v.1, dual g v.2) = f v) : ∀ v, f v = 0 := by
  have hl : ∀ v, f (v,0) = 0 := invariant_additive_zero
    (f.comp (AddMonoidHom.inl W W)) (by
      intro g v
      simpa only [AddMonoidHom.comp_apply, AddMonoidHom.inl_apply,
        dual, Matrix.mulVec_zero] using hf g (v,0))
  have hr : ∀ v, f (0,v) = 0 := invariant_additive_zero
    (f.comp (AddMonoidHom.inr W W)) (by
      intro g v
      simpa only [AddMonoidHom.comp_apply, AddMonoidHom.inr_apply,
        dual, Matrix.mulVec_zero] using hf g (0,v))
  intro v
  have hv : v = (v.1,0) + (0,v.2) := by ext <;> simp
  rw [hv, map_add, hl, hr, add_zero]

private noncomputable def dualCoordinates : Module.Dual (ZMod 2) BinaryLinearThree.Vector ≃+ W :=
  graphNaturalDual.toLinearEquiv.toAddEquiv.symm

private theorem dualCoordinates_action (g : S)
    (v : Module.Dual (ZMod 2) BinaryLinearThree.Vector) :
    dualCoordinates (BinaryLinearThree.W.dual g v) = dual g (dualCoordinates v) := by
  apply graphNaturalDual.toLinearEquiv.toAddEquiv.injective
  change graphNaturalDual.toLinearEquiv.toAddEquiv
      (graphNaturalDual.toLinearEquiv.toAddEquiv.symm (BinaryLinearThree.W.dual g v)) = _
  rw [AddEquiv.apply_symm_apply]
  have hh := LinearMap.congr_fun (graphNaturalDual.isIntertwining' g)
    (dualCoordinates v)
  change graphNaturalDual.toLinearEquiv.toAddEquiv (dual g (dualCoordinates v)) =
    BinaryLinearThree.W.dual g (graphNaturalDual.toLinearEquiv.toAddEquiv (dualCoordinates v)) at hh
  rw [show graphNaturalDual.toLinearEquiv.toAddEquiv (dualCoordinates v) = v from
    graphNaturalDual.toLinearEquiv.toAddEquiv.apply_symm_apply v] at hh
  exact hh.symm

variable {G : Type*} [_root_.Group G] {K D P : Subgroup G}

/-- The literal section model in inverse-transpose coordinates, with unchanged actor. -/
theorem section_coordinates
    (actor : K →* S)
    (h : HasSectionModel K D P actor
      (BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual)) :
    ∃ q : D →* Multiplicative (W × W),
      Function.Surjective q ∧ q.ker = P.subgroupOf D ∧
      ∀ (k : K) (x y : D), (y : G) = k * (x : G) * (k : G)⁻¹ →
        (q y).toAdd = (dual (actor k) (q x).toAdd.1, dual (actor k) (q x).toAdd.2) := by
  obtain ⟨_, _, _, hn, f, hf⟩ := h
  let := hn
  let c := (dualCoordinates.prodCongr dualCoordinates).toMultiplicative
  let q := c.toMonoidHom.comp (f.toMonoidHom.comp (QuotientGroup.mk' (P.subgroupOf D)))
  refine ⟨q, c.surjective.comp (f.surjective.comp (QuotientGroup.mk'_surjective _)), ?_, ?_⟩
  · ext x
    change c (f (QuotientGroup.mk' _ x)) = 1 ↔ _
    rw [map_eq_one_iff c c.injective, map_eq_one_iff f f.injective]
    exact QuotientGroup.eq_one_iff x
  · intro k x y hy
    have hh := hf k x y hy
    change (dualCoordinates (f (QuotientGroup.mk' _ y)).toAdd.1,
      dualCoordinates (f (QuotientGroup.mk' _ y)).toAdd.2) = _
    rw [hh]
    exact Prod.ext (dualCoordinates_action _ _) (dualCoordinates_action _ _)

private theorem square_mul (x y : G) (hx : Commute (x^2) y⁻¹)
    (hc : Commute ⁅x,y⁆ (x^2*y^2)) : (x*y)^2 = x^2*y^2*⁅x,y⁆ := by
  symm
  calc
    x^2*y^2*⁅x,y⁆ = ⁅x,y⁆*(x^2*y^2) := hc.eq.symm
    _ = x*y*x⁻¹*(y⁻¹*x^2)*y^2 := by simp only [commutatorElement_def, mul_assoc]
    _ = x*y*x⁻¹*(x^2*y⁻¹)*y^2 := by rw [hx.eq]
    _ = (x*y)^2 := by simp only [pow_two]; group

/-- Squares modulo U vanish on the actual doubled-dual section.
The target Z/U is the fixed component of Z = C ⊕ U. -/
theorem squares_mem_moved {Z U : Subgroup G}
    (actor : K →* S) (hactor : Function.Surjective actor)
    (q : D →* Multiplicative (W × W)) (hq : Function.Surjective q)
    (hker : q.ker = P.subgroupOf D)
    (hact : ∀ (k : K) (x y : D), (y : G) = k * (x : G) * (k : G)⁻¹ →
      (q y).toAdd = (dual (actor k) (q x).toAdd.1, dual (actor k) (q x).toAdd.2))
    (hnD : K ≤ normalizer D) (hZ : Z ≤ centralizer (D : Set G))
    (hZZ : IsMulCommutative Z) (hUZ : U ≤ Z)
    (hmoved : ⁅Z,K⁆ ≤ U) (hcomm : ⁅D,D⁆ ≤ U)
    (hP : IsElementaryAbelian 2 P) (hsq : ∀ x ∈ D, x^2 ∈ Z) :
    ∀ x ∈ D, x^2 ∈ U := by
  let := hZZ
  let : CommGroup Z := IsMulCommutative.instCommGroup
  let π := QuotientGroup.mk' (U.subgroupOf Z)
  let s : D →* (Z ⧸ U.subgroupOf Z) := {
    toFun x := π ⟨(x:G)^2, hsq x x.property⟩
    map_one' := by
      have he : (⟨(1:G)^2, hsq 1 D.one_mem⟩ : Z) = 1 := Subtype.ext (one_pow 2)
      exact (congrArg π he).trans π.map_one
    map_mul' x y := by
      have hc : ⁅(x:G),(y:G)⁆ ∈ U := hcomm (commutator_mem_commutator x.property y.property)
      have he : (⟨((x:G)*y)^2, hsq (x*y) (x*y).property⟩ : Z) =
          ⟨(x:G)^2, hsq x x.property⟩ * ⟨(y:G)^2, hsq y y.property⟩ * ⟨⁅(x:G),(y:G)⁆, hUZ hc⟩ := by
        apply Subtype.ext
        exact square_mul (x:G) (y:G) (hZ (hsq x x.property) y⁻¹ (D.inv_mem y.property)).symm
          (hZ (hUZ hc) _ (D.mul_mem (D.pow_mem x.property 2) (D.pow_mem y.property 2))).symm
      change π (⟨((x:G)*y)^2, hsq (x*y) (x*y).property⟩ : Z) =
        π ⟨(x:G)^2, hsq x x.property⟩ * π ⟨(y:G)^2, hsq y y.property⟩
      have hcπ : π ⟨⁅(x:G),(y:G)⁆, hUZ hc⟩ = 1 :=
        (QuotientGroup.eq_one_iff (N := U.subgroupOf Z) _).mpr hc
      rw [he, map_mul, map_mul, hcπ, mul_one] }
  have hPs : q.ker ≤ s.ker := by
    intro x hx
    have hxP : (x:G) ∈ P := by
      change x ∈ P.subgroupOf D
      rwa [← hker]
    let := hP
    have hx2 := elemPow_eq_one_of_isElementaryAbelian (p:=2) (x:G) hxP
    change π ⟨(x:G)^2, _⟩ = 1
    have hh : (⟨(x:G)^2, hsq x x.property⟩ : Z) = 1 := Subtype.ext hx2
    rw [hh, map_one]
  let t : Multiplicative (W × W) →* (Z ⧸ U.subgroupOf Z) :=
    q.liftOfSurjective hq ⟨s,hPs⟩
  have ht : ∀ x, t (q x) = s x := by
    intro x
    exact q.liftOfRightInverse_comp_apply _ _ _ x
  have hsact (k : K) (x y : D) (hy : (y:G) = k*(x:G)*(k:G)⁻¹) : s y = s x := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (y:G)^2 / (x:G)^2 ∈ U
    rw [hy, conj_pow, div_eq_mul_inv, ← commutatorElement_def]
    apply hmoved
    rw [commutator_comm Z K]
    exact commutator_mem_commutator k.property (hsq x x.property)
  have hz : ∀ v, t (Multiplicative.ofAdd v) = 1 := by
    exact invariant_doubled_additive_zero t.toAdditive (by
      intro g v
      obtain ⟨k,rfl⟩ := hactor g
      obtain ⟨x,hx⟩ := hq (Multiplicative.ofAdd v)
      have hv : (q x).toAdd = v := congrArg Multiplicative.toAdd hx
      let y := D.normalizerMonoidHom ⟨k,hnD k.property⟩ x
      rw [← hv, ← hact k x y rfl]
      change t (q y) = t (q x)
      rw [ht, ht]
      exact hsact k x y rfl)
  intro x hx
  have hh := hz (q ⟨x,hx⟩).toAdd
  change t (q ⟨x,hx⟩) = 1 at hh
  rw [ht] at hh
  exact (QuotientGroup.eq_one_iff (N := U.subgroupOf Z) ⟨x^2,hsq x hx⟩).mp hh

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch.MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.CenterRadical.QuadraticRadical
