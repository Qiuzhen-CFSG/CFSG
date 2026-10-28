module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.CoreOrbit.Definitions
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Group

/-!
# Lifting the quotient orbit and counting involutions

An H-conjugator induces an actual equivalence between the involution fibers
of Q/HC. The omega equality from J.2.6 excludes involutions of HC minus U,
so all involutions in Q minus U lie over the fifteen nonidentity quotient
cosets. Uniform fiber size sixteen gives 240. Composing each quotient
conjugator with a Q-conjugator in the seed fiber proves H-transitivity.

These are reductions with the fiber geometry and quotient action explicit;
they do not assert that those source obligations have already been discharged.

Source: Aschbacher–Smith, J.2.8(1), printed pp.437–438 / PDF pp.448–449.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
variable {G : Type*} [Group G] [Finite G]

/-- Conjugation gives an equivalence of involution fibers. -/
def fiberConj (d : TypeRuSetup G) (h : d.H) (a : CoreQuotient d) :
    fiber d a ≃ fiber d (quotientConj d h a) :=
  (coreConj d h).toEquiv.subtypeEquiv (fun x => by
    change (coreMap d x = a ∧ orderOf (x : G) = 2) ↔
      (coreMap d (coreConj d h x) = quotientConj d h a ∧
        orderOf (coreConj d h x : G) = 2)
    rw [← quotientConj_mk, (quotientConj d h).injective.eq_iff]
    have ho : orderOf (coreConj d h x : G) = orderOf (x : G) :=
      (MulAut.conj (h : G)).orderOf_eq x
    rw [ho])

theorem involution_not_HC (d : TypeRuSetup G) (homega : omegaOneAmbient d.HC = d.U)
    {x : G} (hx : x ∉ d.U) (ho : orderOf x = 2) : x ∉ d.HC := by
  intro hc
  apply hx
  rw [← homega]
  exact (omegaOneAmbient_le_iff d.HC (omegaOneAmbient d.HC)).mp le_rfl x hc
    (ho ▸ pow_orderOf_eq_one x)

theorem coreMap_ne_one (d : TypeRuSetup G) {x : d.Q}
    (hx : (x : G) ∉ d.HC) : coreMap d x ≠ 1 := by
  intro he
  apply hx
  exact (QuotientGroup.eq_one_iff (N := d.HC.subgroupOf d.Q) x).mp he

/-- Decompose the involutions of Q minus U over the nonidentity quotient cosets. -/
def outsideEquivFibers (d : TypeRuSetup G) (hU : d.U ≤ d.HC)
    (homega : omegaOneAmbient d.HC = d.U) :
    involutionsOutside d.Q d.U ≃
      (Σ a : {a : CoreQuotient d // a ≠ 1}, fiber d a) where
  toFun x := ⟨⟨coreMap d ⟨x, x.property.1⟩,
      coreMap_ne_one d (involution_not_HC d homega x.property.2.1 x.property.2.2)⟩,
    ⟨⟨x, x.property.1⟩, rfl, x.property.2.2⟩⟩
  invFun x := ⟨x.2.val, x.2.val.property, (fun hu => x.1.property
      (x.2.property.1.symm.trans ((QuotientGroup.eq_one_iff _).mpr (hU hu)))),
    x.2.property.2⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨a, ha⟩, ⟨x, hx, ho⟩⟩; cases hx; rfl

/-- Fifteen conjugate quotient fibers, each of size sixteen, contain 240 involutions. -/
theorem outside_card_of_fiber (d : TypeRuSetup G) (hU : d.U ≤ d.HC)
    (homega : omegaOneAmbient d.HC = d.U)
    (hcard : Nat.card (CoreQuotient d) = 16)
    (w : d.Q) (hcover : ∀ a : CoreQuotient d, a ≠ 1 →
      ∃ h : d.H, quotientConj d h (coreMap d w) = a)
    (hsize : Nat.card (fiber d (coreMap d w)) = 16) :
    Nat.card (involutionsOutside d.Q d.U) = 240 := by
  classical
  let : Fintype (CoreQuotient d) := Fintype.ofFinite _
  have hsize' (a : {a : CoreQuotient d // a ≠ 1}) : Nat.card (fiber d a) = 16 := by
    obtain ⟨h, hh⟩ := hcover a a.property
    rw [← hh, ← Nat.card_congr (fiberConj d h (coreMap d w))]
    exact hsize
  have hn : Fintype.card {a : CoreQuotient d // a ≠ 1} = 15 := by
    rw [Fintype.card_subtype_compl]
    simp only [← Nat.card_eq_fintype_card, hcard, Nat.card_unique]
  rw [Nat.card_congr (outsideEquivFibers d hU homega), Nat.card_sigma]
  simp only [hsize', Finset.sum_const, Finset.card_univ, smul_eq_mul, hn]

theorem conjugate_into_fiber (d : TypeRuSetup G) (h : d.H)
    (w : d.Q) (x : d.Q) (ho : orderOf (x : G) = 2)
    (he : quotientConj d h (coreMap d w) = coreMap d x) :
    ∃ y : fiber d (coreMap d w), (coreConj d h y : d.Q) = x := by
  let x' : fiber d (quotientConj d h (coreMap d w)) := ⟨x, he.symm, ho⟩
  exact ⟨(fiberConj d h (coreMap d w)).symm x',
    congrArg Subtype.val ((fiberConj d h (coreMap d w)).apply_symm_apply x')⟩

/-- Quotient transitivity and actual Q-conjugators in the seed fiber give H-transitivity. -/
theorem outside_transitive_of_fiber (d : TypeRuSetup G)
    (homega : omegaOneAmbient d.HC = d.U) (w : d.Q)
    (hcover : ∀ a : CoreQuotient d, a ≠ 1 →
      ∃ h : d.H, quotientConj d h (coreMap d w) = a)
    (htrans : ∀ x : fiber d (coreMap d w),
      ∃ q : d.Q, (q : G) * w * (q : G)⁻¹ = x) :
    TransitiveOn d.H (involutionsOutside d.Q d.U) := by
  have hreach (x : G) (hx : x ∈ involutionsOutside d.Q d.U) :
      ∃ h : d.H, (h : G) * w * (h : G)⁻¹ = x := by
    let xQ : d.Q := ⟨x, hx.1⟩
    obtain ⟨h, he⟩ := hcover (coreMap d xQ)
      (coreMap_ne_one d (involution_not_HC d homega hx.2.1 hx.2.2))
    obtain ⟨y, hy⟩ := conjugate_into_fiber d h w xQ hx.2.2 he
    obtain ⟨q, hq⟩ := htrans y
    refine ⟨h * ⟨q, pCoreIn_le 2 d.H q.property⟩, ?_⟩
    have hy' : (h : G) * (y : d.Q) * (h : G)⁻¹ = x := congrArg Subtype.val hy
    simpa only [coe_mul, mul_inv_rev, mul_assoc] using
      (congrArg (fun v : G => (h : G) * v * (h : G)⁻¹) hq).trans hy'
  intro x y hx hy
  obtain ⟨a, ha⟩ := hreach x hx
  obtain ⟨b, hb⟩ := hreach y hy
  refine ⟨b * a⁻¹, ?_⟩
  rw [← ha, ← hb]
  simp only [coe_mul, coe_inv, mul_inv_rev, inv_inv]
  group

def fiberEquivCentralizer (d : TypeRuSetup G) (s : ConjugateSeed d)
    (hf : ∀ x : d.Q, x ∈ fiber d (coreMap d s.w) ↔
      (s.w : G)⁻¹ * x ∈ seedCentralizer d s) :
    fiber d (coreMap d s.w) ≃ seedCentralizer d s where
  toFun x := ⟨(s.w : G)⁻¹ * x, (hf x).mp x.property⟩
  invFun u := ⟨⟨s.w * (u : G), d.Q.mul_mem s.w.property
    (d.ru2.six.kernel_le u.property.1)⟩, (hf _).mpr (by simp only [inv_mul_cancel_left]; exact u.property)⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; simp
  right_inv u := by apply Subtype.ext; simp

theorem fiber_card (d : TypeRuSetup G) (s : ConjugateSeed d) (f : FiberGeometry d s) :
    Nat.card (fiber d (coreMap d s.w)) = 16 :=
  (Nat.card_congr (fiberEquivCentralizer d s f.involutions)).trans f.centralizer_card


end CFSG.Quasithin.ChapterJ.Fusion.CoreOrbit
