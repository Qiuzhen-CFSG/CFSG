module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.InvolutionLifting
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelCore
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.Transport
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Fusion

/-!
# The two-central HS cover: lifting, core purity, and square reduction

Every two-central model involution lifts to an involution. The cover's actual
O₂(O²(C_K(u))) maps into the model centralizer's two-core, whose involutions
are all two-central. This discharges the core-purity premise in the normalizer
fusion argument, retaining the literal quotient maps and subgroup inclusions.

The distinguished-square calculation is proved from a central core element
whose image squares to u*. For any other square root x, multiplying by that
central element gives an element with involutory or trivial image. Lifting
and purity make its square one, forcing the two original squares to agree.
This argument includes central elements of the core. `CoverStructure` constructs
the central root, using the residual transport from `CoverResidual` and the
center calculation from `ModelOrbit`. The present module keeps the lifting,
purity, and conditional reduction independent of those later arguments.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423.
The completed branch is exported by `CentralizerRestriction.Assembly`.
-/

public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
open CentralizerRestriction
variable {K : Type*} [Group K] [Finite K]

/-- The exact purity premise used by the normalizer/Frattini fusion argument. -/
theorem core_image_twoCentral
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (hu : orderOf (modelMap e u) = 2) (hc : TwoCentral (modelMap e u))
    (r : K) (hr : r ∈ centralizerCore u) (hr2 : orderOf (modelMap e r) = 2) :
    TwoCentral (modelMap e r) :=
  model_centralizer_core_twoCentral _ hu hc _
    (core_image_le_model_centralizer_core e hZ u (mem_map_of_mem (modelMap e) hr)) hr2

/-- In the cover core, an element whose image squares to one also squares to one. -/
theorem core_square_one_of_image_square_one
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (hu : orderOf (modelMap e u) = 2) (hc : TwoCentral (modelMap e u))
    (r : K) (hr : r ∈ centralizerCore u) (hr2 : modelMap e r ^ 2 = 1) :
    r ^ 2 = 1 := by
  by_cases hr1 : modelMap e r = 1
  · have hz : r ∈ center K := by
      rw [← modelMap_ker e]
      exact hr1
    have hp := pow_card_eq_one' (x := (⟨r, hz⟩ : center K))
    rw [hZ] at hp
    exact congrArg Subtype.val hp
  · have ho : orderOf (modelMap e r) = 2 := orderOf_eq_prime hr2 hr1
    have ho' := order_two_of_twoCentral_image e hZ r ho (core_image_twoCentral e hZ u hu hc r hr ho)
    rw [← ho', pow_orderOf_eq_one]

/-- A central core root gives the distinguished square, including all central roots.
Existence and centrality of this root must still be supplied by the local structure. -/
theorem hasUniqueCoreSquareLift_of_central_root
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (hu : orderOf (modelMap e u) = 2) (hc : TwoCentral (modelMap e u))
    (a : centralizerCore u) (ha : a ∈ center (centralizerCore u))
    (haimage : modelMap e ((a : K) ^ 2) = modelMap e u) :
    HasUniqueCoreSquareLift u := by
  have ha4 : ((a : K) ^ 2) ^ 2 = 1 :=
    core_square_one_of_image_square_one e hZ u hu hc _
      ((centralizerCore u).pow_mem a.property 2)
      (by rw [haimage, ← hu, pow_orderOf_eq_one])
  refine ⟨(a : K) ^ 2, ⟨e.injective haimage, a, a.property, rfl⟩, ?_⟩
  rintro v ⟨hv, x, hx, rfl⟩
  have hximage : modelMap e (x ^ 2) = modelMap e u := congrArg e hv
  have hax : Commute (a : K) x :=
    (congrArg Subtype.val (mem_center_iff.mp ha ⟨x, hx⟩)).symm
  have hprod : (modelMap e ((a : K) * x)) ^ 2 = 1 := by
    rw [← map_pow, hax.mul_pow, map_mul, haimage, hximage, ← pow_two,
      ← hu, pow_orderOf_eq_one]
  have hprod2 := core_square_one_of_image_square_one e hZ u hu hc _
    ((centralizerCore u).mul_mem a.property hx) hprod
  rw [hax.mul_pow] at hprod2
  calc
    x ^ 2 = (a : K) ^ 2 * ((a : K) ^ 2 * x ^ 2) := by
      rw [← mul_assoc, ← pow_two, ha4, one_mul]
    _ = (a : K) ^ 2 := by rw [hprod2, mul_one]

/-- The normalizer fusion application with its core-purity premise discharged. -/
theorem involution_image_twoCentral_of_frattini_fusion_in_twoCentral_core
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (hu : orderOf (modelMap e u) = 2) (hc : TwoCentral (modelMap e u))
    (j : M e) (hjR : (j : K) ∈ centralizerCore u)
    (hER : E e ≤ (centralizerCore u).subgroupOf (M e))
    (hj : orderOf (QuotientGroup.mk' (E e) j) = 2)
    (hfixed : Qbar e ⊓ centralizer ({QuotientGroup.mk' (E e) j} : Set _) ≤
      ⁅Qbar e, zpowers (QuotientGroup.mk' (E e) j)⁆)
    (x : M e) (hx : x ^ 2 = 1) (hximage : orderOf (modelMap e (x : K)) = 2)
    (hcoset : QuotientGroup.mk' (Q e) x = QuotientGroup.mk' (Q e) j) :
    TwoCentral (modelMap e (x : K)) := by
  obtain ⟨y, hy, hxy⟩ := conjugate_into_centralizerCore e u j hjR hER hj hfixed x hx hcoset
  obtain ⟨g, hg⟩ := isConj_iff.mp ((modelMap e).map_isConj hxy)
  have horder : orderOf (modelMap e y) = 2 := by
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq _).trans hximage
  have hcentral := (core_image_twoCentral e hZ u hu hc y hy horder).map (MulAut.conj g⁻¹)
  have heq : (MulAut.conj g⁻¹) (modelMap e y) = modelMap e (x : K) := by
    rw [← hg]
    simp [mul_assoc]
  exact heq ▸ hcentral

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
