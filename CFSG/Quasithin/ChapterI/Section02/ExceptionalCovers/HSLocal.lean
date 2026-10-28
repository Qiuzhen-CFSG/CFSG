module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Classes
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Fusion
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CorePreimage
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Assembly

/-!
# The HS local covering argument of I.2.2(5)

The actual involution classes have their two-central marks, and the literal
preimage M and its two-core/Frattini maps are fixed. The terminal module
calculation C_Qbar(j)=[Qbar,j] implies coset fusion and then conjugacy into
the centralizer core. When that core's quotient involutions are two-central,
the given involution's image is therefore two-central as well.

Assembly constructs the required centralizer inputs to the abelian normalizer
core, order-seven decomposition, nonsplit four-dimensional module and fusion
argument. Odd-index conjugacy extends the normalizer's involution obstruction
to the whole cover. Thus two-central involutions lift involutorily, the other
class lifts to order four, and every noncentral involution of the cover has
the unique core square of (5c). Only the earlier multiplier center bound and
genuine B.4.8(2) remain explicit; the parent retains their discharge and the
independent outer-inversion clause. The original conditional fusion API below
is preserved.

Source: Aschbacher–Smith I.2.2(5), printed pp.411–412 / PDF pp.422–423.
-/

public section
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
variable {K : Type*} [Group K] [Finite K]

/-- The actual quotient-coset fusion rules out a non-two-central image.
The core purity and B.4.8 fixed-point premises are still explicit. -/
theorem involution_image_twoCentral_of_frattini_fusion
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (u : K) (j : M e) (hjR : (j : K) ∈ centralizerCore u)
    (hER : E e ≤ (centralizerCore u).subgroupOf (M e))
    (hj : orderOf (QuotientGroup.mk' (E e) j) = 2)
    (hfixed : Qbar e ⊓ centralizer ({QuotientGroup.mk' (E e) j} : Set _) ≤
      ⁅Qbar e, zpowers (QuotientGroup.mk' (E e) j)⁆)
    (hcore : ∀ r ∈ centralizerCore u, orderOf (modelMap e r) = 2 →
      TwoCentral (modelMap e r))
    (x : M e) (hx : x ^ 2 = 1) (hximage : orderOf (modelMap e (x : K)) = 2)
    (hcoset : QuotientGroup.mk' (Q e) x = QuotientGroup.mk' (Q e) j) :
    TwoCentral (modelMap e (x : K)) := by
  obtain ⟨y, hy, hxy⟩ := conjugate_into_centralizerCore e u j hjR hER hj hfixed x hx hcoset
  obtain ⟨g, hg⟩ := isConj_iff.mp ((modelMap e).map_isConj hxy)
  have horder : orderOf (modelMap e y) = 2 := by
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq _).trans hximage
  have hcentral := (hcore y hy horder).map (MulAut.conj g⁻¹)
  have heq : (MulAut.conj g⁻¹) (modelMap e y) = modelMap e (x : K) := by
    rw [← hg]
    simp [mul_assoc]
  exact heq ▸ hcentral

end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal
