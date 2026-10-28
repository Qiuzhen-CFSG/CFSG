module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.OutsideProducts.SelectedAction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.OutsideProducts

/-!
# The selected quaternion action in the outside-product count

The selected involution is outer on both actual quaternion factors, so the
outside-product incidence theorem no longer needs a separate action premise.
The intrinsic central-norm exclusion and eight-norm count remain explicit;
the outside-products assembly owns their discharge.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, Lemmas 2.2–2.3(2)(b) and the product count in 4.3.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census

open Subgroup

variable {G : Type*} [Group G] [Finite G] {z t : G}

/-- Application to the literal outside-product fiber, with only the independent
intrinsic norm facts still explicit in addition to the census inputs. -/
public theorem outside_products_card_of_selected_action (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    (a : SelectedFusionData h) (o : OrbitData z a.u)
    (hcentral : ∀ x : Core z, x ^ 2 = 1 →
      (MulAut.conjNormal (⟨a.u, a.u_centralizes⟩ : Centralizer z) x * x) ∈ center (Core z) →
      MulAut.conjNormal (⟨a.u, a.u_centralizes⟩ : Centralizer z) x * x = 1)
    (hcount : Nat.card {x : Core z // x ^ 2 = 1 ∧
      (MulAut.conjNormal (⟨a.u, a.u_centralizes⟩ : Centralizer z) x * x) ^ 2 ≠ 1} = 8)
    (htQ : t ∈ coreInG z) (ht : orderOf t = 2) (hnt : ¬ IsConj z t) :
    Nat.card (OutsideProducts z t) = 16 := by
  obtain ⟨q⟩ := h.quaternionCentralProduct
  exact outside_products_card_of_quaternion_action h d a o q
    (selected_bothOuter h hn a q) hcentral hcount htQ ht hnt

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census
