module

public import CFSG.Quasithin.Chapter13.Section09.SourceSetup
public import Theory.GroupTheory.InvolutionFusionCover

/-!
# Transfer in the marked 13.9 configuration

The first paragraph of 13.9.9 identifies the involutions of an index-two
subgroup `M₀` of the original wreath subgroup. Once its intersection with
the original Sylow subgroup is shown to have only the two marked ambient
classes, Thompson transfer supplies all ambient involutions. The
nonfusion of `z,t` is the earlier result 13.9.2(5).

The theorem below discharges transfer and its simplicity hypothesis.
The local index and class-coverage calculations remain explicit; this is
not a completed proof of 13.9.9.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.9.9(5), printed p.972 (PDF p.989).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section09.FusionAlignment

variable {G : Type*} [Group G] [Finite G] {C : GroupClass}

/-- The ambient two-class conclusion follows from the involutions of the
literal `T ∩ M₀`, with nonfusion supplied by 13.9.2(5). -/
theorem two_classes_of_index_two_local_cover
    (hG : IsSimpleQTKE C G) (d : Configuration G) (M₀ : Subgroup G)
    (hindex : (M₀.subgroupOf (d.T : Subgroup G)).index = 2)
    (z t : G) (hz : orderOf z = 2) (ht : orderOf t = 2)
    (hzt : ¬ IsConj z t)
    (hcover : ∀ x : G, x ∈ M₀ → orderOf x = 2 → IsConj z x ∨ IsConj t x) :
    orderOf z = 2 ∧ orderOf t = 2 ∧ ¬ IsConj z t ∧
      ∀ x : G, orderOf x = 2 → IsConj z x ∨ IsConj t x := by
  let := hG.simple
  refine ⟨hz, ht, hzt, ?_⟩
  have hno := Subgroup.index_ne_two_of_nonabelian_simple hG.nonabelian
  intro x hx
  obtain ⟨y, hy, hxy⟩ := d.T.exists_isConj_mem_of_index_two_ambient
    hno (M₀.subgroupOf (d.T : Subgroup G)) hindex x hx
  have hyorder : orderOf (y : G) = 2 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hxy
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq x).trans hx
  rcases hcover y hy hyorder with hzy | hty
  · exact Or.inl (hzy.trans hxy.symm)
  · exact Or.inr (hty.trans hxy.symm)

end CFSG.Quasithin.Chapter13.Section09.FusionAlignment
