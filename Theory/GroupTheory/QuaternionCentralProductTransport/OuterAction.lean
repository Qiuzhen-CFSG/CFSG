module
public import Theory.GroupTheory.QuaternionCentralProductTransport
public import Theory.GroupTheory.QuaternionCentralProductC2Rank
import all Theory.GroupTheory.QuaternionCentralProductTransport

/-!
# Transport of outer quaternion-factor actions

An equivariant multiplicative equivalence carries both factor preservation and
non-inner restrictions to the transported quaternion presentation. The internal
transport import exposes its factor definitions only in this proof extension.
The Chapter 14 Sylow-rank consumer uses the literal subgroup inclusion.

Source application: Aschbacher–Smith, 14.4.4(6), printed p.1007.
-/

namespace Subgroup.QuaternionCentralProductData
variable {Q R : Type*} [Group Q] [Group R]
    (d : QuaternionCentralProductData Q)

/-- Transport outer restrictions through an equivariant equivalence while
retaining the two specified quaternion factors. -/
public theorem BothOuter.map {a : MulAut Q} (h : d.BothOuter a)
    (e : Q ≃* R) (b : MulAut R) (he : ∀ x, b (e x) = e (a x)) :
    (d.map e).BothOuter b := by
  have hm : b.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.toMonoidHom :=
    MonoidHom.ext he
  have hp (A : Subgroup Q) (ha : A.map a.toMonoidHom = A) :
      (A.map e.toMonoidHom).map b.toMonoidHom = A.map e.toMonoidHom := by
    rw [Subgroup.map_map, hm, ← Subgroup.map_map, ha]
  have ho (A : Subgroup Q)
      (ha : ¬ ∃ c : A, ∀ x : A, a (x : Q) = (c : Q) * x * (c : Q)⁻¹) :
      ¬ ∃ c : A.map e.toMonoidHom, ∀ x : A.map e.toMonoidHom,
        b (x : R) = (c : R) * x * (c : R)⁻¹ := by
    rintro ⟨c,hc⟩
    obtain ⟨v,hv,hvc⟩ := c.property
    apply ha
    refine ⟨⟨v,hv⟩,?_⟩
    intro x
    apply e.injective
    change e (a (x : Q)) = e (v * (x : Q) * v⁻¹)
    change e v = (c : R) at hvc
    rw [← he, map_mul, map_mul, map_inv, hvc]
    exact hc ⟨e x, mem_map_of_mem e.toMonoidHom x.property⟩
  exact ⟨hp d.left h.left_map, hp d.right h.right_map,
    ho d.left h.left_outer, ho d.right h.right_outer⟩
end Subgroup.QuaternionCentralProductData
