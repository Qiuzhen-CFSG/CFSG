module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.NativeSource16.OddResidual.CyclicCircles
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.LinearGeometry.FieldAction

/-!
# The circles of tu and tv

A fixed distinguished involution is a coboundary for an outer involution of
the actual linear circle. In ambient conjugation coordinates this says that
u and tu are conjugate by an element of the opposite circle. Conjugation
preserves the distinguished set, so it transports their literal circles.
This supplies the two additional linear models used by the Frattini plane
argument, without asserting that the old mark z centralizes tu.

Source: GLS IV, Chapter 2, Proposition 16.5, using Chapter 4, Lemma 3.4(a).
-/

namespace BenderSuzuki.ZD.Source16OddResidual
open Subgroup Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] {Z : Set G} {M : Subgroup G}

/-- Conjugate involutions have isomorphic actual distinguished circles. -/
public theorem circle_equiv_of_isConj (h : IsProductDisconnected Z M)
    {u w : G} (hc : IsConj u w) :
    Nonempty (localCircle Z (centralizer ({u} : Set G)) ≃*
      localCircle Z (centralizer ({w} : Set G))) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  let e := MulAut.conj g
  have he : e u=w := hg
  have hziff (x : G) : e x∈Z ↔ x∈Z := by
    constructor
    · intro hx
      have hh := h.invariant g⁻¹ (e x) hx
      simpa [e,MulAut.conj_apply,mul_assoc] using hh
    · exact h.invariant g x
  have hciff (x : G) : e x∈centralizer ({w}:Set G) ↔ x∈centralizer ({u}:Set G) := by
    simp only [mem_centralizer_singleton_iff,←he,←map_mul,e.injective.eq_iff]
  have hmap : (localCircleIn Z (centralizer ({u}:Set G))).map e.toMonoidHom =
      localCircleIn Z (centralizer ({w}:Set G)) := by
    rw [localCircleIn_eq_closure,localCircleIn_eq_closure,MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨(hziff y).mpr hy.1,(hciff y).mpr hy.2⟩
    · intro hx
      obtain ⟨y,rfl⟩ := e.surjective x
      exact ⟨y,⟨(hziff y).mp hx.1,(hciff y).mp hx.2⟩,rfl⟩
  let fu := (localCircle Z (centralizer ({u}:Set G))).equivMapOfInjective
    (centralizer ({u}:Set G)).subtype (centralizer ({u}:Set G)).subtype_injective
  let fw := (localCircle Z (centralizer ({w}:Set G))).equivMapOfInjective
    (centralizer ({w}:Set G)).subtype (centralizer ({w}:Set G)).subtype_injective
  exact ⟨fu.trans (((localCircleIn Z (centralizer ({u}:Set G))).equivMapOfInjective
    e.toMonoidHom e.injective).trans ((MulEquiv.subgroupCongr hmap).trans fw.symm))⟩

/-- The source outer-field coboundary is an actual conjugacy u∼tu in G. -/
public theorem isConj_twist_of_outer_circle
    (h : IsProductDisconnected Z M) {t u v : G} (ht : t∈Z)
    (htv : Commute t v) (htu : Commute t u) {n : ℕ}
    (e : localCircle Z (centralizer ({v}:Set G)) ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (a : MulAut (localCircle Z (centralizer ({v}:Set G))))
    (ha : a^2=1) (ho : ¬∃g,a=MulAut.conj g)
    (hact : ∀x, localCircleHom Z (centralizer ({v}:Set G)) (a x) =
      u*localCircleHom Z (centralizer ({v}:Set G)) x*u⁻¹) :
    IsConj u (t*u) := by
  let F := centralizer ({v}:Set G)
  let f := localCircleHom Z F
  have htF : t∈F := mem_centralizer_singleton_iff.mpr htv.eq
  let tC : localCircle Z F := ⟨⟨t,htF⟩,subset_closure ht⟩
  have htC : PFAppendixIII.IsInvolution tC :=
    IsInvolution.subtype (IsInvolution.subtype (h.involutions t ht) htF) _
  have hat : a tC=tC := by
    apply localCircleHom_injective Z F
    change f (a tC)=t
    rw [hact]
    exact mul_inv_eq_iff_eq_mul.mpr htu.symm.eq
  obtain ⟨g,hg⟩ := RankOneModelGeometry.LinearGeometry.outer_fixed_involution_coboundary e a ha ho tC htC hat
  have hh : (f g)⁻¹*(u*f g*u⁻¹)=t := by
    have hm := congrArg f hg
    rw [map_mul,map_inv,hact] at hm
    exact hm
  apply isConj_iff.mpr
  refine ⟨(f g)⁻¹,?_⟩
  calc
    (f g)⁻¹*u*((f g)⁻¹)⁻¹ = ((f g)⁻¹*(u*f g*u⁻¹))*u := by group
    _ = t*u := by rw [hh]

/-- The model of the original u-circle transports to the actual tu-circle. -/
public theorem twisted_circle_model
    (h : IsProductDisconnected Z M) {t u v : G} (ht : t∈Z)
    (htv : Commute t v) (htu : Commute t u) {n k : ℕ}
    (eu : localCircle Z (centralizer ({u}:Set G)) ≃* MatrixGroups.PSL2BinaryMatrixGroup k)
    (ev : localCircle Z (centralizer ({v}:Set G)) ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (a : MulAut (localCircle Z (centralizer ({v}:Set G))))
    (ha : a^2=1) (ho : ¬∃g,a=MulAut.conj g)
    (hact : ∀x, localCircleHom Z (centralizer ({v}:Set G)) (a x) =
      u*localCircleHom Z (centralizer ({v}:Set G)) x*u⁻¹) :
    Nonempty (localCircle Z (centralizer ({t*u}:Set G)) ≃* MatrixGroups.PSL2BinaryMatrixGroup k) := by
  obtain ⟨f⟩ := circle_equiv_of_isConj h (isConj_twist_of_outer_circle h ht htv htu ev a ha ho hact)
  exact ⟨f.symm.trans eu⟩

end BenderSuzuki.ZD.Source16OddResidual
