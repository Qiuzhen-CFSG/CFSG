module
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Full common centralizers and local conjugation

When the common centralizer of two elements lies in an endpoint, an
endpoint equivalence restricts to an equivalence of that full ambient
common centralizer with the corresponding endpoint common centralizer.
The maps are literal restrictions, so the resulting cardinal comparison
uses the chosen endpoint map. Normalizer control inside C(t) is stable
under conjugation by local elements of C(t).

Source motivation: the common-centralizer and root-orbit steps of
Aschbacher--Smith F.4.42, printed p.295.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory
variable {G X : Type*} [Group G] [Group X]

/-- Restrict an endpoint equivalence to the full ambient common centralizer. -/
def pairCentralizerEquiv (Q : Subgroup G) (e : Q ≃* X) (s t : Q)
    (hC : centralizer ({s.val} : Set G) ⊓ centralizer ({t.val} : Set G) ≤ Q) :
    (centralizer ({s.val} : Set G) ⊓ centralizer ({t.val} : Set G) : Subgroup G) ≃*
      (centralizer ({e s} : Set X) ⊓ centralizer ({e t} : Set X) : Subgroup X) where
  toFun x := ⟨e ⟨x.val,hC x.property⟩,by
    constructor
    · apply mem_centralizer_singleton_iff.mpr
      rw [←map_mul,←map_mul]
      exact congrArg e (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.1))
    · apply mem_centralizer_singleton_iff.mpr
      rw [←map_mul,←map_mul]
      exact congrArg e (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2))⟩
  invFun y := ⟨(e.symm y.val).val,by
    have hm (v : Q) (hv : y.val ∈ centralizer ({e v} : Set X)) :
        (e.symm y.val).val ∈ centralizer ({v.val} : Set G) := by
      apply mem_centralizer_singleton_iff.mpr
      have hh : e.symm y.val * v = v * e.symm y.val := by
        apply e.injective
        simpa only [map_mul,e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hv
      exact congrArg Q.subtype hh
    exact ⟨hm s y.property.1,hm t y.property.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    change (e.symm (e ⟨x.val,hC x.property⟩)).val = x.val
    exact congrArg Q.subtype (e.symm_apply_apply _)
  right_inv y := by
    apply Subtype.ext
    exact e.apply_symm_apply _
  map_mul' x y := by
    apply Subtype.ext
    change e (⟨x.val,hC x.property⟩ * ⟨y.val,hC y.property⟩) =
      e ⟨x.val,hC x.property⟩ * e ⟨y.val,hC y.property⟩
    exact e.map_mul _ _

/-- Conjugating the root subgroup by a local element centralizing t preserves
its normalizer bound inside the full centralizer of t. -/
theorem normalizer_inf_centralizer_conjugate_le
    {P B : Subgroup G} {t g : G}
    (hN : normalizer (B : Set G) ⊓ centralizer ({t} : Set G) ≤ P)
    (hgP : g ∈ P) (hgt : g ∈ centralizer ({t} : Set G)) :
    normalizer (B.map (MulAut.conj g).toMonoidHom : Set G) ⊓
      centralizer ({t} : Set G) ≤ P := by
  let e := MulAut.conj g
  have ht : e t = t := by
    change g*t*g⁻¹=t
    rw [mem_centralizer_singleton_iff.mp hgt,mul_inv_cancel_right]
  have hC : (centralizer ({t} : Set G)).map e.toMonoidHom = centralizer ({t} : Set G) := by
    rw [CentralizerSmallKernelTransport.map_centralizer,ht]
  have hP : P.map e.toMonoidHom = P :=
    mem_normalizer_iff_map_conj_eq.mp (P.le_normalizer hgP)
  have hh := map_mono hN (f := e.toMonoidHom)
  rw [map_inf _ _ _ e.injective,map_equiv_normalizer_eq,hC,hP] at hh
  exact hh

end Theory.GroupTheory
