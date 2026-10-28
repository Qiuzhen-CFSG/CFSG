module
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.OrderOfElement
/-!
# Fusion into a marked centralizer outside an index-two half

Conjugators in M preserve a normal residual subgroup F. If its intersection
with T is contained in S, a class outside S stays outside S whenever it is
brought back into T. A commuting marked involution and its M-conjugator
place the class in the specified centralizer.

Source application: Aschbacher--Smith 2.4.29, printed p.546.
-/
public section
namespace Subgroup

/-- Conjugation within M carries an outside-S class into the marked centralizer,
provided its residual coset is preserved by M. -/
theorem exists_fused_outside_in_marked_centralizer
    {G : Type*} [Group G]
    (M T S F : Subgroup G) (hTM : T ≤ M) (hSF : S ≤ F)
    (hTF : T ⊓ F ≤ S) (hn : M ≤ normalizer (F : Set G))
    (u b j i : G) (hMu : M ⊓ centralizer ({u} : Set G) ≤ T)
    (hiT : i ∈ T) (hiS : i ∉ S)
    (hij : ∃m∈M, m*i*m⁻¹=j)
    (hbu : ∃n∈M, n*b*n⁻¹=u) (hjb : j*b=b*j) :
    ∃r∈T ⊓ centralizer ({u}:Set G), r∉S ∧
      orderOf r=orderOf i ∧ IsConj i r := by
  obtain ⟨m,hm,hmj⟩ := hij
  obtain ⟨n,hnM,hnu⟩ := hbu
  let c := n*m
  let e : G ≃* G := MulAut.conj c
  let r := e i
  have hcM : c∈M := M.mul_mem hnM hm
  have hrM : r∈M := M.mul_mem (M.mul_mem hcM (hTM hiT)) (M.inv_mem hcM)
  have hri : IsConj i r := isConj_iff.mpr ⟨c,rfl⟩
  have hrj : r = (MulAut.conj n) j := by
    change (n*m)*i*(n*m)⁻¹=n*j*n⁻¹
    rw [←hmj]
    simp [mul_assoc]
  have hru : r∈centralizer ({u}:Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    rw [hrj,←hnu]
    change (MulAut.conj n) j * (MulAut.conj n) b = (MulAut.conj n) b * (MulAut.conj n) j
    simpa only [map_mul] using congrArg (MulAut.conj n) hjb
  have hrT : r∈T := hMu ⟨hrM,hru⟩
  have hrF : r∉F := by
    intro hh
    have hiF : i∈F := (mem_normalizer_iff.mp (hn hcM) i).mpr hh
    exact hiS (hTF ⟨hiT,hiF⟩)
  exact ⟨r,⟨hrT,hru⟩,fun hh=>hrF (hSF hh),e.orderOf_eq i,hri⟩
end Subgroup
