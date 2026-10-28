module
public import Theory.GroupTheory.OddKernelInvolutionCentralizer
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic

/-!
# Element centralizers under a central prime-group kernel

For a surjection with central p-kernel, the image of an element centralizer
is normal in the quotient element centralizer, with p-group quotient.
The commutator with a chosen lift gives a homomorphism into the kernel;
its kernel is exactly the lifted centralizer. No surjectivity of the
centralizer map is assumed.

Source application: the full central covers in Aschbacher--Smith 4.2.13
and 12.1.9, printed pp.612,793.
-/

public section
open Subgroup
open scoped commutatorElement
namespace MonoidHom
variable {G H : Type*} [Group G] [Group H]

/-- The literal element-centralizer map has normal image and p-group cokernel. -/
theorem elementCentralizerMap_normal_pGroup_cokernel {p : ℕ}
    (f : G →* H) (hf : Function.Surjective f)
    (hc : f.ker ≤ center G) (hp : IsPGroup p f.ker) (z : G) :
    ∃ hN : (f.elementCentralizerMap z).range.Normal,
      letI := hN
      IsPGroup p (centralizer ({f z} : Set H) ⧸ (f.elementCentralizerMap z).range) := by
  let C := centralizer ({f z} : Set H)
  let P := C.comap f
  have hm (x : P) : ⁅(x : G),z⁆ ∈ f.ker := by
    change f ⁅(x : G),z⁆ = 1
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact mem_centralizer_singleton_iff.mp x.property
  let δ : P →* f.ker :=
    { toFun := fun x => ⟨⁅(x : G),z⁆,hm x⟩
      map_one' := Subtype.ext (commutatorElement_one_left z)
      map_mul' := fun a b => Subtype.ext (by
        change ⁅(a : G)*(b : G),z⁆ = ⁅(a : G),z⁆ * ⁅(b : G),z⁆
        have hb := mem_center_iff.mp (hc (hm b)) (a : G)
        have ha := mem_center_iff.mp (hc (hm a)) ⁅(b : G),z⁆
        rw [commutatorElement_mul_left_eq_conj_mul,hb]
        simpa only [mul_assoc,mul_inv_cancel_left] using ha) }
  let q : P →* C := (f.comp P.subtype).codRestrict _ (fun x => x.property)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x,hx⟩ := hf y
    have hxP : x ∈ P := by
      change f x ∈ C
      rw [hx]
      exact y.property
    exact ⟨⟨x,hxP⟩,Subtype.ext hx⟩
  have he : δ.ker.map q = (f.elementCentralizerMap z).range := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hxz : (x : G) ∈ centralizer ({z} : Set G) :=
        mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp
          (congrArg Subtype.val hx))
      exact ⟨⟨x,hxz⟩,rfl⟩
    · rintro ⟨x,rfl⟩
      have hxP : (x : G) ∈ P := by
        apply mem_centralizer_singleton_iff.mpr
        simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp x.property)
      refine ⟨⟨x,hxP⟩,?_,rfl⟩
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mem_centralizer_singleton_iff.mp x.property)
  have hN : (f.elementCentralizerMap z).range.Normal :=
    he ▸ (inferInstance : δ.ker.Normal).map q hq
  let := hN
  let π := QuotientGroup.map δ.ker (f.elementCentralizerMap z).range q (by
    rw [←he]; exact le_comap_map q δ.ker)
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (f.elementCentralizerMap z).range y
    obtain ⟨x,rfl⟩ := hq y
    exact ⟨QuotientGroup.mk' δ.ker x,rfl⟩
  have hδ : IsPGroup p (P ⧸ δ.ker) :=
    (hp.to_subgroup δ.range).of_equiv (QuotientGroup.quotientKerEquivRange δ).symm
  exact ⟨hN,hδ.of_surjective π hπ⟩
end MonoidHom
