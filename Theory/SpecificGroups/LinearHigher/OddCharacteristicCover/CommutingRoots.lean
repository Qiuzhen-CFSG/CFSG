module

public import Theory.GroupTheory.CentralOddKernelCommutators
public import Theory.SpecificGroups.LinearHigher.OddCharacteristicCover.Geometry

/-!
# Commuting root preimages over a prime field

For roots sharing an index, express a root through a spare fourth coordinate.
For disjoint roots, the Weyl exchange makes their central commutator an
involution, killed by the odd kernel. Every prime-field coefficient is an
integer multiple of one, extending the unit-root calculation to all roots.

Source application: the distant relation in Steinberg's degree-four presentation,
including defining-prime central kernels and the field of order three.
-/

open scoped commutatorElement MatrixGroups
namespace Theory.SpecificGroups.LinearHigher.OddCharacteristicCover
open Subgroup CentralExtension.OddKernel
variable {E : Type*} [Group E] {p : ℕ} [Fact p.Prime]
variable (f : E →* PSL(4,ZMod p)) (hf : Function.Surjective f)
  (hc : f.ker ≤ center E) (hcop : (Nat.card f.ker).Coprime 2)

include hf hc hcop

public theorem unit_roots_commute (r s : Root 4) {x y : E}
    (hx : f x=projectiveRoot r 1) (hy : f y=projectiveRoot s 1)
    (hrs : r.val.2 ≠ s.val.1) (hsr : s.val.2 ≠ r.val.1) : Commute x y := by
  by_cases ho : r.val.1=s.val.1 ∨ r.val.2=s.val.2
  · obtain ⟨m,hmr1,hmr2,hms1,hms2⟩ := exists_outside_overlap r s ho
    obtain ⟨a,ha⟩ := hf (projectiveRoot (root r.val.1 m hmr1.symm) 1)
    obtain ⟨b,hb⟩ := hf (projectiveRoot (root m r.val.2 hmr2) 1)
    have hab : f ⁅a,b⁆=projectiveRoot r 1 := by
      rw [map_commutatorElement,ha,hb,
        projectiveRoot_relations.chain r.val.1 m r.val.2 hmr1.symm hmr2 r.property,mul_one]
      exact congrArg (fun q : Root 4 => projectiveRoot q (1:ZMod p)) (Subtype.ext rfl)
    have hcomm : Commute y ⁅a,b⁆ := by
      apply commute_commutator_of_image_commute f hc
      · rw [hy,ha]
        exact commutatorElement_eq_one_iff_commute.mp
          (projectiveRoot_relations.distant _ _ _ _ hsr hms1)
      · rw [hy,hb]
        exact commutatorElement_eq_one_iff_commute.mp
          (projectiveRoot_relations.distant _ _ _ _ hms2.symm hrs)
    apply commutatorElement_eq_one_iff_commute.mp
    rw [CentralExtension.commutator_eq_of_image_eq f hc (hx.trans hab.symm) rfl]
    exact hcomm.symm.commutator_eq
  · push Not at ho
    obtain ⟨t,htx,hty⟩ := disjoint_root_swap (F:=ZMod p) r s ho.1 hsr.symm hrs ho.2
    obtain ⟨T,hT⟩ := hf t
    apply commute_of_image_swap f hc hcop
      (commutatorElement_eq_one_iff_commute.mp (by
        rw [hx,hy]; exact projectiveRoot_relations.distant r s 1 1 hrs hsr))
      (t:=T)
    · rw [map_mul,map_mul,map_inv,hT,hx,hy,htx]
    · rw [map_mul,map_mul,map_inv,hT,hx,hy,hty]

public theorem commuting_root_preimages (r s : Root 4) (a b : ZMod p) {x y : E}
    (hx : f x=projectiveRoot r a) (hy : f y=projectiveRoot s b)
    (hrs : r.val.2 ≠ s.val.1) (hsr : s.val.2 ≠ r.val.1) : Commute x y := by
  obtain ⟨u,hu⟩ := hf (projectiveRoot r 1)
  obtain ⟨v,hv⟩ := hf (projectiveRoot s 1)
  have hcomm := unit_roots_commute f hf hc hcop r s hu hv hrs hsr
  have hxa : f x=f (u^a.val) := by
    rw [map_pow,hu,projectiveRoot_pow,mul_one,ZMod.natCast_zmod_val,hx]
  have hyb : f y=f (v^b.val) := by
    rw [map_pow,hv,projectiveRoot_pow,mul_one,ZMod.natCast_zmod_val,hy]
  apply commutatorElement_eq_one_iff_commute.mp
  rw [CentralExtension.commutator_eq_of_image_eq f hc hxa hyb]
  exact (hcomm.pow_pow a.val b.val).commutator_eq

end Theory.SpecificGroups.LinearHigher.OddCharacteristicCover