module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SylowFusion.SecondNormalizer.CentralizerAlternative.Quotient
public import Theory.GroupTheory.PerfectCentralPGroupSplit
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Splitting the alternating-five branch of the cubic centralizer

An alternating-five model for the literal quotient M/⟨y⟩ gives a
surjection M → A₅ with central kernel of order three. Since A₅ is perfect
and its Sylow three-subgroups are cyclic, the central p-group splitting
theorem supplies a section. Multiplication then identifies M with C₃ × A₅.

This proves the lifting step in Aschbacher, *Sporadic Groups* (1994), 47.3,
printed p.262. Recognition of M/⟨y⟩ remains a separate hypothesis.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer

private theorem product_of_central_section {E B : Type*} [Group E] [Group B]
    (f : E →* B) (hc : f.ker ≤ center E)
    (s : B →* E) (hs : f.comp s = MonoidHom.id B) :
    Nonempty (E ≃* (f.ker × B)) := by
  have hs' (b : B) : f (s b) = b := DFunLike.congr_fun hs b
  let m : f.ker × B →* E := f.ker.subtype.noncommCoprod s
    (fun a b => (mem_center_iff.mp (hc a.property) (s b)).symm)
  have hm (a : f.ker) (b : B) : f (m (a, b)) = b := by
    change f ((a : E) * s b) = b
    rw [map_mul, a.property, one_mul, hs']
  have hi : Function.Injective m := by
    rintro ⟨a, b⟩ ⟨c, d⟩ he
    have hbd : b = d := (hm a b).symm.trans ((congrArg f he).trans (hm c d))
    subst d
    refine Prod.ext ?_ rfl
    apply Subtype.ext
    exact mul_right_cancel he
  have hsur : Function.Surjective m := by
    intro x
    have hk : x * (s (f x))⁻¹ ∈ f.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs', mul_inv_cancel]
    refine ⟨(⟨x * (s (f x))⁻¹, hk⟩, f x), ?_⟩
    change x * (s (f x))⁻¹ * s (f x) = x
    simp [mul_assoc]
  exact ⟨(MulEquiv.ofBijective m ⟨hi, hsur⟩).symm⟩

variable {G : Type*} [Group G] [Finite G]
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The exceptional quotient lifts to the actual direct-product centralizer;
no assumption about the first cubic centralizer is used. -/
theorem cubicCentralizer_equiv_of_quotient_alternatingFive
    {y : G} (hyo : orderOf y = 3)
    (e : CubicQuotient y ≃* alternatingGroup (Fin 5)) :
    Nonempty (cubicCentralizer y ≃*
      (Multiplicative (ZMod 3) × alternatingGroup (Fin 5))) := by
  let f := e.toMonoidHom.comp (cubicQuotientMap y)
  have hf : Function.Surjective f := e.surjective.comp (cubicQuotientMap_surjective y)
  have hk : f.ker = cubicKernel y := by
    ext x
    change e (cubicQuotientMap y x) = 1 ↔ x ∈ cubicKernel y
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  have hc : f.ker ≤ center (cubicCentralizer y) := hk ▸ cubicKernel_le_center y
  have hcard : Nat.card f.ker = 3 := hk ▸ cubicKernel_card hyo
  have hp : IsPGroup 3 f.ker := IsPGroup.of_card (n := 1) hcard
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have hcyclic (P : Sylow 3 (alternatingGroup (Fin 5))) : IsCyclic P := by
    apply isCyclic_of_prime_card (p := 3)
    rw [P.card_eq_multiplicity, InvolutionGeometry.card_A5]
    decide +kernel
  obtain ⟨s, hs⟩ := PerfectCentralCovering.exists_section_of_central_pGroup_kernel
    f hf hc hp hcyclic
  obtain ⟨ep⟩ := product_of_central_section f hc s hs
  let ek : f.ker ≃* Multiplicative (ZMod 3) :=
    mulEquivOfPrimeCardEq (p := 3) hcard (by simp [Nat.card_eq_fintype_card])
  exact ⟨ep.trans (ek.prodCongr (MulEquiv.refl _))⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SecondNormalizer
