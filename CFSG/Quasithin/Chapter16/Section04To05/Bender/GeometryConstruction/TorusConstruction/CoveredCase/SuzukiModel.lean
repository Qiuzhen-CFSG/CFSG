module

public import Theory.SpecificGroups.Suzuki.RootCenter

/-!
# The concrete Sz(8) Sylow facts used in the covered branch

The root multiplication formula shows that a root element squares to one
exactly when its first coordinate vanishes. Huppert–Blackburn identifies
these same elements as both the center and the derived group. Sylow
conjugacy transports these facts and the order 64 to an arbitrary Sylow
subgroup of a group actually isomorphic to the matrix model Sz(8).

Source: Huppert–Blackburn, Finite Groups III, XI.3.1; application to
Aschbacher–Smith, 16.5.1, printed p.1194.
-/

@[expose] public section

open Subgroup BenderSuzuki BenderSuzuki.MatrixGroups PFAppendixIII
open scoped Pointwise LinearAlgebra.Projectivization commutatorElement

namespace CFSG.Quasithin.CoveredSuzukiModel

theorem root_center_iff_square (x : SuzukiRootClosure 1) :
    x ∈ center (SuzukiRootClosure 1) ↔ x ^ 2 = 1 := by
  let K := BinaryGaloisField (2 * 1 + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (1 + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (1 + 1)) :=
    iterateFrobeniusEquiv_def K 2 (1 + 1)
  obtain ⟨_, _, _, _, _, _, _, _, hmul, hc, hz, _⟩ :=
    External.huppert_blackburn_XI_3_1 1 (by omega) pi
      (External.binaryGaloisField_tits_formula_sq 1 pi hpi)
  change commutator (SuzukiRootClosure 1) = center (SuzukiRootClosure 1) at hc
  change ∀ x : SuzukiRootClosure 1, x ∈ commutator (SuzukiRootClosure 1) ↔
    ∃ b : K, (x : GL (Fin 4) K) = SuzukiRootGL 1 0 b at hz
  rw [hc] at hz
  have hsq (a b : K) : (SuzukiRootGL 1 a b) ^ 2 = SuzukiRootGL 1 0 (a * pi a) := by
    rw [pow_two, hmul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add]
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := (hz x).mp hx
    apply Subtype.ext
    change (x : GL (Fin 4) K) ^ 2 = 1
    rw [hb, hsq, zero_mul, External.suzukiRootGL_zero_zero]
  · intro hx
    obtain ⟨a, b, hab⟩ :=
      (External.suzukiRootGL_mem_closure_iff 1 pi
        (External.binaryGaloisField_tits_formula_sq 1 pi hpi) hpi x).mp x.property
    have hmat : (SuzukiRootGL 1 a b) ^ 2 = 1 := by
      rw [← hab]
      exact congrArg Subtype.val hx
    rw [hsq] at hmat
    have hab0 := congrArg (fun A : GL (Fin 4) K => (A : Matrix (Fin 4) (Fin 4) K) 0 2) hmat
    have ha0 : a * pi a = 0 := by
      simpa [SuzukiRootGL, SuzukiRootMatrix] using hab0
    have ha : a = 0 := (mul_eq_zero.mp ha0).elim id (fun hh => pi.injective (hh.trans pi.map_zero.symm))
    exact (hz x).mpr ⟨b, ha ▸ hab⟩

theorem root_derived_center : commutator (SuzukiRootClosure 1) = center (SuzukiRootClosure 1) := by
  let K := BinaryGaloisField (2 * 1 + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (1 + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (1 + 1)) :=
    iterateFrobeniusEquiv_def K 2 (1 + 1)
  exact (External.huppert_blackburn_XI_3_1 1 (by omega) pi
    (External.binaryGaloisField_tits_formula_sq 1 pi hpi)).2.2.2.2.2.2.2.2.2.1

theorem sylow_equiv_root {H : Type*} [Group H] [Finite H]
    (e : H ≃* SuzukiMatrixGroup 1) (S : Sylow 2 H) :
    Nonempty (S ≃* SuzukiRootClosure 1) := by
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow 1 (by omega)
  let P' : Sylow 2 H := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H P' S
  let f := e.symm.trans (MulAut.conj g)
  have hf : (SuzukiRootSubgroup 1).map f.toMonoidHom = (S : Subgroup H) := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((P : Subgroup (SuzukiMatrixGroup 1)).map e.symm.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = (S : Subgroup H) at hh
    change (SuzukiRootSubgroup 1).map
      ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
    simpa only [hP, map_map] using hh
  exact ⟨(((SuzukiRootSubgroup 1).equivMapOfInjective f.toMonoidHom f.injective).trans
    (MulEquiv.subgroupCongr hf)).symm.trans (subgroupOfEquivOfLe (suzukiRootClosure_le 1))⟩

theorem sylow_facts {H : Type*} [Group H] [Finite H]
    (e : H ≃* SuzukiMatrixGroup 1) (S : Sylow 2 H) :
    Nat.card S = 64 ∧
      (∀ x : S, x ∈ center S ↔ x ^ 2 = 1) ∧
      (∀ x y : S, ⁅x,y⁆ ^ 2 = 1) := by
  obtain ⟨f⟩ := sylow_equiv_root e S
  refine ⟨?_, ?_, ?_⟩
  · have hc := suzukiRootSubgroup_card 1 (by omega)
    change Nat.card ((SuzukiRootClosure 1).subgroupOf (SuzukiMatrixSubgroup 1)) = _ at hc
    rw [Nat.card_congr (subgroupOfEquivOfLe (suzukiRootClosure_le 1)).toEquiv] at hc
    exact (Nat.card_congr f.toEquiv).trans hc
  · intro x
    constructor
    · intro hx
      apply f.injective
      rw [map_pow, map_one]
      exact (root_center_iff_square (f x)).mp (centerCongr f ⟨x,hx⟩).property
    · intro hx
      have hfx := (root_center_iff_square (f x)).mpr (by rw [← map_pow, hx, map_one])
      have hh := (centerCongr f.symm ⟨f x, hfx⟩).property
      change f.symm (f x) ∈ center S at hh
      simpa only [f.symm_apply_apply] using hh
  · intro x y
    apply f.injective
    rw [map_pow, map_commutatorElement, map_one]
    apply (root_center_iff_square _).mp
    rw [← root_derived_center]
    exact commutator_mem_commutator (mem_top _) (mem_top _)

end CFSG.Quasithin.CoveredSuzukiModel
