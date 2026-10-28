module
public import Theory.GroupTheory.CentralizerSmallKernelTransport
import all Theory.GroupTheory.CentralizerSmallKernelTransport
public import Mathlib.GroupTheory.Sylow

/-!
# Extremal representatives in a prescribed Sylow subgroup

An element of prime-power order has a conjugate y in any chosen Sylow S
such that C_S(y) is Sylow in C_G(y). Choose a Sylow of C_G(x), containing
its central element x, extend it to an ambient Sylow, and conjugate that
Sylow to S. Maximality in the conjugated centralizer gives the assertion.
The internal import exposes only the implementation of the restricted
centralizer equivalence used in this transport.

Source application: Aschbacher–Smith 14.2.17(1), printed pp.986–987,
with G here equal to the source point centralizer.
-/

public section
open Subgroup
open scoped Pointwise
namespace Sylow
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- An element of prime-power order has a conjugate in any prescribed Sylow
whose centralizer there is Sylow in the full element centralizer. -/
theorem exists_isConj_with_centralizer_sylow
    (S : Sylow p G) (x : G) (n : ℕ) (hx : orderOf x = p^n) :
    ∃ y : S, IsConj x (y:G) ∧
      ∃ P : Sylow p (centralizer ({(y:G)} : Set G)),
        (P : Subgroup (centralizer ({(y:G)} : Set G))) =
          (S : Subgroup G).subgroupOf (centralizer ({(y:G)} : Set G)) := by
  let C := centralizer ({x} : Set G)
  let xC : C := ⟨x,mem_centralizer_singleton_iff.mpr rfl⟩
  have hxC : xC ∈ center C := by
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (mem_centralizer_singleton_iff.mp c.property)
  have hZ : zpowers xC ≤ center C := zpowers_le.mpr hxC
  let : (zpowers xC).Normal := ⟨by
    intro y hy c
    rw [mem_center_iff.mp (hZ hy) c,mul_inv_cancel_right]
    exact hy⟩
  have hzp : IsPGroup p (zpowers xC) := IsPGroup.of_card (n:=n) (by
    rw [Nat.card_zpowers,←orderOf_coe]
    exact hx)
  let P : Sylow p C := Classical.choice inferInstance
  have hxP : xC ∈ P := hzp.le_sylow_of_normal P (mem_zpowers xC)
  obtain ⟨R,hPR⟩ := (P.isPGroup'.map C.subtype).exists_le_sylow
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq G R S
  let f := MulAut.conj b
  have hmap : (R : Subgroup G).map f.toMonoidHom = S := congrArg Sylow.toSubgroup hb
  have hxR : x ∈ R := hPR (mem_map_of_mem C.subtype hxP)
  have hy : f x ∈ (S : Subgroup G) := by
    rw [←hmap]
    exact mem_map_of_mem f.toMonoidHom hxR
  let e := Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv f x
  let P' : Sylow p (centralizer ({f x} : Set G)) := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  have hle : (P' : Subgroup (centralizer ({f x} : Set G))) ≤
      (S : Subgroup G).subgroupOf (centralizer ({f x} : Set G)) := by
    rintro c ⟨a,ha,rfl⟩
    change f (a:G) ∈ (S : Subgroup G)
    rw [←hmap]
    exact mem_map_of_mem f.toMonoidHom (hPR (mem_map_of_mem C.subtype ha))
  refine ⟨⟨f x,hy⟩,isConj_iff.mpr ⟨b,rfl⟩,P',?_⟩
  exact (P'.is_maximal' (S.isPGroup'.comap_subtype) hle).symm
end Sylow
