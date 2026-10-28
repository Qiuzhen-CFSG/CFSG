module
public import Theory.SpecificGroups.SymmetricThreeProduct.Parabolics.Intermediate
/-!
# The core quotient of an intermediate Omega subgroup

Transporting the two coordinate parabolics through conjugation and the
specified ambient isomorphism identifies every strict proper Sylow
overgroup modulo its two-core with S₃. Source: Aschbacher--Smith15.2.5,
printed pp.1107--1108.
-/
public section
open Subgroup
namespace SymmetricThreeProduct
variable {D : Type*} [Group D] [Finite D]
theorem intermediate_core_quotient (e : D ≃* G) (S : Sylow 2 D) (A : Subgroup D)
    (hSA : (S : Subgroup D) < A) (hA : A ≠ ⊤) :
    Nonempty ((A ⧸ pCore 2 A) ≃* S3) := by
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let B := e.mapSubgroup A
  have hPB : (P : Subgroup G) < B := e.mapSubgroup.strictMono hSA
  have hB : B ≠ ⊤ := by
    intro he
    exact hA (e.mapSubgroup.injective (he.trans e.mapSubgroup.map_top.symm))
  let j : A ≃* B := e.subgroupMap A
  rcases strict_intermediate_over_sylow P B hPB hB with hk | hk
  · obtain ⟨k⟩ := hk
    let a := j.trans k
    exact ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans leftCoreQuotientEquiv⟩
  · obtain ⟨k⟩ := hk
    let a := j.trans k
    exact ⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans rightCoreQuotientEquiv⟩
end SymmetricThreeProduct
