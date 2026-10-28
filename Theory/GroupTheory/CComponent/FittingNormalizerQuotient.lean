module
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreOvergroup
public import Theory.GroupTheory.Fitting.TwoCorePreimage
public import Theory.GroupTheory.CComponent.InvolutionCore
public import Theory.GroupTheory.PCoreFrattiniTransport
/-!
# Quasisimple quotients from Fitting normalization

Suppose a finite group is a C-component and its Fitting preimage modulo O₂
normalizes a subgroup whose own quotient modulo O₂ is quasisimple. Then the
ambient quotient modulo O₂ is quasisimple as well. Otherwise that quotient
has trivial component layer. The subgroup image has a normalizer containing
the generalized Fitting subgroup and hence with trivial two-core. Its
quasisimple quotient therefore becomes an ordinary component, which promotes
to the ambient quotient, a contradiction.

This supplies the quotient prerequisite in the C.2.6/C.2.7 application of
Aschbacher–Smith, Lemma 10.2.6, printed pp.748–749.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- Fitting normalization of a subgroup with quasisimple two-core quotient
forces the ambient C-component quotient to be quasisimple. -/
theorem quasisimple_quotient_of_fitting_normalizes
    (hG : (⊤ : Subgroup G).IsCComponent) (B : Subgroup G)
    (hB : IsQuasisimple (B ⧸ pCore 2 B))
    (hF : twoFittingCore G ≤ normalizer (B : Set G)) :
    IsQuasisimple (G ⧸ pCore 2 G) := by
  classical
  let Q := G ⧸ pCore 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  have htop : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      hG.map_quotient (pCore 2 G)
  by_contra hn
  have hE : componentLayer Q = ⊥ := by
    apply bot_unique
    apply sSup_le
    intro A hA
    have he' : A = ⊤ := hA.isCComponent.eq_of_le htop le_top
    let := hA.2
    exact (hn (IsQuasisimple.of_mulEquiv
      ((MulEquiv.subgroupCongr he').trans topEquiv))).elim
  have hfit : generalizedFitting Q = fittingSubgroup Q := by
    rw [generalizedFitting,hE,sup_bot_eq]
  let P := B.map q
  let C := normalizer (P : Set Q)
  have hFC : generalizedFitting Q ≤ C := by
    rw [hfit]
    have hh := map_mono (f := q) hF
    have hmap : (twoFittingCore G).map q = fittingSubgroup Q :=
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
    rw [hmap] at hh
    exact hh.trans (B.le_normalizer_map q)
  have hC2 : pCore 2 C = ⊥ :=
    twoCore_eq_bot_of_generalizedFitting_le C hFC (pCore_quotient_pCore_eq_bot 2)
  have hPC : P ≤ C := P.le_normalizer
  let A := P.subgroupOf C
  let : A.Normal := normal_in_normalizer
  let e : A ≃* P := subgroupOfEquivOfLe hPC
  have hA2 : pCore 2 A = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : A.Normal).isSubnormal,hC2]
    ext x
    change (x : C) = 1 ↔ x = 1
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have hP2 : pCore 2 P = ⊥ := by
    have hh := pCore_map_iso 2 e
    rw [hA2,Subgroup.map_bot] at hh
    exact hh.symm
  have hk : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eqv := (q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hk
  let := hB
  let : IsQuasisimple P := IsQuasisimple.of_mulEquiv
    (eqv.trans ((QuotientGroup.quotientMulEquivOfEq hP2).trans QuotientGroup.quotientBot))
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv e.symm
  have hcomp : IsComponent Q P := IsComponent.of_generalizedFitting_overgroup hPC
    ⟨(inferInstance : A.Normal).isSubnormal,inferInstance⟩ hFC
  have hPbot : P = ⊥ := bot_unique
    ((show P ≤ componentLayer Q from le_sSup hcomp).trans hE.le)
  exact hcomp.isCComponent.ne_bot hPbot
end Theory.GroupTheory
