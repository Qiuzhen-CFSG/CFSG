module

public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import Theory.GroupTheory.CComponent.SixCoverTheta

/-!
# The actual theta of the normalizer in the A₆ source branch

Source 1.2.7 places the original L as a C-component in its maximal two-local
normalizer. Only this local group is strongly quasithin, so the rank bound
is applied there. The original central A₆ quotient then gives theta(N(L))=L
by the ordinary/triple-cover calculation. The last result is the literal
monotonicity used for point-centralizing subgroups in 13.3.9.

Theorem A and Theorem C remain genuine earlier inputs. If T-normalization
has already been constructed, this argument does not need structural 12.2.2.
Source: Aschbacher--Smith, 12.2.8 and 13.3.9, printed pp.797 and 887.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G}

private def centerQuotientCongr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro y hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

omit [Finite G] in
private theorem map_cubic_closure (M : Subgroup G) :
    (closure {x : M | orderOf x=3}).map M.subtype =
      closure {x : G | x ∈ M ∧ orderOf x=3} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.property,(M.orderOf_coe y).trans hy⟩
  · rintro ⟨hx,h3⟩
    exact ⟨⟨x,hx⟩,(M.orderOf_coe ⟨x,hx⟩).symm.trans h3,rfl⟩

private noncomputable def twoCoreCentralQuotientEquiv (A : Type*) [Group A] :
    ((A ⧸ pCore 2 A) ⧸ center (A ⧸ pCore 2 A)) ≃*
      (A ⧸ (center (A ⧸ pCore 2 A)).comap (QuotientGroup.mk' (pCore 2 A))) := by
  let f := (QuotientGroup.mk' (center (A ⧸ pCore 2 A))).comp
    (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp
    (QuotientGroup.mk'_surjective _)
  have hk : f.ker = (center (A ⧸ pCore 2 A)).comap (QuotientGroup.mk' (pCore 2 A)) := by
    ext a
    simp [f]
  exact (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hk)

namespace Hypothesis1221
variable (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
variable (hT : (T : Subgroup G) ≤ normalizer (L : Set G))
variable (hA : ∀ (X : Type u) [Group X] [Finite X],
  ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
variable (hC : ∀ (X : Type u) [Group X] [Finite X],
  ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
include h hT hA hC

theorem source_theta_eq_of_central_quotient_six
    (e : ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃*
      alternatingGroup (Fin 6)) :
    closure {x : G | x ∈ normalizer (L : Set G) ∧ orderOf x=3}=L := by
  let M := normalizer (L : Set G)
  let D := L.subgroupOf M
  let : D.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  let eD : (D ⧸ pCore 2 D) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ (subgroupOfEquivOfLe L.le_normalizer) (pCore_map_iso 2 _)
  let : IsQuasisimple (D ⧸ pCore 2 D) := IsQuasisimple.of_mulEquiv eD.symm
  have he := SixCComponentTheta.cubic_closure_eq_of_central_quotient_six D
    (h.sylow_normalized_component hT hA hC) ((centerQuotientCongr eD).trans e)
    ((h.sylow_normalized_sqtk hT hA hC).stronglyQuasithin 3 Nat.prime_three (by decide))
  have hm := congrArg (map M.subtype) he
  rw [map_cubic_closure, map_subgroupOf_eq_of_le L.le_normalizer] at hm
  exact hm

theorem source_theta_eq_of_six_action_quotient
    (e : (L ⧸ (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L))) ≃*
      alternatingGroup (Fin 6)) :
    closure {x : G | x ∈ normalizer (L : Set G) ∧ orderOf x=3}=L :=
  h.source_theta_eq_of_central_quotient_six hT hA hC
    ((twoCoreCentralQuotientEquiv L).trans e)

theorem source_theta_le_of_subgroup_normalizer_six
    (e : ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃*
      alternatingGroup (Fin 6)) {Y : Subgroup G}
    (hY : Y ≤ normalizer (L : Set G)) :
    closure {x : G | x ∈ Y ∧ orderOf x=3} ≤ L := by
  rw [←h.source_theta_eq_of_central_quotient_six hT hA hC e]
  exact Subgroup.closure_mono fun _ hx => ⟨hY hx.1,hx.2⟩
end Hypothesis1221
end CFSG.Quasithin.Chapter12.Section02
