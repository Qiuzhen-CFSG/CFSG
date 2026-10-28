module

public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The component marking on a reduced noncentral module

If a normal subgroup has centerless quasisimple quotient by its two-core,
its nontrivial action on a reduced normal elementary module has precisely
that two-core as kernel. The induced isomorphism retains the actual quotient
map, so model markings can be transferred to a chosen reduced submodule.

Source: the reduced-module comparison in Aschbacher--Smith B.2.10 and
15.1.27--28, printed pp.77 and 1102--1103.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]
variable (W K : Subgroup G) [W.Normal] [K.Normal]
variable (hr : IsPReduced 2 W) [IsQuasisimple (K ⧸ pCore 2 K)]
variable (hz : center (K ⧸ pCore 2 K) = ⊥) (hm : ⁅W,K⁆ ≠ ⊥)

include hr hz hm

/-- The chosen reduced module detects the whole centerless component quotient. -/
theorem reduced_quasisimple_subgroupMap_ker :
    ((QuotientGroup.mk' (centralizer (W : Set G))).subgroupMap K).ker = pCore 2 K := by
  let C := centralizer (W : Set G)
  let q := QuotientGroup.mk' C
  let f := q.subgroupMap K
  have hcore : pCore 2 K ≤ f.ker := by
    have hpc : (pCore 2 K).map K.subtype ≤ pCore 2 G :=
      le_sSup ⟨inferInstance, pCore_isPGroup.map K.subtype⟩
    have hc := hpc.trans (le_centralizer_iff.mp hr.le_centralizer_pCore)
    intro k hk
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (N := C) (k : G)).mpr
      (hc (mem_map_of_mem K.subtype hk))
  let a := QuotientGroup.lift (pCore 2 K) f hcore
  have hker : a.ker = ⊥ := by
    rcases IsQuasisimple.normal_le_center_or_eq_top a.ker with hc | ht
    · exact bot_unique (hc.trans hz.le)
    · exfalso
      apply hm
      rw [commutator_comm]
      apply commutator_eq_bot_iff_le_centralizer.mpr
      intro k hk
      have he : a (QuotientGroup.mk' (pCore 2 K) (⟨k,hk⟩ : K)) = 1 :=
        ht.ge (mem_top _)
      have he' : q k = 1 := congrArg Subtype.val he
      exact (QuotientGroup.eq_one_iff (N := C) k).mp he'
  refine le_antisymm ?_ hcore
  intro k hk
  have ha : a (QuotientGroup.mk' (pCore 2 K) k) = 1 := hk
  exact (QuotientGroup.eq_one_iff k).mp (mem_bot.mp (hker.le ha))

/-- The isomorphism to the literal image on the specified reduced module. -/
@[expose] noncomputable def reducedQuasisimpleImageEquiv :
    (K ⧸ pCore 2 K) ≃* K.map (QuotientGroup.mk' (centralizer (W : Set G))) :=
  (QuotientGroup.quotientMulEquivOfEq
    (reduced_quasisimple_subgroupMap_ker W K hr hz hm).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      ((QuotientGroup.mk' (centralizer (W : Set G))).subgroupMap K)
      ((QuotientGroup.mk' (centralizer (W : Set G))).subgroupMap_surjective K))

/-- The component marking sends each original element through the original map. -/
@[simp] theorem reducedQuasisimpleImageEquiv_apply (k : K) :
    reducedQuasisimpleImageEquiv W K hr hz hm (QuotientGroup.mk' (pCore 2 K) k) =
      (QuotientGroup.mk' (centralizer (W : Set G))).subgroupMap K k := by
  rfl

end Theory.GroupTheory
