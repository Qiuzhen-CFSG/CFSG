module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationAction
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Theory.GroupTheory.PResidual.SylowCentralizer

/-!
# The full fixed-core normalizer modulo its actual action kernel

The six-letter normalizer action maps the component onto A6. Its two-residual
therefore lies in the component times the full action kernel. The original
Sylow two-subgroup supplies the quotient. Applying the residual supplement
again to that kernel proves M = LT O^2(C_M(V)). This retains the full
centralizer kernel in both covering rows, and proves its relative normality
and its containment in every original vector centralizer.

FixedModuleAt applies the factorization to the original nonzero fixed part.
The further ordinary assertion that this residual vanishes is not assumed
or asserted here. Source: Aschbacher--Smith 13.4.6(4), printed p.898.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual two-residual of the full normalizer's action kernel. -/
@[expose] def normalizerActionResidual (L V : Subgroup G) : Subgroup G :=
  (pResidual 2 (normalizer (L : Set G) ⊓ centralizer (V : Set G) : Subgroup G)).map
    (normalizer (L : Set G) ⊓ centralizer (V : Set G) : Subgroup G).subtype

/-- The original full normalizer is LT times its full module centralizer. -/
theorem normalizer_sylow_action_kernel_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    normalizer (L : Set G) = (L ⊔ (T : Subgroup G)) ⊔
      (normalizer (L : Set G) ⊓ centralizer (V : Set G)) := by
  let M := normalizer (L : Set G)
  let C := M ⊓ centralizer (V : Set G)
  let S := T.subtype D.sylow_normalizes_component
  obtain ⟨q,_,hqL,hker⟩ := Nonsolvable.exists_core_normalizer_permutation D m
    (normalizer_component_le_module_at h structural D m)
  have hr : (pResidual 2 M).map M.subtype ≤ L ⊔ C := by
    rintro x ⟨a,ha,rfl⟩
    have hqa : q a ∈ alternatingGroup (Fin 6) := by
      rw [←Equiv.Perm.twoResidual_eq_alternating]
      exact map_pResidual_le 2 q (mem_map_of_mem q ha)
    obtain ⟨v,hv⟩ := m.quotient.surjective ⟨q a,hqa⟩
    obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective _ v
    let li : M := inclusion L.le_normalizer l
    have he : q li = q a := (hqL l).trans (congrArg Subtype.val hv)
    have hk : li⁻¹ * a ∈ q.ker := by
      rw [MonoidHom.mem_ker,map_mul,map_inv,he,inv_mul_cancel]
    have hc : (li⁻¹ * a).val ∈ C := ⟨(li⁻¹ * a).property,by
      rw [hker] at hk
      exact hk⟩
    have hh := (L ⊔ C).mul_mem (mem_sup_left l.property) (mem_sup_right hc)
    change l.val * (l.val⁻¹ * a.val) ∈ L ⊔ C at hh
    change a.val ∈ L ⊔ C
    simpa only [mul_inv_cancel_left] using hh
  have hs := congrArg (map M.subtype) (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hs
  have hS : (S : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le D.sylow_normalizes_component
  rw [hS] at hs
  apply le_antisymm ?_ (sup_le (sup_le L.le_normalizer D.sylow_normalizes_component) inf_le_left)
  change M ≤ (L ⊔ (T : Subgroup G)) ⊔ C
  rw [←hs]
  exact sup_le (hr.trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
    (le_sup_right.trans le_sup_left)

/-- Retain the exact remaining normalizer residual, with normality in M
and point-centralizer containment proved on the original embedded groups. -/
theorem normalizer_action_residual_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    normalizer (L : Set G) = (L ⊔ (T : Subgroup G)) ⊔ normalizerActionResidual L V ∧
      normalizer (L : Set G) ≤ normalizer (normalizerActionResidual L V : Set G) ∧
      normalizerActionResidual L V ≤ centralizer (V : Set G) ∧
      IsPPerfect 2 (normalizerActionResidual L V) ∧
      ∀ z ∈ V, normalizerActionResidual L V ≤ centralizer ({z} : Set G) := by
  let M := normalizer (L : Set G)
  let C := M ⊓ centralizer (V : Set G)
  have hnC : M ≤ normalizer (C : Set G) :=
    (le_inf M.le_normalizer ((normalizer_component_le_module_at h structural D m).trans
      (normalizer_le_normalizer_centralizer V))).trans inf_normalizer_le_normalizer_inf
  have hsup := embedded_pResidual_sup_sylow_of_normalizes T C
    (D.sylow_normalizes_component.trans hnC)
  have hMC := normalizer_sylow_action_kernel_at h structural D m
  change M = (L ⊔ (T : Subgroup G)) ⊔ C at hMC
  have he : M = (L ⊔ (T : Subgroup G)) ⊔ normalizerActionResidual L V := by
    change M = (L ⊔ (T : Subgroup G)) ⊔ (pResidual 2 C).map C.subtype
    calc
      M = L ⊔ (C ⊔ (T : Subgroup G)) := by
        simpa only [sup_assoc,sup_comm (T : Subgroup G) C] using hMC
      _ = L ⊔ ((pResidual 2 C).map C.subtype ⊔ (T : Subgroup G)) := by rw [hsup]
      _ = _ := by rw [sup_assoc,sup_comm (T : Subgroup G)]
  have hYC : normalizerActionResidual L V ≤ C := map_subtype_le _
  refine ⟨he,hnC.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C)),
    hYC.trans inf_le_right,?_,?_⟩
  · exact isPPerfect_embedded_pResidual 2 C
  · intro z hz
    exact (hYC.trans inf_le_right).trans (centralizer_le (Set.singleton_subset_iff.mpr hz))

/-- The remaining normalizer residual acts trivially on the actual central
quotient of L; the full central core is retained in either covering row. -/
theorem normalizer_action_residual_commutator_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    ⁅L,normalizerActionResidual L V⁆ ≤
      (Section08.TransvectionRecognition.Component.ModelExtension.centralCore L).map L.subtype := by
  let M := normalizer (L : Set G)
  let Y := normalizerActionResidual L V
  have hYC : Y ≤ M ⊓ centralizer (V : Set G) := map_subtype_le _
  have hYL : Y ≤ M := hYC.trans inf_le_left
  have hcomm : ⁅L,Y⁆ ≤ L := le_normalizer_iff_commutator_le_left.mp hYL
  obtain ⟨q,_,hqL,hker⟩ := Nonsolvable.exists_core_normalizer_permutation D m
    (normalizer_component_le_module_at h structural D m)
  apply commutator_le.mpr
  intro l hl y hy
  let k : L := ⟨⁅l,y⁆,hcomm (commutator_mem_commutator hl hy)⟩
  let a : M := ⟨l,L.le_normalizer hl⟩
  let b : M := ⟨y,hYL hy⟩
  have hqb : q b = 1 := by
    have hb : b ∈ q.ker := by rw [hker]; exact (hYC hy).2
    exact hb
  have hkq : q (inclusion L.le_normalizer k) = 1 := by
    have he : inclusion L.le_normalizer k = ⁅a,b⁆ := Subtype.ext rfl
    rw [he,map_commutatorElement,hqb]
    simp
  have hk : k ∈ Section08.TransvectionRecognition.Component.ModelExtension.centralCore L := by
    apply (QuotientGroup.eq_one_iff k).mp
    apply m.quotient.map_eq_one_iff.mp
    apply Subtype.ext
    exact (hqL k).symm.trans hkq
  exact mem_map_of_mem L.subtype hk

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
