module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingCoreSource
public import Theory.GroupAction.ModelConjugation
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.CrossingPairCentralizer

/-!
# Centralizer generation on the literal crossing component

The disjoint original two-cores make the crossing-core action faithful on
the prescribed component model. Model fixed-subgroup generation therefore
lifts to the join of actual component centralizers. Normality in the
original involution centralizers makes the crossed components normalize
each other; they are distinct by core disjointness and hence commute.

Source: Aschbacher--Smith 2.5.21, printed p.566.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
omit [Finite G] in
theorem normalizes_crossing_of_centralizer_generation
    (K C : Subgroup G) (x : G)
    (hnormal : ∀ i ∈ C, orderOf i = 2 → centralizer ({i} : Set G) ≤ normalizer (K : Set G))
    (hgen : K ≤ ⨆ (j : G) (_ : j ∈ C.conjBy x⁻¹) (_ : orderOf j = 2),
      K ⊓ centralizer ({j} : Set G)) :
    K ≤ normalizer (K.conjBy x⁻¹ : Set G) := by
  apply hgen.trans
  refine iSup_le fun j => iSup_le fun hj => iSup_le fun hj2 => ?_
  obtain ⟨i, hi, hij⟩ := hj
  have hi2 : orderOf i = 2 := by
    have he := (MulAut.conj x⁻¹).orderOf_eq i
    change MulAut.conj x⁻¹ i = j at hij
    rw [hij, hj2] at he
    exact he.symm
  have h := CrossingPair.crossing_factor_normalized K i x (hnormal i hi hi2)
  have hij' : x⁻¹ * i * x = j := by simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hij
  rw [hij'] at h
  exact inf_le_right.trans h

theorem MathieuSourceSetup.crossing_centralizer_generation_of_model
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    {Q : Type*} [Group Q] (eK : K ≃* Q)
    (x : G) (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hx2 : x ^ 2 ∈ (S : Subgroup H).map H.subtype)
    (hmodel : ∀ (a : ((twoCore H).conjBy x⁻¹) →* MulAut Q),
      Function.Injective a → ∀ N : Subgroup Q,
      (∀ i : (twoCore H).conjBy x⁻¹, orderOf i = 2 → (a i).fixedSubgroup ≤ N) → N = ⊤) :
    K ≤ ⨆ (j : G) (_ : j ∈ (twoCore H).conjBy x⁻¹) (_ : orderOf j = 2),
      K ⊓ centralizer ({j} : Set G) := by
  let Y := (S : Subgroup H).map H.subtype
  let D := (twoCore H).conjBy x⁻¹
  let W : Subgroup G := ⨆ (j : G) (_ : j ∈ D) (_ : orderOf j = 2),
    K ⊓ centralizer ({j} : Set G)
  have hc := MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  have hCY : twoCore H ≤ Y := hc ▸ inf_le_left
  have hDY : D ≤ Y := by
    have hy : Y.conjBy x⁻¹ = Y :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (Y : Set G)).inv_mem hxN)
    exact (map_mono hCY).trans hy.le
  have hDK : D ≤ normalizer (K : Set G) := hDY.trans ((map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance))
  let a := Theory.GroupAction.ModelConjugation.action D K hDK eK
  have hai : Function.Injective a := by
    apply (injective_iff_map_eq_one a).mpr
    intro d hd
    have hh : d ∈ a.ker := hd
    rw [Theory.GroupAction.ModelConjugation.action_ker] at hh
    have hdC : (d : G) ∈ twoCore H := hc ▸ ⟨hDY d.property, hh⟩
    have hdis := (generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c)
      ⟨c.component_le,c.component⟩ hgen hxT hxS hxN hx2).1
    exact Subtype.ext (disjoint_def.mp hdis hdC d.property)
  let f : Q →* G := K.subtype.comp eK.symm.toMonoidHom
  have hN : W.comap f = ⊤ := by
    apply hmodel a hai
    intro d hd b hb
    have he : a d b = b := (MulAut.mem_fixedSubgroup _ _).mp hb
    change eK (K.normalizerMonoidHom (inclusion hDK d) (eK.symm b)) = b at he
    have hc' : (d : G) * (eK.symm b : G) * (d : G)⁻¹ = (eK.symm b : G) := by
      have hh := congrArg (fun k : K => (k : G)) (eK.injective (he.trans (eK.apply_symm_apply b).symm))
      exact hh
    have hd2 : orderOf (d : G) = 2 := (orderOf_coe d).trans hd
    have hw : K ⊓ centralizer ({(d : G)} : Set G) ≤ W :=
      le_iSup_of_le (d : G) (le_iSup_of_le d.property (le_iSup_of_le hd2 le_rfl))
    exact hw ⟨(eK.symm b).property, mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp hc').symm⟩
  intro k hk
  have hh : eK ⟨k,hk⟩ ∈ W.comap f := hN ▸ mem_top _
  change (eK.symm (eK ⟨k,hk⟩) : G) ∈ W at hh
  simpa only [eK.symm_apply_apply] using hh


/-- Mutual source conjugacy turns normalization into commutation of distinct components. -/
theorem MathieuSourceSetup.crossing_commutes_of_normalizes
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hC : twoCore H ≠ ⊥)
    (x : G) (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hx2 : x ^ 2 ∈ (S : Subgroup H).map H.subtype)
    (hKN : K ≤ normalizer (K.conjBy x⁻¹ : Set G)) : ⁅K, K.conjBy x⁻¹⁆ = ⊥ := by
  let Y := (S : Subgroup H).map H.subtype
  let L := K.conjBy x⁻¹
  let C := twoCore H
  have hYL : Y ≤ normalizer (K : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  have hLL : L.conjBy x⁻¹ = K := by
    change (K.conjBy x⁻¹).conjBy x⁻¹ = K
    rw [conjBy_conjBy]
    have hx : x⁻¹ * x⁻¹ ∈ normalizer (K : Set G) := by
      have h : (x ^ 2)⁻¹ ∈ normalizer (K : Set G) := (normalizer (K : Set G)).inv_mem (hYL hx2)
      simpa only [pow_two, mul_inv_rev] using h
    exact mem_normalizer_iff_map_conj_eq.mp hx
  have hLN : L ≤ normalizer (K : Set G) := by
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hKN
    rw [map_equiv_normalizer_eq] at hh
    exact hLL ▸ hh
  have hneq : K ≠ L := by
    intro he
    have hc := MathieuSourceSetup.core_eq_sylow_centralizer c hgen
    have hcx : C.conjBy x⁻¹ = C := by
      change (twoCore H).conjBy x⁻¹ = twoCore H
      rw [hc]
      exact (CrossingPair.sylow_centralizer_crossing K Y x hxN).symm.trans
        (by change Y ⊓ centralizer (L : Set G) = Y ⊓ centralizer (K : Set G); rw [←he])
    have hd := (generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c)
      ⟨c.component_le,c.component⟩ hgen hxT hxS hxN hx2).1
    rw [hcx] at hd
    exact hC (disjoint_self.mp hd)
  let : IsQuasisimple K := (show IsComponentIn K H from ⟨c.component_le,c.component⟩).quasisimple
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv ((MulAut.conj x⁻¹).subgroupMap K)
  have hKJ : IsComponentIn K (K ⊔ L) := by
    refine ⟨le_sup_left, ?_, IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe le_sup_left).symm⟩
    exact ((normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le K.le_normalizer hLN)).isSubnormal
  have hLJ : IsComponentIn L (K ⊔ L) := by
    refine ⟨le_sup_right, ?_, IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe le_sup_right).symm⟩
    exact ((normal_subgroupOf_iff_le_normalizer le_sup_right).mpr (sup_le hKN L.le_normalizer)).isSubnormal
  exact hKJ.commutator_eq_bot_of_ne hLJ hneq

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
