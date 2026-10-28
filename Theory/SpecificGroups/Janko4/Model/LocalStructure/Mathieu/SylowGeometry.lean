module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.AdequateLocal.Generation
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.Normalizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore

/-!
# A Mathieu local subgroup adapted to any Janko four Sylow subgroup

The characteristic elementary kernel of max1 makes every automorphism preserving
one of its Sylow images preserve max1. Its odd index lets Sylow conjugacy move
this configuration to any prescribed Sylow subgroup of the actual matrix model.

An element centralizing such a Sylow lies in the embedded elementary kernel.
The certified two kernel orbits leave only the marked pair: the full centralizer
of the other seed has insufficient two-part. The proved max1--pair-centralizer
generation theorem then gives generation for every nonidentity Sylow centralizer
element. No full model order, simplicity, or outer-automorphism premise is used.

Source: GLS3, Table 5.3i, printed p.270; the local generation used in
Aschbacher--Smith, 2.3.9(7), printed p.526. The actual ATLAS matrices and words
retain their attribution in `Cardinality.Subgroup` and the imported certificates.
-/

public section
namespace Janko4.LocalStructure

open Subgroup
open Janko4 Janko4.Cardinality Janko4.Max1AmalgamRigidity

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel
  localX localY localKernelSeed

/-- The actual max1 subgroup is invariant under every automorphism preserving its Sylow image. -/
theorem max1_invariant_of_sylow_image_invariant (P : Sylow 2 M) (alpha : MulAut Model)
    (hP : (P.toSubgroup.map M.subtype).map alpha.toMonoidHom =
      P.toSubgroup.map M.subtype) : M.map alpha.toMonoidHom = M := by
  let U : Subgroup Model := P.toSubgroup.map M.subtype
  let q : P ≃* U := P.toSubgroup.equivMapOfInjective M.subtype M.subtype_injective
  let gamma : MulAut U := (alpha.subgroupMap U).trans (MulEquiv.subgroupCongr hP)
  let u : MulAut P := (q.trans gamma).trans q.symm
  have hu (p : P) : ((u p : M) : Model) = alpha (p : M) := by
    exact congrArg U.subtype (q.apply_symm_apply (gamma (q p)))
  have hKP : K ≤ P.toSubgroup := LocalStructure.localKernel_le_sylow P
  have hchar := LocalStructure.localKernel_sylow_characteristic P
  have hE : E.map alpha.toMonoidHom = E := by
    apply eq_of_le_of_card_ge
    · rintro _ ⟨e, he, rfl⟩
      obtain ⟨k, hk, rfl⟩ := (mem_map (f := M.subtype) (K := K)).mp he
      let p : P := ⟨k, hKP hk⟩
      have hp : u p ∈ K.subgroupOf P.toSubgroup :=
        (characteristic_iff_le_comap.mp hchar u) hk
      exact mem_map.mpr ⟨u p, hp, hu p⟩
    · exact (Nat.card_congr (alpha.subgroupMap E).toEquiv).le
  have hn := E.map_equiv_normalizer_eq alpha
  have hN : normalizer (E : Set Model) = M := by
    apply le_antisymm LocalStructure.normalizer_embedded_localKernel_le_max1
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      K.le_normalizer_map M.subtype
  rwa [hE, hN] at hn

/-- Every nonidentity element centralizing a local Sylow generates the model with max1 through its centralizer. -/
theorem centralizer_sup_max1_of_centralizes_sylow (P : Sylow 2 M) (t : Model) (ht : t ≠ 1)
    (hc : t ∈ centralizer (P.toSubgroup.map M.subtype : Set Model)) :
    centralizer ({t} : Set Model) ⊔ M = ⊤ := by
  have hEP : E ≤ P.toSubgroup.map M.subtype :=
    map_mono (LocalStructure.localKernel_le_sylow P)
  have htE : t ∈ E := by
    have he := centralizer_le hEP hc
    rwa [LocalStructure.centralizer_embedded_localKernel] at he
  obtain ⟨tM, htK, rfl⟩ := (mem_map (f := M.subtype) (K := K)).mp htE
  have htM : tM ≠ 1 := fun he => ht (congrArg M.subtype he)
  obtain ⟨g, hg | hg⟩ := Simplicity.Max1Fusion.kernel_nonidentity_orbits
    matrixA_mul_self matrixB_pow_four tM htK htM
  · have hconj : IsConj (tM : Model) AdequateLocal.Certificates.seed :=
      isConj_iff.mpr ⟨(g : Model), (congrArg M.subtype hg).symm⟩
    have hle : P.toSubgroup.map M.subtype ≤ centralizer ({(tM : Model)} : Set Model) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mpr (hc x hx)
    have hd := card_dvd_of_le hle
    have hcard : Nat.card (P.toSubgroup.map M.subtype) = 2 ^ 21 := by
      rw [card_map_of_injective M.subtype_injective, P.card_eq_multiplicity,
        max1Subgroup_card]
      decide +kernel
    have hseedcard : Nat.card (centralizer ({AdequateLocal.Certificates.seed} : Set Model)) =
        1816657920 := InvolutionCentralizers.Second.ambient_card
    rw [hcard, card_centralizer_eq_of_isConj _ _ hconj, hseedcard] at hd
    norm_num at hd
  · let alpha := MulAut.conj (g : Model)
    have hct : (centralizer ({(tM : Model)} : Set Model)).map alpha.toMonoidHom = C := by
      apply le_antisymm
      · rintro _ ⟨x, hx, rfl⟩
        apply mem_centralizer_singleton_iff.mpr
        have he := congrArg alpha (mem_centralizer_singleton_iff.mp hx)
        have ht' : alpha (tM : Model) = v := (congrArg M.subtype hg).symm
        change alpha x * v = v * alpha x
        simpa only [map_mul, ht'] using he
      · intro x hx
        refine ⟨alpha.symm x, ?_, alpha.apply_symm_apply x⟩
        apply mem_centralizer_singleton_iff.mpr
        apply alpha.injective
        have ht' : alpha (tM : Model) = v := (congrArg M.subtype hg).symm
        simpa only [map_mul, alpha.apply_symm_apply, ht'] using
          mem_centralizer_singleton_iff.mp hx
    have hM : M.map alpha.toMonoidHom = M :=
      mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer g.property)
    change centralizer ({(tM : Model)} : Set Model) ⊔ M = ⊤
    apply (map_injective (f := alpha.toMonoidHom) alpha.injective)
    rw [Subgroup.map_sup, hct, hM, AdequateLocal.centralizer_sup_max1_eq_top]
    exact (map_top_of_surjective _ alpha.surjective).symm

private theorem map_aut_mul (A : Subgroup Model) (alpha beta : MulAut Model) :
    A.map (alpha * beta).toMonoidHom =
      (A.map beta.toMonoidHom).map alpha.toMonoidHom := by
  rw [map_map]
  rfl

/-- An actual max1 conjugate adapted to a prescribed ambient Sylow subgroup, including invariance and generation. -/
theorem exists_sylow_mathieu_seed (R : Sylow 2 Model) :
    ∃ P : Subgroup Model, (R : Subgroup Model) ≤ P ∧
      Nonempty (P ≃* M) ∧
      (∀ alpha : MulAut Model, (R : Subgroup Model).map alpha.toMonoidHom = R →
        P.map alpha.toMonoidHom = P) ∧
      (∀ t : Model, t ≠ 1 → t ∈ centralizer (R : Set Model) →
        centralizer ({t} : Set Model) ⊔ P = ⊤) := by
  let T : Sylow 2 M := default
  let U : Subgroup Model := T.toSubgroup.map M.subtype
  let Q : Sylow 2 Model := (T.isPGroup'.map M.subtype).toSylow
    (AdequateLocal.sylow_image_odd_index T)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model Q R
  let e : MulAut Model := MulAut.conj g
  have he : U.map e.toMonoidHom = R := congrArg Sylow.toSubgroup hg
  let P := M.map e.toMonoidHom
  refine ⟨P, ?_, ⟨(e.subgroupMap M).symm⟩, ?_, ?_⟩
  · rw [← he]
    exact map_mono (map_subtype_le _)
  · intro alpha ha
    let beta : MulAut Model := e⁻¹ * (alpha * e)
    have hbU : U.map beta.toMonoidHom = U := by
      simp only [beta, map_aut_mul, he, ha]
      rw [← he]
      change (U.map e.toMonoidHom).map e.symm.toMonoidHom = U
      simp [map_map]
    have hbM := max1_invariant_of_sylow_image_invariant T beta hbU
    apply map_injective (f := e.symm.toMonoidHom) e.symm.injective
    calc
      (P.map alpha.toMonoidHom).map e.symm.toMonoidHom = M.map beta.toMonoidHom := by
        simp only [beta, map_aut_mul, P, MulAut.inv_def]
      _ = M := hbM
      _ = P.map e.symm.toMonoidHom := by simp [P, map_map]
  · intro t ht hc
    have hne : e.symm t ≠ 1 := by
      intro hh
      apply ht
      apply e.symm.injective
      simpa only [map_one] using hh
    have hc' : e.symm t ∈ centralizer (U : Set Model) := by
      intro u hu
      apply e.injective
      have heu : e u ∈ (R : Subgroup Model) := he ▸ mem_map_of_mem e.toMonoidHom hu
      simpa only [map_mul, e.apply_symm_apply] using hc (e u) heu
    have hgen := centralizer_sup_max1_of_centralizes_sylow T (e.symm t) hne hc'
    apply top_le_iff.mp
    have hm := congrArg (Subgroup.map e.toMonoidHom) hgen
    rw [Subgroup.map_sup, map_top_of_surjective _ e.surjective] at hm
    rw [← hm]
    refine sup_le_sup ?_ le_rfl
    rintro _ ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e x * t = t * e x
    simpa only [map_mul, e.apply_symm_apply] using
      congrArg e (mem_centralizer_singleton_iff.mp hx)

end Janko4.LocalStructure

end
