module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.ElementaryCore.Families
public import Theory.Frattini.PGroupMap
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.Alternating.theorem_5_2_1_2

/-!
# Frattini and omega reduction for the elementary core

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Lemma 2.5.24, printed p.568. This module proves the Frattini and omega
reduction in the elementary-core branch. The
faithful action on the actual Sylow image is used throughout; the marked
cyclic-four subgroup is lifted back through the actual kernel rather than
identified only in a quotient. The commutator supplies Y inside Φ(S),
and the kernel gives the complementary factor Φ_C. Squares then calculate
the iterated Frattini subgroup. The modular centralizer bounds the omega
image by a four-group. Finally, crossing disjointness makes the conjugate
core inject into that image, giving the rank bound and the equality case.
-/

@[expose] public section

open Subgroup AlternatingSix.ShadowLocal
open scoped commutatorElement
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore
open AlternatingSix.ShadowLocal.Identification
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

private theorem model_cyclicFour_le_commutator_inner :
    AlternatingSix.ShadowLocal.Holomorph.cyclicFour ≤
      ⁅AlternatingSix.ShadowLocal.Holomorph.innerD,
        (⊤ : Subgroup AlternatingSix.ShadowLocal.Holomorph.Model)⁆ := by
  rw [AlternatingSix.ShadowLocal.Holomorph.cyclicFour]
  apply zpowers_le.mpr
  have h : ⁅AlternatingSix.ShadowLocal.Holomorph.reflection,
      AlternatingSix.ShadowLocal.Holomorph.rotation⁆ =
      AlternatingSix.ShadowLocal.Holomorph.rotation ^ 6 := by
    decide +kernel
  have hc := Subgroup.commutator_mem_commutator
    (subset_closure (show AlternatingSix.ShadowLocal.Holomorph.reflection ∈
      ({AlternatingSix.ShadowLocal.Holomorph.rotation ^ 2,
        AlternatingSix.ShadowLocal.Holomorph.reflection} :
          Set AlternatingSix.ShadowLocal.Holomorph.Model) by simp))
    (show AlternatingSix.ShadowLocal.Holomorph.rotation ∈
      (⊤ : Subgroup AlternatingSix.ShadowLocal.Holomorph.Model) by trivial)
  rw [h] at hc
  have hr : AlternatingSix.ShadowLocal.Holomorph.rotation ^ 2 =
      (AlternatingSix.ShadowLocal.Holomorph.rotation ^ 6) ^ 3 := by
    decide +kernel
  rw [hr]
  exact Subgroup.pow_mem _ hc 3

private theorem cyclicFour_le_commutator_inner (P : Sylow 2 AutA6) :
    SylowGeometry.cyclicFour P ≤
      ⁅sylowInner P, (⊤ : Subgroup P)⁆ := by
  intro a ha
  rw [SylowGeometry.cyclicFour] at ha
  have ha' : (sylowEquiv P).symm a ∈
      AlternatingSix.ShadowLocal.Holomorph.cyclicFour :=
    Subgroup.mem_map_equiv.mp ha
  have h := model_cyclicFour_le_commutator_inner ha'
  have hm : a ∈
      (⁅AlternatingSix.ShadowLocal.Holomorph.innerD,
        (⊤ : Subgroup AlternatingSix.ShadowLocal.Holomorph.Model)⁆).map
          (sylowEquiv P).toMonoidHom :=
    Subgroup.mem_map_equiv.mpr h
  rw [Subgroup.map_commutator,
    map_top_of_surjective _ (sylowEquiv P).surjective] at hm
  simpa only [← AlternatingSix.ShadowLocal.Identification.sylowEquiv_innerD] using hm

private theorem model_center_innerD_le_cyclicFour (y :
    AlternatingSix.ShadowLocal.Holomorph.innerD)
    (hy : y ∈ center AlternatingSix.ShadowLocal.Holomorph.innerD) :
    (y : AlternatingSix.ShadowLocal.Holomorph.Model) ∈
      AlternatingSix.ShadowLocal.Holomorph.cyclicFour := by
  rw [AlternatingSix.ShadowLocal.Holomorph.mem_cyclicFour]
  rw [mem_center_iff] at hy
  revert y
  simp [AlternatingSix.ShadowLocal.Holomorph.mem_innerD]
  decide +kernel

private theorem center_inner_le_cyclicFour (P : Sylow 2 AutA6) :
    (center (sylowInner P)).map (sylowInner P).subtype ≤
      SylowGeometry.cyclicFour P := by
  intro a ha
  rcases Subgroup.mem_map.mp ha with ⟨b, hb, rfl⟩
  have hbP : (b : P) ∈
      AlternatingSix.ShadowLocal.Holomorph.innerD.map (sylowEquiv P).toMonoidHom := by
    rw [sylowEquiv_innerD P]
    exact b.property
  obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hbP
  let yD : AlternatingSix.ShadowLocal.Holomorph.innerD := ⟨y, hy⟩
  have hycenter : yD ∈ center AlternatingSix.ShadowLocal.Holomorph.innerD := by
    rw [mem_center_iff]
    intro w
    have hw' : (sylowEquiv P w : P) ∈ sylowInner P := by
      rw [← sylowEquiv_innerD P]
      exact Subgroup.mem_map_of_mem (sylowEquiv P).toMonoidHom w.property
    have hc := (mem_center_iff.mp hb) ⟨sylowEquiv P w, hw'⟩
    apply Subtype.ext
    have hyb : (sylowEquiv P).symm (b : P) = y := by
      apply (sylowEquiv P).injective
      simpa using hye.symm
    simpa [yD, hyb] using congrArg (fun z : P => (sylowEquiv P).symm z)
      (congrArg Subtype.val hc)
  have hycyc := model_center_innerD_le_cyclicFour yD hycenter
  have hbcyc : (b : P) ∈
      (AlternatingSix.ShadowLocal.Holomorph.cyclicFour.map
        (sylowEquiv P).toMonoidHom) := ⟨y, hycyc, hye⟩
  change (b : P) ∈
    AlternatingSix.ShadowLocal.Holomorph.cyclicFour.map
      (sylowEquiv P).toMonoidHom
  exact hbcyc

private theorem model_omega_bound :
    omegaOneAmbient (centralizer (AlternatingSix.ShadowLocal.Holomorph.cyclicFour :
      Set AlternatingSix.ShadowLocal.Holomorph.Model)) ≤
      AlternatingSix.ShadowLocal.Holomorph.centralTwo ⊔
        AlternatingSix.ShadowLocal.Holomorph.transpositionSubgroup := by
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro x hx hx2
  rw [mem_centralizer_iff] at hx
  rw [AlternatingSix.ShadowLocal.Holomorph.mem_centralTwo_sup_transposition]
  revert x
  simp [AlternatingSix.ShadowLocal.Holomorph.mem_cyclicFour]
  decide +kernel

private theorem sylow_omega_bound (P : Sylow 2 AutA6) :
    omegaOneAmbient (centralizer (SylowGeometry.cyclicFour P : Set P)) ≤
      center P ⊔ SylowGeometry.transpositionSubgroup P := by
  intro x hx
  have hcent :
      (centralizer (AlternatingSix.ShadowLocal.Holomorph.cyclicFour :
        Set AlternatingSix.ShadowLocal.Holomorph.Model)).map
          (sylowEquiv P).toMonoidHom =
        centralizer (SylowGeometry.cyclicFour P : Set P) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ z hz
      rcases hz with ⟨z, hz, rfl⟩
      change (sylowEquiv P z) * (sylowEquiv P x) =
        (sylowEquiv P x) * (sylowEquiv P z)
      simpa only [map_mul] using congrArg (sylowEquiv P) (hx z hz)
    · intro hy
      refine ⟨(sylowEquiv P).symm y, ?_, ?_⟩
      · intro z hz
        have h := hy (sylowEquiv P z) ⟨z, hz, rfl⟩
        change z * (sylowEquiv P).symm y =
          (sylowEquiv P).symm y * z
        simpa only [map_mul, (sylowEquiv P).symm_apply_apply] using
          congrArg (sylowEquiv P).symm h
      · exact (sylowEquiv P).apply_symm_apply y
  have homega := map_omegaOneAmbient_injective
    (sylowEquiv P).toMonoidHom (sylowEquiv P).injective
      (centralizer (AlternatingSix.ShadowLocal.Holomorph.cyclicFour :
        Set AlternatingSix.ShadowLocal.Holomorph.Model))
  rw [hcent] at homega
  have hxmap : x ∈
      (omegaOneAmbient (centralizer (AlternatingSix.ShadowLocal.Holomorph.cyclicFour :
        Set AlternatingSix.ShadowLocal.Holomorph.Model))).map
        (sylowEquiv P).toMonoidHom := by
    rw [homega]
    exact hx
  have he : (sylowEquiv P).symm x ∈
      omegaOneAmbient (centralizer (AlternatingSix.ShadowLocal.Holomorph.cyclicFour :
        Set AlternatingSix.ShadowLocal.Holomorph.Model)) :=
    (mem_map_equiv.mp hxmap)
  have he' := model_omega_bound he
  have hmap :
      (AlternatingSix.ShadowLocal.Holomorph.centralTwo ⊔
        AlternatingSix.ShadowLocal.Holomorph.transpositionSubgroup).map
          (sylowEquiv P).toMonoidHom =
        center P ⊔ SylowGeometry.transpositionSubgroup P := by
    rw [Subgroup.map_sup, ← AlternatingSix.ShadowLocal.Holomorph.center_model,
      center_map_equiv, SylowGeometry.transpositionSubgroup]
  have he'' : x ∈
      (AlternatingSix.ShadowLocal.Holomorph.centralTwo ⊔
        AlternatingSix.ShadowLocal.Holomorph.transpositionSubgroup).map
          (sylowEquiv P).toMonoidHom := by
    rw [mem_map_equiv]
    exact he'
  rwa [hmap] at he''

private theorem model_center_le_cyclicFour :
    AlternatingSix.ShadowLocal.Holomorph.centralTwo ≤
      AlternatingSix.ShadowLocal.Holomorph.cyclicFour := by
  rw [AlternatingSix.ShadowLocal.Holomorph.centralTwo,
    AlternatingSix.ShadowLocal.Holomorph.cyclicFour]
  apply zpowers_le.mpr
  exact ⟨2, by decide +kernel⟩

private theorem center_le_cyclicFour (P : Sylow 2 AutA6) :
    center P ≤ SylowGeometry.cyclicFour P := by
  rw [← center_map_equiv (sylowEquiv P),
    AlternatingSix.ShadowLocal.Holomorph.center_model]
  rw [SylowGeometry.cyclicFour]
  exact map_mono model_center_le_cyclicFour

private theorem center_preimage (d : EarlierSetup κ G) {a : d.S}
    (ha : d.toImageSylow a ∈ center d.imageSylow) :
    (a : G) ∈ d.SC ⊔ zpowers d.zK := by
  have haI : d.toImageSylow a ∈ sylowInner d.imageSylow :=
    (SylowGeometry.cyclicFour_le_inner d.imageSylow)
      (center_le_cyclicFour d.imageSylow ha)
  let q : sylowInner d.imageSylow := ⟨d.toImageSylow a, haI⟩
  obtain ⟨k, hk⟩ := innerAction_surjective d q
  have hqk : d.toImageSylow ⟨(k : G), k.property.1⟩ = d.toImageSylow a := by
    exact congrArg (fun z : sylowInner d.imageSylow => (z : d.imageSylow)) hk
  have hkcenter : (k : G) ∈ centerIn (d.S ⊓ d.K : Subgroup G) := by
    rw [centerIn]
    refine ⟨k.property, ?_⟩
    intro c hc
    let cs : (d.S ⊓ d.K : Subgroup G) := ⟨c, hc⟩
    have he : innerAction d k * innerAction d cs =
        innerAction d cs * innerAction d k := by
      rw [hk]
      have h := (mem_center_iff.mp ha) (d.toImageSylow ⟨c, hc.1⟩)
      simpa [q, cs, innerAction, MonoidHom.comp_apply, Subgroup.inclusion] using h.symm
    have hei : k * cs = cs * k := by
      apply (innerAction_injective d)
      simpa only [map_mul] using he
    have he' := congrArg (fun z : (d.S ⊓ d.K : Subgroup G) => (z : G)) hei
    simpa [cs] using he'.symm
  have hkz : (k : G) ∈ zpowers d.zK := by
    rw [← d.center_sk]
    exact hkcenter
  have hker : (a : G) * (k : G)⁻¹ ∈ d.SC := by
    let c : d.S := a * (⟨(k : G), k.property.1⟩ : d.S)⁻¹
    have hc : c ∈ d.toImageSylow.ker := by
      rw [MonoidHom.mem_ker]
      change d.toImageSylow (a * (⟨(k : G), k.property.1⟩ : d.S)⁻¹) = 1
      rw [map_mul, map_inv, hqk, mul_inv_cancel]
    rw [d.toImageSylow_kernel] at hc
    change ((c : d.S) : G) ∈ d.SC
    exact hc
  have hprod : (a : G) * (k : G)⁻¹ * (k : G) ∈ d.SC ⊔ zpowers d.zK :=
    Subgroup.mul_mem_sup hker hkz
  simpa [mul_assoc] using hprod

private theorem commutator_SK_S_le_K (d : EarlierSetup κ G) :
    ⁅d.S ⊓ d.K, d.S⁆ ≤ d.K := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have haK : (a : G) ∈ d.K := ha.2
  have hainvK : ((a : G)⁻¹) ∈ d.K := d.K.inv_mem haK
  have hbH : (b : G) ∈ d.H := d.s_le_h hb
  have hconj : (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ d.K := by
    have hainvH : (⟨(a : G)⁻¹, d.k_le_h hainvK⟩ : d.H) ∈
        d.K.subgroupOf d.H := hainvK
    exact d.normalK.conj_mem
      (⟨(a : G)⁻¹, d.k_le_h hainvK⟩ : d.H) hainvH
      (⟨(b : G), hbH⟩ : d.H)
  rw [commutatorElement_def]
  simpa only [mul_assoc] using d.K.mul_mem haK hconj

theorem frattini_SC_eq_bot (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) : frattini d.SC = ⊥ := by
  let : IsElementaryAbelian 2 d.SC := hEA
  let : Fact (IsPGroup 2 d.SC) := ⟨hEA.isPGroup 2 d.SC⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := 2)

theorem cyclic_le_phi (d : EarlierSetup κ G) : cyclic d ≤ phi d.S := by
  let A : Subgroup d.S := (d.S ⊓ d.K).subgroupOf d.S
  let C : Subgroup d.S := ⁅A, (⊤ : Subgroup d.S)⁆
  have hAmap : A.map d.toImageSylow = sylowInner d.imageSylow := by
    apply le_antisymm
    · rintro y ⟨a, ha, rfl⟩
      exact (innerAction d ⟨a, ha⟩).property
    · intro y hy
      obtain ⟨a, ha⟩ := innerAction_surjective d ⟨y, hy⟩
      refine ⟨(⟨a, a.property.1⟩ : d.S), ?_, ?_⟩
      · exact a.property
      · apply Subtype.ext
        simpa [innerAction, Subgroup.inclusion, MonoidHom.comp_apply] using
          congrArg Subtype.val ha
  have hCmap : C.map d.toImageSylow =
      ⁅sylowInner d.imageSylow, (⊤ : Subgroup d.imageSylow)⁆ := by
    rw [Subgroup.map_commutator, hAmap,
      map_top_of_surjective _ (toImageSylow_surjective d)]
  have hcycC : cyclic d ≤ C.map d.S.subtype := by
    intro y hy
    have hiy : (innerEquiv d ⟨y, cyclic_le d hy⟩ : d.imageSylow) ∈
        SylowGeometry.cyclicFour d.imageSylow :=
      (mem_liftInner d (SylowGeometry.cyclicFour d.imageSylow)
        ⟨y, cyclic_le d hy⟩).mp hy
    have hcomm := cyclicFour_le_commutator_inner d.imageSylow hiy
    rw [← hCmap] at hcomm
    obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp hcomm
    have hcK : (c : G) ∈ d.K := by
      have hCK : C.map d.S.subtype ≤ d.K := by
        change (⁅A, (⊤ : Subgroup d.S)⁆).map d.S.subtype ≤ d.K
        rw [Subgroup.map_commutator,
          Subgroup.map_subgroupOf_eq_of_le inf_le_left,
          ← MonoidHom.range_eq_map, range_subtype]
        exact commutator_SK_S_le_K d
      exact hCK (mem_map_of_mem d.S.subtype hc)
    have hcs : (c : G) ∈ d.S ⊓ d.K := ⟨c.property, hcK⟩
    have heq : innerAction d ⟨c, hcs⟩ =
        innerAction d ⟨y, cyclic_le d hy⟩ := by
      apply Subtype.ext
      change d.toImageSylow c =
        ((innerEquiv d ⟨y, cyclic_le d hy⟩ : d.imageSylow) : d.imageSylow)
      exact hcy
    have hcy' : (c : G) = y := by
      exact congrArg (fun z : (d.S ⊓ d.K : Subgroup G) => (z : G))
        ((innerAction_injective d) heq)
    refine ⟨c, hc, ?_⟩
    change (c : G) = y
    exact hcy'
  have hCphi : C.map d.S.subtype ≤ phi d.S := by
    calc
      C.map d.S.subtype =
          ⁅A.map d.S.subtype, (⊤ : Subgroup d.S).map d.S.subtype⁆ := by
        change (⁅A, (⊤ : Subgroup d.S)⁆).map d.S.subtype = _
        rw [Subgroup.map_commutator]
      _ = ⁅d.S ⊓ d.K, d.S⁆ := by
        rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left]
        rw [← MonoidHom.range_eq_map, range_subtype]
      _ ≤ ⁅d.S, d.S⁆ := commutator_mono inf_le_left le_rfl
      _ = (_root_.commutator d.S).map d.S.subtype :=
        (Subgroup.map_subtype_commutator d.S).symm
      _ ≤ phi d.S := by
        let : Fact (IsPGroup 2 d.S) := ⟨d.isTwoGroupS⟩
        exact map_mono (commutator_le_frattini_of_isPGroup
          (R := d.S) (p := 2))
  exact hcycC.trans hCphi

private theorem mem_SC_of_toImage_eq_one (d : EarlierSetup κ G)
    {a : d.S} (h : d.toImageSylow a = 1) : (a : G) ∈ d.SC := by
  have hk : a ∈ d.toImageSylow.ker := (MonoidHom.mem_ker).mpr h
  rw [d.toImageSylow_kernel] at hk
  exact hk

theorem phi_eq_cyclic_sup_phiC (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) :
    phi d.S = cyclic d ⊔ phiC d := by
  let : IsElementaryAbelian 2 d.SC := hEA
  let : Fact (IsPGroup 2 d.S) := ⟨d.isTwoGroupS⟩
  let : Fact (IsPGroup 2 d.imageSylow) := ⟨d.imageSylow.isPGroup'⟩
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨a, ha, rfl⟩
    have hya : d.toImageSylow a ∈ frattini d.imageSylow := by
      have hmap := frattini_map_le_of_isPGroup (p := 2) d.toImageSylow
      exact hmap (mem_map_of_mem d.toImageSylow ha)
    rw [SylowGeometry.frattini_eq] at hya
    let q : sylowInner d.imageSylow :=
      ⟨d.toImageSylow a, (SylowGeometry.cyclicFour_le_inner d.imageSylow) hya⟩
    let k : (d.S ⊓ d.K : Subgroup G) :=
      (innerEquiv d).symm q
    have hkcyc : (k : G) ∈ cyclic d :=
      (mem_liftInner d (SylowGeometry.cyclicFour d.imageSylow) k).mpr (by
        simpa [k] using hya)
    have hkim : d.toImageSylow ⟨k, k.property.1⟩ = d.toImageSylow a := by
      have he : innerAction d k = q := (innerEquiv d).apply_symm_apply q
      simpa [innerAction, MonoidHom.comp_apply, MonoidHom.codRestrict_apply,
        Subgroup.inclusion, q, k] using congrArg
        (fun z : sylowInner d.imageSylow => (z : AutA6)) he
    have hker : (k : G)⁻¹ * (a : G) ∈ d.SC := by
      have hkS : (k : G) ∈ d.S := k.property.1
      let ks : d.S := ⟨(k : G), hkS⟩
      let c : d.S := ks⁻¹ * a
      apply mem_SC_of_toImage_eq_one d (a := c)
      change d.toImageSylow (ks⁻¹ * a) = 1
      rw [map_mul, map_inv, hkim]
      exact inv_mul_cancel _
    have hkphi : (k : G) ∈ phi d.S := cyclic_le_phi d hkcyc
    have hphiS_le : phi d.S ≤ d.S := by
      intro z hz
      rcases hz with ⟨q, hq, rfl⟩
      exact q.property
    have hphik : (k : G)⁻¹ * (a : G) ∈ phi d.S := by
      exact (phi d.S).mul_mem ((phi d.S).inv_mem hkphi) (by
        exact ⟨a, ha, rfl⟩)
    have hphiC : (k : G)⁻¹ * (a : G) ∈ phiC d := ⟨hphik, hker⟩
    have hprod : (k : G) * ((k : G)⁻¹ * (a : G)) ∈ cyclic d ⊔ phiC d :=
      Subgroup.mul_mem_sup hkcyc hphiC
    simpa [mul_assoc] using hprod
  · exact sup_le (cyclic_le_phi d) inf_le_left

theorem cyclic_le_centralizer_phiC (d : EarlierSetup κ G) :
    cyclic d ≤ centralizer (phiC d : Set G) := by
  intro c hc b hb
  have hbK : b ∈ centralizer (d.K : Set G) :=
    (d.centralizer_K ▸ hb.2).2
  exact (mem_centralizer_iff.mp hbK c (cyclic_le d hc).2).symm

private theorem cyclic_le_relativeCentralizer (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) :
    cyclic d ≤ d.S ⊓ centralizer (phi d.S : Set G) := by
  let : IsMulCommutative (cyclic d) := IsCyclic.isMulCommutative
  have hcycC := cyclic_le_centralizer_phiC d
  have hnorm : cyclic d ≤ normalizer (phiC d : Set G) :=
    hcycC.trans (centralizer_le_normalizer _)
  intro a ha
  refine ⟨(cyclic_le d ha).1, ?_⟩
  intro y hy
  have hsup : y ∈ cyclic d ⊔ phiC d := by
    rw [← phi_eq_cyclic_sup_phiC d hEA]
    exact hy
  have hprod : y ∈ (cyclic d : Set G) * (phiC d : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hnorm]
    exact hsup
  obtain ⟨c, hc, e, he, rfl⟩ := hprod
  have hac : a * c = c * a := by
    simpa using congrArg Subtype.val
      ((inferInstance : IsMulCommutative (cyclic d)).is_comm.comm
        ⟨a, ha⟩ ⟨c, hc⟩)
  have hae : a * e = e * a := (hcycC ha e he).symm
  calc
    (c * e) * a = c * (e * a) := by simp [mul_assoc]
    _ = c * (a * e) := by rw [hae]
    _ = (c * a) * e := by simp [mul_assoc]
    _ = (a * c) * e := by rw [hac]
    _ = a * (c * e) := by simp [mul_assoc]

private theorem sc_le_relativeCentralizer (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) :
    d.SC ≤ d.S ⊓ centralizer (phi d.S : Set G) := by
  let : IsElementaryAbelian 2 d.SC := hEA
  have hcycC := cyclic_le_centralizer_phiC d
  have hnorm : cyclic d ≤ normalizer (phiC d : Set G) :=
    hcycC.trans (centralizer_le_normalizer _)
  intro a ha
  refine ⟨(d.centralizer_K ▸ ha).1, ?_⟩
  intro y hy
  have hsup : y ∈ cyclic d ⊔ phiC d := by
    rw [← phi_eq_cyclic_sup_phiC d hEA]
    exact hy
  have hprod : y ∈ (cyclic d : Set G) * (phiC d : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hnorm]
    exact hsup
  obtain ⟨c, hc, e, he, rfl⟩ := hprod
  have hac : (a : G) * c = c * a := by
    have hk : (a : G) ∈ centralizer (d.K : Set G) := (d.centralizer_K ▸ ha).2
    exact (mem_centralizer_iff.mp hk c (cyclic_le d hc).2).symm
  have hae : (a : G) * e = e * a := by
    simpa using congrArg Subtype.val
      ((inferInstance : IsMulCommutative d.SC).is_comm.comm
        ⟨a, ha⟩ ⟨e, he.2⟩)
  calc
    (c * e) * (a : G) = c * (e * (a : G)) := by simp [mul_assoc]
    _ = c * ((a : G) * e) := by rw [hae]
    _ = (c * (a : G)) * e := by simp [mul_assoc]
    _ = ((a : G) * c) * e := by rw [hac]
    _ = (a : G) * (c * e) := by simp [mul_assoc]

private theorem zK_le_cyclic (d : EarlierSetup κ G) :
    zpowers d.zK ≤ cyclic d := by
  apply zpowers_le.mpr
  have hzcenter : d.zK ∈ centerIn (d.S ⊓ d.K : Subgroup G) := by
    rw [d.center_sk]
    exact mem_zpowers d.zK
  have hzSK : d.zK ∈ d.S ⊓ d.K := hzcenter.1
  have hqcenter : innerAction d ⟨d.zK, hzSK⟩ ∈
      center (sylowInner d.imageSylow) := by
    rw [mem_center_iff]
    intro b
    obtain ⟨c, rfl⟩ := innerAction_surjective d b
    have hcSK : c * (⟨d.zK, hzSK⟩ : (d.S ⊓ d.K : Subgroup G)) =
        ⟨d.zK, hzSK⟩ * c := by
      apply Subtype.ext
      exact hzcenter.2 c c.property
    change innerAction d c * innerAction d ⟨d.zK, hzSK⟩ =
      innerAction d ⟨d.zK, hzSK⟩ * innerAction d c
    rw [← map_mul, ← map_mul]
    exact congrArg (innerAction d) hcSK
  have hmap : (innerAction d ⟨d.zK, hzSK⟩ : d.imageSylow) ∈
      SylowGeometry.cyclicFour d.imageSylow := by
    apply center_inner_le_cyclicFour
    exact ⟨innerAction d ⟨d.zK, hzSK⟩, hqcenter, rfl⟩
  exact (mem_liftInner d _ ⟨d.zK, hzSK⟩).mpr (by
    have he : innerAction d ⟨d.zK, hzSK⟩ =
        (innerEquiv d) ⟨d.zK, hzSK⟩ := rfl
    exact he ▸ hmap)

private theorem core_sup_zK_le_plus (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) :
    d.SC ⊔ zpowers d.zK ≤ plus d := by
  let : IsElementaryAbelian 2 d.SC := hEA
  let : IsElementaryAbelian 2 (zpowers d.zK) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one
      (d.zK_order ▸ pow_orderOf_eq_one d.zK)
  have hcomm : zpowers d.zK ≤ centralizer (d.SC : Set G) := by
    intro z hz c hc
    have hzK : z ∈ d.K := by
      have hz0 : d.zK ∈ d.K := (d.center_sk ▸ mem_zpowers d.zK).1.2
      exact (zpowers_le.mpr hz0) hz
    have hcK : (c : G) ∈ centralizer (d.K : Set G) :=
      (d.centralizer_K ▸ hc).2
    exact (mem_centralizer_iff.mp hcK z hzK).symm
  let A : Subgroup G := d.SC ⊔ zpowers d.zK
  let : IsElementaryAbelian 2 A :=
    IsElementaryAbelian.sup_of_le_centralizer hcomm
  have hH : A ≤ d.S ⊓ centralizer (phi d.S : Set G) := by
    apply sup_le
    · exact sc_le_relativeCentralizer d hEA
    · exact (zK_le_cyclic d).trans (cyclic_le_relativeCentralizer d hEA)
  have hAomega : A ≤ omegaOneAmbient A := by
    rw [omegaOneAmbient_eq_self]
  change A ≤ omegaOneAmbient (d.S ⊓ centralizer (phi d.S : Set G))
  exact hAomega.trans (omegaOneAmbient_mono hH)

private theorem mem_transpositionPreimage_iff (d : EarlierSetup κ G) {a : d.S} :
    (a : G) ∈ transpositionPreimage d ↔
      d.toImageSylow a ∈ SylowGeometry.transpositionSubgroup d.imageSylow := by
  constructor
  · rintro ⟨b, hb, hba⟩
    have hba' : b = a := Subtype.ext hba
    simpa [hba'] using hb
  · intro ha
    exact ⟨a, ha, rfl⟩

private theorem sc_le_transpositionPreimage (d : EarlierSetup κ G) :
    d.SC ≤ transpositionPreimage d := by
  intro c hc
  let a : d.S := ⟨c, (d.centralizer_K ▸ hc).1⟩
  change (a : G) ∈ transpositionPreimage d
  apply (mem_transpositionPreimage_iff d).mpr
  have haK : a ∈ d.toImageSylow.ker := by
    rw [d.toImageSylow_kernel]
    exact hc
  exact (MonoidHom.mem_ker.mp haK) ▸
    (SylowGeometry.transpositionSubgroup d.imageSylow).one_mem

private theorem plus_image_mem (d : EarlierSetup κ G) {x : G} (hx : x ∈ plus d)
    (hx2 : x ^ 2 = 1) :
    d.toImageSylow ⟨x, (omegaOneAmbient_le _ hx).1⟩ ∈
      center d.imageSylow ⊔ SylowGeometry.transpositionSubgroup d.imageSylow := by
  have hxH : x ∈ d.S ⊓ centralizer (phi d.S : Set G) :=
    omegaOneAmbient_le _ hx
  let a : d.S := ⟨x, hxH.1⟩
  have hq2 : (d.toImageSylow a) ^ 2 = 1 := by
    have ha2 : a ^ 2 = 1 := Subtype.ext hx2
    simpa only [map_pow, map_one] using congrArg d.toImageSylow ha2
  have hqcent : d.toImageSylow a ∈
      centralizer (SylowGeometry.cyclicFour d.imageSylow : Set d.imageSylow) := by
    intro y hy
    let k : (d.S ⊓ d.K : Subgroup G) :=
      (innerEquiv d).symm ⟨y, (SylowGeometry.cyclicFour_le_inner d.imageSylow) hy⟩
    have hky : (k : G) ∈ cyclic d :=
      (mem_liftInner d (SylowGeometry.cyclicFour d.imageSylow) k).mpr (by
        exact (innerEquiv d).apply_symm_apply ⟨y, _⟩ ▸ hy)
    have hk : innerAction d k =
        (⟨y, (SylowGeometry.cyclicFour_le_inner d.imageSylow) hy⟩ :
          sylowInner d.imageSylow) :=
      (innerEquiv d).apply_symm_apply _
    have hxy := hxH.2 (k : G) (cyclic_le_phi d hky)
    have hxyS : (⟨(k : G), k.property.1⟩ : d.S) * a =
        a * (⟨(k : G), k.property.1⟩ : d.S) := Subtype.ext hxy
    have he : d.toImageSylow ⟨k, k.property.1⟩ * d.toImageSylow a =
        d.toImageSylow a * d.toImageSylow ⟨k, k.property.1⟩ := by
      simpa only [map_mul] using congrArg d.toImageSylow hxyS
    have hkimage : d.toImageSylow ⟨k, k.property.1⟩ = y := by
      simpa only [innerAction, MonoidHom.comp_apply, Subgroup.inclusion,
        MonoidHom.codRestrict_apply, MonoidHom.mk'_apply] using congrArg
          (fun z : sylowInner d.imageSylow => (z : d.imageSylow)) hk
    rw [hkimage] at he
    exact he
  have hqomega : d.toImageSylow a ∈
      omegaOneAmbient (centralizer (SylowGeometry.cyclicFour d.imageSylow :
        Set d.imageSylow)) :=
    (omegaOneAmbient_le_iff _ _).mp le_rfl _ hqcent hq2
  exact sylow_omega_bound d.imageSylow hqomega

private theorem image_centerInS (d : EarlierSetup κ G) {a : d.S}
    (ha : (a : G) ∈ centerIn d.S) :
    d.toImageSylow a ∈ center d.imageSylow := by
  rw [mem_center_iff]
  intro b
  obtain ⟨c, rfl⟩ := toImageSylow_surjective d b
  have hc := ha.2 (c : G) c.property
  have hcs : c * a = a * c := by
    exact Subtype.ext hc
  simpa only [map_mul] using congrArg d.toImageSylow hcs

private theorem plus_le_transposition_sup_zK (d : EarlierSetup κ G) :
    plus d ≤ transpositionPreimage d ⊔ zpowers d.zK := by
  have hA_B : d.SC ⊔ zpowers d.zK ≤
      transpositionPreimage d ⊔ zpowers d.zK :=
    sup_le ((sc_le_transpositionPreimage d).trans le_sup_left) le_sup_right
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro x hx hx2
  have hxS : x ∈ d.S := hx.1
  let a : d.S := ⟨x, hxS⟩
  have hq2 : (d.toImageSylow a) ^ 2 = 1 := by
    have ha2 : a ^ 2 = 1 := Subtype.ext hx2
    simpa only [map_pow, map_one] using congrArg d.toImageSylow ha2
  have hqcent : d.toImageSylow a ∈
      centralizer (SylowGeometry.cyclicFour d.imageSylow : Set d.imageSylow) := by
    intro y hy
    let k : (d.S ⊓ d.K : Subgroup G) :=
      (innerEquiv d).symm ⟨y, (SylowGeometry.cyclicFour_le_inner d.imageSylow) hy⟩
    have hky : (k : G) ∈ cyclic d :=
      (mem_liftInner d (SylowGeometry.cyclicFour d.imageSylow) k).mpr (by
        exact (innerEquiv d).apply_symm_apply ⟨y, _⟩ ▸ hy)
    have hk : innerAction d k =
        (⟨y, (SylowGeometry.cyclicFour_le_inner d.imageSylow) hy⟩ :
          sylowInner d.imageSylow) :=
      (innerEquiv d).apply_symm_apply _
    have hxy := hx.2 (k : G) (cyclic_le_phi d hky)
    have hxyS : (⟨(k : G), k.property.1⟩ : d.S) * a =
        a * (⟨(k : G), k.property.1⟩ : d.S) := by
      exact Subtype.ext hxy
    have he : d.toImageSylow ⟨k, k.property.1⟩ * d.toImageSylow a =
        d.toImageSylow a * d.toImageSylow ⟨k, k.property.1⟩ := by
      simpa only [map_mul] using congrArg d.toImageSylow hxyS
    have hkimage : d.toImageSylow ⟨k, k.property.1⟩ = y := by
      simpa only [innerAction, MonoidHom.comp_apply, Subgroup.inclusion,
        MonoidHom.codRestrict_apply, MonoidHom.mk'_apply] using congrArg
          (fun z : sylowInner d.imageSylow => (z : d.imageSylow)) hk
    rw [hkimage] at he
    exact he
  have hqomega : d.toImageSylow a ∈
      omegaOneAmbient (centralizer (SylowGeometry.cyclicFour d.imageSylow :
        Set d.imageSylow)) :=
    (omegaOneAmbient_le_iff _ _).mp le_rfl _ hqcent hq2
  have hq : d.toImageSylow a ∈
      center d.imageSylow ⊔ SylowGeometry.transpositionSubgroup d.imageSylow :=
    sylow_omega_bound d.imageSylow hqomega
  have hnorm : center d.imageSylow ≤
      normalizer (SylowGeometry.transpositionSubgroup d.imageSylow : Set d.imageSylow) :=
    center_le_normalizer _
  have hprod : d.toImageSylow a ∈
      (center d.imageSylow : Set d.imageSylow) *
        (SylowGeometry.transpositionSubgroup d.imageSylow : Set d.imageSylow) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hnorm]
    exact hq
  obtain ⟨c, hc, t, ht, hct⟩ := hprod
  obtain ⟨u, hu⟩ := toImageSylow_surjective d t
  have huT : (u : G) ∈ transpositionPreimage d :=
    (mem_transpositionPreimage_iff d).mpr (by simpa [hu] using ht)
  let v : d.S := a * u⁻¹
  have hv_eq : d.toImageSylow v = c := by
    change d.toImageSylow (a * u⁻¹) = c
    rw [map_mul, map_inv, hu, ← hct]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have hvcenter : d.toImageSylow v ∈ center d.imageSylow := hv_eq ▸ hc
  have hvA : (v : G) ∈ d.SC ⊔ zpowers d.zK := center_preimage d hvcenter
  have hvB : (v : G) ∈ transpositionPreimage d ⊔ zpowers d.zK :=
    hA_B hvA
  have huB : (u : G) ∈ transpositionPreimage d ⊔ zpowers d.zK :=
    (le_sup_left : transpositionPreimage d ≤
      transpositionPreimage d ⊔ zpowers d.zK) huT
  have hvu := Subgroup.mul_mem_sup hvB huB
  simpa [v, mul_assoc] using hvu

private theorem model_outer_coset_mul : ∀ a b :
    AlternatingSix.ShadowLocal.Holomorph.Model,
    a ∈ AlternatingSix.ShadowLocal.Holomorph.centralTwo ⊔
      AlternatingSix.ShadowLocal.Holomorph.transpositionSubgroup →
    b ∈ AlternatingSix.ShadowLocal.Holomorph.centralTwo ⊔
      AlternatingSix.ShadowLocal.Holomorph.transpositionSubgroup →
    a ∉ AlternatingSix.ShadowLocal.Holomorph.centralTwo →
    b ∉ AlternatingSix.ShadowLocal.Holomorph.centralTwo →
    a⁻¹ * b ∈ AlternatingSix.ShadowLocal.Holomorph.centralTwo := by
  intro a b ha hb hna hnb
  rw [AlternatingSix.ShadowLocal.Holomorph.mem_centralTwo_sup_transposition] at ha hb
  rw [AlternatingSix.ShadowLocal.Holomorph.mem_centralTwo] at hna hnb
  revert a b
  simp [AlternatingSix.ShadowLocal.Holomorph.mem_centralTwo]
  decide +kernel

private theorem outer_coset_mul (P : Sylow 2 AutA6) {a b : P}
    (ha : a ∈ center P ⊔ SylowGeometry.transpositionSubgroup P)
    (hb : b ∈ center P ⊔ SylowGeometry.transpositionSubgroup P)
    (hna : a ∉ center P) (hnb : b ∉ center P) :
    a⁻¹ * b ∈ center P := by
  have hmap :
      (AlternatingSix.ShadowLocal.Holomorph.centralTwo ⊔
        AlternatingSix.ShadowLocal.Holomorph.transpositionSubgroup).map
          (sylowEquiv P).toMonoidHom =
        center P ⊔ SylowGeometry.transpositionSubgroup P := by
    rw [Subgroup.map_sup, ← AlternatingSix.ShadowLocal.Holomorph.center_model,
      center_map_equiv, SylowGeometry.transpositionSubgroup]
  have ha' : (sylowEquiv P).symm a ∈
      AlternatingSix.ShadowLocal.Holomorph.centralTwo ⊔
        AlternatingSix.ShadowLocal.Holomorph.transpositionSubgroup := by
    apply mem_map_equiv.mp
    rw [hmap]
    exact ha
  have hb' : (sylowEquiv P).symm b ∈
      AlternatingSix.ShadowLocal.Holomorph.centralTwo ⊔
        AlternatingSix.ShadowLocal.Holomorph.transpositionSubgroup := by
    apply mem_map_equiv.mp
    rw [hmap]
    exact hb
  have hcenterMap :
      AlternatingSix.ShadowLocal.Holomorph.centralTwo.map
          (sylowEquiv P).toMonoidHom = center P := by
    rw [← AlternatingSix.ShadowLocal.Holomorph.center_model,
      center_map_equiv]
  have hna' : (sylowEquiv P).symm a ∉
      AlternatingSix.ShadowLocal.Holomorph.centralTwo := by
    intro h
    apply hna
    have hm : a ∈
        AlternatingSix.ShadowLocal.Holomorph.centralTwo.map
          (sylowEquiv P).toMonoidHom := mem_map_equiv.mpr h
    rw [hcenterMap] at hm
    exact hm
  have hnb' : (sylowEquiv P).symm b ∉
      AlternatingSix.ShadowLocal.Holomorph.centralTwo := by
    intro h
    apply hnb
    have hm : b ∈
        AlternatingSix.ShadowLocal.Holomorph.centralTwo.map
          (sylowEquiv P).toMonoidHom := mem_map_equiv.mpr h
    rw [hcenterMap] at hm
    exact hm
  have hc := model_outer_coset_mul _ _ ha' hb' hna' hnb'
  have hc' : (sylowEquiv P).symm (a⁻¹ * b) ∈
      AlternatingSix.ShadowLocal.Holomorph.centralTwo := by
    simpa only [map_mul, map_inv] using hc
  rw [← AlternatingSix.ShadowLocal.Holomorph.center_model] at hc'
  rw [← center_map_equiv (sylowEquiv P), mem_map_equiv]
  simpa only [MulEquiv.map_mul, MulEquiv.map_inv,
    (sylowEquiv P).apply_symm_apply] using hc'

theorem plus_eq_core_or_transposition (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) :
    plus d = d.SC ⊔ zpowers d.zK ∨
      plus d = transpositionPreimage d ⊔ zpowers d.zK := by
  have hA : d.SC ⊔ zpowers d.zK ≤ plus d :=
    core_sup_zK_le_plus d hEA
  have hB : plus d ≤ transpositionPreimage d ⊔ zpowers d.zK :=
    plus_le_transposition_sup_zK d
  by_cases hle : plus d ≤ d.SC ⊔ zpowers d.zK
  · exact Or.inl (le_antisymm hle hA)
  · have hex : ∃ x : G, x ∈ plus d ∧ x ∉ d.SC ⊔ zpowers d.zK ∧
        x ∈ d.S ⊓ centralizer (phi d.S : Set G) ∧ x ^ 2 = 1 := by
      by_contra hno
      apply hle
      change omegaOneAmbient (d.S ⊓ centralizer (phi d.S : Set G)) ≤
        d.SC ⊔ zpowers d.zK
      apply (omegaOneAmbient_le_iff _ _).mpr
      intro x hx hx2
      by_contra hxa
      apply hno
      refine ⟨x, ?_, hxa, hx, hx2⟩
      exact (omegaOneAmbient_le_iff _ _).mp le_rfl x hx hx2
    obtain ⟨x, hxplus, hxnot, hxH, hx2⟩ := hex
    have hxS : x ∈ d.S := hxH.1
    let xs : d.S := ⟨x, hxS⟩
    have hxq : d.toImageSylow xs ∈
        center d.imageSylow ⊔ SylowGeometry.transpositionSubgroup d.imageSylow :=
      plus_image_mem d hxplus hx2
    have hxqouter : d.toImageSylow xs ∉ center d.imageSylow := by
      intro hc
      apply hxnot
      exact center_preimage d hc
    have htpS : transpositionPreimage d ≤ d.S := by
      rintro y ⟨a, ha, rfl⟩
      exact a.property
    have hzcenterS : zpowers d.zK ≤ centerIn d.S := by
      rw [d.center_s]
      exact le_sup_right
    have hzS : zpowers d.zK ≤ d.S := hzcenterS.trans inf_le_left
    have hScent : d.S ≤ centralizer (zpowers d.zK : Set G) := by
      intro s hs z hz
      exact (mem_centralizer_iff.mp (hzcenterS hz).2 s hs).symm
    have hnorm : transpositionPreimage d ≤
        normalizer (zpowers d.zK : Set G) :=
      htpS.trans (hScent.trans (centralizer_le_normalizer _))
    apply Or.inr
    apply le_antisymm hB
    intro y hy
    have hy' : y ∈ (transpositionPreimage d : Set G) *
        (zpowers d.zK : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ hnorm]
      exact hy
    obtain ⟨u, hu, v, hv, rfl⟩ := hy'
    let us : d.S := ⟨u, htpS hu⟩
    let vs : d.S := ⟨v, hzS hv⟩
    have huT : d.toImageSylow us ∈
        SylowGeometry.transpositionSubgroup d.imageSylow :=
      (mem_transpositionPreimage_iff d).mp hu
    have hvC : d.toImageSylow vs ∈ center d.imageSylow :=
      image_centerInS d (hzcenterS hv)
    have hyq : d.toImageSylow (us * vs) ∈
        center d.imageSylow ⊔ SylowGeometry.transpositionSubgroup d.imageSylow := by
      rw [map_mul]
      exact (center d.imageSylow ⊔ SylowGeometry.transpositionSubgroup d.imageSylow).mul_mem
        ((le_sup_right : SylowGeometry.transpositionSubgroup d.imageSylow ≤
          center d.imageSylow ⊔ SylowGeometry.transpositionSubgroup d.imageSylow) huT)
        ((le_sup_left : center d.imageSylow ≤
          center d.imageSylow ⊔ SylowGeometry.transpositionSubgroup d.imageSylow) hvC)
    by_cases hycenter : d.toImageSylow (us * vs) ∈ center d.imageSylow
    · have hyA : (u * v : G) ∈ d.SC ⊔ zpowers d.zK := by
        exact center_preimage d hycenter
      have hyP : (u * v : G) ∈ plus d := hA hyA
      exact hyP
    · have hdiff : d.toImageSylow (xs⁻¹ * (us * vs)) ∈ center d.imageSylow := by
        have hd := outer_coset_mul d.imageSylow hxq hyq hxqouter hycenter
        simpa only [map_mul, map_inv] using hd
      have hdA : (x⁻¹ * (u * v) : G) ∈ d.SC ⊔ zpowers d.zK := by
        exact center_preimage d hdiff
      have hdP : (x⁻¹ * (u * v) : G) ∈ plus d := hA hdA
      have hp := (plus d).mul_mem hxplus hdP
      simpa [mul_assoc] using hp

theorem phi_phi_eq_zpowers_zK (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) :
    phi (phi d.S) = zpowers d.zK := by
  let : IsElementaryAbelian 2 d.SC := hEA
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : Fact (IsPGroup 2 d.S) := ⟨d.isTwoGroupS⟩
  have hphiS_le : phi d.S ≤ d.S := by
    intro z hz
    rcases hz with ⟨q, hq, rfl⟩
    exact q.property
  have hPphi : IsPGroup 2 (phi d.S) :=
    d.isTwoGroupS.of_injective (Subgroup.inclusion hphiS_le)
      (Subgroup.inclusion_injective hphiS_le)
  let : Fact (IsPGroup 2 (phi d.S)) := ⟨hPphi⟩
  let : IsElementaryAbelian 2 (phiC d) := {
    toIsMulCommutative := {
      is_comm.comm a b := by
        apply Subtype.ext
        change (a : G) * (b : G) = (b : G) * (a : G)
        simpa using congrArg Subtype.val
          ((inferInstance : IsMulCommutative d.SC).is_comm.comm
            ⟨a.1, a.2.2⟩ ⟨b.1, b.2.2⟩) }
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro a
      apply Subtype.ext
      have he : Monoid.exponent d.SC ∣ 2 :=
        IsElementaryAbelian.exponent_dvd_p 2 d.SC
      have hp := (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he)
        (⟨a.1, a.2.2⟩ : d.SC)
      simpa using congrArg Subtype.val hp
  }
  have hcycC : cyclic d ≤ centralizer (phiC d : Set G) := by
    intro c hc b hb
    have hbK : b ∈ centralizer (d.K : Set G) :=
      (d.centralizer_K ▸ hb.2).2
    exact (mem_centralizer_iff.mp hbK c (cyclic_le d hc).2).symm
  let : Fact (IsPGroup 2 (cyclic d)) :=
    ⟨d.isTwoGroupS.of_injective
      (Subgroup.inclusion ((cyclic_le d).trans inf_le_left))
      (Subgroup.inclusion_injective ((cyclic_le d).trans inf_le_left))⟩
  have hcycCnorm : cyclic d ≤ normalizer (phiC d : Set G) :=
    hcycC.trans (centralizer_le_normalizer _)
  have hsq : ∀ x : phi d.S,
      (x : G) ^ 2 ∈ (frattini (cyclic d)).map (cyclic d).subtype := by
    intro x
    have hsup : (x : G) ∈ cyclic d ⊔ phiC d :=
      by
        rw [← phi_eq_cyclic_sup_phiC d hEA]
        exact x.property
    have hprod : (x : G) ∈ (cyclic d : Set G) * (phiC d : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right _ _ hcycCnorm]
      exact hsup
    obtain ⟨c, hc, e, he, hxe⟩ := hprod
    have hce : Commute c e :=
      (mem_centralizer_iff.mp (hcycC hc) e he).symm
    have he2 : e ^ 2 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian (A := phiC d) e he
    have hc2 : c ^ 2 ∈ (frattini (cyclic d)).map (cyclic d).subtype :=
      by
        simpa using mem_map_of_mem (cyclic d).subtype
          (pth_power_mem_frattini_of_isPGroup (p := 2)
            (⟨c, hc⟩ : cyclic d))
    rw [← hxe, hce.mul_pow, he2, mul_one]
    exact hc2
  have hcomm : commutator (phi d.S) ≤
      ((frattini (cyclic d)).map (cyclic d).subtype).comap (phi d.S).subtype := by
    rw [_root_.commutator_def]
    apply Subgroup.commutator_le.mpr
    intro a _ b _
    change ⁅(a : G), (b : G)⁆ ∈
      (frattini (cyclic d)).map (cyclic d).subtype
    have hid : ⁅(a : G), (b : G)⁆ =
        (a : G) ^ 2 * ((a : G)⁻¹ * (b : G)) ^ 2 * ((b : G) ^ 2)⁻¹ := by
      simp [commutatorElement_def, pow_two, mul_assoc]
    rw [hid]
    exact ((frattini (cyclic d)).map (cyclic d).subtype).mul_mem
      (((frattini (cyclic d)).map (cyclic d).subtype).mul_mem
        (hsq a) (hsq (a⁻¹ * b)))
      (((frattini (cyclic d)).map (cyclic d).subtype).inv_mem (hsq b))
  have hfr_le : (frattini (phi d.S)).map (phi d.S).subtype ≤
      (frattini (cyclic d)).map (cyclic d).subtype := by
    rw [Subgroup.map_le_iff_le_comap,
      frattini_eq_closure_commutator_union_powers (p := 2)]
    apply (closure_le _).mpr
    rintro y (hy | ⟨y, rfl⟩)
    · exact hcomm hy
    · exact hsq y
  have hfr_ge : (frattini (cyclic d)).map (cyclic d).subtype ≤
      (frattini (phi d.S)).map (phi d.S).subtype := by
    have hi := frattini_map_le_of_isPGroup (p := 2)
      (Subgroup.inclusion (cyclic_le_phi d))
    calc
      (frattini (cyclic d)).map (cyclic d).subtype =
          ((frattini (cyclic d)).map
            (Subgroup.inclusion (cyclic_le_phi d))).map (phi d.S).subtype := by
        rw [Subgroup.map_map]
        rfl
      _ ≤ (frattini (phi d.S)).map (phi d.S).subtype :=
        Subgroup.map_mono hi
  have hfr : (frattini (phi d.S)).map (phi d.S).subtype =
      (frattini (cyclic d)).map (cyclic d).subtype :=
    le_antisymm hfr_le hfr_ge
  have hzc : zpowers d.zK ≤ cyclic d := zK_le_cyclic d
  let Z : Subgroup (cyclic d) := (zpowers d.zK).subgroupOf (cyclic d)
  have hZcard : Nat.card Z = 2 := by
    change Nat.card ((zpowers d.zK).subgroupOf (cyclic d)) = 2
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzc).toEquiv,
      Nat.card_zpowers, d.zK_order]
  have hfrcyc : frattini (cyclic d) = Z :=
    GLS3.Chapter5.frattini_eq_of_isCyclic_card_four Z (cyclic_card d) hZcard
  calc
    phi (phi d.S) = (frattini (phi d.S)).map (phi d.S).subtype := rfl
    _ = (frattini (cyclic d)).map (cyclic d).subtype := hfr
    _ = Z.map (cyclic d).subtype := congrArg _ hfrcyc
    _ = zpowers d.zK := by
      exact Subgroup.map_subgroupOf_eq_of_le hzc

/-- The two factors in the source Frattini product intersect trivially. -/
theorem cyclic_disjoint_phiC (d : EarlierSetup κ G) :
    Disjoint (cyclic d) (phiC d) :=
  d.disjoint_k_sc.mono ((cyclic_le d).trans inf_le_right) inf_le_right

/-- The actual internal direct-product decomposition in the source. -/
theorem phi_direct_product (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) :
    phi d.S = cyclic d ⊔ phiC d ∧ Disjoint (cyclic d) (phiC d) ∧
      cyclic d ≤ centralizer (phiC d : Set G) :=
  ⟨phi_eq_cyclic_sup_phiC d hEA, cyclic_disjoint_phiC d,
    cyclic_le_centralizer_phiC d⟩

/-- The characteristic double-Frattini line fixes the earlier involutions. -/
theorem involutions_of_elementary_core (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) :
    d.z = d.zK ∧ d.x⁻¹ * d.t * d.x = d.t * d.zK :=
  involutions_of_double_phi d (phi_phi_eq_zpowers_zK d hEA)

private theorem crossing_le_plus (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) : rightConjugate d.x d.SC ≤ plus d := by
  have h := map_mono (le_sup_left.trans (core_sup_zK_le_plus d hEA))
    (f := (MulAut.conj d.x⁻¹).toMonoidHom)
  change rightConjugate d.x d.SC ≤ rightConjugate d.x (plus d) at h
  rwa [crossing_plus] at h

/-- The whole omega subgroup has action in the marked four-group. -/
theorem plus_action_le (d : EarlierSetup κ G) :
    plus d ≤ ((centralizer (sylowInner d.imageSylow : Set d.imageSylow)).comap
      d.toImageSylow).map d.S.subtype := by
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro a ha ha2
  have hp : a ∈ plus d := (omegaOneAmbient_le_iff _ _).mp le_rfl a ha ha2
  refine ⟨⟨a, ha.1⟩, ?_, rfl⟩
  change d.toImageSylow ⟨a, ha.1⟩ ∈
    centralizer (sylowInner d.imageSylow : Set d.imageSylow)
  rw [SylowGeometry.centralizer_inner]
  exact plus_image_mem d hp ha2

private theorem plus_action_mem (d : EarlierSetup κ G) {a : d.S}
    (ha : (a : G) ∈ plus d) : d.toImageSylow a ∈
      centralizer (sylowInner d.imageSylow : Set d.imageSylow) := by
  obtain ⟨b, hb, he⟩ := plus_action_le d ha
  exact d.S.subtype_injective he ▸ hb

private def crossingToFour (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) : rightConjugate d.x d.SC →*
      centralizer (sylowInner d.imageSylow : Set d.imageSylow) :=
  (d.toImageSylow.comp (inclusion (d.rightConjugate_le d.sc_le_s))).codRestrict _
    (fun a => plus_action_mem d (crossing_le_plus d hEA a.property))

private theorem crossingToFour_injective (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) : Function.Injective (crossingToFour d hEA) := by
  intro a b he
  exact d.crossing_action_injective (congrArg Subtype.val he)

private theorem card_innerCentralizer (d : EarlierSetup κ G) :
    Nat.card (centralizer (sylowInner d.imageSylow : Set d.imageSylow)) = 4 := by
  rw [Nat.card_congr (SylowGeometry.centralizerInnerEquiv d.imageSylow).toEquiv]
  simp [Holomorph.E4, Holomorph.C2]

/-- Crossing disjointness makes the core inject into the four-element action image. -/
theorem card_SC_le_four (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) : Nat.card d.SC ≤ 4 := by
  have h := Nat.card_le_card_of_injective (crossingToFour d hEA)
    (crossingToFour_injective d hEA)
  rwa [rightConjugate_card, card_innerCentralizer] at h

/-- The source rank reduction, before excluding its two branches. -/
theorem primeRank_SC_le_two (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) : primeRank 2 d.SC ≤ 2 := by
  let := hEA
  exact IsElementaryAbelian.primeRank_le_of_card_le (p := 2) d.SC (card_SC_le_four d hEA)

/-- The nontrivial elementary core has precisely the two orders needed by assembly. -/
theorem card_SC_eq_two_or_four (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) : Nat.card d.SC = 2 ∨ Nat.card d.SC = 4 := by
  have hlo : 2 ≤ Nat.card d.SC := by
    have h := Subgroup.card_le_of_le (zpowers_le.mpr d.t_mem)
    rwa [Nat.card_zpowers, d.t_order] at h
  have hhi := card_SC_le_four d hEA
  obtain ⟨n, hn⟩ := (hEA.isPGroup 2 d.SC).exists_card_eq
  have hnb : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hn] using hhi
  interval_cases n <;> simp_all

/-- In the order-four case the disjoint cores generate the entire omega subgroup. -/
theorem plus_eq_sup_crossing_of_card_four (d : EarlierSetup κ G)
    (hEA : IsElementaryAbelian 2 d.SC) (hcard : Nat.card d.SC = 4) :
    plus d = d.SC ⊔ rightConjugate d.x d.SC := by
  have hsurj : Function.Surjective (crossingToFour d hEA) :=
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨crossingToFour_injective d hEA, by
        rw [rightConjugate_card, hcard, card_innerCentralizer]⟩).2
  apply le_antisymm
  · intro a ha
    have haS := (omegaOneAmbient_le _ ha).1
    obtain ⟨c, hc⟩ := hsurj ⟨d.toImageSylow ⟨a, haS⟩, plus_action_mem d ha⟩
    have he : d.toImageSylow ⟨c, d.rightConjugate_le d.sc_le_s c.property⟩ =
        d.toImageSylow ⟨a, haS⟩ := congrArg Subtype.val hc
    have hk : a * (c : G)⁻¹ ∈ d.SC := by
      apply mem_SC_of_toImage_eq_one d
        (a := (⟨a, haS⟩ : d.S) * ⟨c, d.rightConjugate_le d.sc_le_s c.property⟩⁻¹)
      rw [map_mul, map_inv, he, mul_inv_cancel]
    have hm := Subgroup.mul_mem_sup hk c.property
    simpa only [inv_mul_cancel_right] using hm
  · exact sup_le (le_sup_left.trans (core_sup_zK_le_plus d hEA)) (crossing_le_plus d hEA)

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore
