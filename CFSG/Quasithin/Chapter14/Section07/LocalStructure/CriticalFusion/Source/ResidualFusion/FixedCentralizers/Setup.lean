module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.Basic
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Centralizer, Sylow and component reductions for 14.7.68

For the original fixed element u, write G_u = C_G(u) and T_u = C_T(u).
The product H = KT and the previously proved K-centralization give
H ∩ G_u = KT_u. Fixation modulo the point makes T_u normal in T, so
KT_u is normal in H and T_u is Sylow in KT_u.

A nonidentity subgroup characteristic in T_u and normal in KT_u then has
normalizer H by maximal two-locality. The normalizer condition in two-groups
promotes T_u to a Sylow subgroup of G_u. Its genuine Chapter 1 local family
contains K. The universal earlier A.3.12 and A.3.8 implications enlarge K
to a C-component normal in G_u. If G_u escapes H, that component strictly
contains K and also escapes H. The original z and H satisfy all hypotheses
of 1.1.5, through the proved 1.1.6.

`FixedCharacteristicWitness` records the intermediate characteristic subgroup;
this module does not assert its existence. Its construction uses the actual
dual chief factors and C.1.26. Likewise, the universal A.3 inputs remain
explicit: their existing source owners are qt-a-03 and
qt-1-02-adequate-assembly. The subsequent component exclusions and final
centralizer bound remain with the fixed-centralizer assembly.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.68(2), printed pp.1071–1072; 1.1.6 and 1.2.4, pp.503–505.
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Data
variable (d : Data T L V F W)

def fixedCentralizer (_d : Data T L V F W) (u : F.U) : Subgroup G := centralizer ({(u : G)} : Set G)
def fixedSylow (u : F.U) : Subgroup G := (T : Subgroup G) ⊓ d.fixedCentralizer u

theorem K_le_fixedCentralizer (u : F.U) (hu : (u : G) ∈ d.U₀) :
    K F ≤ d.fixedCentralizer u :=
  d.K_centralizes_U₀.trans (centralizer_le (Set.singleton_subset_iff.mpr hu))

theorem fixedCentralizer_inter_H (u : F.U) (hu : (u : G) ∈ d.U₀) :
    F.H ⊓ d.fixedCentralizer u = K F ⊔ d.fixedSylow u := by
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (K F : Set G) * ((T : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left (K F) (T : Subgroup G)
        ((F.invariant 1).trans (H_normalizes_K F)), ← d.residual_product]
      exact hx.1
    obtain ⟨k, hk, t, ht, rfl⟩ := hxprod
    apply mul_mem_sup hk
    refine ⟨ht, ?_⟩
    change t ∈ d.fixedCentralizer u
    have hkt := (d.fixedCentralizer u).mul_mem
      ((d.fixedCentralizer u).inv_mem (d.K_le_fixedCentralizer u hu hk)) hx.2
    simpa only [inv_mul_cancel_left] using hkt
  · exact sup_le (le_inf (K_le_H F) (d.K_le_fixedCentralizer u hu))
      (le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right)

theorem T_normalizes_fixedSylow (u : F.U) (hu : d.FixedModuloPoint u) :
    (T : Subgroup G) ≤ normalizer (d.fixedSylow u : Set G) := by
  have hn := d.fixedModuloPoint_centralizer_normal u hu
  have he : (d.fixedSylow u).subgroupOf (T : Subgroup G) =
      (d.fixedCentralizer u).subgroupOf (T : Subgroup G) := by
    ext x
    exact and_iff_right x.property
  apply (normal_subgroupOf_iff_le_normalizer inf_le_left).mp
  change ((d.fixedSylow u).subgroupOf (T : Subgroup G)).Normal
  rwa [he]

theorem fixedCentralizer_inter_H_normal (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hfix : d.FixedModuloPoint u) :
    ((F.H ⊓ d.fixedCentralizer u : Subgroup G).subgroupOf F.H).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
  rw [d.fixedCentralizer_inter_H u hu, d.residual_product]
  refine sup_le ((show K F ≤ K F ⊔ d.fixedSylow u from le_sup_left).trans le_normalizer) ?_
  exact (le_inf ((F.invariant 1).trans (H_normalizes_K F))
    (d.T_normalizes_fixedSylow u hfix)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

theorem fixedSylow_isSylow_inter_H (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hfix : d.FixedModuloPoint u) :
    Chapter1.IsSylowIn 2 (d.fixedSylow u) (F.H ⊓ d.fixedCentralizer u : Subgroup G) := by
  let J := F.H ⊓ d.fixedCentralizer u
  let N := J.subgroupOf F.H
  have hN : N.Normal := d.fixedCentralizer_inter_H_normal u hu hfix
  obtain ⟨P, hP⟩ := @Sylow.exists_subgroupOf_eq_of_normal F.H _ _ 2 _
    (T.subtype (F.invariant 1)) N hN
  let e : N ≃* J := subgroupOfEquivOfLe inf_le_left
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((P : Subgroup N).map e.toMonoidHom).map J.subtype = d.fixedSylow u
  rw [hP]
  ext x
  constructor
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨hb, b.property.2⟩
  · rintro ⟨ht, hc⟩
    exact ⟨⟨x, (F.invariant 1 ht), hc⟩,
      ⟨⟨⟨x, F.invariant 1 ht⟩, ⟨F.invariant 1 ht, hc⟩⟩, ht, rfl⟩, rfl⟩

/-- The characteristic subgroup is inside the actual C_T(u); normality is
relative to K C_T(u), and no ambient normality is imposed. Its existence is
the missing chief-factor/C.1.26 step. -/
structure FixedCharacteristicWitness (u : F.U) where
  subgroup : Subgroup (d.fixedSylow u)
  characteristic : subgroup.Characteristic
  nontrivial : subgroup ≠ ⊥
  normal : ((subgroup.map (d.fixedSylow u).subtype).subgroupOf
    (K F ⊔ d.fixedSylow u)).Normal

namespace FixedCharacteristicWitness
variable {d} {u : F.U} (c : d.FixedCharacteristicWitness u)

theorem normalizer_eq (hfix : d.FixedModuloPoint u)
    (hmax : IsMaximalTwoLocal F.H) :
    normalizer (c.subgroup.map (d.fixedSylow u).subtype : Set G) = F.H := by
  let := c.characteristic
  have hC : c.subgroup.map (d.fixedSylow u).subtype ≤ K F ⊔ d.fixedSylow u :=
    (map_subtype_le _).trans le_sup_right
  have hH : F.H ≤ normalizer (c.subgroup.map (d.fixedSylow u).subtype : Set G) := by
    rw [d.residual_product]
    exact sup_le
      (le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer hC).mp c.normal))
      ((d.T_normalizes_fixedSylow u hfix).trans
        (normalizer_le_normalizer_characteristic_image _ _))
  have hlocal : IsTwoLocal (normalizer (c.subgroup.map (d.fixedSylow u).subtype : Set G)) :=
    ⟨_, fun he => c.nontrivial
      ((c.subgroup.map_eq_bot_iff_of_injective (d.fixedSylow u).subtype_injective).mp he),
      ((T.isPGroup'.to_le inf_le_left).to_subgroup c.subgroup).map _, rfl⟩
  exact le_antisymm (hmax.2 hlocal hH) hH

include c in
theorem fixedSylow_isSylow (hu : (u : G) ∈ d.U₀) (hfix : d.FixedModuloPoint u)
    (hmax : IsMaximalTwoLocal F.H) :
    Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u) := by
  let := c.characteristic
  have hnorm : normalizer (d.fixedSylow u : Set G) ≤ F.H :=
    (normalizer_le_normalizer_characteristic_image _ c.subgroup).trans_eq
      (c.normalizer_eq hfix hmax)
  obtain ⟨hp, _, hm⟩ := Chapter1.isSylowIn_iff.mp (d.fixedSylow_isSylow_inter_H u hu hfix)
  refine Chapter1.isSylowIn_iff.mpr ⟨hp, inf_le_right, ?_⟩
  intro P hP hSP hPG
  exact prime_overgroup_eq_of_normalizer_control (d.fixedSylow u) (d.fixedCentralizer u)
    F.H hnorm (fun Q hQ hSQ hQG hQH => hm Q hQ hSQ (le_inf hQH hQG))
    P hP hSP hPG

end FixedCharacteristicWitness

include d in
theorem fixedElement_order (u : F.U) (hne : (u : G) ≠ 1) : orderOf (u : G) = 2 := by
  let := d.U_elementary
  exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (u : G) u.property) hne

theorem fixedCentralizer_sqtk (u : F.U) (hne : (u : G) ≠ 1) :
    IsSQTK KnownSimple.IsKnownSimple (d.fixedCentralizer u) :=
  d.counterexample.qtke.involution_centralizer_sqtk (d.fixedElement_order u hne)

theorem point_le_fixedSylow (u : F.U) : F.Vi 1 ≤ d.fixedSylow u := by
  intro x hx
  refine ⟨d.natural.chosen.le_sylow (F.le_seed 1 hx), ?_⟩
  apply mem_centralizer_singleton_iff.mpr
  exact mem_centralizer_iff.mp
    (d.H_centralizes_point (d.conjugationSection.section_le u.property)) x hx

theorem fixedJoin_core_ne_bot (u : F.U) : (K F ⊔ d.fixedSylow u).pCoreIn 2 ≠ ⊥ := by
  have hJH : K F ⊔ d.fixedSylow u ≤ F.H :=
    sup_le (K_le_H F) (inf_le_left.trans (F.invariant 1))
  have hpoint : F.Vi 1 ≤ (K F ⊔ d.fixedSylow u).pCoreIn 2 :=
    le_pCoreIn_of_normalizes d.point_twoGroup
      ((d.point_le_fixedSylow u).trans le_sup_right) hJH
  intro he
  have hz : d.z ∈ (K F ⊔ d.fixedSylow u).pCoreIn 2 :=
    hpoint (by rw [d.point]; exact mem_zpowers d.z)
  rw [he] at hz
  exact d.z_ne_one hz

theorem K_mem_fixedLocalFamily (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hfix : d.FixedModuloPoint u) : K F ∈ Chapter1.L G (d.fixedSylow u) := by
  refine ⟨d.component.subgroupOf_of_le le_sup_left
    (sup_le (K_le_H F) (inf_le_left.trans (F.invariant 1))), ?_, d.fixedJoin_core_ne_bot u⟩
  rw [← d.fixedCentralizer_inter_H u hu]
  exact d.fixedSylow_isSylow_inter_H u hu hfix

theorem fixedCentralizer_core_ne_bot (u : F.U) (hne : (u : G) ≠ 1) :
    (d.fixedCentralizer u).pCoreIn 2 ≠ ⊥ :=
  Chapter1.mem_H_of_isTwoLocal
    (Theory.GroupTheory.isTwoLocal_involution_centralizer (d.fixedElement_order u hne))

theorem fixedCentralizer_quotient_sqtk (u : F.U) (hne : (u : G) ≠ 1) :
    IsSQTK KnownSimple.IsKnownSimple ((d.fixedCentralizer u) ⧸ pCore 2 (d.fixedCentralizer u)) :=
  Chapter1.Section02.uniqueness_local_quotient_sqtk d.counterexample.qtke
    (d.fixedCentralizer_core_ne_bot u hne)

/-- Apply the actual earlier A.3.12 and A.3.8 implications to C_G(u).
The containing component is normal only relative to C_G(u). -/
theorem exists_fixedComponent
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
      ∀ (S : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents S →
      ∃! D : Subgroup X, D.IsCComponent ∧ B ≤ D)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
      ∀ D : Subgroup X, D.IsCComponent →
      D.Normal ∨ (normalizer (D : Set X)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel D)
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u)) :
    ∃ Lu : Subgroup G, Lu ≤ d.fixedCentralizer u ∧
      (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent ∧ K F ≤ Lu ∧
      (Lu.subgroupOf (d.fixedCentralizer u)).Normal := by
  obtain ⟨S, hS⟩ := hsyl
  have hloc : (K F).subgroupOf (d.fixedCentralizer u) ∈
      Chapter1.L (d.fixedCentralizer u) (S : Subgroup (d.fixedCentralizer u)) := by
    rw [← Chapter1.mem_L_map_iff (d.fixedCentralizer u).subtype
      (d.fixedCentralizer u).subtype_injective,
      map_subgroupOf_eq_of_le (d.K_le_fixedCentralizer u hu), hS]
    exact d.K_mem_fixedLocalFamily u hu hfix
  obtain ⟨D, hD, hKD, _, hn⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_of_A_3_12_A_3_8
      hA312 hA38 (d.fixedCentralizer_quotient_sqtk u hne) S hloc
  have hSnorm : (S : Subgroup (d.fixedCentralizer u)) ≤
      normalizer ((K F).subgroupOf (d.fixedCentralizer u) : Set (d.fixedCentralizer u)) := by
    rw [← subgroupOf_normalizer_eq (d.K_le_fixedCentralizer u hu)]
    intro s hs
    have hsT : (s : G) ∈ (T : Subgroup G) :=
      (show (s : G) ∈ d.fixedSylow u by rw [← hS]; exact mem_map_of_mem _ hs).1
    exact H_normalizes_K F (F.invariant 1 hsT)
  have hmap : (D.map (d.fixedCentralizer u).subtype).subgroupOf (d.fixedCentralizer u) = D :=
    comap_map_eq_self_of_injective (d.fixedCentralizer u).subtype_injective _
  refine ⟨D.map (d.fixedCentralizer u).subtype, map_subtype_le _, hmap.symm ▸ hD, ?_,
    hmap.symm ▸ hn hSnorm⟩
  simpa only [map_subgroupOf_eq_of_le (d.K_le_fixedCentralizer u hu)] using
    map_mono (f := (d.fixedCentralizer u).subtype) hKD

/-- A containing component normal in C_G(u) must escape H when C_G(u) does.
If it lay in H, restriction to H ∩ C_G(u) would identify it with K. -/
theorem fixedComponent_not_le_H (u : F.U) (hu : (u : G) ∈ d.U₀)
    (hNK : normalizer (K F : Set G) = F.H) (hout : ¬ d.fixedCentralizer u ≤ F.H)
    {Lu : Subgroup G} (hLu : Lu ≤ d.fixedCentralizer u)
    (hc : (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent)
    (hKLu : K F ≤ Lu) (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal) :
    ¬ Lu ≤ F.H := by
  intro hLH
  have hKH : K F ≤ F.H ⊓ d.fixedCentralizer u :=
    le_inf (K_le_H F) (d.K_le_fixedCentralizer u hu)
  have hLJ : Lu ≤ F.H ⊓ d.fixedCentralizer u := le_inf hLH hLu
  have he := (d.component.subgroupOf_of_le hKH inf_le_left).eq_of_le
    (hc.subgroupOf_of_le hLJ inf_le_right) (comap_mono hKLu)
  have hKL : K F = Lu := by
    simpa only [map_subgroupOf_eq_of_le hKH, map_subgroupOf_eq_of_le hLJ] using
      congrArg (map (F.H ⊓ d.fixedCentralizer u : Subgroup G).subtype) he
  have hGnorm := (normal_subgroupOf_iff_le_normalizer hLu).mp hn
  rw [← hKL, hNK] at hGnorm
  exact hout hGnorm


/-- All hypotheses of the source 1.1.5 are verified on C_G(u), with the
original z and H. The only Sylow premise is the one constructed from C.1.26. -/
theorem fixedCentralizer_lemma115 (u : F.U) (hne : (u : G) ≠ 1)
    (hmax : IsMaximalTwoLocal F.H)
    (S : Sylow 2 (d.fixedCentralizer u))
    (hS : (S : Subgroup (d.fixedCentralizer u)).map (d.fixedCentralizer u).subtype =
      d.fixedSylow u) : Chapter1.Lemma115Hypotheses (d.fixedCentralizer u) S F.H d.z := by
  have hB : IsPGroup 2 (zpowers (u : G)) := by
    let := d.U_elementary
    exact (IsElementaryAbelian.zpowers_of_pow_eq_one
      (elemPow_eq_one_of_isElementaryAbelian (u : G) u.property)).isPGroup 2 _
  have hBne : zpowers (u : G) ≠ ⊥ := by
    intro he
    have huBot : (u : G) ∈ (⊥ : Subgroup G) := he ▸ mem_zpowers (u : G)
    exact hne huBot
  have hCG : centralizer (zpowers (u : G) : Set G) = d.fixedCentralizer u := by
    rw [zpowers_eq_closure, centralizer_closure]
    rfl
  have hzU : d.z ∈ F.U := d.U₀_le_U d.z_mem_U₀
  have hzT : d.z ∈ (T : Subgroup G) :=
    (d.point_le_fixedSylow u (by rw [d.point]; exact mem_zpowers d.z)).1
  apply Chapter1.lemma_1_1_6 hBne hB
    (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr rfl)) hCG.le
    (hCG.ge.trans (centralizer_le_normalizer (zpowers (u : G) : Set G))) S T
    (hS ▸ inf_le_left) (d.fixedElement_order ⟨d.z, hzU⟩ d.z_ne_one) hzT
    (fun t ht => mem_centralizer_singleton_iff.mp
      (d.centralizer_eq ▸ F.invariant 1 ht)) hmax d.centralizer_eq.ge
  intro N hN hTN
  exact Chapter1.mem_He_iff.mpr (d.counterexample.qtke.evenCharacteristic T N hN hTN)

/-- The characteristic-subgroup reduction feeds a genuine normal component
strictly containing K and escaping H. Excluding these components is the
remaining ambient argument of 14.7.68(2). -/
theorem exists_larger_fixedComponent
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
      ∀ (S : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents S →
      ∃! D : Subgroup X, D.IsCComponent ∧ B ≤ D)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK KnownSimple.IsKnownSimple X → pCore 2 X = ⊥ →
      ∀ D : Subgroup X, D.IsCComponent →
      D.Normal ∨ (normalizer (D : Set X)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel D)
    (u : F.U) (hu : (u : G) ∈ d.U₀) (hne : (u : G) ≠ 1)
    (hfix : d.FixedModuloPoint u) (c : d.FixedCharacteristicWitness u)
    (hNK : normalizer (K F : Set G) = F.H) (hmax : IsMaximalTwoLocal F.H)
    (hout : ¬ d.fixedCentralizer u ≤ F.H) :
    ∃ Lu : Subgroup G, Lu ≤ d.fixedCentralizer u ∧
      (Lu.subgroupOf (d.fixedCentralizer u)).IsCComponent ∧ K F < Lu ∧
      (Lu.subgroupOf (d.fixedCentralizer u)).Normal ∧ ¬ Lu ≤ F.H := by
  obtain ⟨Lu, hLu, hc, hKLu, hn⟩ := d.exists_fixedComponent hA312 hA38 u hu hne hfix
    (c.fixedSylow_isSylow hu hfix hmax)
  have hLH := d.fixedComponent_not_le_H u hu hNK hout hLu hc hKLu hn
  exact ⟨Lu, hLu, hc, lt_of_le_of_ne hKLu (fun he => hLH (he ▸ K_le_H F)), hn, hLH⟩
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
