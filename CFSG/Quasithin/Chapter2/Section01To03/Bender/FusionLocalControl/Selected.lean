module

public import Theory.Quasithin
public import Theory.GroupTheory.MinimalNormalPCore
public import Theory.GroupTheory.TwoLocalUniquenessControl
public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Theory.GroupTheory.SetStrongClosure
public import Theory.GroupTheory.AbelianWeakClosureFusion
public import Theory.GroupTheory.UniqueFixedCosetFusion
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The elementary normal subgroup in the Bender reduction

A minimal normal subgroup inside the two-core of M is elementary abelian.
Maximal two-local uniqueness identifies its normalizer with M and controls
the centralizer of a nonidentity element in its intersection with Z(T).
The conjugation action is the literal normalizer action; minimality proves
that it has no proper nontrivial invariant subgroup.

Strong closure, when supplied by the preceding fusion-family theorem, gives
Burnside fusion in U and then its conjugacy-class intersection with M. Together
with centralizer containment this constructs the unique fixed coset of z.
The selection itself uses only maximal two-local uniqueness. No recognition,
strong embedding, or centrality of all of U in T is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Proposition 2.2.2, p. 519.
-/

@[expose] public section

open Subgroup
open Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G]

theorem weakClosure_of_strongClosure (T : Sylow 2 G) (U : Subgroup G)
    (hc : IsStronglyClosedSet (U : Set G) (T : Subgroup G) ⊤) :
    ∀ g : G, U.conjBy g ≤ (T : Subgroup G) → U.conjBy g = U := by
  intro g hg
  apply eq_of_le_of_card_ge
  · rintro x ⟨u, hu, rfl⟩
    have h := hc.2 u hu g⁻¹ (mem_top _) (by
      simpa only [inv_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hg (mem_map.mpr ⟨u, hu, rfl⟩))
    simpa only [inv_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, SetLike.mem_coe] using h
  · exact (card_map_of_injective (K := U) (MulAut.conj g).injective).ge

theorem fusion_into_normal_abelian (T : Sylow 2 G) {M U : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hMU : M ≤ normalizer (U : Set G))
    [IsMulCommutative U]
    (hc : IsStronglyClosedSet (U : Set G) (T : Subgroup G) ⊤)
    (hNM : normalizer (U : Set G) ≤ M)
    {x y : G} (hx : x ∈ U) (hy : y ∈ M) (hxy : IsConj x y) :
    y ∈ U ∧ ∃ m ∈ M, m * x * m⁻¹ = y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  have hxp : IsPGroup 2 (zpowers x) := T.isPGroup'.of_injective
    (inclusion (zpowers_le.mpr (hc.1 hx))) (inclusion_injective _)
  have hyp : IsPGroup 2 (zpowers y) := by
    have hle : zpowers y ≤ (zpowers x).map (MulAut.conj g).toMonoidHom :=
      zpowers_le.mpr ⟨x, mem_zpowers x, hg⟩
    exact (hxp.map _).of_injective (inclusion hle) (inclusion_injective hle)
  obtain ⟨a, haM, ha⟩ := UniqueFixedCoset.p_element_conjugate_into_sylow T hTM hy hyp
  have hcurrent : a * y * a⁻¹ ∈ U := by
    have he : (a * g) * x * (a * g)⁻¹ = a * y * a⁻¹ := by
      calc
        _ = a * (g * x * g⁻¹) * a⁻¹ := by group
        _ = _ := by rw [hg]
    have hh := hc.2 x hx (a * g)⁻¹ (mem_top _) (by simpa only [inv_inv, he] using ha)
    simpa only [inv_inv, he, SetLike.mem_coe] using hh
  have hyU : y ∈ U := by
    have hh := (mem_normalizer_iff.mp (hMU (M.inv_mem haM)) (a * y * a⁻¹)).mp hcurrent
    simpa only [inv_inv, mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel, one_mul, inv_mul_cancel_left] using hh
  obtain ⟨n, hn, hne⟩ := T.normalizer_fuses_of_abelian_weakly_closed U hc.1
    (weakClosure_of_strongClosure T U hc) hx hyU hxy
  exact ⟨hyU, n, hNM hn, hne⟩

theorem exists_selected_subgroup (T : Sylow 2 G) (M : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M) :
    ∃ U : Subgroup G, U ≠ ⊥ ∧ U ≤ M.pCoreIn 2 ∧
      IsElementaryAbelian 2 U ∧ M ≤ normalizer (U : Set G) ∧
      normalizer (U : Set G) = M ∧ U ≤ (T : Subgroup G) ∧
      (∀ W : Subgroup G, W ≤ U → M ≤ normalizer (W : Set G) → W = ⊥ ∨ W = U) ∧
      ∃ z : G, z ∈ U ∧ z ≠ 1 ∧ (∀ t ∈ (T : Subgroup G), Commute z t) ∧
        centralizer ({z} : Set G) ≤ M := by
  obtain ⟨Q, hQne, hQp, hMQ⟩ := hM.1
  have hQM : Q ≤ M := hMQ ▸ Q.le_normalizer
  have hMQn : M ≤ normalizer (Q : Set G) := hMQ.le
  have hcore : pCore 2 M ≠ ⊥ := by
    have hle := le_pCoreIn_of_normalizes hQp hQM hMQn
    intro he
    have hbot : M.pCoreIn 2 = ⊥ := by simp [pCoreIn, he]
    exact hQne (bot_unique (hbot ▸ hle))
  obtain ⟨V, hVn, hVne, hVcore, hVe, hVmin⟩ := exists_minimal_normal_le_pCore hcore
  let _ : V.Normal := hVn
  let _ : IsElementaryAbelian 2 V := hVe
  let U := V.map M.subtype
  have hUne : U ≠ ⊥ := fun h => hVne ((V.map_eq_bot_iff_of_injective M.subtype_injective).mp h)
  have hUcore : U ≤ M.pCoreIn 2 := map_mono hVcore
  have hUM : U ≤ M := map_subtype_le _
  have hMU : M ≤ normalizer (U : Set G) := by
    apply le_normalizer_iff.mpr
    intro m hm u hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact ⟨⟨m, hm⟩ * v * ⟨m, hm⟩⁻¹, hVn.conj_mem v hv ⟨m, hm⟩, rfl⟩
  let _ : IsElementaryAbelian 2 U := IsElementaryAbelian.map_subtype
  have hUp := IsElementaryAbelian.isPGroup 2 U
  have hNU : normalizer (U : Set G) = M := le_antisymm
    (normalizer_le_of_unique_maximalTwoLocal hunique hUp hUne (hTM.trans hMU)) hMU
  have hUT : U ≤ (T : Subgroup G) := by
    have hh := hUcore.trans (pCoreIn_le_sylow M (T.subtype hTM))
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using hh
  have hmin : ∀ W : Subgroup G, W ≤ U → M ≤ normalizer (W : Set G) →
      W = ⊥ ∨ W = U := by
    intro W hWU hMW
    have hWM := hWU.trans hUM
    let _ : (W.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hWM).mpr hMW
    have hWV : W.subgroupOf M ≤ V := by
      intro w hw
      obtain ⟨v, hv, he⟩ := hWU hw
      exact (M.subtype_injective he) ▸ hv
    rcases hVmin (W.subgroupOf M) inferInstance hWV with hb | ht
    · left
      have hh := congrArg (fun A : Subgroup M => A.map M.subtype) hb
      simpa only [map_subgroupOf_eq_of_le hWM, Subgroup.map_bot] using hh
    · right
      have hh := congrArg (fun A : Subgroup M => A.map M.subtype) ht
      simpa only [map_subgroupOf_eq_of_le hWM] using hh
  let _ : (U.subgroupOf (T : Subgroup G)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUT).mpr (hTM.trans hMU)
  let _ : Nontrivial U := (nontrivial_iff_ne_bot U).mpr hUne
  let _ : Nontrivial (U.subgroupOf (T : Subgroup G)) :=
    (subgroupOfEquivOfLe hUT).symm.injective.nontrivial
  let _ : Fact (IsPGroup 2 T) := ⟨T.isPGroup'⟩
  obtain ⟨z, hzne, hzcenter⟩ := exists_nontrivial_center_mem_normal
    (p := 2) (U.subgroupOf (T : Subgroup G))
  have hzU : ((z : T) : G) ∈ U := z.property
  have hz1 : ((z : T) : G) ≠ 1 := by
    intro he
    exact hzne (Subtype.ext (Subtype.ext he))
  have hzc : ∀ t ∈ (T : Subgroup G), Commute ((z : T) : G) t := by
    intro t ht
    exact (congrArg Subtype.val (mem_center_iff.mp hzcenter ⟨t, ht⟩)).symm
  have hZp : IsPGroup 2 (zpowers ((z : T) : G)) := T.isPGroup'.of_injective
    (inclusion (zpowers_le.mpr (z : T).property)) (inclusion_injective _)
  have hZne : zpowers ((z : T) : G) ≠ ⊥ := by
    intro he
    exact hz1 (by simpa only [he, mem_bot] using mem_zpowers ((z : T) : G))
  have hTZ : (T : Subgroup G) ≤ normalizer (zpowers ((z : T) : G) : Set G) := by
    apply le_trans _ (centralizer_le_normalizer _)
    rw [zpowers_eq_closure, centralizer_closure]
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hzc t ht).symm.eq
  have hCM : centralizer ({((z : T) : G)} : Set G) ≤ M := by
    have hn := normalizer_le_of_unique_maximalTwoLocal hunique hZp hZne hTZ
    rw [zpowers_eq_closure] at hn
    have hh := centralizer_le_normalizer (closure ({((z : T) : G)} : Set G) : Set G)
    rw [centralizer_closure] at hh
    exact hh.trans hn
  exact ⟨U, hUne, hUcore, inferInstance, hMU, hNU, hUT, hmin,
    ((z : T) : G), hzU, hz1, hzc, hCM⟩

/-- The actual conjugation action associated with relative normality. -/
def conjugationAction (M U : Subgroup G) (hMU : M ≤ normalizer (U : Set G)) :
    M →* MulAut U := U.normalizerMonoidHom.comp (inclusion hMU)

omit [Finite G] in
theorem conjugationAction_irreducible {M U : Subgroup G}
    (hMU : M ≤ normalizer (U : Set G))
    (hmin : ∀ W : Subgroup G, W ≤ U → M ≤ normalizer (W : Set G) → W = ⊥ ∨ W = U)
    (W : Subgroup U)
    (hW : ∀ m : M, ∀ u : U, u ∈ W → conjugationAction M U hMU m u ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have hMW : M ≤ normalizer (W.map U.subtype : Set G) := by
    apply le_normalizer_iff.mpr
    intro m hm x hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨conjugationAction M U hMU ⟨m, hm⟩ u, hW ⟨m, hm⟩ u hu, rfl⟩
  rcases hmin (W.map U.subtype) (map_subtype_le _) hMW with hb | ht
  · exact Or.inl ((W.map_eq_bot_iff_of_injective U.subtype_injective).mp hb)
  · right
    apply map_injective U.subtype_injective
    simpa only [← MonoidHom.range_eq_map, range_subtype] using ht

theorem unique_fixed_coset_of_selected (T : Sylow 2 G) {M U : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hMU : M ≤ normalizer (U : Set G))
    [IsMulCommutative U]
    (hc : IsStronglyClosedSet (U : Set G) (T : Subgroup G) ⊤)
    (hNM : normalizer (U : Set G) ≤ M) {z : G} (hz : z ∈ U)
    (hC : centralizer ({z} : Set G) ≤ M) :
    ∃! q : G ⧸ M, z • q = q := by
  apply UniqueFixedCoset.unique_of_fusion_and_centralizer (hTM (hc.1 hz)) hC
  intro g hg
  obtain ⟨_, m, hm, he⟩ := fusion_into_normal_abelian T hTM hMU hc hNM hz hg
    (isConj_iff.mpr ⟨g, rfl⟩)
  exact ⟨m, hm, he.symm⟩
end CFSG.Quasithin.Chapter2.BenderFusion
