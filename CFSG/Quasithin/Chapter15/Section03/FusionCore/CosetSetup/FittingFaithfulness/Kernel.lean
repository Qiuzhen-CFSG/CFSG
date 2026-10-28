module

public import Theory.GroupTheory.CComponent.RadicalFree
public import Theory.GroupTheory.Fitting.Subgroup
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.QuotientActions
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# Detecting the kernel after removing a centralized two-layer

A normal subgroup disjoint from the genuine generalized Fitting subgroup is
trivial: its solvable radical has trivial Fitting subgroup, and a nonsolvable
radical-free remainder would contain an ordinary component.

An actor fixing a two-subgroup C and acting trivially modulo C embeds modulo
its pointwise kernel into displacement functions with values in C. This makes
the actor a two-group when its pointwise kernel is a two-group. The argument
requires no commutativity of the group acted on.

These are the kernel arguments used in Aschbacher–Smith, proof of 15.3.49(a),
printed p.1142 (combined manuscript of 1 March 2004).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness

open Subgroup Theory.GroupTheory

theorem normal_eq_bot_of_disjoint_generalizedFitting {G : Type*} [Group G] [Finite G]
    (N : Subgroup G) [N.Normal]
    (hdis : N ⊓ generalizedFitting G = ⊥) : N = ⊥ := by
  have hsolv (D : Subgroup G) [D.Normal] [Group.IsSolvable D] (hDN : D ≤ N) : D = ⊥ := by
    have hF : fittingSubgroupOf D ≤ generalizedFitting G := by
      apply le_trans _ (fitting_le_generalizedFitting G)
      exact le_sSup ⟨fittingSubgroupOf_normal D inferInstance,
        fittingSubgroupOf_isNilpotent D⟩
    have hb : fittingSubgroupOf D = ⊥ := le_bot_iff.mp
      ((le_inf ((map_subtype_le _).trans hDN) hF).trans hdis.le)
    have hb' : fittingSubgroup D = ⊥ :=
      (map_eq_bot_iff_of_injective _ D.subtype_injective).mp hb
    exact (Subgroup.card_le_one_iff_eq_bot D).mp
      (le_of_eq ((fitting_eq_bot_iff_card_eq_one_of_solvable D).mp hb'))
  let R := (solvableRadical N).map N.subtype
  let : Group.IsSolvable R := Group.isSolvable_of_surjective
    (N.subtype.subgroupMap_surjective (solvableRadical N))
  have hR : R = ⊥ := hsolv R (map_subtype_le _)
  have hrad : solvableRadical N = ⊥ :=
    (map_eq_bot_iff_of_injective _ N.subtype_injective).mp hR
  by_cases hnsolv : Group.IsSolvable N
  · let := hnsolv
    exact hsolv N le_rfl
  obtain ⟨L, hL⟩ := exists_isCComponent_of_not_isSolvable hnsolv
  have hcomp : IsComponent N L :=
    (isCComponent_iff_isSubnormal_and_isQuasisimple_of_solvableRadical_eq_bot hrad).mp hL
  let := hcomp.2
  have hmap : IsComponent G (L.map N.subtype) := by
    refine ⟨(hL.map_subtype (inferInstance : N.Normal).isSubnormal).subnormal, ?_⟩
    exact IsQuasisimple.of_mulEquiv (L.equivMapOfInjective N.subtype N.subtype_injective)
  have hb : L.map N.subtype = ⊥ := le_bot_iff.mp
    ((le_inf (map_subtype_le _) (component_le_generalizedFitting G _ hmap)).trans hdis.le)
  exact (hL.ne_bot ((map_eq_bot_iff_of_injective _ N.subtype_injective).mp hb)).elim

open Subgroup
open scoped commutatorElement

theorem layer_kernel_pgroup {G : Type*} [Group G] [Finite G]
    (U C D : Subgroup G) (hC : IsPGroup 2 C)
    (hfix : D ≤ centralizer (C : Set G)) (hcomm : ⁅U,D⁆ ≤ C)
    (hdetect : D ⊓ centralizer (U : Set G) ≤ pCore 2 G) : IsPGroup 2 D := by
  have hmem (d : D) (u : U) : (u : G)⁻¹ * ((d : G) * u * (d : G)⁻¹) ∈ C := by
    simpa [commutatorElement_def, mul_assoc] using
      hcomm (commutator_mem_commutator (U.inv_mem u.property) d.property)
  let f : D →* (U → C) := {
    toFun := fun d u => ⟨(u : G)⁻¹ * ((d : G) * u * (d : G)⁻¹), hmem d u⟩
    map_one' := by funext u; apply Subtype.ext; simp
    map_mul' := by
      intro d e
      funext u
      apply Subtype.ext
      change (u : G)⁻¹ * (((d : G) * e) * u * ((d : G) * e)⁻¹) =
        ((u : G)⁻¹ * ((d : G) * u * (d : G)⁻¹)) *
          ((u : G)⁻¹ * ((e : G) * u * (e : G)⁻¹))
      have hf := hfix d.property _ (hmem e u)
      calc
        _ = (u : G)⁻¹ * ((d : G) * u *
          ((u : G)⁻¹ * ((e : G) * u * (e : G)⁻¹)) * (d : G)⁻¹) := by group
        _ = (u : G)⁻¹ * ((d : G) * u) *
          (((u : G)⁻¹ * ((e : G) * u * (e : G)⁻¹)) * (d : G)⁻¹) := by group
        _ = _ := by
          rw [(show Commute ((u : G)⁻¹ * ((e : G) * u * (e : G)⁻¹)) (d : G) from hf).inv_right.eq]
          group }
  have hk : IsPGroup 2 f.ker := by
    apply (pCore_isPGroup (p := 2) (G := G)).comap_of_injective D.subtype
      D.subtype_injective |>.to_le
    intro d hd
    apply hdetect
    refine ⟨d.property, ?_⟩
    change (d : G) ∈ centralizer (U : Set G)
    rw [mem_centralizer_iff]
    intro u hu
    have he := congrArg Subtype.val (congrFun hd ⟨u, hu⟩)
    change u⁻¹ * ((d : G) * u * (d : G)⁻¹) = 1 at he
    have he' : (d : G) * u * (d : G)⁻¹ = u := (inv_mul_eq_one.mp he).symm
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  have hp : IsPGroup 2 (U → C) := by
    obtain ⟨n, hn⟩ := hC.exists_card_dvd_pow
    intro v
    refine ⟨n, ?_⟩
    funext u
    exact orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard (v u)).trans hn)
  intro d
  obtain ⟨n, hn⟩ := hp (f d)
  have hm : d ^ (2 ^ n) ∈ f.ker := by rw [MonoidHom.mem_ker, map_pow]; exact hn
  obtain ⟨m, hm⟩ := hk ⟨d ^ (2 ^ n), hm⟩
  refine ⟨n + m, ?_⟩
  simpa [pow_add, pow_mul] using congrArg Subtype.val hm

/-- Removing a two-layer centralized by the inverse image of F*(G/O₂(G))
preserves the faithful quotient action. No commutativity of U is required. -/
theorem centralizerModulo_le_twoCore
    {G : Type*} [Group G] [Finite G]
    (U C Z : Subgroup G) [U.Normal] [C.Normal] [Z.Normal]
    (hC : IsPGroup 2 C)
    (hsmall : centralizerModulo ⊤ U Z ≤ pCore 2 G)
    (hfit : (generalizedFitting (G ⧸ pCore 2 G)).comap
      (QuotientGroup.mk' (pCore 2 G)) ≤ centralizer (C : Set G)) :
    centralizerModulo ⊤ U C ≤ pCore 2 G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let K := centralizerModulo ⊤ U C
  let R := (generalizedFitting (G ⧸ pCore 2 G)).comap q
  let : (U.map (QuotientGroup.mk' C)).Normal := (inferInstance : U.Normal).map _
    (QuotientGroup.mk'_surjective _)
  let : K.Normal := by unfold K centralizerModulo; infer_instance
  let : R.Normal := inferInstanceAs
    ((generalizedFitting (G ⧸ pCore 2 G)).comap q).Normal
  let : (K.map q).Normal := (inferInstance : K.Normal).map q
    (QuotientGroup.mk'_surjective _)
  let D := K ⊓ R
  have hcomm : ⁅U,D⁆ ≤ C := commutator_le.mpr (fun u hu d hd =>
    (mem_centralizerModulo_iff.mp hd.1).2 u hu)
  have hdetect : D ⊓ centralizer (U : Set G) ≤ pCore 2 G := by
    intro d hd
    apply hsmall
    apply mem_centralizerModulo_iff.mpr
    refine ⟨mem_top _, fun u hu => ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm.mpr ((mem_centralizer_iff.mp hd.2) u hu)]
    exact Z.one_mem
  have hDp : IsPGroup 2 D := layer_kernel_pgroup U C D hC
    (inf_le_right.trans hfit) hcomm hdetect
  have hDQ : D ≤ pCore 2 G := le_sSup ⟨inferInstance, hDp⟩
  have hdis : K.map q ⊓ generalizedFitting (G ⧸ pCore 2 G) = ⊥ := by
    apply le_bot_iff.mp
    rintro x ⟨⟨k, hk, rfl⟩, hf⟩
    exact (QuotientGroup.eq_one_iff _).mpr (hDQ ⟨hk, hf⟩)
  have hk := normal_eq_bot_of_disjoint_generalizedFitting (K.map q) hdis
  simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hk

/-- The representative form required by the commutator duality consumer. -/
theorem faithful_on_representatives
    {G : Type*} [Group G] [Finite G]
    (U C Z : Subgroup G) [U.Normal] [C.Normal] [Z.Normal]
    (hC : IsPGroup 2 C)
    (hsmall : centralizerModulo ⊤ U Z ≤ pCore 2 G)
    (hfit : (generalizedFitting (G ⧸ pCore 2 G)).comap
      (QuotientGroup.mk' (pCore 2 G)) ≤ centralizer (C : Set G)) :
    ∀ g : G, (∀ u : U,
      QuotientGroup.mk' (C.subgroupOf U)
        ⟨g * u * g⁻¹, (inferInstance : U.Normal).conj_mem u u.property g⟩ =
      QuotientGroup.mk' (C.subgroupOf U) u) → g ∈ pCore 2 G := by
  intro g hg
  apply centralizerModulo_le_twoCore U C Z hC hsmall hfit
  apply mem_centralizerModulo_iff.mpr
  refine ⟨mem_top _, fun u hu => ?_⟩
  have hc := QuotientGroup.eq_iff_div_mem.mp (hg ⟨u, hu⟩)
  change g * u * g⁻¹ / u ∈ C at hc
  simpa only [commutatorElement_def, div_eq_mul_inv, mul_inv_rev, inv_inv, mul_assoc]
    using C.inv_mem hc

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.FittingFaithfulness
end
