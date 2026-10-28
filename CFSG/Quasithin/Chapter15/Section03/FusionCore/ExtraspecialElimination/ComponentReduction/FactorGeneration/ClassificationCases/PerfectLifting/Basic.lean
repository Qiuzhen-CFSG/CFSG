module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationPreparation
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.ExtraspecialLocal.SourceData
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.SaturatedLift

/-!
# Perfect factors above the star quotient

An actual quasisimple model, or a product of two such models, determines the
C-components of J* and bounds their H*-conjugacy orbits by two. These facts
lift to the C-components of J = localSpan A H. Relative normalization by the
two-perfect Y₀ and the residual-normalizer argument then give L = [L,Y₀],
once L is excluded from M. A noncentral cubic element in the model supplies
that exclusion using theta(M ∩ H) = Y₀ and the solvability of Y₀, which follows
from the extraspecial source alternative. No solvability of M ∩ H is inferred.

The quotient classification identifies the layer of J with its solvable
residual and proves J = J∞ (J ∩ O₂(H)). It does not absorb the second factor.
The kernel equivalence states that remaining obligation explicitly; it
is not a proof of source 15.3.49(i). In particular, no perfectness of J or
strong-offender assertion is assumed. The general lemmas apply to the
selected endpoint A, whose source provenance must be retained in final
assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6,
printed pp.99–110, and the proof of 15.3.49(i), printed pp.1143–1144.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.PerfectLifting
variable {G : Type*} [Group G] [Finite G]

private theorem normalizes_of_star_normalizes
    (H Y0 L : Subgroup G) (hLH : L ≤ H) (hYH : Y0 ≤ H)
    (hL : (L.subgroupOf H).IsCComponent)
    (hn : starImage H Y0 ≤ normalizer (starImage H L : Set (H ⧸ pCore 2 H))) :
    Y0 ≤ normalizer (L : Set G) := by
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have hi : Y0.subgroupOf H ≤ normalizer (L.subgroupOf H : Set H) := by
    rw [← normalizer_cComponent_quotient hL (pCore 2 H)]
    exact map_le_iff_le_comap.mp hn
  apply le_normalizer_iff.mpr
  intro y hy l hl
  exact le_normalizer_iff.mp hi (⟨y, hYH hy⟩ : H) hy (⟨l, hLH hl⟩ : H) hl

/-- A normalized component cannot centralize Y0 modulo O₂(H): that would
put it in the solvable local intersection. -/
private theorem component_commutator_of_not_le_M
    (H M Y0 L : Subgroup G) (hLM : ¬ L ≤ M)
    (hLH : L ≤ H) (hYH : Y0 ≤ H) (hL : (L.subgroupOf H).IsCComponent)
    (hY : IsPPerfect 2 Y0) (hN : normalizer (Y0 : Set G) = M)
    (hQM : localTwoCore H ≤ M)
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (horbit : (Set.range fun h : H ⧸ pCore 2 H =>
      (starImage H L).map (MulAut.conj h).toMonoidHom).ncard ≤ 2) :
    L = ⁅L, Y0⁆ := by
  have hn := normalizes_of_star_normalizes H Y0 L hLH hYH hL
    (star_normalizes_of_two_conjugates H Y0 L hYH hY horbit)
  have hc : Theory.GroupTheory.IsComponent (H ⧸ pCore 2 H) (starImage H L) :=
    ⟨hL.subnormal.map (QuotientGroup.mk'_surjective _), hq⟩
  rcases hc.commutator_dichotomy (starImage H Y0) with hb | he
  · have hcomm := commutator_le_twoCore_of_star_commutes H L Y0 hLH hYH hn hb
    exact (hLM
      (le_M_of_commutator_le_twoCore H M Y0 L hY hN hLH hL.subnormal hQM hcomm)).elim
  · apply commutator_eq_of_star_eq H L Y0 hLH hYH hL hn
    apply le_antisymm (he ▸ le_iSup_conjugates _ _)
    rw [← starImage_commutator H L Y0 hLH hYH]
    exact map_mono (comap_mono (le_normalizer_iff_commutator_le_left.mp hn))

/-- The solvable-intersection version of the local commutator argument. -/
theorem component_commutator_of_quasisimple_star
    (H M Y0 L : Subgroup G) [Group.IsSolvable (M ⊓ H : Subgroup G)]
    (hLH : L ≤ H) (hYH : Y0 ≤ H) (hL : (L.subgroupOf H).IsCComponent)
    (hY : IsPPerfect 2 Y0) (hN : normalizer (Y0 : Set G) = M)
    (hQM : localTwoCore H ≤ M)
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (horbit : (Set.range fun h : H ⧸ pCore 2 H =>
      (starImage H L).map (MulAut.conj h).toMonoidHom).ncard ≤ 2) :
    L = ⁅L, Y0⁆ :=
  component_commutator_of_not_le_M H M Y0 L
    (component_not_le_solvable_intersection H M L hLH hL)
    hLH hYH hL hY hN hQM hq horbit

private theorem theta_top_eq_top_of_noncentral_cubic {D : Type*} [Group D]
    [Theory.GroupTheory.IsQuasisimple D]
    (x : D) (hx : orderOf x = 3) (hn : x ∉ center D) : theta (⊤ : Subgroup D) = ⊤ := by
  have hnorm : (theta (⊤ : Subgroup D)).Normal := by
    rw [← normalizer_eq_top_iff]
    apply top_unique
    simpa only [normalizer_eq_top] using normalizer_le_normalizer_theta (⊤ : Subgroup D)
  let := hnorm
  rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top
      (theta (⊤ : Subgroup D)) with hc | ht
  · exact (hn (hc (subset_closure ⟨mem_top x, hx⟩))).elim
  · exact ht

/-- The model fact needed to prevent a perfect factor from lying in M
is only a noncentral element of order three. No simplicity or order
certification beyond the given quasisimple branch data is used. -/
theorem component_commutator_of_noncentral_cubic
    (H M Y0 L : Subgroup G) [Group.IsSolvable Y0]
    (hLH : L ≤ H) (hYH : Y0 ≤ H) (hL : (L.subgroupOf H).IsCComponent)
    (hY : IsPPerfect 2 Y0) (hN : normalizer (Y0 : Set G) = M)
    (hQM : localTwoCore H ≤ M) (hθ : theta (M ⊓ H) = Y0)
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (horbit : (Set.range fun h : H ⧸ pCore 2 H =>
      (starImage H L).map (MulAut.conj h).toMonoidHom).ncard ≤ 2)
    (x : starImage H L) (hx : orderOf x = 3) (hn : x ∉ center (starImage H L)) :
    L = ⁅L, Y0⁆ := by
  apply component_commutator_of_not_le_M H M Y0 L _ hLH hYH hL hY hN hQM hq horbit
  intro hLM
  let := hq
  have ht : theta (starImage H L) = starImage H L := by
    have hh := theta_map_of_injective (starImage H L).subtype
      (starImage H L).subtype_injective (⊤ : Subgroup (starImage H L))
    rw [theta_top_eq_top_of_noncentral_cubic x hx hn,
      ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hh.symm
  have hle : starImage H L ≤ starImage H Y0 := by
    rw [← ht, ← starImage_theta H L hLH]
    exact map_mono (comap_mono ((theta_mono (le_inf hLM hLH)).trans_eq hθ))
  let : Group.IsSolvable (Y0.subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hYH).toMonoidHom) (subgroupOfEquivOfLe hYH).injective
  let : Group.IsSolvable (starImage H Y0) :=
    Group.isSolvable_of_surjective ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective _)
  let : IsSimpleGroup (starImage H L ⧸ center (starImage H L)) := hq.simple
  let : Nontrivial (starImage H L) := (QuotientGroup.mk'_surjective (center (starImage H L))).nontrivial
  exact Group.IsPerfect.not_isSolvable (starImage H L)
    (Group.isSolvable_of_isSolvable_injective (inclusion_injective hle))

/-- Solvability of Y0 follows from the actual order-27 two-core quotient
of Y in the extraspecial source branch. -/
theorem Y0_solvable_of_extraspecial
    (M Y V Y0 : Subgroup G)
    (h : CosetSetup.ExtraspecialLocal.ExtraspecialCase M Y V) (hY0 : Y0 ≤ Y) :
    Group.IsSolvable Y0 := by
  have hp : IsPGroup 3 (Y ⧸ pCore 2 Y) := IsPGroup.of_card (n := 3) h.quotient_card
  let : Group.IsNilpotent (Y ⧸ pCore 2 Y) := hp.isNilpotent
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable Y := (Group.isSolvable_iff_subgroup_quotient (pCore 2 Y)).mpr
    ⟨inferInstance, inferInstance⟩
  exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hY0)

/-- The universal commutator clause can be proved before the conjugate span
is known to be perfect. The star-factor conditions are classification inputs. -/
theorem all_components_commutator
    (H M Y0 A : Subgroup G) [Group.IsSolvable (M ⊓ H : Subgroup G)]
    (hAH : A ≤ H) (hYH : Y0 ≤ H)
    (hY : IsPPerfect 2 Y0) (hN : normalizer (Y0 : Set G) = M)
    (hQM : localTwoCore H ≤ M)
    (hfactors : ∀ L : Subgroup G, L ≤ localSpan A H →
      (L.subgroupOf (localSpan A H)).IsCComponent →
      Theory.GroupTheory.IsQuasisimple (starImage H L) ∧
        (Set.range fun h : H ⧸ pCore 2 H =>
          (starImage H L).map (MulAut.conj h).toMonoidHom).ncard ≤ 2) :
    ∀ L : Subgroup G, L ≤ localSpan A H →
      (L.subgroupOf (localSpan A H)).IsCComponent → L = ⁅L, Y0⁆ := by
  intro L hLJ hL
  obtain ⟨hq, ho⟩ := hfactors L hLJ hL
  exact component_commutator_of_quasisimple_star H M Y0 L
    (hLJ.trans (conjugateSpanBy_le_self hAH)) hYH
    (localSpan_component_isCComponent A H L hAH hLJ hL) hY hN hQM hq ho

private theorem cComponent_of_quasisimple {D : Type*} [Group D]
    (L : Subgroup D) (hs : L.IsSubnormal) [Theory.GroupTheory.IsQuasisimple L] :
    L.IsCComponent := by
  let : IsSimpleGroup (L ⧸ center L) := Theory.GroupTheory.IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  refine ⟨(nontrivial_iff_ne_bot L).mp inferInstance, inferInstance, hs, ?_⟩
  intro K hKL hK hp hsub
  rcases Theory.GroupTheory.IsQuasisimple.subnormal_le_center_or_eq_top
      (K.subgroupOf L) hsub.subgroupOf with hc | ht
  · let := hp
    let : Group.IsPerfect (K.subgroupOf L) :=
      Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKL).symm.toMonoidHom)
        (subgroupOfEquivOfLe hKL).symm.surjective
    have hb : K.subgroupOf L = ⊥ := by
      rw [← commutator_eq_self (H := K.subgroupOf L)]
      exact le_bot_iff.mp ((commutator_mono hc le_top).trans
        (commutator_center_left (⊤ : Subgroup L)).le)
    have he := congrArg (map L.subtype) hb
    exact (hK (by simpa only [map_subgroupOf_eq_of_le hKL, Subgroup.map_bot] using he)).elim
  · exact subgroupOf_eq_top.mp ht

private theorem quasisimple_layer_eq_top {D : Type*} [Group D]
    [Theory.GroupTheory.IsQuasisimple D] : cComponentLayer D = ⊤ := by
  let : Theory.GroupTheory.IsQuasisimple (⊤ : Subgroup D) :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv topEquiv.symm
  exact top_unique (le_cComponentLayer (cComponent_of_quasisimple ⊤ IsSubnormal.top))

omit [Finite G] in
/-- A genuine quasisimple model gives the whole star layer, without making
any assertion about the kernel of J → J*. -/
theorem starLayer_eq_top_of_quasisimple_model {D : Type*} [Group D]
    [Theory.GroupTheory.IsQuasisimple D]
    (H A : Subgroup G) (e : starImage H (localSpan A H) ≃* D) :
    cComponentLayer (starImage H (localSpan A H)) = ⊤ := by
  let := Theory.GroupTheory.IsQuasisimple.of_mulEquiv e.symm
  exact quasisimple_layer_eq_top

private theorem layer_eq_top_of_two_components {D : Type*} [Group D]
    (B C : Subgroup D) (hB : Theory.GroupTheory.IsComponent D B)
    (hC : Theory.GroupTheory.IsComponent D C) (hgen : B ⊔ C = ⊤) :
    cComponentLayer D = ⊤ := by
  let := hB.2
  let := hC.2
  exact top_unique (hgen ▸ sup_le
    (le_cComponentLayer (cComponent_of_quasisimple B hB.1))
    (le_cComponentLayer (cComponent_of_quasisimple C hC.1)))

private theorem component_eq_of_pair_cover {D : Type*} [Group D] [Finite D]
    (B C : Subgroup D) (hB : Theory.GroupTheory.IsComponent D B)
    (hC : Theory.GroupTheory.IsComponent D C) (hgen : B ⊔ C = ⊤)
    (K : Subgroup D) (hK : K.IsCComponent) : K = B ∨ K = C := by
  let := hB.2
  let := hC.2
  have htop := layer_eq_top_of_two_components B C hB hC hgen
  have hnorm : K.Normal := by
    rw [← normalizer_eq_top_iff]
    exact top_unique (htop ▸ cComponentLayer_le_normalizer hK)
  let := hnorm
  rcases hB.normal_dichotomy K with hBK | hBK
  · exact Or.inl ((cComponent_of_quasisimple B hB.1).eq_of_le hK hBK).symm
  rcases hC.normal_dichotomy K with hCK | hCK
  · exact Or.inr ((cComponent_of_quasisimple C hC.1).eq_of_le hK hCK).symm
  have hc : (⊤ : Subgroup D) ≤ centralizer (K : Set D) := by
    rw [← hgen]
    exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hBK)
      (commutator_eq_bot_iff_le_centralizer.mp hCK)
  have hh : ⁅K, K⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr (le_top.trans hc)
  exact (hK.ne_bot ((Subgroup.isPerfect_iff.mp hK.perfect).symm.trans hh)).elim

private theorem star_factors_of_pair_cover
    (H A : Subgroup G) (hAH : A ≤ H)
    (B C : Subgroup (starImage H (localSpan A H)))
    (hB : Theory.GroupTheory.IsComponent (starImage H (localSpan A H)) B)
    (hC : Theory.GroupTheory.IsComponent (starImage H (localSpan A H)) C)
    (hgen : B ⊔ C = ⊤) :
    ∀ L : Subgroup G, L ≤ localSpan A H →
      (L.subgroupOf (localSpan A H)).IsCComponent →
      Theory.GroupTheory.IsQuasisimple (starImage H L) ∧
        (Set.range fun h : H ⧸ pCore 2 H =>
          (starImage H L).map (MulAut.conj h).toMonoidHom).ncard ≤ 2 := by
  let Jstar := starImage H (localSpan A H)
  have hn : Jstar.Normal := (localSpan_normal A H hAH).map _ (QuotientGroup.mk'_surjective _)
  let := hn
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have hclass (K : Subgroup (H ⧸ pCore 2 H)) (hK : K.IsCComponent) (hKJ : K ≤ Jstar) :
      K = B.map Jstar.subtype ∨ K = C.map Jstar.subtype := by
    rcases component_eq_of_pair_cover B C hB hC hgen (K.subgroupOf Jstar)
      (hK.subgroupOf hKJ) with he | he
    · left
      rw [← he, map_subgroupOf_eq_of_le hKJ]
    · right
      rw [← he, map_subgroupOf_eq_of_le hKJ]
  have hqB : Theory.GroupTheory.IsQuasisimple (B.map Jstar.subtype) := by
    let := hB.2
    exact Theory.GroupTheory.IsQuasisimple.of_mulEquiv
      (B.equivMapOfInjective Jstar.subtype Jstar.subtype_injective)
  have hqC : Theory.GroupTheory.IsQuasisimple (C.map Jstar.subtype) := by
    let := hC.2
    exact Theory.GroupTheory.IsQuasisimple.of_mulEquiv
      (C.equivMapOfInjective Jstar.subtype Jstar.subtype_injective)
  intro L hLJ hL
  have hLH := localSpan_component_isCComponent A H L hAH hLJ hL
  have hK : (starImage H L).IsCComponent := hLH.map_quotient (pCore 2 H)
  have hKJ : starImage H L ≤ Jstar := map_mono (comap_mono hLJ)
  refine ⟨?_, ?_⟩
  · rcases hclass _ hK hKJ with he | he
    · exact he ▸ hqB
    · exact he ▸ hqC
  · have hrange : (Set.range fun h : H ⧸ pCore 2 H =>
        (starImage H L).map (MulAut.conj h).toMonoidHom) ⊆
        {B.map Jstar.subtype, C.map Jstar.subtype} := by
      rintro _ ⟨h, rfl⟩
      apply Set.mem_insert_iff.mpr
      have hconj : (starImage H L).map (MulAut.conj h).toMonoidHom ≤ Jstar := by
        rintro _ ⟨k, hk, rfl⟩
        exact hn.conj_mem k (hKJ hk) h
      rcases hclass _ (hK.map_equiv (MulAut.conj h)) hconj with he | he
      · exact Or.inl he
      · exact Or.inr (Set.mem_singleton_iff.mpr he)
    calc
      _ ≤ ({B.map Jstar.subtype, C.map Jstar.subtype} : Set (Subgroup (H ⧸ pCore 2 H))).ncard :=
        Set.ncard_le_ncard hrange
      _ ≤ 2 := by
        by_cases he : B.map Jstar.subtype = C.map Jstar.subtype
        · simp only [he, Set.pair_eq_singleton, Set.ncard_singleton]; decide
        · rw [Set.ncard_pair he]

private theorem product_component_pair {D E : Type*} [Group D] [Group E]
    [Theory.GroupTheory.IsQuasisimple D] [Theory.GroupTheory.IsQuasisimple E] :
    ∃ B C : Subgroup (D × E), Theory.GroupTheory.IsComponent (D × E) B ∧
      Theory.GroupTheory.IsComponent (D × E) C ∧ B ⊔ C = ⊤ := by
  let B := (⊤ : Subgroup D).prod (⊥ : Subgroup E)
  let C := (⊥ : Subgroup D).prod (⊤ : Subgroup E)
  let eB : B ≃* D := ((Subgroup.prodEquiv _ _).trans .prodUnique).trans topEquiv
  let eC : C ≃* E := ((Subgroup.prodEquiv _ _).trans .uniqueProd).trans topEquiv
  let : Theory.GroupTheory.IsQuasisimple B :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv eB.symm
  let : Theory.GroupTheory.IsQuasisimple C :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv eC.symm
  refine ⟨B, C, ⟨(inferInstance : B.Normal).isSubnormal, inferInstance⟩,
    ⟨(inferInstance : C.Normal).isSubnormal, inferInstance⟩, ?_⟩
  apply top_unique
  rintro ⟨d, e⟩ _
  have hd : (d, (1 : E)) ∈ B := ⟨mem_top _, rfl⟩
  have he : ((1 : D), e) ∈ C := ⟨rfl, mem_top _⟩
  simpa only [Prod.mk_mul_mk, mul_one, one_mul] using
    (B ⊔ C).mul_mem (mem_sup_left hd) (mem_sup_right he)

omit [Finite G] in
/-- This handles the actor-group part common to the two perfect factors
in B.5.6(3) and (5), irrespective of the module-extension alternative. -/
theorem starLayer_eq_top_of_product_model {D E : Type*} [Group D] [Group E]
    [Theory.GroupTheory.IsQuasisimple D] [Theory.GroupTheory.IsQuasisimple E]
    (H A : Subgroup G) (e : starImage H (localSpan A H) ≃* D × E) :
    cComponentLayer (starImage H (localSpan A H)) = ⊤ := by
  apply map_injective (f := e.toMonoidHom) e.injective
  obtain ⟨B, C, hB, hC, hgen⟩ := product_component_pair (D := D) (E := E)
  rw [map_cComponentLayer_equiv e, layer_eq_top_of_two_components B C hB hC hgen,
    map_top_of_surjective _ e.surjective]

/-- In the single quasisimple actor branch, every lifted component has
quasisimple star image and at most two H*-conjugates (in fact one). -/
theorem starFactors_of_quasisimple_model {D : Type*} [Group D]
    [Theory.GroupTheory.IsQuasisimple D]
    (H A : Subgroup G) (hAH : A ≤ H)
    (e : starImage H (localSpan A H) ≃* D) :
    ∀ L : Subgroup G, L ≤ localSpan A H →
      (L.subgroupOf (localSpan A H)).IsCComponent →
      Theory.GroupTheory.IsQuasisimple (starImage H L) ∧
        (Set.range fun h : H ⧸ pCore 2 H =>
          (starImage H L).map (MulAut.conj h).toMonoidHom).ncard ≤ 2 := by
  let := Theory.GroupTheory.IsQuasisimple.of_mulEquiv e.symm
  let : Theory.GroupTheory.IsQuasisimple (⊤ : Subgroup (starImage H (localSpan A H))) :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv topEquiv.symm
  exact star_factors_of_pair_cover H A hAH ⊤ ⊤
    ⟨IsSubnormal.top, inferInstance⟩ ⟨IsSubnormal.top, inferInstance⟩ (sup_idem _)

/-- In the product actor branch, the star images are precisely among the
two actual quasisimple factors; H* can only permute those factors. -/
theorem starFactors_of_product_model {D E : Type*} [Group D] [Group E]
    [Theory.GroupTheory.IsQuasisimple D] [Theory.GroupTheory.IsQuasisimple E]
    (H A : Subgroup G) (hAH : A ≤ H)
    (e : starImage H (localSpan A H) ≃* D × E) :
    ∀ L : Subgroup G, L ≤ localSpan A H →
      (L.subgroupOf (localSpan A H)).IsCComponent →
      Theory.GroupTheory.IsQuasisimple (starImage H L) ∧
        (Set.range fun h : H ⧸ pCore 2 H =>
          (starImage H L).map (MulAut.conj h).toMonoidHom).ncard ≤ 2 := by
  obtain ⟨B, C, hB, hC, hgen⟩ := product_component_pair (D := D) (E := E)
  apply star_factors_of_pair_cover H A hAH (B.map e.symm.toMonoidHom)
    (C.map e.symm.toMonoidHom) (hB.map_equiv e.symm) (hC.map_equiv e.symm)
  rw [← Subgroup.map_sup, hgen, map_top_of_surjective _ e.symm.surjective]

private theorem residual_eq_top_of_layer_eq_top {D : Type*} [Group D]
    (h : cComponentLayer D = ⊤) : solvableResidual D = ⊤ := by
  let := cComponentLayer_isPerfect (G := D)
  exact top_unique (h ▸ le_solvableResidual_of_isPerfect (cComponentLayer D))

private theorem layer_eq_residual_of_surjective {D : Type*} [Group D]
    (f : G →* D) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (hD : cComponentLayer D = ⊤) : cComponentLayer G = solvableResidual G := by
  apply cComponentLayer_eq_residual_of_quotient f.ker
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_cComponentLayer_equiv e, map_solvableResidual_eq e.toMonoidHom e.surjective,
    hD, residual_eq_top_of_layer_eq_top hD]

/-- For J=⟨A^H⟩, the actual star projection determines its C-component
layer as its solvable residual. This does not assert that J is perfect. -/
theorem layer_eq_residual_of_star_layer
    (H A : Subgroup G) (hAH : A ≤ H)
    (hstar : cComponentLayer (starImage H (localSpan A H)) = ⊤) :
    cComponentLayer (localSpan A H) = solvableResidual (localSpan A H) := by
  let JH := (localSpan A H).subgroupOf H
  let f := spanStarProjection H A
  have hk : IsPGroup 2 f.ker := spanStarProjection_kernel_twoGroup H A
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  have he := layer_eq_residual_of_surjective f (spanStarProjection_surjective H A) hstar
  let e := subgroupOfEquivOfLe (conjugateSpanBy_le_self hAH)
  have hm := congrArg (map e.toMonoidHom) he
  rwa [map_cComponentLayer_equiv, map_solvableResidual_eq _ e.surjective] at hm

/-- The solvable residual and the intersection with O₂(H) generate J.
This displays the kernel left over after the star classification. -/
theorem residual_sup_kernel_of_star_layer
    (H A : Subgroup G) (hAH : A ≤ H)
    (hstar : cComponentLayer (starImage H (localSpan A H)) = ⊤) :
    (solvableResidual (localSpan A H)).map (localSpan A H).subtype ⊔
      (localSpan A H ⊓ localTwoCore H) = localSpan A H := by
  let J := localSpan A H
  have hJH : J ≤ H := conjugateSpanBy_le_self hAH
  let f := (spanStarProjection H A).comp (subgroupOfEquivOfLe hJH).symm.toMonoidHom
  have hf : Function.Surjective f :=
    (spanStarProjection_surjective H A).comp (subgroupOfEquivOfLe hJH).symm.surjective
  have hr : (solvableResidual J).map f = ⊤ :=
    (map_solvableResidual_eq f hf).trans (residual_eq_top_of_layer_eq_top hstar)
  have hs : solvableResidual J ⊔ f.ker = ⊤ := by
    have hh := congrArg (comap f) hr
    simpa only [comap_map_eq, comap_top] using hh
  have hker : f.ker.map J.subtype = J ⊓ localTwoCore H := by
    ext x
    constructor
    · rintro ⟨j, hj, rfl⟩
      refine ⟨j.property, ⟨⟨j, hJH j.property⟩, ?_, rfl⟩⟩
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val hj
    · rintro ⟨hxJ, y, hy, rfl⟩
      refine ⟨⟨y, hxJ⟩, ?_, rfl⟩
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff y).mpr hy
  have hm := congrArg (map J.subtype) hs
  simpa only [Subgroup.map_sup, hker, ← MonoidHom.range_eq_map, range_subtype] using hm

/-- Kernel absorption is precisely the missing part of generation in J,
after the star classification. It is not an assumption of a source theorem. -/
theorem layer_eq_span_iff_kernel_le_residual
    (H A : Subgroup G) (hAH : A ≤ H)
    (hstar : cComponentLayer (starImage H (localSpan A H)) = ⊤) :
    (cComponentLayer (localSpan A H)).map (localSpan A H).subtype = localSpan A H ↔
      localSpan A H ⊓ localTwoCore H ≤
        (solvableResidual (localSpan A H)).map (localSpan A H).subtype := by
  rw [layer_eq_residual_of_star_layer H A hAH hstar]
  constructor
  · intro he
    rw [he]
    exact inf_le_left
  · intro hk
    have h := residual_sup_kernel_of_star_layer H A hAH hstar
    rwa [sup_eq_left.mpr hk] at h

private theorem star_component_models_of_pair {D : Type*} [Group D] [Finite D]
    (H A L : Subgroup G) (hAH : A ≤ H) (hLJ : L ≤ localSpan A H)
    (hL : (L.subgroupOf (localSpan A H)).IsCComponent)
    (e : starImage H (localSpan A H) ≃* D)
    (B C : Subgroup D) (hB : Theory.GroupTheory.IsComponent D B)
    (hC : Theory.GroupTheory.IsComponent D C) (hgen : B ⊔ C = ⊤) :
    Nonempty (starImage H L ≃* B) ∨ Nonempty (starImage H L ≃* C) := by
  let Jstar := starImage H (localSpan A H)
  have hKJ : starImage H L ≤ Jstar := map_mono (comap_mono hLJ)
  let K := (starImage H L).subgroupOf Jstar
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  have hK : K.IsCComponent :=
    ((localSpan_component_isCComponent A H L hAH hLJ hL).map_quotient
      (pCore 2 H)).subgroupOf hKJ
  let ek : starImage H L ≃* K.map e.toMonoidHom :=
    (subgroupOfEquivOfLe hKJ).symm.trans (K.equivMapOfInjective e.toMonoidHom e.injective)
  rcases component_eq_of_pair_cover B C hB hC hgen _ (hK.map_equiv e) with he | he
  · exact Or.inl ⟨ek.trans (MulEquiv.subgroupCongr he)⟩
  · exact Or.inr ⟨ek.trans (MulEquiv.subgroupCongr he)⟩

/-- The star image of every component has the specified single actor model. -/
theorem starModel_of_quasisimple_model {D : Type*} [Group D]
    [Theory.GroupTheory.IsQuasisimple D]
    (H A L : Subgroup G) (hAH : A ≤ H) (hLJ : L ≤ localSpan A H)
    (hL : (L.subgroupOf (localSpan A H)).IsCComponent)
    (e : starImage H (localSpan A H) ≃* D) :
    Nonempty (starImage H L ≃* D) := by
  let : Finite D := Finite.of_surjective e e.surjective
  let : Theory.GroupTheory.IsQuasisimple (⊤ : Subgroup D) :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv topEquiv.symm
  have hm := star_component_models_of_pair H A L hAH hLJ hL e ⊤ ⊤
    ⟨IsSubnormal.top, inferInstance⟩ ⟨IsSubnormal.top, inferInstance⟩ (sup_idem _)
  rcases hm with hf | hf
  all_goals
    obtain ⟨f⟩ := hf
    exact ⟨f.trans topEquiv⟩

/-- Each star component is identified with one of the two actual model factors. -/
theorem starModel_of_product_model {D E : Type*} [Group D] [Group E]
    [Theory.GroupTheory.IsQuasisimple D] [Theory.GroupTheory.IsQuasisimple E]
    (H A L : Subgroup G) (hAH : A ≤ H) (hLJ : L ≤ localSpan A H)
    (hL : (L.subgroupOf (localSpan A H)).IsCComponent)
    (e : starImage H (localSpan A H) ≃* D × E) :
    Nonempty (starImage H L ≃* D) ∨ Nonempty (starImage H L ≃* E) := by
  let : Finite (D × E) := Finite.of_surjective e e.surjective
  let B := (⊤ : Subgroup D).prod (⊥ : Subgroup E)
  let C := (⊥ : Subgroup D).prod (⊤ : Subgroup E)
  let eB : B ≃* D := ((Subgroup.prodEquiv _ _).trans .prodUnique).trans topEquiv
  let eC : C ≃* E := ((Subgroup.prodEquiv _ _).trans .uniqueProd).trans topEquiv
  let : Theory.GroupTheory.IsQuasisimple B := Theory.GroupTheory.IsQuasisimple.of_mulEquiv eB.symm
  let : Theory.GroupTheory.IsQuasisimple C := Theory.GroupTheory.IsQuasisimple.of_mulEquiv eC.symm
  have hgen : B ⊔ C = ⊤ := by
    apply top_unique
    rintro ⟨d, f⟩ _
    have hd : (d, (1 : E)) ∈ B := ⟨mem_top _, rfl⟩
    have hf : ((1 : D), f) ∈ C := ⟨rfl, mem_top _⟩
    simpa only [Prod.mk_mul_mk, mul_one, one_mul] using
      (B ⊔ C).mul_mem (mem_sup_left hd) (mem_sup_right hf)
  rcases star_component_models_of_pair H A L hAH hLJ hL e B C
      ⟨(inferInstance : B.Normal).isSubnormal, inferInstance⟩
      ⟨(inferInstance : C.Normal).isSubnormal, inferInstance⟩ hgen with hf | hf
  · obtain ⟨f⟩ := hf
    exact Or.inl ⟨f.trans eB⟩
  · obtain ⟨f⟩ := hf
    exact Or.inr ⟨f.trans eC⟩

private theorem noncentral_cubic_transport {D E : Type*} [Group D] [Group E]
    (e : D ≃* E) (x : E) (hx : orderOf x = 3) (hn : x ∉ center E) :
    ∃ y : D, orderOf y = 3 ∧ y ∉ center D := by
  refine ⟨e.symm x, (e.symm.orderOf_eq x).trans hx, ?_⟩
  intro hc
  have hh := ((centerCongr e) ⟨e.symm x, hc⟩).property
  change e (e.symm x) ∈ center E at hh
  exact hn (by simpa only [MulEquiv.apply_symm_apply] using hh)

/-- Universal Y₀-commutator generation in the single perfect-actor branch.
Only the indicated cubic witness is needed from its concrete model. -/
theorem all_components_commutator_of_quasisimple_model {D : Type*} [Group D]
    [Theory.GroupTheory.IsQuasisimple D]
    (H M Y0 A : Subgroup G) [Group.IsSolvable Y0]
    (hAH : A ≤ H) (hYH : Y0 ≤ H)
    (hY : IsPPerfect 2 Y0) (hN : normalizer (Y0 : Set G) = M)
    (hQM : localTwoCore H ≤ M) (hθ : theta (M ⊓ H) = Y0)
    (e : starImage H (localSpan A H) ≃* D)
    (x : D) (hx : orderOf x = 3) (hn : x ∉ center D) :
    ∀ L : Subgroup G, L ≤ localSpan A H →
      (L.subgroupOf (localSpan A H)).IsCComponent → L = ⁅L, Y0⁆ := by
  intro L hLJ hL
  obtain ⟨f⟩ := starModel_of_quasisimple_model H A L hAH hLJ hL e
  obtain ⟨y, hy, hyn⟩ := noncentral_cubic_transport f x hx hn
  obtain ⟨hq, ho⟩ := starFactors_of_quasisimple_model H A hAH e L hLJ hL
  exact component_commutator_of_noncentral_cubic H M Y0 L
    (hLJ.trans (conjugateSpanBy_le_self hAH)) hYH
    (localSpan_component_isCComponent A H L hAH hLJ hL) hY hN hQM hθ hq ho y hy hyn

/-- Universal Y₀-commutator generation for the two perfect factors.
This argument is independent of the natural, double-natural, indecomposable,
or hyperplane alternatives for their common section module. -/
theorem all_components_commutator_of_product_model {D E : Type*} [Group D] [Group E]
    [Theory.GroupTheory.IsQuasisimple D] [Theory.GroupTheory.IsQuasisimple E]
    (H M Y0 A : Subgroup G) [Group.IsSolvable Y0]
    (hAH : A ≤ H) (hYH : Y0 ≤ H)
    (hY : IsPPerfect 2 Y0) (hN : normalizer (Y0 : Set G) = M)
    (hQM : localTwoCore H ≤ M) (hθ : theta (M ⊓ H) = Y0)
    (e : starImage H (localSpan A H) ≃* D × E)
    (x : D) (hx : orderOf x = 3) (hn : x ∉ center D)
    (z : E) (hz : orderOf z = 3) (hzn : z ∉ center E) :
    ∀ L : Subgroup G, L ≤ localSpan A H →
      (L.subgroupOf (localSpan A H)).IsCComponent → L = ⁅L, Y0⁆ := by
  intro L hLJ hL
  have hw : ∃ y : starImage H L, orderOf y = 3 ∧ y ∉ center (starImage H L) := by
    rcases starModel_of_product_model H A L hAH hLJ hL e with hf | hf
    · obtain ⟨f⟩ := hf
      exact noncentral_cubic_transport f x hx hn
    · obtain ⟨f⟩ := hf
      exact noncentral_cubic_transport f z hz hzn
  obtain ⟨y, hy, hyn⟩ := hw
  obtain ⟨hq, ho⟩ := starFactors_of_product_model H A hAH e L hLJ hL
  exact component_commutator_of_noncentral_cubic H M Y0 L
    (hLJ.trans (conjugateSpanBy_le_self hAH)) hYH
    (localSpan_component_isCComponent A H L hAH hLJ hL) hY hN hQM hθ hq ho y hy hyn

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.FactorGeneration.ClassificationCases.PerfectLifting
