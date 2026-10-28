module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OrthogonalImage
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.WreathRecognition
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.ComponentLocalOrbitCore

/-!
# Residual structure in Lemmas 15.3.7 and 15.3.9

The literal residual is `Y = O²(⟨O₂(M ∩ Mc)^M⟩)`, formed inside `M`
and embedded into `G`. The noncentral intersection core and the compatible
natural orthogonal action give its image and `[V,Y] = V`. The earlier local
dichotomy then gives the intersection product, normalizer and uniqueness;
the star commutator bound gives `O₂(YT) = C_T(V)`.

The assembly constructs all inputs to the two three-group alternatives,
including an actual order-nine model and an inverter lifted from `Rc`.
It derives `C_Rc(V) = O₂(M)` from the core-free actor and `C_M(V) ≤ Mc`.
Thus `lemma_15_3_7_from_earlier_source` retains the complete `E₉` and
exponent-three extraspecial alternatives, including `O^{3′}(M)`,
`O₂,Z(Y)`, `θ(M)`, and both cyclicity assertions.

For 15.3.9, the contrary equality constructs an actual `S₄` wreath
isomorphism via the compatible affine model and its automorphism group.
The exact 13.9.1 exclusion then gives strict core containment and excludes
an actual `A₄ × A₄` residual. Neither exclusion is an input.

`ResidualEarlierInputs` identifies every remaining earlier input: the
standing local choices, the relevant conclusions of 15.3.2 and 15.3.4,
14.1.17(1),(3),(4), the quasithin rank bound and characteristic two.
The natural action is 15.3.2(1); 15.3.9 additionally uses `V = V(M)` and
13.9.1. These inputs remain for the parent source assembly. When applying
14.1.17, use `Y₀ = O²(M)` and its Sylow supplement `Y₀T = M`, so its
normal-closure residual is precisely the one used here. Every star below
is an image in `M/O₂(M)`; relative normality is always inside `M`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemmas 15.3.7 and 15.3.9, printed pp.1122–1123 (PDF pp.1139–1140).
-/

open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03
variable {G : Type*} [Group G] [Finite G]

private theorem join_image_eq_top (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M V)
    (himage : ((residualY M Mc).subgroupOf M).map d.actor =
      twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    (((residualY M Mc).subgroupOf M) ⊔ (T.subtype hTM : Subgroup M)).map d.actor = ⊤ := by
  rw [Subgroup.map_sup, himage]
  exact twoResidualAmbient_top_sup_sylow ((T.subtype hTM).mapSurjective d.onto)

/-- The two-core equality in 15.3.7, from its residual-image calculation,
the earlier star commutator bound, and the intrinsic actor's trivial two-core. -/
public theorem residualY_sylow_core_of_action_image (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M V)
    (himage : ((residualY M Mc).subgroupOf M).map d.actor =
      twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hcomm : ⁅(centralizer (V : Set G)).subgroupOf M,
      ((M ⊓ Mc).pCoreIn 2).subgroupOf M⁆ ≤ pCore 2 M)
    (hcore : pCore 2 OrthogonalActor = ⊥) :
    (residualY M Mc ⊔ (T : Subgroup G)).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  have hcommY : ⁅d.actor.ker, (residualY M Mc).subgroupOf M⁆ ≤ pCore 2 M := by
    apply residualY_commutator_le
    rwa [d.ker_actor]
  have honto : Function.Surjective
      (d.actor.domRestrict ((residualY M Mc).subgroupOf M ⊔ (T.subtype hTM : Subgroup M))) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.domRestrict_range]
    exact join_image_eq_top M Mc V T hTM d himage
  have h := congrArg (Subgroup.map M.subtype)
    (twoCore_join_eq_sylow_inf_ker d.actor ((residualY M Mc).subgroupOf M)
      (T.subtype hTM) hcommY honto hcore)
  rw [map_pCoreIn_of_injective 2 _ M.subtype M.subtype_injective,
    Subgroup.map_sup, map_subgroupOf_eq_of_le
      (Chapter14.SourcePreliminaries.sourceResidual_le M Mc),
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM,
    Subgroup.map_inf _ _ _ M.subtype_injective,
    map_subgroupOf_eq_of_le hTM, d.ker_actor, subgroupOf_map_subtype] at h
  simpa only [inf_comm (centralizer (V : Set G)) M, ← inf_assoc,
    inf_eq_left.mpr hTM] using h

/-- The natural-action commutator equality puts `V` in the two-core of
`Y`, before wreath recognition makes the containment strict. -/
public theorem module_le_residualY_core_of_commutator (M Mc V : Subgroup G) (d : NaturalOrthogonalAction M V)
    (hVM : V ≤ M) (hcomm : ⁅V, residualY M Mc⁆ = V) :
    V ≤ (residualY M Mc).pCoreIn 2 := by
  have hYn : M ≤ normalizer (residualY M Mc : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)).mp (residualY_normal M Mc)
  have hVY : V ≤ residualY M Mc := by
    rw [← hcomm]
    exact le_normalizer_iff_commutator_le_right.mp (hVM.trans hYn)
  have hp : IsPGroup 2 V := IsPGroup.of_card (n := 4) (by simpa using d.card_vector)
  exact le_pCoreIn_of_normalizes hp hVY
    ((Chapter14.SourcePreliminaries.sourceResidual_le M Mc).trans d.normalizes)

/-- The nontrivial module in `O₂(Y)` makes the normalizer two-local,
so maximality identifies it with `M`. -/
public theorem residualY_normalizer_eq_of_commutator (M Mc V : Subgroup G)
    (d : NaturalOrthogonalAction M V) (hM : IsMaximalTwoLocal M)
    (hVM : V ≤ M) (hcomm : ⁅V, residualY M Mc⁆ = V) :
    normalizer (residualY M Mc : Set G) = M := by
  apply normalizer_eq_of_nontrivial_core M (residualY M Mc) V
    (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) hM (residualY_normal M Mc)
  · intro h
    have hc := card_eq_one.mpr h
    rw [d.card_vector] at hc
    norm_num at hc
  · exact module_le_residualY_core_of_commutator M Mc V d hVM hcomm

/-- The factorization is a literal product: normalization of the kernel
by `T` identifies the subgroup join with `C_M(V)T`. -/
public theorem intersection_eq_centralizer_mul_sylow
    (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc)
    (hMc : IsMaximalTwoLocal Mc) (hne : Mc ≠ M)
    (hC : M ⊓ centralizer (V : Set G) ≤ Mc) (d : NaturalOrthogonalAction M V)
    (hcases : ∀ X : Subgroup G, (T : Subgroup G) ≤ X → X ≤ M →
      twoResidualAmbient X ≤ centralizer (V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X M) :
    ((M ⊓ Mc : Subgroup G) : Set G) =
      ((M ⊓ centralizer (V : Set G) : Subgroup G) : Set G) * (T : Set G) := by
  have hCM : d.actor.ker.map M.subtype = M ⊓ centralizer (V : Set G) := by
    rw [d.ker_actor, subgroupOf_map_subtype, inf_comm]
  have hnorm : M ≤ normalizer ((M ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
    rw [← hCM]
    have h := Subgroup.le_normalizer_map (H := d.actor.ker) M.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h
  rw [intersection_eq_centralizer_sup_sylow M Mc V T hTM hTMc hMc hne hC hcases]
  exact coe_mul_of_right_le_normalizer_left _ _ (hTM.trans hnorm)

/-- Assemble the factorization, uniqueness, normalizer and core assertions.
The final source assembly below discharges the action calculations and then
proves the three-group alternatives and strict containment. -/
public theorem residualY_local_structure_of_action_calculations
    (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc)
    (hMc : IsMaximalTwoLocal Mc) (hne : Mc ≠ M)
    (hC : M ⊓ centralizer (V : Set G) ≤ Mc)
    (hVM : V ≤ M) (d : NaturalOrthogonalAction M V)
    (hcases : ∀ X : Subgroup G, (T : Subgroup G) ≤ X → X ≤ M →
      twoResidualAmbient X ≤ centralizer (V : Set G) ∨
        Chapter4.UniqueMaximalOvergroup X M)
    (hcomm : ⁅(centralizer (V : Set G)).subgroupOf M,
      ((M ⊓ Mc).pCoreIn 2).subgroupOf M⁆ ≤ pCore 2 M)
    (himage : ((residualY M Mc).subgroupOf M).map d.actor =
      twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hVcomm : ⁅V, residualY M Mc⁆ = V)
    (hcore : pCore 2 OrthogonalActor = ⊥) :
    M ⊓ Mc = (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) ∧
      M = normalizer (residualY M Mc : Set G) ∧
      Chapter4.UniqueMaximalOvergroup (residualY M Mc ⊔ (T : Subgroup G)) M ∧
      (residualY M Mc ⊔ (T : Subgroup G)).pCoreIn 2 =
        (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      V ≤ (residualY M Mc).pCoreIn 2 := by
  have hnoncentral : ¬ residualY M Mc ≤ centralizer (V : Set G) := by
    intro h
    have hz : V = ⊥ := hVcomm.symm.trans
      ((commutator_comm _ _).trans (commutator_eq_bot_iff_le_centralizer.mpr h))
    have hc := card_eq_one.mpr hz
    rw [d.card_vector] at hc
    norm_num at hc
  have hu := residualY_unique_of_not_centralizing M Mc V T hTM hnoncentral hcases
  exact ⟨intersection_eq_centralizer_sup_sylow M Mc V T hTM hTMc hMc hne hC hcases,
    (residualY_normalizer_eq_of_commutator M Mc V d hu.1 hVM hVcomm).symm,
    hu, residualY_sylow_core_of_action_image M Mc V T hTM d himage hcomm hcore,
    module_le_residualY_core_of_commutator M Mc V d hVM hVcomm⟩

private def elementaryNineCoordinates :
    Multiplicative (Fin 2 → ZMod 3) ≃* ThreeAlternatives.ElementaryNine where
  toFun x := (Multiplicative.ofAdd (Multiplicative.toAdd x 0),
    Multiplicative.ofAdd (Multiplicative.toAdd x 1))
  invFun x := Multiplicative.ofAdd ![Multiplicative.toAdd x.1, Multiplicative.toAdd x.2]
  left_inv x := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> rfl
  right_inv x := rfl
  map_mul' x y := rfl

omit [Finite G] in
private theorem core_le_kernel (M V : Subgroup G) (d : NaturalOrthogonalAction M V) :
    pCore 2 M ≤ d.actor.ker := by
  have hn : ((pCore 2 M).map d.actor).Normal :=
    (inferInstance : (pCore 2 M).Normal).map _ d.onto
  have hle : (pCore 2 M).map d.actor ≤ pCore 2 OrthogonalActor :=
    le_sSup ⟨hn, pCore_isPGroup.map _⟩
  apply (Subgroup.map_eq_bot_iff _).mp
  exact le_bot_iff.mp (orthogonalActor_twoCore_eq_bot ▸ hle)

omit [Finite G] in
private theorem core_inter_kernel (M Mc V : Subgroup G)
    (d : NaturalOrthogonalAction M V)
    (hC : M ⊓ centralizer (V : Set G) ≤ Mc) :
    ((M ⊓ Mc).pCoreIn 2).subgroupOf M ⊓ d.actor.ker = pCore 2 M := by
  let C := d.actor.ker
  have hCI : C.map M.subtype ≤ M ⊓ Mc := by
    change d.actor.ker.map M.subtype ≤ _
    rw [d.ker_actor, subgroupOf_map_subtype, inf_comm]
    exact le_inf inf_le_left hC
  have hCcore : C.pCoreIn 2 = pCore 2 M := by
    rw [pCoreIn, pCore_eq_comap_of_normal, map_comap_eq, range_subtype,
      inf_eq_right.mpr (core_le_kernel M V d)]
  apply (Subgroup.map_injective M.subtype_injective)
  rw [Subgroup.map_inf _ _ _ M.subtype_injective,
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans inf_le_left)]
  change (M ⊓ Mc).pCoreIn 2 ⊓ C.map M.subtype = (pCore 2 M).map M.subtype
  apply le_antisymm
  · have hi := inf_pCoreIn_le_of_le 2 hCI
    rw [← map_pCoreIn_of_injective 2 C M.subtype M.subtype_injective, hCcore] at hi
    simpa only [inf_comm] using hi
  · apply le_inf
    · have hQI : (pCore 2 M).map M.subtype ≤ M ⊓ Mc :=
        (map_mono (core_le_kernel M V d)).trans hCI
      exact le_pCoreIn_of_normalizes (pCore_isPGroup.map M.subtype) hQI
        (inf_le_left.trans (by
          have h := le_normalizer_map (H := pCore 2 M) M.subtype
          simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h))
    · exact map_mono (core_le_kernel M V d)

private theorem lifted_inverter (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc)
    (d : NaturalOrthogonalAction M V)
    (hRc : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G)) :
    ∃ r : M, r ∈ ((M ⊓ Mc).pCoreIn 2).subgroupOf M ∧ d.actor r ≠ 1 ∧
    (d.actor r) ^ 2 = 1 ∧ ∀ y ∈ (residualY M Mc).subgroupOf M,
      d.actor (r * y * r⁻¹) = (d.actor y)⁻¹ := by
  obtain ⟨r, hr, horder, hinv⟩ :=
    intersectionCoreImage_exists_residual_inverter M Mc V T hTM hTMc d hRc
  obtain ⟨s, hs, rfl⟩ := hr
  refine ⟨s, hs, ?_, ?_, ?_⟩
  · intro he
    simp [he] at horder
  · simpa only [horder] using pow_orderOf_eq_one (d.actor s)
  · intro y hy
    simpa only [map_mul, map_inv] using hinv (d.actor y)
      ((residualY_orthogonal_image M Mc V T hTM hTMc d hRc) ▸ mem_map_of_mem d.actor hy)



/-- Earlier source results used for 15.3.7. No conclusion of 15.3.7 or
15.3.9 is a field. The parent supplies the standing local hypotheses and
15.3.2–4; the Chapter 14 assembly supplies the three 14.1.17 inputs. -/
public structure ResidualEarlierInputs (M Mc V : Subgroup G) (T : Sylow 2 G) : Prop where
  /-- Standing choice of the common Sylow subgroup. -/
  sylow_le : (T : Subgroup G) ≤ M
  sylow_le_partner : (T : Subgroup G) ≤ Mc
  /-- Standing maximal two-local choice of Mc, distinct from M. -/
  partner_maximal : IsMaximalTwoLocal Mc
  partner_ne : Mc ≠ M
  /-- From Z ≤ V and Mc = C_G(Z), by 15.3.2(2) and 15.3.4. -/
  centralizer_le_partner : M ⊓ centralizer (V : Set G) ≤ Mc
  /-- V = V(M) is a subgroup of M. -/
  module_le : V ≤ M
  /-- The residual-centralizer or uniqueness conclusion of 15.3.2(4). -/
  overgroup_dichotomy : ∀ X : Subgroup G, (T : Subgroup G) ≤ X → X ≤ M →
    twoResidualAmbient X ≤ centralizer (V : Set G) ∨
      Chapter4.UniqueMaximalOvergroup X M
  /-- 14.1.17(1), for the actual intersection core. -/
  core_noncentral : ¬ (M ⊓ Mc).pCoreIn 2 ≤ centralizer (V : Set G)
  /-- 14.1.17(3), first assertion; every star is in M/O₂(M). -/
  star_centralizes : ThreeAlternatives.star M (M ⊓ centralizer (V : Set G)) ≤
    centralizer ((ThreeAlternatives.star M (residualY M Mc) ⊔
      ThreeAlternatives.star M ((M ⊓ Mc).pCoreIn 2) :
        Subgroup (ThreeAlternatives.StarGroup M)) : Set (ThreeAlternatives.StarGroup M))
  /-- 14.1.17(3), second assertion: the literal odd core of the center. -/
  star_odd_center : ThreeAlternatives.star M (residualY M Mc ⊓ centralizer (V : Set G)) ≤
    ThreeAlternatives.oddCenterIn
      (ThreeAlternatives.star M (M ⊓ centralizer (V : Set G)) ⊔
        ThreeAlternatives.star M ((M ⊓ Mc).pCoreIn 2))
  /-- 14.1.17(4) at p=3, on the actual cyclic conjugation action. -/
  faithful_cyclic : ∀ r : ThreeAlternatives.StarGroup M,
    r ∈ ThreeAlternatives.star M ((M ⊓ Mc).pCoreIn 2) → r ≠ 1 →
    Function.Injective
      ((MulAut.conjNormal : ThreeAlternatives.StarGroup M →*
        MulAut (pCore 3 (ThreeAlternatives.StarGroup M))).domRestrict (zpowers r)) →
    ∀ P : Sylow 3 (centralizer (zpowers r : Set (ThreeAlternatives.StarGroup M))), IsCyclic P
  /-- Standing quasithinness, restricted to the proper local subgroup M. -/
  rank_bound : primeRank 3 M ≤ 2
  /-- Standing characteristic two at the maximal two-local M. -/
  characteristic_two : centralizer (pCore 2 M : Set M) ≤ pCore 2 M

omit [Finite G] in
private theorem earlier_commutator_bound (M Mc V : Subgroup G) (T : Sylow 2 G)
    (h : ResidualEarlierInputs M Mc V T) :
    ⁅(centralizer (V : Set G)).subgroupOf M,
      ((M ⊓ Mc).pCoreIn 2).subgroupOf M⁆ ≤ pCore 2 M := by
  have hC : (M ⊓ centralizer (V : Set G)).subgroupOf M =
      (centralizer (V : Set G)).subgroupOf M := by
    ext x
    exact ⟨fun hx => hx.2, fun hx => ⟨x.property, hx⟩⟩
  rw [← QuotientGroup.ker_mk' (pCore 2 M), ← Subgroup.map_eq_bot_iff,
    map_commutator]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  have hc := h.star_centralizes.trans (centralizer_le
    (show ThreeAlternatives.star M ((M ⊓ Mc).pCoreIn 2) ≤
      ThreeAlternatives.star M (residualY M Mc) ⊔
        ThreeAlternatives.star M ((M ⊓ Mc).pCoreIn 2) from le_sup_right))
  simpa only [ThreeAlternatives.star, hC] using hc

private theorem threeAlternatives_inputs (M Mc V : Subgroup G) (T : Sylow 2 G)
    (d : NaturalOrthogonalAction M V) (h : ResidualEarlierInputs M Mc V T) :
    ThreeAlternatives.SourceInputs M Mc V T d := by
  have himage := residualY_orthogonal_image M Mc V T
    h.sylow_le h.sylow_le_partner d h.core_noncentral
  have hcomm := residualY_orthogonal_commutator M Mc V T
    h.sylow_le h.sylow_le_partner d h.core_noncentral
  have hlocal := residualY_local_structure_of_action_calculations M Mc V T
    h.sylow_le h.sylow_le_partner h.partner_maximal h.partner_ne
    h.centralizer_le_partner h.module_le d h.overgroup_dichotomy
    (earlier_commutator_bound M Mc V T h) himage hcomm orthogonalActor_twoCore_eq_bot
  refine {
    sylow_le := h.sylow_le
    sylow_le_partner := h.sylow_le_partner
    module_le := h.module_le
    core_le_kernel := core_le_kernel M V d
    core_inter_kernel := core_inter_kernel M Mc V d h.centralizer_le_partner
    residual_image := himage
    image_model := ?_
    inverter := lifted_inverter M Mc V T h.sylow_le h.sylow_le_partner d h.core_noncentral
    star_centralizes := h.star_centralizes
    star_odd_center := h.star_odd_center
    faithful_cyclic := h.faithful_cyclic
    rank_bound := h.rank_bound
    characteristic_two := h.characteristic_two
    intersection := hlocal.1
    join_core := hlocal.2.2.2.1
    module_le_core := hlocal.2.2.2.2 }
  obtain ⟨e⟩ := orthogonalActor_residual_equiv_elementaryNine
  exact ⟨((MulEquiv.subgroupCongr himage).trans e).trans elementaryNineCoordinates⟩

/-- All assertions of 15.3.7 from the preceding source inputs. The image,
commutator, core calculations, inverter, and both complete alternatives are
proved here; the intersection is also given as a literal subset product. -/
public theorem lemma_15_3_7_from_earlier_source
    (M Mc V : Subgroup G) (T : Sylow 2 G)
    (d : NaturalOrthogonalAction M V) (h : ResidualEarlierInputs M Mc V T) :
    ((residualY M Mc).subgroupOf M).map d.actor =
        twoResidualAmbient (⊤ : Subgroup OrthogonalActor) ∧
    M ⊓ Mc = (M ⊓ centralizer (V : Set G)) ⊔ (T : Subgroup G) ∧
    ((M ⊓ Mc : Subgroup G) : Set G) =
      ((M ⊓ centralizer (V : Set G) : Subgroup G) : Set G) * (T : Set G) ∧
    M = normalizer (residualY M Mc : Set G) ∧
    Chapter4.UniqueMaximalOvergroup (residualY M Mc ⊔ (T : Subgroup G)) M ∧
    (residualY M Mc ⊔ (T : Subgroup G)).pCoreIn 2 =
      (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
    (ThreeAlternatives.ElementaryAlternative M Mc V ∨
      ThreeAlternatives.ExtraspecialAlternative M Mc V d) := by
  have hi := threeAlternatives_inputs M Mc V T d h
  have hcomm := residualY_orthogonal_commutator M Mc V T
    h.sylow_le h.sylow_le_partner d h.core_noncentral
  have hlocal := residualY_local_structure_of_action_calculations M Mc V T
    h.sylow_le h.sylow_le_partner h.partner_maximal h.partner_ne
    h.centralizer_le_partner h.module_le d h.overgroup_dichotomy
    (earlier_commutator_bound M Mc V T h) hi.residual_image hcomm orthogonalActor_twoCore_eq_bot
  exact ⟨hi.residual_image, hi.intersection,
    intersection_eq_centralizer_mul_sylow M Mc V T h.sylow_le h.sylow_le_partner
      h.partner_maximal h.partner_ne h.centralizer_le_partner d h.overgroup_dichotomy,
    hlocal.2.1, hlocal.2.2.1, hi.join_core, ThreeAlternatives.residual_alternatives hi⟩

/-- Both assertions of 15.3.9, using the actual wreath recognition and the
exact 13.9.1 exclusion. The module-core containment and residual image are
discharged from the earlier source inputs, not assumed. -/
public theorem lemma_15_3_9_from_earlier_source
    (M Mc V : Subgroup G) (T : Sylow 2 G)
    (d : NaturalOrthogonalAction M V) (h : ResidualEarlierInputs M Mc V T)
    (hV : V = localModule T M)
    (hexclude : ¬ Nonempty (M ≃*
      RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2)))) :
    V < (residualY M Mc).pCoreIn 2 ∧
      ¬ Nonempty (residualY M Mc ≃* (alternatingGroup (Fin 4) × alternatingGroup (Fin 4))) := by
  have himage := residualY_orthogonal_image M Mc V T
    h.sylow_le h.sylow_le_partner d h.core_noncentral
  have hcomm := residualY_orthogonal_commutator M Mc V T
    h.sylow_le h.sylow_le_partner d h.core_noncentral
  exact WreathRecognition.residualY_exclusions M Mc V T h.sylow_le d hV
    (module_le_residualY_core_of_commutator M Mc V d h.module_le hcomm)
    ((Theory.GroupTheory.inf_centralizer_pCoreIn_le_iff 2 M).mpr h.characteristic_two) himage hexclude

end CFSG.Quasithin.Chapter15.Section03
