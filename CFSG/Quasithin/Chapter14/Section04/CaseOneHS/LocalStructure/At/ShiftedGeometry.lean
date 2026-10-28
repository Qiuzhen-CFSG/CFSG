module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.Source
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.Assembly
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.FaithfulPreparation

/-!
# Original shifted-center geometry at G,T

The marked parabolic action and its kernel give the original two center
intersections. The same natural L-action selects the shifted conjugator and
residual pair. Under the preceding central-seed exclusion, the shifted center
acts faithfully with the required moved plane and type-a2 involution.
These are the geometric inputs to the faithful and Goldschmidt branches.
Source: Aschbacher--Smith 12.8.10--13 and 14.3.28--30, pp.853--856,1002.

The universal APIs are preserved. The proofs below specialize their
source arguments without promoting a local earlier implication to a
universal statement. This extension remains above Section04.
-/

public noncomputable section

/- The corresponding universal proof is in CaseOneHS/LocalStructure/SourceAction/Geometry.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_parabolic_action_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (∃ hn : ((F.E g).subgroupOf (F.W ⊔ F.X g)).Normal, letI := hn
      IsElementaryAbelian 2 ((F.W ⊔ F.X g : Subgroup G) ⧸
        (F.E g).subgroupOf (F.W ⊔ F.X g))) ∧
    F.xHatKernel g (F.P_le_G₂ (by decide) L chosen.normalizes hgP) = F.E g ∧
    (∀ u : F.U, (u : G) ∉ F.W →
      (F.xHatStabilizer g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
        (QuotientGroup.mk' (center F.U) u) : Set G) ⊆
          (conjugate F.ZU g : Set G) * (F.E g : Set G)) ∧
    F.W.relIndex F.U = 2 := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨_, _, hVZ⟩ := source_closure_at d earlier hq chosen structural alternatives F hne
  obtain ⟨hcomm, hsquare⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape_at F alternatives)
  have hspan := (source_seed_geometry_at d earlier hq chosen F).2.1
  obtain ⟨e, _, hgen, _, _, _, _, _, hfactor, hPH, hcore, hindex, _⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT_at structural) hcomm hsquare hspan hne g hgP hgH
  have hsplit := F.binary_core_factorization L g hgP hfactor hPH hgen.symm e hcore hindex
  have hn := F.binary_source_E_normal_in_core L chosen.normalizes g hgP hgen.symm hcomm
  let := hn
  have he := F.binary_source_quotient_elementary L chosen.normalizes g hgP hgen.symm hcore
    (F.binary_core_normalizes_U L hfactor hPH) hsplit hcomm hsquare
  have hpair : ∃ hn : ((F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)).Normal, letI := hn
      IsElementaryAbelian 2 (((F.I₂ L).pCoreIn 2 : Subgroup G) ⧸
        (F.E g).subgroupOf ((F.I₂ L).pCoreIn 2)) := ⟨hn, he⟩
  rw [hsplit] at hpair
  have ha := F.binary_source_parabolic_action_clauses (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural) hcomm hsquare
    hspan hne hVZ g hgP hgH
  exact ⟨hpair, ha.2.1.1, ha.2.2, hindex⟩
theorem source_conjugate_center_kernel_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (F.uhatAction.comp (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).ker =
      (conjugate (F.Vi 1) g).subgroupOf (conjugate F.ZU g) := by
  let := chosen.elementary
  have ha := (source_parabolic_action_at d earlier hq chosen structural alternatives F hne g hgP hgH).2.1
  have hgG := F.P_le_G₂ (by decide) L chosen.normalizes hgP
  have hi := (source_center_intersections_at d earlier hq chosen structural alternatives F hne g hgP hgH).2.2
  rw [hI, bot_sup_eq] at hi
  have hVE := F.seed_le_E_of_normalizes g (F.P_le_seed_normalizer L chosen.normalizes hgP)
  ext z
  change F.uhatAction (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP z) = 1 ↔
    (z : G) ∈ conjugate (F.Vi 1) g
  have hk : F.uhatAction (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP z) = 1 ↔
      (z : G) ∈ F.E g := by
    rw [← ha, F.mem_xHatKernel]
    exact ⟨fun he => ⟨F.conjugate_ZU_le_X g z.property,
      (F.mem_uhatAction_ker_iff _).mp he⟩,
      fun he => (F.mem_uhatAction_ker_iff _).mpr he.2⟩
  rw [hk]
  constructor
  · intro he
    rw [← hi]
    exact ⟨z.property, (show F.E g ≤ F.U from inf_le_left.trans inf_le_left) he⟩
  · intro hz
    exact hVE (conjugate_le_of_normalizes (F.le_seed 1) g
      (F.P_le_seed_normalizer L chosen.normalizes hgP) hz)
theorem source_conjugate_center_image_order_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    2 * Nat.card (F.uhatAction.comp
      (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range =
      Nat.card (center F.U) := by
  let := chosen.elementary
  let f := F.uhatAction.comp (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)
  have hpoint : conjugate (F.Vi 1) g ≤ conjugate F.ZU g := map_mono (F.point_le_ZU (by decide))
  have hk : Nat.card f.ker = 2 := by
    rw [source_conjugate_center_kernel_at d earlier hq chosen structural alternatives F hne hI g hgP hgH,
      Nat.card_congr (subgroupOfEquivOfLe hpoint).toEquiv]
    change Nat.card ((F.Vi 1).map (MulAut.conj g⁻¹).toMonoidHom) = 2
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective]
    simpa using F.card 1 (by decide)
  have hh := f.ker.card_mul_index
  have hconj : Nat.card (conjugate F.ZU g) = Nat.card F.ZU :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have hcenter : Nat.card F.ZU = Nat.card (center F.U) :=
    card_map_of_injective F.U.subtype_injective
  rwa [index_ker, hk, hconj, hcenter] at hh
theorem source_conjugate_center_image_nontrivial_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (F.uhatAction.comp
      (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range ≠ ⊥ := by
  let := chosen.elementary
  intro hbot
  have hc := source_conjugate_center_image_order_at d earlier hq chosen structural alternatives
    F hne hI g hgP hgH
  rw [hbot, card_bot, mul_one] at hc
  have hcenter : Nat.card F.ZU = 2 :=
    (card_map_of_injective F.U.subtype_injective).trans hc.symm
  apply hZ
  apply (eq_of_le_of_card_ge (F.point_le_ZU (by decide)) ?_).symm
  rw [hcenter]
  simpa using (F.card 1 (by decide)).ge
theorem source_conjugate_center_image_equiv_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    Nonempty ((F.uhatAction.comp
      (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range ≃*
        F.tilde F.ZU) := by
  let := chosen.elementary
  let f := F.uhatAction.comp (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)
  let c : F.ZU ≃* conjugate F.ZU g := F.ZU.equivMapOfInjective
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
  have hZH : F.ZU ≤ F.H := (map_subtype_le (center F.U)).trans F.U_le_H
  let q := (F.tildeMap F.ZU hZH).comp c.symm.toMonoidHom
  have hqsurj : Function.Surjective q := (F.tildeMap_surjective F.ZU hZH).comp c.symm.surjective
  have hk : f.ker = q.ker := by
    rw [source_conjugate_center_kernel_at d earlier hq chosen structural alternatives F hne hI g hgP hgH]
    ext z
    change (z : G) ∈ conjugate (F.Vi 1) g ↔ q z = 1
    have ht : q z = 1 ↔ (c.symm z : G) ∈ F.Vi 1 := by
      change F.tildeMap F.ZU hZH (c.symm z) = 1 ↔ _
      rw [Subtype.ext_iff]
      exact QuotientGroup.eq_one_iff _
    rw [ht]
    have he : (z : G) = (MulAut.conj g⁻¹) (c.symm z : G) := by
      exact congrArg (fun x : conjugate F.ZU g => (x : G)) (c.apply_symm_apply z).symm
    rw [he]
    change (MulAut.conj g⁻¹) (c.symm z : G) ∈ (F.Vi 1).map (MulAut.conj g⁻¹).toMonoidHom ↔ _
    simp only [mem_map_equiv, MulEquiv.symm_apply_apply]
  exact ⟨(QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hk).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hqsurj))⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/SeedGeometry.lean. -/
section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_center_axis_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (F.ZU ⊓ conjugate F.U g).relIndex F.ZU =
      Nat.card (F.uhatAction.comp
        (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range ∧
    F.ZU ⊓ conjugate F.U g ≤ centralizer (conjugate F.ZU g : Set G) := by
  let := chosen.elementary
  let f := F.uhatAction.comp (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)
  obtain ⟨hi,haxis,hker⟩ := source_center_intersections_at d earlier hq chosen structural alternatives
    F hne g hgP hgH
  have ha := (source_parabolic_action_at d earlier hq chosen structural alternatives F hne g hgP hgH).2.1
  have hk : f.ker = (F.U).subgroupOf (conjugate F.ZU g) := by
    ext z
    change F.uhatAction (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP z) = 1 ↔ (z:G) ∈ F.U
    constructor
    · intro he
      have hz : (z:G) ∈ F.xHatKernel g (F.P_le_G₂ (by decide) L chosen.normalizes hgP) :=
        (F.mem_xHatKernel _ _ _).mpr ⟨F.conjugate_ZU_le_X g z.property,
          (F.mem_uhatAction_ker_iff _).mp he⟩
      rw [ha] at hz
      exact hz.1.1
    · intro hz
      have h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
      have hc := (F.localKernel_commutator_squares d.qtke L
        (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
        (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
        (h.flag_escape_at F alternatives)).1
      exact (F.mem_uhatAction_ker_iff _).mpr fun u hu =>
        F.point_le_ZU (by decide) (hc (commutator_mem_commutator hz hu))
  have hD : g ∈ normalizer (Chapter12.Section08.centerIn (F.I₂ L) : Set G) :=
    (normalizer_le_normalizer_characteristic_image (F.I₂ L) (center (F.I₂ L)))
      (le_normalizer_conjugateSpanBy F.U (F.P L) hgP)
  have hconj : conjugate (F.ZU ⊓ conjugate F.U g) g = conjugate F.ZU g ⊓ F.U := by
    rw [haxis, show conjugate (Chapter12.Section08.centerIn (F.I₂ L) ⊔ F.Vi 1) g =
      conjugate (Chapter12.Section08.centerIn (F.I₂ L)) g ⊔ conjugate (F.Vi 1) g from map_sup _ _ _,
      (conjugate_eq_iff _ _).mpr hD, hker]
  refine ⟨?_, ?_⟩
  · rw [← index_ker, hk]
    change _ = (F.U).relIndex (conjugate F.ZU g)
    rw [← inf_relIndex_left (conjugate F.ZU g) F.U, ← hconj]
    exact (relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective).symm
  · apply inf_le_right.trans
    apply le_centralizer_iff.mp
    change conjugate (Chapter12.Section08.centerIn F.U) g ≤ _
    rw [← centerIn_conjugate]
    rintro z ⟨c,hc,rfl⟩ u hu
    exact congrArg Subtype.val (mem_center_iff.mp hc ⟨u,hu⟩)
theorem source_seed_center_displacement_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hcard : Nat.card (F.uhatAction.comp
      (F.conjugateCenterActor (by decide) L chosen.normalizes g hgP)).range = 2)
    (A : Subgroup F.H) [A.Normal] [IsElementaryAbelian 2 A]
    (hAZ : A.map F.H.subtype ≤ F.ZU)
    (a : F.H) (ha : (a:G) ∈ conjugate F.ZU g) :
    Module.finrank (ZMod 2)
      (NormalElementaryQuotient.originalAction A a - LinearMap.id).range ≤ 1 := by
  obtain ⟨hi,hc⟩ := source_center_axis_at d earlier hq chosen structural alternatives F hne g hgP hgH
  rw [hcard] at hi
  let C := centralizer ({(a:G)} : Set G)
  have haxis : F.ZU ⊓ conjugate F.U g ≤ C := by
    intro z hz
    exact mem_centralizer_singleton_iff.mpr (hc hz a ha).symm
  have hidx : C.relIndex (A.map F.H.subtype) ≤ 2 := by
    exact (relIndex_le_of_le_right (H := C) hAZ (show C.relIndex F.ZU ≠ 0 from index_ne_zero_of_finite)).trans
      ((relIndex_le_of_le_left (L := F.ZU) haxis (by rw [hi]; decide)).trans hi.le)
  have he : centralizer (zpowers a : Set F.H) = C.comap F.H.subtype := by
    rw [zpowers_eq_closure, centralizer_closure]
    ext x
    simp only [mem_centralizer_singleton_iff, mem_comap, C]
    exact Subtype.ext_iff
  have hb := NormalElementaryQuotient.original_fixed_index A (zpowers a)
  rw [inf_relIndex_left, he, relIndex_comap] at hb
  rw [hb] at hidx
  have hn : fixedCodim (NormalElementaryQuotient.originalAction A) (zpowers a) ≤ 1 := by
    have hp : 2 ^ fixedCodim (NormalElementaryQuotient.originalAction A) (zpowers a) ≤ 2 ^ 1 := by
      simpa using hidx
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp
  rwa [fixedCodim_zpowers_eq_displacement_rank] at hn
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/Shifted.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_shifted_center_intersection_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (l : G) (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G)) :
    Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) =
      conjugate F.ZU g ⊓ conjugate F.ZU l := by
  rw [centerIn_conjugate,
    ← (source_center_intersections_at d earlier hq chosen structural alternatives F hne g hgP hgH).1,
    conjugate_inf, shifted_center_fixed F g l hl, inf_comm]
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/Conjugator.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open BinaryLinear BinaryLinear.OuterCyclic BinaryLinear.InvariantNodeActions
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
omit [Finite G] in
private theorem conjugator_lift_basis_permutation_at [IsElementaryAbelian 2 V]
    (hfull : ∀ a : MulAut V, ∃ x ∈ L, ∀ v : V, x * (v : G) * x⁻¹ = (a v : G))
    (β : Additive V ≃ₗ[ZMod 2] Space 3) (b : Basis 2) (s : Equiv.Perm (Fin 3)) :
    ∃ x ∈ L, ∀ i : Fin 3,
      x⁻¹ * ((β.symm (b i)).toMul : G) * x = (β.symm (b (s i))).toMul := by
  let a := (naturalFlagActorEquiv β).symm (b.equiv b s)
  obtain ⟨x, hx, he⟩ := hfull a
  refine ⟨x⁻¹, L.inv_mem hx, ?_⟩
  intro i
  simp only [inv_inv]
  rw [he]
  congr 1
  apply Additive.ofMul.injective
  apply β.injective
  have hh := naturalFlagActorEquiv_intertwines β a (β.symm (b i)).toMul
  rw [show naturalFlagActorEquiv β a = b.equiv b s from
    (naturalFlagActorEquiv β).apply_symm_apply _, ofMul_toMul, β.apply_symm_apply,
    Module.Basis.equiv_apply] at hh
  simpa only [ofMul_toMul, β.apply_symm_apply] using hh.symm
omit [Finite G] in
private theorem conjugator_basis_point_ne_one_at [IsElementaryAbelian 2 V]
    (β : Additive V ≃ₗ[ZMod 2] Space 3) (b : Basis 2) (i : Fin 3) :
    ((β.symm (b i)).toMul : G) ≠ 1 := by
  intro he
  have hv : (β.symm (b i)).toMul = 1 := Subtype.ext he
  have hz : β.symm (b i) = 0 := congrArg Additive.ofMul hv
  exact b.ne_zero i (β.symm.injective (hz.trans β.symm.map_zero.symm))
omit [Finite G] in
private theorem conjugator_basis_point_in_cut_at [IsElementaryAbelian 2 V]
    (F : InvariantFlag T V 3) (β : Additive V ≃ₗ[ZMod 2] Space 3) (b : Basis 2)
    (hc : ∀ i : Fin 2, F.naturalFlagSpace β (i.val + 1) = cutSpace b i)
    (i : Fin 2) (j : Fin 3) :
    ((β.symm (b j)).toMul : G) ∈ F.Vi (i.val + 1) ↔ j.val ≤ i.val := by
  rw [← F.mem_naturalFlagSpace β (i.val + 1), ofMul_toMul, β.apply_symm_apply,
    hc, basis_mem_cutSpace]
omit [Finite G] in
private theorem conjugator_seed_normalizes_subgroup_at [IsMulCommutative V]
    (A : Subgroup G) (hA : A ≤ V) : V ≤ normalizer (A : Set G) := by
  have hVV : V ≤ centralizer (V : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  apply hVV.trans
  exact (centralizer_le hA).trans (Subgroup.centralizer_le_normalizer _)
theorem source_shifted_conjugator_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) :
    ∃ g l : G, g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H ∧ l ∈ L ∧
      l ∈ centralizer (conjugate (F.Vi 1) g : Set G) ∧
      F.Vi 2 = F.Vi 1 ⊔ conjugate (F.Vi 1) g ∧
      V = F.Vi 2 ⊔ conjugate (F.Vi 1) l ∧
      conjugate (F.Vi 2) l = conjugate (F.Vi 1) g ⊔ conjugate (F.Vi 1) l := by
  classical
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  let β := h.naturalMarking.coordinates
  obtain ⟨b, _, hc⟩ := F.exists_naturalFlag_marking L chosen.normalizes h.full_L_action β
  let v : Fin 3 → G := fun i => (β.symm (b i)).toMul
  have hv (i : Fin 3) : v i ∈ V := (β.symm (b i)).toMul.property
  have hv1 (i : Fin 3) : v i ≠ 1 := conjugator_basis_point_ne_one_at β b i
  have hv2 (i : Fin 3) : v i ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian _ (hv i)
  have hp : F.Vi 1 = zpowers (v 0) := by
    symm
    apply eq_of_le_of_card_ge
      (zpowers_le.mpr ((conjugator_basis_point_in_cut_at F β b hc 0 0).mpr (by decide)))
    rw [Nat.card_zpowers, orderOf_eq_prime_iff.mpr ⟨hv2 0, hv1 0⟩]
    simpa using (F.card 1 (by decide)).le
  have hv10 : v 1 ∉ F.Vi 1 := by
    exact fun hh => (by decide : ¬ (1 : Fin 3).val ≤ (0 : Fin 2).val)
      ((conjugator_basis_point_in_cut_at F β b hc 0 1).mp hh)
  have hv12 : v 1 ∈ F.Vi 2 := (conjugator_basis_point_in_cut_at F β b hc 1 1).mpr (by decide)
  have hv22 : v 2 ∉ F.Vi 2 := by
    exact fun hh => (by decide : ¬ (2 : Fin 3).val ≤ (1 : Fin 2).val)
      ((conjugator_basis_point_in_cut_at F β b hc 1 2).mp hh)
  have hplane : F.Vi 2 = F.Vi 1 ⊔ zpowers (v 1) := by
    symm
    apply eq_of_le_of_card_ge (sup_le (F.monotone (by decide)) (zpowers_le.mpr hv12))
    rw [card_sup_zpowers_of_normalizing_involution _ _ (hv2 1) hv10
      (conjugator_seed_normalizes_subgroup_at _ (F.le_seed 1) (hv 1))]
    norm_num [F.card 1 (by decide), F.card 2 (by decide)]
  have hspace : V = F.Vi 2 ⊔ zpowers (v 2) := by
    symm
    apply eq_of_le_of_card_ge (sup_le (F.le_seed 2) (zpowers_le.mpr (hv 2)))
    rw [card_sup_zpowers_of_normalizing_involution _ _ (hv2 2) hv22
      (conjugator_seed_normalizes_subgroup_at _ (F.le_seed 2) (hv 2))]
    have hvcard : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
    norm_num [hvcard, F.card 2 (by decide)]
  obtain ⟨g, hgL, hg⟩ := conjugator_lift_basis_permutation_at h.full_L_action β b (Equiv.swap 0 1)
  obtain ⟨l, hlL, hl⟩ := conjugator_lift_basis_permutation_at h.full_L_action β b (Equiv.swap 0 2)
  have hg0 : g⁻¹ * v 0 * g = v 1 := by simpa only [Equiv.swap_apply_left] using hg 0
  have hg1 : g⁻¹ * v 1 * g = v 0 := by simpa only [Equiv.swap_apply_right] using hg 1
  have hl0 : l⁻¹ * v 0 * l = v 2 := by simpa only [Equiv.swap_apply_left] using hl 0
  have hl1 : l⁻¹ * v 1 * l = v 1 := by simpa only [Equiv.swap_apply_of_ne_of_ne (by decide : (1 : Fin 3) ≠ 0) (by decide : (1 : Fin 3) ≠ 2)] using hl 1
  have hgp : conjugate (F.Vi 1) g = zpowers (v 1) := by
    rw [hp, conjugate, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hg0]
  have hlp : conjugate (F.Vi 1) l = zpowers (v 2) := by
    rw [hp, conjugate, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hl0]
  have hgplane : conjugate (F.Vi 2) g = F.Vi 2 := by
    rw [hplane, hp]
    simp only [conjugate, Subgroup.map_sup, MonoidHom.map_zpowers, MulAut.conj_apply,
      MulEquiv.coe_toMonoidHom, inv_inv, hg0, hg1]
    exact sup_comm _ _
  have hgP : g ∈ F.P L := by
    refine ⟨mem_sup_left hgL, ?_⟩
    apply Subgroup.mem_iInf.mpr
    intro i
    apply Subgroup.mem_iInf.mpr
    intro hi
    have he : i = 2 := by omega
    subst i
    exact (conjugate_eq_iff _ _).mp hgplane
  have hgH : g ∉ F.H := by
    intro hh
    have he := (conjugate_eq_iff (F.Vi 1) g).mpr hh
    rw [hgp] at he
    exact hv10 (he ▸ mem_zpowers (v 1))
  have hlC : l ∈ centralizer (conjugate (F.Vi 1) g : Set G) := by
    rw [hgp, zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
    have hh := congrArg (fun x : G => l * x) hl1
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh.symm
  refine ⟨g, l, hgL, hgP, hgH, hlL, hlC, ?_, ?_, ?_⟩
  · rw [hgp]; exact hplane
  · rw [hlp]; exact hspace
  · rw [hgp, hlp, hplane, hp]
    simp only [conjugate, Subgroup.map_sup, MonoidHom.map_zpowers, MulAut.conj_apply,
      MulEquiv.coe_toMonoidHom, inv_inv, hl0, hl1]
    exact sup_comm _ _
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/ResidualPair.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
omit [Finite G] in
private theorem residualPair_conjugate_mul_at (A : Subgroup G) (a b : G) :
    conjugate A (a * b) = conjugate (conjugate A a) b := by
  simp only [conjugate, map_map]
  congr 1
  ext x
  simp [mul_assoc]
omit [Finite G] in
private theorem residualPair_residual_normalized_at (P : Subgroup G) :
    P ≤ normalizer ((pResidual 2 P).map P.subtype : Set G) := by
  have h := (pResidual 2 P).le_normalizer_map P.subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h
theorem source_point_fixed_residual_pair_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) :
    ∃ k ∈ L, k ∈ F.H ∧ L = F.orderedResidual L 1 ⊔
      conjugate (F.orderedResidual L 1) k := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨_, hs⟩ := F.ordered_generation_of_full_binary_action (by decide) L
    chosen.normalizes h.full_L_action (h.centralizer_LT_at structural)
  obtain ⟨k, hk, he⟩ := hs 1 (by decide) (by decide)
  have ht := F.initialResiduals_terminal_of_full_binary_action (by decide) L
    chosen.normalizes ((pResidual_eq_top_iff 2 L).mp h.residual)
    (h.sylow_normalizes_at structural) h.full_L_action
  change F.initialResiduals L 2 = L at ht
  rw [ht, F.initialResiduals_one] at he
  let f := F.naturalFlagAction L chosen.normalizes
  let k' : (L ⊔ (T : Subgroup G) : Subgroup G) := ⟨k, hk.1⟩
  obtain ⟨x, hxL, hx⟩ := h.full_L_action (f k')
  have hc : k * x⁻¹ ∈ centralizer (V : Set G) := by
    have hx' : x⁻¹ * k ∈ centralizer (V : Set G) := by
      intro v hv
      have hh := hx ⟨v, hv⟩
      change x * v * x⁻¹ = k * v * k⁻¹ at hh
      have hh' := congrArg (fun y : G => x⁻¹ * y * k) hh
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh'
    have hxN := chosen.normalizes hxL
    have hn := normalizer_le_normalizer_centralizer V hxN
    have hh := (mem_normalizer_iff.mp hn (x⁻¹ * k)).mp hx'
    simpa only [mul_inv_cancel_left] using hh
  have hcP : k * x⁻¹ ∈ F.P L := by
    refine ⟨(L ⊔ (T : Subgroup G)).mul_mem hk.1 (mem_sup_left (L.inv_mem hxL)), ?_⟩
    apply Subgroup.mem_iInf.mpr
    intro i
    apply Subgroup.mem_iInf.mpr
    intro _
    exact Subgroup.centralizer_le_normalizer _ (centralizer_le (F.le_seed i) hc)
  have hcR : k * x⁻¹ ∈ normalizer (F.orderedResidual L 1 : Set G) := by
    rw [orderedResidual, F.orderedParabolic_one]
    exact residualPair_residual_normalized_at _ hcP
  have hconj : conjugate (F.orderedResidual L 1) k =
      conjugate (F.orderedResidual L 1) x := by
    have hh := residualPair_conjugate_mul_at (F.orderedResidual L 1) (k * x⁻¹) x
    rw [(conjugate_eq_iff _ _).mpr hcR, inv_mul_cancel_right] at hh
    exact hh
  have hxH : x ∈ F.H := by
    have hkH := F.orderedParabolic_le_H (by decide) L (by decide : 2 ≤ 1 + 1) hk
    have hcH : k * x⁻¹ ∈ F.H := Subgroup.centralizer_le_normalizer _
      (centralizer_le (F.le_seed 1) hc)
    have hh := F.H.mul_mem (F.H.inv_mem hcH) hkH
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hh
  exact ⟨x, hxL, hxH, he.trans (congrArg (_ ⊔ ·) hconj)⟩
theorem source_shifted_residual_pair_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (g : G) (hgL : g ∈ L) (hgP : g ∈ F.P L) :
    ∃ l ∈ L, l ∈ centralizer (conjugate (F.Vi 1) g : Set G) ∧
      L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l := by
  obtain ⟨k, hkL, hkH, hgen⟩ :=
    source_point_fixed_residual_pair_at d earlier hq chosen structural F
  let l := g⁻¹ * k * g
  have hgR : conjugate (F.orderedResidual L 1) g = F.orderedResidual L 1 := by
    apply (conjugate_eq_iff _ _).mpr
    rw [orderedResidual, F.orderedParabolic_one]
    exact residualPair_residual_normalized_at _ hgP
  have hlC : l ∈ centralizer (conjugate (F.Vi 1) g : Set G) := by
    have hkC : k ∈ centralizer (F.Vi 1 : Set G) :=
      normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide)) hkH
    have hh := map_centralizer_le_centralizer_image (F.Vi 1 : Set G)
      (MulAut.conj g⁻¹).toMonoidHom (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hkC)
    simpa only [l, conjugate, coe_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hh
  refine ⟨l, L.mul_mem (L.mul_mem (L.inv_mem hgL) hkL) hgL, hlC, ?_⟩
  have he := congrArg (fun A : Subgroup G => conjugate A g) hgen
  have hgN := (conjugate_eq_iff L g).mpr (L.le_normalizer hgL)
  change conjugate L g = (F.orderedResidual L 1 ⊔
    conjugate (F.orderedResidual L 1) k).map (MulAut.conj g⁻¹).toMonoidHom at he
  rw [hgN, Subgroup.map_sup] at he
  change L = conjugate (F.orderedResidual L 1) g ⊔
    conjugate (conjugate (F.orderedResidual L 1) k) g at he
  rw [hgR] at he
  apply he.trans
  apply congrArg (F.orderedResidual L 1 ⊔ ·)
  rw [show l = g⁻¹ * k * g from rfl, residualPair_conjugate_mul_at, residualPair_conjugate_mul_at,
    show conjugate (F.orderedResidual L 1) g⁻¹ = F.orderedResidual L 1 from
      (conjugate_eq_iff _ _).mpr ((normalizer _).inv_mem ((conjugate_eq_iff _ _).mp hgR))]
theorem source_ordered_residual_le_parabolic_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    F.orderedResidual L 1 ≤ F.I₂ L ∧
      F.Gi 2 ≤ normalizer (F.I₂ L : Set G) := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  obtain ⟨g, hgP, hgH⟩ := source_conjugator_at d earlier hq chosen structural F
  obtain ⟨hc, hs⟩ := F.localKernel_commutator_squares d.qtke L
    (normalizer (L : Set G)) (by decide) chosen.le_sylow chosen.normalizes
    (h.sylow_normalizes_at structural) h.residual (fun _ => ⟨h.naturalMarking⟩)
    (h.flag_escape_at F alternatives)
  obtain ⟨_, hI, _, _, hIG, hIN, _⟩ := F.binary_generation (by decide) L chosen.normalizes
    (h.binarySeedAction_surjective F) (h.centralizer_LT_at structural) hc hs
    (source_seed_geometry_at d earlier hq chosen F).2.1 hne g hgP hgH
  refine ⟨?_, (normal_subgroupOf_iff_le_normalizer hIG).mp hIN⟩
  rw [orderedResidual, F.orderedParabolic_one, hI]
  exact le_sup_left
theorem source_closure_centralizer_of_seed_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hseed : centralLTSeed F L = ⊥) :
    F.U ⊓ centralizer (L : Set G) = ⊥ := by
  have hUT := CaseOneHS.source_closure_le_sylow_at d earlier hq chosen structural alternatives F
  have hn : (T : Subgroup G) ≤ normalizer
      (F.U ⊓ centralizer (L : Set G) : Set G) :=
    (le_inf ((F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H))
      (((SourceAssembly.At.higherRankHypothesis d earlier hq chosen).sylow_normalizes_at structural).trans
        (normalizer_le_normalizer_centralizer L))).trans inf_normalizer_le_normalizer_inf
  apply eq_bot_of_normalized_of_omega_center_disjoint (T : Subgroup G) _
    T.isPGroup' (inf_le_left.trans hUT) hn
  apply le_bot_iff.mp
  rintro x ⟨hxZ, hxU, hxL⟩
  have hxT : x ∈ (T : Subgroup G) := hUT hxU
  have hxC : x ∈ Chapter12.Section08.centerIn (L ⊔ (T : Subgroup G)) := by
    rw [centerIn_eq_inf_centralizer]
    refine ⟨mem_sup_right hxT, ?_⟩
    have hz : zpowers x ≤ centralizer (T : Set G) :=
      zpowers_le.mpr (omega_centralizes_sylow (show x ∈ sylowOmega T from hxZ))
    have hl : zpowers x ≤ centralizer (L : Set G) := zpowers_le.mpr hxL
    have hj : L ⊔ (T : Subgroup G) ≤ centralizer (zpowers x : Set G) :=
      sup_le (le_centralizer_iff.mp hl) (le_centralizer_iff.mp hz)
    exact le_centralizer_iff.mp hj (mem_zpowers x)
  exact hseed ▸ (show x ∈ centralLTSeed F L from ⟨hxC, hxU⟩)
theorem source_shifted_disjoint_of_residual_pair_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (l : G) (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G))
    (hgen : L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l) :
    F.ZU ⊓ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) = ⊥ := by
  have hI := source_ordered_residual_le_parabolic_at d earlier hq chosen structural alternatives F hne
  have hgen' : L ≤ F.I₂ L ⊔ conjugate (F.I₂ L) l := by
    conv_lhs => rw [hgen]
    exact sup_le_sup hI.1 (map_mono hI.1)
  have hmeet : F.ZU ⊓ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) =
      Chapter12.Section08.centerIn (F.I₂ L) ⊓
        Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) := by
    rw [source_shifted_center_intersection_at d earlier hq chosen structural alternatives F hne
      g hgP hgH l hl, ← inf_assoc,
      (source_center_intersections_at d earlier hq chosen structural alternatives F hne g hgP hgH).1]
    have hle : Chapter12.Section08.centerIn (F.I₂ L) ≤ conjugate F.ZU g :=
      ((source_center_intersections_at d earlier hq chosen structural alternatives F hne g hgP hgH).1.ge).trans inf_le_right
    rw [← inf_assoc, inf_eq_left.mpr hle]
  apply le_bot_iff.mp
  rw [← source_closure_centralizer_of_seed_at d earlier hq chosen structural alternatives F hseed]
  refine le_inf (inf_le_left.trans (map_subtype_le (center F.U))) ?_
  rw [hmeet]
  apply le_centralizer_iff.mp
  apply hgen'.trans
  apply sup_le
  · exact le_centralizer_iff.mp (inf_le_left.trans (centerIn_le_centralizer _))
  · exact le_centralizer_iff.mp (inf_le_right.trans (centerIn_le_centralizer _))
theorem source_shifted_generating_geometry_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) :
    ∃ g l : G, g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H ∧ l ∈ L ∧
      l ∈ centralizer (conjugate (F.Vi 1) g : Set G) ∧
      F.Vi 2 = F.Vi 1 ⊔ conjugate (F.Vi 1) g ∧
      V = F.Vi 2 ⊔ conjugate (F.Vi 1) l ∧
      conjugate (F.Vi 2) l = conjugate (F.Vi 1) g ⊔ conjugate (F.Vi 1) l ∧
      L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l := by
  let := chosen.elementary
  obtain ⟨g, k, hgL, hgP, hgH, hkL, _, hplane, hspace, _⟩ :=
    source_shifted_conjugator_at d earlier hq chosen F
  have hnot : ¬ L ≤ F.Gi 2 := by
    intro hL
    have hkP : conjugate (F.Vi 1) k ≤ F.Vi 2 :=
      conjugate_le_of_normalizes (F.monotone (by decide)) k (hL hkL)
    have he : V = F.Vi 2 := hspace.trans (sup_eq_left.mpr hkP)
    have hvcard : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
    rw [he, F.card 2 (by decide)] at hvcard
    norm_num at hvcard
  obtain ⟨l, hlL, hlC, hgen⟩ :=
    source_shifted_residual_pair_at d earlier hq chosen structural F g hgL hgP
  have hlfix : conjugate (conjugate (F.Vi 1) g) l = conjugate (F.Vi 1) g :=
    (conjugate_eq_iff _ _).mpr (Subgroup.centralizer_le_normalizer _ hlC)
  have hshift : conjugate (F.Vi 2) l =
      conjugate (F.Vi 1) g ⊔ conjugate (F.Vi 1) l := by
    conv_lhs => rw [hplane]
    rw [conjugate, Subgroup.map_sup]
    change conjugate (F.Vi 1) l ⊔ conjugate (conjugate (F.Vi 1) g) l = _
    rw [hlfix, sup_comm]
  have hnle : ¬ conjugate (F.Vi 1) l ≤ F.Vi 2 := by
    intro hle
    have hpg : conjugate (F.Vi 1) g ≤ F.Vi 2 := hplane ▸ le_sup_right
    have hpl : conjugate (F.Vi 2) l = F.Vi 2 :=
      eq_of_le_of_card_ge (hshift ▸ sup_le hpg hle) (by
        rw [conjugate, card_map_of_injective (MulAut.conj l⁻¹).injective])
    have hlP := (conjugate_eq_iff _ _).mp hpl
    have hR : F.orderedResidual L 1 ≤ F.Gi 2 :=
      (F.orderedResidual_le L 1).trans (by
        rw [F.orderedParabolic_one]
        exact F.P_le_G₂ (by decide) L chosen.normalizes)
    apply hnot
    conv_lhs => rw [hgen]
    exact sup_le hR (conjugate_le_of_normalizes hR l
      ((F.Gi 2).le_normalizer hlP))
  have hPV : conjugate (F.Vi 1) l ≤ V :=
    conjugate_le_of_normalizes (F.le_seed 1) l (chosen.normalizes hlL)
  have hspace' : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l := by
    obtain ⟨y, hy, hyout⟩ := Set.not_subset.mp hnle
    have hy2 : y ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian y (hPV hy)
    have hy1 : y ≠ 1 := fun he => hyout (he ▸ (F.Vi 2).one_mem)
    have he : zpowers y = conjugate (F.Vi 1) l := eq_of_le_of_card_ge
      (zpowers_le.mpr hy) (by
        rw [Nat.card_zpowers, orderOf_eq_prime_iff.mpr ⟨hy2, hy1⟩,
          conjugate, card_map_of_injective (MulAut.conj l⁻¹).injective]
        simpa using (F.card 1 (by decide)).le)
    symm
    apply eq_of_le_of_card_ge (sup_le (F.le_seed 2) hPV)
    rw [← he, card_sup_zpowers_of_normalizing_involution _ y hy2 hyout]
    · have hvcard : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
      norm_num [hvcard, F.card 2 (by decide)]
    · apply Subgroup.centralizer_le_normalizer _
      intro z hz
      exact congrArg Subtype.val (mul_comm' (⟨z, F.le_seed 2 hz⟩ : V) ⟨y, hPV hy⟩)
  exact ⟨g, l, hgL, hgP, hgH, hlL, hlC, hplane, hspace', hshift, hgen⟩
theorem source_shifted_center_centralizes_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (l : G) (hlL : l ∈ L)
    (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G))
    (hgen : L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l) :
    Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ≤ centralizer (F.ZU : Set G) := by
  have hdis := source_shifted_disjoint_of_residual_pair_at d earlier hq chosen structural
    alternatives F hne hseed g hgP hgH l hl hgen
  let A := Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)
  have hAH : A ≤ F.H := by
    change Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ≤ F.H
    rw [source_shifted_center_intersection_at d earlier hq chosen structural alternatives F hne
      g hgP hgH l hl]
    exact inf_le_left.trans ((F.conjugate_ZU_le_X g).trans
      (F.X_le_H g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)))
  have hAN : A ≤ normalizer (F.ZU : Set G) := hAH.trans F.H_normalizes_ZU
  have hplaneV : conjugate (F.Vi 2) l ≤ V :=
    conjugate_le_of_normalizes (F.le_seed 2) l (chosen.normalizes hlL)
  have hZN : F.ZU ≤ normalizer (conjugate (F.Vi 2) l : Set G) :=
    ((centerIn_le_centralizer F.U).trans
      (centralizer_le (hplaneV.trans (le_conjugateSpanBy V F.H)))).trans
        (Subgroup.centralizer_le_normalizer _)
  have hZGi : F.ZU ≤ conjugate (F.Gi 2) l := by
    simpa only [Gi, conjugate, map_equiv_normalizer_eq] using hZN
  have hGI := (source_ordered_residual_le_parabolic_at d earlier hq chosen structural alternatives F hne).2
  have hconj : conjugate (F.Gi 2) l ≤ normalizer (conjugate (F.I₂ L) l : Set G) := by
    simpa only [conjugate, map_equiv_normalizer_eq] using
      map_mono (f := (MulAut.conj l⁻¹).toMonoidHom) hGI
  have hNA : F.ZU ≤ normalizer (A : Set G) :=
    (hZGi.trans hconj).trans
      (normalizer_le_normalizer_characteristic_image _ (center (conjugate (F.I₂ L) l)))
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply le_bot_iff.mp
  exact (le_inf (le_normalizer_iff_commutator_le_right.mp hAN)
    (le_normalizer_iff_commutator_le_left.mp hNA)).trans hdis.le
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/ShiftedAmalgam.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
theorem source_shifted_amalgam_of_seed_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ g l e : G, g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H ∧ l ∈ L ∧
      l ∈ centralizer (conjugate (F.Vi 1) g : Set G) ∧
      V = F.Vi 2 ⊔ conjugate (F.Vi 1) l ∧
      L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l ∧
      Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) =
        conjugate F.ZU g ⊓ conjugate F.ZU l ∧
      F.ZU ⊓ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) = ⊥ ∧
      orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧ e ∈ F.ZU ∧ e ∉ F.Vi 1 ∧
      let a := l⁻¹ * e * l
      let K := conjugateSpanBy (zpowers a) F.H
      orderOf a = 2 ∧ a ∈ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ∧
        K ≤ centralizer (F.ZU : Set G) ∧
        amalgamGroup F L K ≤ centralizer ({e} : Set G) ∧
        IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)) ∧
        pCore 2 (AmalgamQuotient F L K) = ⊥ := by
  obtain ⟨g, l, hgL, hgP, hgH, hlL, hlC, _, hspace, _, hgen⟩ :=
    source_shifted_generating_geometry_at d earlier hq chosen structural F
  have hdis := source_shifted_disjoint_of_residual_pair_at d earlier hq chosen structural
    alternatives F hne hseed g hgP hgH l hlC hgen
  have hc := source_shifted_center_centralizes_at d earlier hq chosen structural alternatives
    F hne hseed g hgP hgH l hlL hlC hgen
  obtain ⟨e, he, heI, heT, heU, heV⟩ :=
    source_center_involution_at d earlier hq chosen structural alternatives F hne hI
  have haI : l⁻¹ * e * l ∈ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) := by
    rw [centerIn_conjugate]
    simpa only [conjugate, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      mem_map_of_mem (MulAut.conj l⁻¹).toMonoidHom heI
  have hK := actor_span_centralizes F (l⁻¹ * e * l) (hc haI)
  refine ⟨g, l, e, hgL, hgP, hgH, hlL, hlC, hspace, hgen,
    source_shifted_center_intersection_at d earlier hq chosen structural alternatives
      F hne g hgP hgH l hlC, hdis, he, heI, heT, heU, heV, ?_, haI, hK,
    amalgamGroup_le_centralizer F _ e heI heT heU hK,
    source_amalgam_reduced d chosen F _ e he heI heT heU hK,
    source_amalgam_quotient_core d chosen F _ e he heI heT heU hK⟩
  have hh := (MulAut.conj l⁻¹).orderOf_eq e
  simpa only [MulAut.conj_apply, inv_inv, he] using hh
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/ShiftedAction.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
omit [Finite G] in
private theorem shiftedAction_conjugate_mul'_at (A : Subgroup G) (a b : G) :
    conjugate A (a * b) = conjugate (conjugate A a) b := by
  simp only [conjugate, map_map]
  congr 1
  ext x
  simp [mul_assoc]
omit [Finite G] in
private theorem shiftedAction_centers_eq_of_points_at (F : InvariantFlag T V 3) (g l : G)
    (hp : conjugate (F.Vi 1) g = conjugate (F.Vi 1) l) :
    conjugate F.ZU g = conjugate F.ZU l := by
  have hh : g * l⁻¹ ∈ F.H := by
    apply (conjugate_eq_iff _ _).mp
    rw [shiftedAction_conjugate_mul'_at, hp]
    simpa only [inv_inv] using conjugate_conjugate_inv (F.Vi 1) l⁻¹
  have hz := (conjugate_eq_iff F.ZU (g * l⁻¹)).mpr (F.H_normalizes_ZU hh)
  have he := congrArg (fun A : Subgroup G => conjugate A l) hz
  simpa only [shiftedAction_conjugate_mul'_at, conjugate_conjugate_inv] using he
theorem source_point_fixer_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) (g l : G)
    (hgV : g ∈ normalizer (V : Set G)) (hlV : l ∈ normalizer (V : Set G))
    (hgH : g ∉ F.H) (hlH : l ∉ F.H) :
    ∃ k ∈ L, k ∈ F.H ∧
      conjugate (conjugate (F.Vi 1) g) k = conjugate (F.Vi 1) l ∧
      conjugate (conjugate F.ZU g) k = conjugate F.ZU l := by
  let := chosen.elementary
  obtain ⟨z, _, hp⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzV : z ∈ V := F.le_seed 1 (hp ▸ mem_zpowers z)
  have hz : z ≠ 1 := by
    intro he
    have hc := F.card 1 (by decide)
    rw [hp, he, zpowers_one_eq_bot, card_bot] at hc
    norm_num at hc
  let y := g⁻¹ * z * g
  let w := l⁻¹ * z * l
  have hyV : y ∈ V := by
    simpa only [y, inv_inv] using (mem_normalizer_iff.mp ((normalizer (V : Set G)).inv_mem hgV) z).mp hzV
  have hwV : w ∈ V := by
    simpa only [w, inv_inv] using (mem_normalizer_iff.mp ((normalizer (V : Set G)).inv_mem hlV) z).mp hzV
  have hy : y ≠ 1 := by
    intro he
    apply hz
    simpa [y, mul_assoc] using congrArg (fun a : G => g * a * g⁻¹) he
  have hw : w ≠ 1 := by
    intro he
    apply hz
    simpa [w, mul_assoc] using congrArg (fun a : G => l * a * l⁻¹) he
  have hyz : z ≠ y := by
    intro he
    apply hgH
    apply (conjugate_eq_iff _ _).mp
    rw [hp, conjugate, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    change zpowers y = zpowers z
    rw [← he]
  have hwz : z ≠ w := by
    intro he
    apply hlH
    apply (conjugate_eq_iff _ _).mp
    rw [hp, conjugate, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    change zpowers w = zpowers z
    rw [← he]
  let z' : Additive V := Additive.ofMul ⟨z, hzV⟩
  let y' : Additive V := Additive.ofMul ⟨y, hyV⟩
  let w' : Additive V := Additive.ofMul ⟨w, hwV⟩
  have hz' : z' ≠ 0 := fun he => hz (congrArg (fun v : Additive V => (v.toMul : G)) he)
  have hy' : y' ≠ 0 := fun he => hy (congrArg (fun v : Additive V => (v.toMul : G)) he)
  have hw' : w' ≠ 0 := fun he => hw (congrArg (fun v : Additive V => (v.toMul : G)) he)
  obtain ⟨f, hfz, hfy⟩ := BinaryLinear.exists_linearEquiv_pair z' y' z' w'
    hz' hy' hz' hw'
    (fun he => hyz (congrArg (fun v : Additive V => (v.toMul : G)) he))
    (fun he => hwz (congrArg (fun v : Additive V => (v.toMul : G)) he))
  let a : MulAut V := MulEquiv.toAdditive.symm f.toAddEquiv
  obtain ⟨x, hx, he⟩ := (SourceAssembly.At.higherRankHypothesis d earlier hq chosen).full_L_action a
  have hxz : x * z * x⁻¹ = z := (he ⟨z, hzV⟩).trans
    (congrArg (fun v : Additive V => (v.toMul : G)) hfz)
  have hxy : x * y * x⁻¹ = w := (he ⟨y, hyV⟩).trans
    (congrArg (fun v : Additive V => (v.toMul : G)) hfy)
  have hkH : x⁻¹ ∈ F.H := by
    apply (conjugate_eq_iff _ _).mp
    rw [hp, conjugate, MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, hxz]
  have hkP : conjugate (conjugate (F.Vi 1) g) x⁻¹ = conjugate (F.Vi 1) l := by
    rw [hp]
    simp only [conjugate, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv]
    exact congrArg zpowers hxy
  refine ⟨x⁻¹, L.inv_mem hx, hkH, hkP, ?_⟩
  rw [← shiftedAction_conjugate_mul'_at]
  exact shiftedAction_centers_eq_of_points_at F _ _ ((shiftedAction_conjugate_mul'_at _ _ _).trans hkP)
theorem source_conjugate_center_kernel_bound_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugate F.ZU g ⊓ F.uhatAction.ker.map F.H.subtype ≤
      F.ZU ⊔ conjugate (F.Vi 1) g := by
  let := chosen.elementary
  have hk := (source_parabolic_action_at d earlier hq chosen structural alternatives F hne g hgP hgH).2.1
  have hi := (source_center_intersections_at d earlier hq chosen structural alternatives F hne g hgP hgH).2.2
  intro x hx
  have hxE : x ∈ F.E g := by
    rw [← hk, F.mem_xHatKernel]
    obtain ⟨y, hy, rfl⟩ := hx.2
    exact ⟨F.conjugate_ZU_le_X g hx.1, (F.mem_uhatAction_ker_iff _).mp hy⟩
  have hxi : x ∈ Chapter12.Section08.centerIn (F.I₂ L) ⊔ conjugate (F.Vi 1) g :=
    hi ▸ (show x ∈ conjugate F.ZU g ⊓ F.U from ⟨hx.1, hxE.1.1⟩)
  apply (sup_le_sup (b := F.ZU) ?_ le_rfl) hxi
  rw [← (source_center_intersections_at d earlier hq chosen structural alternatives F hne g hgP hgH).1]
  exact inf_le_left
theorem source_second_center_kernel_bound_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (l : G) (hlV : l ∈ normalizer (V : Set G)) (hlH : l ∉ F.H) :
    conjugate F.ZU l ⊓ F.uhatAction.ker.map F.H.subtype ≤
      F.ZU ⊔ conjugate (F.Vi 1) l := by
  obtain ⟨g, hgP, hgH⟩ := source_conjugator_at d earlier hq chosen structural F
  obtain ⟨k, _, hkH, hkp, hkz⟩ := source_point_fixer_at d earlier hq chosen F g l
    (F.P_le_seed_normalizer L chosen.normalizes hgP) hlV hgH hlH
  have hKN : F.H ≤ normalizer (F.uhatAction.ker.map F.H.subtype : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      F.uhatAction.ker.le_normalizer_map F.H.subtype
  have hh := map_mono (f := (MulAut.conj k⁻¹).toMonoidHom)
    (source_conjugate_center_kernel_bound_at d earlier hq chosen structural alternatives F hne g hgP hgH)
  change conjugate (conjugate F.ZU g ⊓ F.uhatAction.ker.map F.H.subtype) k ≤
    conjugate (F.ZU ⊔ conjugate (F.Vi 1) g) k at hh
  rw [conjugate_inf, hkz, (conjugate_eq_iff _ _).mpr (hKN hkH)] at hh
  have hs : conjugate (F.ZU ⊔ conjugate (F.Vi 1) g) k =
      conjugate F.ZU k ⊔ conjugate (conjugate (F.Vi 1) g) k :=
    Subgroup.map_sup _ _ _
  rw [hs, (conjugate_eq_iff _ _).mpr (F.H_normalizes_ZU hkH), hkp] at hh
  exact hh
omit [Finite G] in
private theorem shiftedAction_inf_sup_points_at (Z A B P W : Subgroup G)
    (hZW : W ⊓ Z = P) (hAW : A ≤ W) (hBW : B ≤ W)
    (hBN : B ≤ normalizer (Z : Set G)) (hAN : A ≤ normalizer (Z : Set G))
    (hdis : (P ⊔ A) ⊓ B = ⊥) :
    (Z ⊔ A) ⊓ (Z ⊔ B) = Z := by
  apply le_antisymm _ (le_inf le_sup_left le_sup_left)
  rintro x ⟨hxA, hxB⟩
  have hxB' : x ∈ (Z : Set G) * (B : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left Z B hBN]
    exact hxB
  obtain ⟨z, hz, b, hb, rfl⟩ := hxB'
  have hbA : b ∈ Z ⊔ A := by
    have hh := (Z ⊔ A).mul_mem ((Z ⊔ A).inv_mem (mem_sup_left hz)) hxA
    simpa only [inv_mul_cancel_left] using hh
  have hbA' : b ∈ (Z : Set G) * (A : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left Z A hAN]
    exact hbA
  obtain ⟨z', hz', a, ha, he⟩ := hbA'
  have hzW : z' ∈ W := by
    have hh := W.mul_mem (hBW hb) (W.inv_mem (hAW ha))
    rw [← he, mul_inv_cancel_right] at hh
    exact hh
  have hzP : z' ∈ P := hZW ▸ (show z' ∈ W ⊓ Z from ⟨hzW, hz'⟩)
  have hbP : b ∈ P ⊔ A := he ▸ (P ⊔ A).mul_mem (mem_sup_left hzP) (mem_sup_right ha)
  have hb1 : b = 1 := by
    have hh : b ∈ (P ⊔ A) ⊓ B := ⟨hbP, hb⟩
    rwa [hdis, mem_bot] at hh
  change z * b ∈ Z
  rw [hb1, mul_one]
  exact hz
theorem source_two_point_intersection_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g l : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hlV : l ∈ normalizer (V : Set G))
    (hspace : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l) :
    (F.ZU ⊔ conjugate (F.Vi 1) g) ⊓
      (F.ZU ⊔ conjugate (F.Vi 1) l) = F.ZU := by
  let := chosen.elementary
  have hPg : conjugate (F.Vi 1) g ≤ V := conjugate_le_of_normalizes
    (F.le_seed 1) g (F.P_le_seed_normalizer L chosen.normalizes hgP)
  have hPl : conjugate (F.Vi 1) l ≤ V := conjugate_le_of_normalizes (F.le_seed 1) l hlV
  have hVN : V ≤ normalizer (F.ZU : Set G) :=
    ((le_conjugateSpanBy V F.H).trans F.U_le_H).trans F.H_normalizes_ZU
  have hdis : F.Vi 2 ⊓ conjugate (F.Vi 1) l = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    change x = 1
    by_contra hx1
    have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x (hPl hx.2)
    have he : zpowers x = conjugate (F.Vi 1) l := eq_of_le_of_card_ge
      (zpowers_le.mpr hx.2) (by
        rw [Nat.card_zpowers, orderOf_eq_prime_iff.mpr ⟨hx2, hx1⟩,
          conjugate, card_map_of_injective (MulAut.conj l⁻¹).injective]
        simpa using (F.card 1 (by decide)).le)
    have hle : conjugate (F.Vi 1) l ≤ F.Vi 2 := he ▸ zpowers_le.mpr hx.1
    have hc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
    rw [hspace, sup_eq_left.mpr hle, F.card 2 (by decide)] at hc
    norm_num at hc
  apply shiftedAction_inf_sup_points_at _ _ _ (F.Vi 1) V
    (CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne).2.2
    hPg hPl (hPl.trans hVN) (hPg.trans hVN)
  rw [← F.plane_eq_point_join_conjugate (by decide) L chosen.normalizes g hgP hgH]
  exact hdis
theorem source_shifted_action_faithful_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (l : G) (hlL : l ∈ L)
    (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G))
    (hgen : L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l)
    (hspace : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l) :
    Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ⊓
      F.uhatAction.ker.map F.H.subtype = ⊥ := by
  have hlH : l ∉ F.H := by
    intro hh
    have hc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
    rw [hspace, (conjugate_eq_iff _ _).mpr hh,
      sup_eq_left.mpr (F.monotone (by decide)), F.card 2 (by decide)] at hc
    norm_num at hc
  have hi := source_shifted_center_intersection_at d earlier hq chosen structural alternatives
    F hne g hgP hgH l hl
  have hd := source_shifted_disjoint_of_residual_pair_at d earlier hq chosen structural alternatives
    F hne hseed g hgP hgH l hl hgen
  have hg := source_conjugate_center_kernel_bound_at d earlier hq chosen structural alternatives
    F hne g hgP hgH
  have hl' := source_second_center_kernel_bound_at d earlier hq chosen structural alternatives
    F hne l (chosen.normalizes hlL) hlH
  have hm := source_two_point_intersection_at d earlier hq chosen structural alternatives
    F hne g l hgP hgH (chosen.normalizes hlL) hspace
  apply le_bot_iff.mp
  intro x hx
  have hxI := hx.1
  rw [hi] at hxI
  have hxZ : x ∈ F.ZU := hm ▸
    (show x ∈ (F.ZU ⊔ conjugate (F.Vi 1) g) ⊓
      (F.ZU ⊔ conjugate (F.Vi 1) l) from ⟨hg ⟨hxI.1, hx.2⟩, hl' ⟨hxI.2, hx.2⟩⟩)
  exact hd ▸ (show x ∈ F.ZU ⊓ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) from
    ⟨hxZ, hx.1⟩)
theorem source_shifted_amalgam_faithful_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ g l e : G, g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H ∧ l ∈ L ∧
      l ∈ centralizer (conjugate (F.Vi 1) g : Set G) ∧
      V = F.Vi 2 ⊔ conjugate (F.Vi 1) l ∧
      L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l ∧
      orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧ e ∈ F.ZU ∧ e ∉ F.Vi 1 ∧
      let a := l⁻¹ * e * l
      let K := conjugateSpanBy (zpowers a) F.H
      ∃ haH : a ∈ F.H,
        orderOf a = 2 ∧ F.uhatAction ⟨a, haH⟩ ≠ 1 ∧
        Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ⊓
          F.uhatAction.ker.map F.H.subtype = ⊥ ∧
        K ≤ centralizer (F.ZU : Set G) ∧
        amalgamGroup F L K ≤ centralizer ({e} : Set G) ∧
        IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)) ∧
        pCore 2 (AmalgamQuotient F L K) = ⊥ := by
  obtain ⟨g, l, e, hgL, hgP, hgH, hlL, hl, hspace, hgen, hi, _,
    he, heI, heT, heU, heV, ha, haI, hK, hKe, hr, hcore⟩ :=
    source_shifted_amalgam_of_seed_at d earlier hq chosen structural alternatives F hne hseed hI
  have hf := source_shifted_action_faithful_at d earlier hq chosen structural alternatives
    F hne hseed g hgP hgH l hlL hl hgen hspace
  have haH : l⁻¹ * e * l ∈ F.H := by
    have hh := haI
    rw [hi] at hh
    exact F.X_le_H g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)
      (F.conjugate_ZU_le_X g hh.1)
  refine ⟨g, l, e, hgL, hgP, hgH, hlL, hl, hspace, hgen, he, heI,
    heT, heU, heV, haH, ha, ?_, hf, hK, hKe, hr, hcore⟩
  intro hk
  have hx : l⁻¹ * e * l ∈ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ⊓
      F.uhatAction.ker.map F.H.subtype :=
    ⟨haI, ⟨⟨l⁻¹ * e * l, haH⟩, hk, rfl⟩⟩
  rw [hf, mem_bot] at hx
  rw [hx, orderOf_one] at ha
  norm_num at ha
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/ShiftedMovement.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
private theorem shiftedMovement_source_commutator_bound_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) : ⁅F.U, F.U⁆ ≤ F.Vi 1 := by
  let := chosen.elementary
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  exact (F.localKernel_commutator_squares d.qtke L (normalizer (L : Set G))
    (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes_at structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape_at F alternatives)).1
private theorem shiftedMovement_source_plane_center_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) :
    Chapter12.Section08.centerIn F.W = F.Vi 2 ⊔ F.ZU := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, _⟩ := CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne
  have hc := (shiftedMovement_source_commutator_bound_at d earlier hq chosen structural alternatives F)
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  exact F.plane_centralizer_center (F.localKernel_markedForm (by decide) htwo hphi hc)
theorem source_center_displacement_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ⁅F.W, conjugate F.ZU g⁆ ≤ F.ZU ⊔ conjugate (F.Vi 1) g := by
  let := chosen.elementary
  have h := F.center_commutator_le_plane (by decide) L chosen.normalizes
    (CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne).2.2
    (shiftedMovement_source_commutator_bound_at d earlier hq chosen structural alternatives F)
    (shiftedMovement_source_plane_center_at d earlier hq chosen structural alternatives F hne) g hgP hgH
  rw [F.plane_eq_point_join_conjugate (by decide) L chosen.normalizes g hgP hgH,
    ← sup_assoc, sup_eq_left.mpr (F.point_le_ZU (by decide))] at h
  exact h
theorem source_two_hyperplane_generation_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g l k : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hlV : l ∈ normalizer (V : Set G))
    (hspace : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l)
    (hkH : k ∈ F.H)
    (hkp : conjugate (conjugate (F.Vi 1) g) k = conjugate (F.Vi 1) l) :
    F.U = F.W ⊔ conjugate F.W k := by
  let := chosen.elementary
  have hkU : conjugate F.U k = F.U :=
    (conjugate_eq_iff _ _).mpr (le_normalizer_conjugateSpanBy V F.H hkH)
  have hkZ : conjugate F.ZU k = F.ZU :=
    (conjugate_eq_iff _ _).mpr (F.H_normalizes_ZU hkH)
  have hkP : conjugate (F.Vi 1) k = F.Vi 1 := (conjugate_eq_iff _ _).mpr hkH
  have hcenter := shiftedMovement_source_plane_center_at d earlier hq chosen structural alternatives F hne
  have hplane := F.plane_eq_point_join_conjugate (by decide) L chosen.normalizes g hgP hgH
  have hzc : Chapter12.Section08.centerIn (conjugate F.W k) =
      F.ZU ⊔ conjugate (F.Vi 1) l := by
    rw [centerIn_conjugate, hcenter, hplane]
    have hmap (A B : Subgroup G) : conjugate (A ⊔ B) k =
        conjugate A k ⊔ conjugate B k := Subgroup.map_sup _ _ _
    rw [hmap, hmap, hkZ, hkP, hkp, sup_comm, ← sup_assoc,
      sup_eq_left.mpr (F.point_le_ZU (by decide))]
  have hcw : Chapter12.Section08.centerIn F.W =
      F.ZU ⊔ conjugate (F.Vi 1) g := by
    rw [hcenter, hplane, sup_comm, ← sup_assoc, sup_eq_left.mpr (F.point_le_ZU (by decide))]
  have hneq : conjugate F.W k ≠ F.W := by
    intro he
    have hEq : F.ZU ⊔ conjugate (F.Vi 1) l =
        F.ZU ⊔ conjugate (F.Vi 1) g := by rw [← hzc, he, hcw]
    have hm := source_two_point_intersection_at d earlier hq chosen structural alternatives
      F hne g l hgP hgH hlV hspace
    rw [hEq, inf_idem] at hm
    have hPZ : F.Vi 2 ≤ F.ZU := by
      rw [hplane]
      exact sup_le (F.point_le_ZU (by decide)) (le_sup_right.trans hm.le)
    have hPP : F.Vi 2 ≤ F.Vi 1 :=
      (le_inf (F.le_seed 2) hPZ).trans
        (CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne).2.2.le
    have hc := card_le_of_le hPP
    rw [F.card 2 (by decide), F.card 1 (by decide)] at hc
    norm_num at hc
  have hnot : ¬ conjugate F.W k ≤ F.W := by
    intro hh
    exact hneq (eq_of_le_of_card_ge hh (by
      rw [conjugate, card_map_of_injective (MulAut.conj k⁻¹).injective]))
  have hWU : conjugate F.W k ≤ F.U := hkU ▸
    (map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) (show F.W ≤ F.U from inf_le_left))
  have hidx := (source_parabolic_action_at d earlier hq chosen structural alternatives F hne g hgP hgH).2.2.2
  have hm := relIndex_mul_relIndex F.W (F.W ⊔ conjugate F.W k) F.U le_sup_left
    (sup_le inf_le_left hWU)
  rw [hidx] at hm
  have hn : F.W.relIndex (F.W ⊔ conjugate F.W k) ≠ 1 := fun he =>
    hnot (le_sup_right.trans (relIndex_eq_one.mp he))
  have hlast : (F.W ⊔ conjugate F.W k).relIndex F.U = 1 := by
    rcases Nat.prime_mul_iff.mp (hm ▸ Nat.prime_two) with hh | hh
    · exact hh.2
    · exact (hn hh.2).elim
  exact le_antisymm (relIndex_eq_one.mp hlast) (sup_le inf_le_left hWU)
theorem source_shifted_movement_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g l : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hlV : l ∈ normalizer (V : Set G))
    (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G))
    (hspace : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l) :
    ∃ k ∈ L, k ∈ F.H ∧
      conjugate (conjugate (F.Vi 1) g) k = conjugate (F.Vi 1) l ∧
      F.U = F.W ⊔ conjugate F.W k ∧
      ⁅F.W, Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)⁆ ≤
        F.ZU ⊔ conjugate (F.Vi 1) g ∧
      ⁅conjugate F.W k, Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)⁆ ≤
        F.ZU ⊔ conjugate (F.Vi 1) l ∧
      ⁅F.U, Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)⁆ ≤ F.ZU ⊔ V := by
  let := chosen.elementary
  have hlH : l ∉ F.H := by
    intro hh
    have hc : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
    rw [hspace, (conjugate_eq_iff _ _).mpr hh,
      sup_eq_left.mpr (F.monotone (by decide)), F.card 2 (by decide)] at hc
    norm_num at hc
  obtain ⟨k, hkL, hkH, hkp, hkz⟩ := source_point_fixer_at d earlier hq chosen F g l
    (F.P_le_seed_normalizer L chosen.normalizes hgP) hlV hgH hlH
  have hgen := source_two_hyperplane_generation_at d earlier hq chosen structural alternatives
    F hne g l k hgP hgH hlV hspace hkH hkp
  have hbound := source_center_displacement_at d earlier hq chosen structural alternatives F hne g hgP hgH
  have hbound' := map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hbound
  rw [map_commutator, Subgroup.map_sup] at hbound'
  change ⁅conjugate F.W k, conjugate (conjugate F.ZU g) k⁆ ≤
    conjugate F.ZU k ⊔ conjugate (conjugate (F.Vi 1) g) k at hbound'
  rw [hkz, hkp, (conjugate_eq_iff _ _).mpr (F.H_normalizes_ZU hkH)] at hbound'
  have hi := source_shifted_center_intersection_at d earlier hq chosen structural alternatives
    F hne g hgP hgH l hl
  have hgZ : Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ≤ conjugate F.ZU g :=
    hi ▸ inf_le_left
  have hlZ : Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ≤ conjugate F.ZU l :=
    hi ▸ inf_le_right
  have hb₁ := (commutator_mono le_rfl hgZ).trans hbound
  have hb₂ := (commutator_mono le_rfl hlZ).trans hbound'
  refine ⟨k, hkL, hkH, hkp, hgen, hb₁, hb₂, ?_⟩
  have hn : F.U ≤ normalizer ((F.ZU ⊔ V : Subgroup G) : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    have hZU : F.ZU ⊔ V ≤ F.U := sup_le (map_subtype_le _) (le_conjugateSpanBy V F.H)
    exact ((commutator_mono le_rfl hZU).trans
      (shiftedMovement_source_commutator_bound_at d earlier hq chosen structural alternatives F)).trans
      ((F.point_le_ZU (by decide)).trans le_sup_left)
  have hkg : conjugate F.W k ≤ F.U := hgen ▸ le_sup_right
  have hc := commutator_sup_le_of_relative_normal F.U F.W (conjugate F.W k)
    (Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)) (F.ZU ⊔ V)
    hn inf_le_left hkg
    (hb₁.trans (sup_le_sup_left (conjugate_le_of_normalizes (F.le_seed 1) g
      (F.P_le_seed_normalizer L chosen.normalizes hgP)) F.ZU))
    (hb₂.trans (sup_le_sup_left (conjugate_le_of_normalizes (F.le_seed 1) l hlV) F.ZU))
  rwa [← hgen] at hc
theorem source_shifted_displacement_range_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (g l : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hlV : l ∈ normalizer (V : Set G))
    (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G))
    (hspace : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l)
    (a : F.H) (ha : (a : G) ∈ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)) :
    (F.uhatDisplacement a).range ≤ F.hatSubspace V := by
  obtain ⟨_, _, _, _, _, _, _, hbound⟩ := source_shifted_movement_at
    d earlier hq chosen structural alternatives F hne g l hgP hgH hlV hl hspace
  rintro v ⟨w, rfl⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (center F.U) w.toMul
  rw [show w = Additive.ofMul (F.uhatProjection u) from
    (congrArg Additive.ofMul hu).symm, F.uhatDisplacement_projection,
    F.mem_hatSubspace_projection V (le_conjugateSpanBy V F.H)]
  rw [commutator_comm] at hbound
  have hh := hbound (commutator_mem_commutator ha u.property)
  change (a : G) * (u : G) * (a : G)⁻¹ / (u : G) ∈ V ⊔ F.ZU
  simpa only [sup_comm, commutatorElement_def, div_eq_mul_inv] using hh
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end

/- The corresponding universal proof is in CaseOneHS/LocalStructure/Centerless/ShiftedType.lean. -/
section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
omit [Finite G] in
private theorem shiftedType_hat_orthogonal_of_centralizes_at (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat] {hc : ⁅F.U, F.U⁆ ≤ F.Vi 1}
    (B : F.UhatCommutatorForm hc) (A D : Subgroup G)
    (hAD : A ≤ centralizer (D : Set G)) :
    F.hatSubspace A ≤ B.form.orthogonal (F.hatSubspace D) := by
  rintro q ⟨u, hu, he⟩ r ⟨v, hv, hvq⟩
  change F.uhatProjection u = q.toMul at he
  change F.uhatProjection v = r.toMul at hvq
  rw [show q = Additive.ofMul (F.uhatProjection u) from congrArg Additive.ofMul he.symm,
    show r = Additive.ofMul (F.uhatProjection v) from congrArg Additive.ofMul hvq.symm,
    B.evaluation]
  have hcomm : ⁅(v : G), (u : G)⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr (hAD hu v hv)
  have hz : (⟨⁅(v : G), (u : G)⁆, hc (commutator_mem_commutator v.property u.property)⟩ : F.Vi 1) = 1 :=
    Subtype.ext hcomm
  rw [hz, map_one]
  rfl
omit [Finite G] in
private theorem shiftedType_hat_sup_at (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (A D : Subgroup G) (hA : A ≤ F.U) (hD : D ≤ F.U) :
    F.hatSubspace (A ⊔ D) = F.hatSubspace A ⊔ F.hatSubspace D := by
  unfold hatSubspace
  rw [subgroupOf_sup hA hD, Subgroup.map_sup]
  rw [OrderIso.map_sup, OrderIso.map_sup]
omit [Finite G] in
private theorem shiftedType_hat_sup_top_at (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (A D : Subgroup G) (hgen : F.U = A ⊔ D) :
    F.hatSubspace A ⊔ F.hatSubspace D = ⊤ := by
  rw [← shiftedType_hat_sup_at F A D (hgen ▸ le_sup_left) (hgen ▸ le_sup_right), ← hgen]
  apply top_unique
  intro q _
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (center F.U) q.toMul
  exact ⟨u, u.property, hu⟩
omit [Finite G] in
private theorem shiftedType_displacement_line_at (F : InvariantFlag T V 3)
    [IsElementaryAbelian 2 F.Uhat] (A P C : Subgroup G) (hP : P ≤ F.U)
    (hbound : ⁅A,C⁆ ≤ F.ZU ⊔ P) (a : F.H) (ha : (a : G) ∈ C) :
    ∀ x ∈ F.hatSubspace A, F.uhatDisplacement a x ∈ F.hatSubspace P := by
  rintro x ⟨u, hu, he⟩
  change F.uhatProjection u = x.toMul at he
  rw [show x = Additive.ofMul (F.uhatProjection u) from congrArg Additive.ofMul he.symm,
    F.uhatDisplacement_projection, F.mem_hatSubspace_projection P hP]
  rw [commutator_comm] at hbound
  have hh := hbound (commutator_mem_commutator ha hu)
  change (a : G) * (u : G) * (a : G)⁻¹ / (u : G) ∈ P ⊔ F.ZU
  simpa only [sup_comm, commutatorElement_def, div_eq_mul_inv, Subgroup.subtype_apply] using hh
theorem source_shifted_alternating_displacement_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hc : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (g l : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hlV : l ∈ normalizer (V : Set G))
    (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G))
    (hspace : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l)
    (a : F.H) (ha : (a : G) ∈ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)) :
    ∀ x, F.uhatBilinearForm (by decide) htwo hphi x (F.uhatDisplacement a x) = 0 := by
  let := chosen.elementary
  let B := F.localKernel_markedForm (by decide) htwo hphi hc
  obtain ⟨k, hkL, hkH, hkp, hgen, hb₁, hb₂, _⟩ := source_shifted_movement_at
    d earlier hq chosen structural alternatives F hne g l hgP hgH hlV hl hspace
  let Pg := conjugate (F.Vi 1) g
  let Pl := conjugate (F.Vi 1) l
  have hgV : Pg ≤ V := conjugate_le_of_normalizes (F.le_seed 1) g
    (F.P_le_seed_normalizer L chosen.normalizes hgP)
  have hlV' : Pl ≤ V := conjugate_le_of_normalizes (F.le_seed 1) l hlV
  have hgC : Pg ≤ centralizer (F.W : Set G) := by
    apply le_centralizer_iff.mp
    have hp : Pg ≤ F.Vi 2 := by
      rw [F.plane_eq_point_join_conjugate (by decide) L chosen.normalizes g hgP hgH]
      exact le_sup_right
    exact inf_le_right.trans (centralizer_le hp)
  have hlC : Pl ≤ centralizer (conjugate F.W k : Set G) := by
    change conjugate (F.Vi 1) l ≤ _
    rw [← hkp]
    have hm := map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hgC
    exact hm.trans (map_centralizer_le_centralizer_image _ _)
  have hgl : Pl ≤ centralizer (Pg : Set G) := by
    intro z hz y hy
    exact congrArg Subtype.val (mul_comm (⟨y, hgV hy⟩ : V) ⟨z, hlV' hz⟩)
  let t : Additive F.Uhat ≃ₗ[ZMod 2] Additive F.Uhat :=
    { (F.uhatAction a).toAdditive with map_smul' := ZMod.map_smul (F.uhatAction a).toAdditive }
  have ht : ∀ x y, B.form (t x) (t y) = B.form x y := by
    intro x y
    change F.uhatBilinearForm (by decide) htwo hphi
      (Additive.ofMul (F.uhatAction a x.toMul)) (Additive.ofMul (F.uhatAction a y.toMul)) = _
    rw [F.uhatBilinearForm_apply, F.uhatCommutator_invariant (by decide) htwo hphi]
    rfl
  exact Theory.LinearAlgebra.alternating_displacement_of_two_subspaces B.form B.alternating
    (F.hatSubspace F.W) (F.hatSubspace (conjugate F.W k))
    (F.hatSubspace Pg) (F.hatSubspace Pl) (shiftedType_hat_sup_top_at F _ _ hgen)
    (shiftedType_hat_orthogonal_of_centralizes_at F B _ _ hgC)
    (shiftedType_hat_orthogonal_of_centralizes_at F B _ _ hlC)
    (shiftedType_hat_orthogonal_of_centralizes_at F B _ _ hgl) t ht
    (shiftedType_displacement_line_at F _ _ _ (hgV.trans (le_conjugateSpanBy V F.H)) hb₁ a ha)
    (shiftedType_displacement_line_at F _ _ _ (hlV'.trans (le_conjugateSpanBy V F.H)) hb₂ a ha)
theorem source_shifted_displacement_eq_seed_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat]
    (htwo : IsPGroup 2 F.U) (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U)
    (hc : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (g l : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hlV : l ∈ normalizer (V : Set G))
    (hl : l ∈ centralizer (conjugate (F.Vi 1) g : Set G))
    (hspace : V = F.Vi 2 ⊔ conjugate (F.Vi 1) l)
    (a : F.H) (ha : (a : G) ∈ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l))
    (hfaith : F.uhatAction a ≠ 1) :
    (F.uhatDisplacement a).range = F.hatSubspace V := by
  let := chosen.elementary
  let B := F.localKernel_markedForm (by decide) htwo hphi hc
  have hN : F.uhatDisplacement a ≠ 0 := by
    intro hzero
    apply hfaith
    ext u
    have h := LinearMap.congr_fun hzero (Additive.ofMul u)
    exact Additive.ofMul.injective (sub_eq_zero.mp h)
  apply Theory.LinearAlgebra.range_eq_plane_of_alternating_displacement
    B.form B.alternating B.nondegenerate (F.uhatDisplacement a) hN
    (source_shifted_alternating_displacement_at d earlier hq chosen structural alternatives
      F hne htwo hphi hc g l hgP hgH hlV hl hspace a ha)
  · exact CaseOneGeometry.seed_hat_dimension F
      (CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne).2.2
  · exact source_shifted_displacement_range_at d earlier hq chosen structural alternatives
      F hne g l hgP hgH hlV hl hspace a ha
theorem source_center_order_le_two_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥) :
    Nat.card (Chapter12.Section08.centerIn (F.I₂ L)) ≤ 2 := by
  let := chosen.elementary
  obtain ⟨htwo, hphi, hvz⟩ := CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne
  let := F.uhat_elementary_of_point (by decide) htwo hphi
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  have hc := (F.localKernel_commutator_squares d.qtke L (normalizer (L : Set G))
    (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes_at structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape_at F alternatives)).1
  let B := F.localKernel_markedForm (by decide) htwo hphi hc
  obtain ⟨g, l, hgL, hgP, hgH, hlL, hl, _, hspace, _, hgen⟩ :=
    source_shifted_generating_geometry_at d earlier hq chosen structural F
  let C := Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)
  have hCH : C ≤ F.H := by
    change Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) ≤ _
    rw [source_shifted_center_intersection_at d earlier hq chosen structural alternatives F hne g hgP hgH l hl]
    exact inf_le_left.trans ((F.conjugate_ZU_le_X g).trans
      (F.X_le_H g (F.P_le_G₂ (by decide) L chosen.normalizes hgP)))
  let actor : C →* F.H := inclusion hCH
  let N (a : C) := F.uhatDisplacement (actor a)
  have hfaith := source_shifted_action_faithful_at d earlier hq chosen structural alternatives
    F hne hseed g hgP hgH l hlL hl hgen hspace
  have hinj : Function.Injective N := by
    intro a b hab
    have heq : F.uhatAction (actor a) = F.uhatAction (actor b) := by
      ext q
      have hh := LinearMap.congr_fun hab (Additive.ofMul q)
      have hh' : Additive.ofMul (F.uhatAction (actor a) q) - Additive.ofMul q =
          Additive.ofMul (F.uhatAction (actor b) q) - Additive.ofMul q := hh
      exact Additive.ofMul.injective (sub_left_inj.mp hh')
    have hker : (a : G) / (b : G) ∈ C ⊓ F.uhatAction.ker.map F.H.subtype := by
      refine ⟨C.div_mem a.property b.property, ⟨actor a / actor b, ?_, rfl⟩⟩
      change F.uhatAction (actor a / actor b) = 1
      rw [map_div, heq]
      simp only [div_eq_mul_inv, mul_inv_cancel]
    have hbot : (a : G) / (b : G) = 1 := by
      change (a : G) / (b : G) ∈ (⊥ : Subgroup G)
      exact hfaith ▸ hker
    exact Subtype.ext (div_eq_one.mp hbot)
  have hcard : Nat.card C ≤ 2 :=
    Theory.LinearAlgebra.card_le_two_of_alternating_plane_maps B.form B.nondegenerate
      (F.hatSubspace V) (CaseOneGeometry.seed_hat_dimension F hvz) N hinj
      (fun a x => B.alternating.eq_iff.mp
        (source_shifted_alternating_displacement_at d earlier hq chosen structural alternatives F hne
          htwo hphi hc g l hgP hgH (chosen.normalizes hlL) hl hspace (actor a) a.property x))
      (fun a => source_shifted_displacement_range_at d earlier hq chosen structural alternatives
        F hne g l hgP hgH (chosen.normalizes hlL) hl hspace (actor a) a.property)
  change Nat.card (Chapter12.Section08.centerIn (conjugate (F.I₂ L) l)) ≤ 2 at hcard
  rw [centerIn_conjugate, conjugate, card_map_of_injective (MulAut.conj l⁻¹).injective] at hcard
  exact hcard
theorem source_shifted_amalgam_type_at (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hseed : centralLTSeed F L = ⊥)
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    Nat.card (Chapter12.Section08.centerIn (F.I₂ L)) = 2 ∧
    ∃ g l e : G, g ∈ L ∧ g ∈ F.P L ∧ g ∉ F.H ∧ l ∈ L ∧
      l ∈ centralizer (conjugate (F.Vi 1) g : Set G) ∧
      V = F.Vi 2 ⊔ conjugate (F.Vi 1) l ∧
      L = F.orderedResidual L 1 ⊔ conjugate (F.orderedResidual L 1) l ∧
      orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧ e ∈ F.ZU ∧ e ∉ F.Vi 1 ∧
      let a := l⁻¹ * e * l
      let K := conjugateSpanBy (zpowers a) F.H
      ∃ haH : a ∈ F.H,
        orderOf a = 2 ∧ F.uhatAction ⟨a, haH⟩ ≠ 1 ∧
        (∃ helem : IsElementaryAbelian 2 F.Uhat, letI := helem
          ∃ B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat),
            B.IsAlt ∧ B.Nondegenerate ∧
            (∀ (h : F.H) (x y : F.Uhat),
              B (Additive.ofMul (F.uhatAction h x)) (Additive.ofMul (F.uhatAction h y)) =
                B (Additive.ofMul x) (Additive.ofMul y)) ∧
            (F.uhatDisplacement ⟨a, haH⟩).range = F.hatSubspace V ∧
            (∀ x, B x (F.uhatDisplacement ⟨a, haH⟩ x) = 0)) ∧
        K ≤ centralizer (F.ZU : Set G) ∧
        amalgamGroup F L K ≤ centralizer ({e} : Set G) ∧
        IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)) ∧
        pCore 2 (AmalgamQuotient F L K) = ⊥ := by
  obtain ⟨g, l, e, hgL, hgP, hgH, hlL, hl, hspace, hgen, he, heI, heT, heU, heV,
    haH, ha, hfaith, _, hK, hKe, hr, hcore⟩ :=
    source_shifted_amalgam_faithful_at d earlier hq chosen structural alternatives F hne hseed hI
  have horder : Nat.card (Chapter12.Section08.centerIn (F.I₂ L)) = 2 := by
    apply Nat.le_antisymm (source_center_order_le_two_at d earlier hq chosen structural alternatives F hne hseed)
    have hh := card_le_of_le (zpowers_le.mpr heI)
    rwa [Nat.card_zpowers, he] at hh
  refine ⟨horder, g, l, e, hgL, hgP, hgH, hlL, hl, hspace, hgen, he, heI, heT, heU, heV,
    haH, ha, hfaith, ?_, hK, hKe, hr, hcore⟩
  let := chosen.elementary
  obtain ⟨htwo, hphi, _⟩ := CaseOneHS.source_closure_at d earlier hq chosen structural alternatives F hne
  let helem := F.uhat_elementary_of_point (by decide) htwo hphi
  let := helem
  let h := SourceAssembly.At.higherRankHypothesis d earlier hq chosen
  have hc := (F.localKernel_commutator_squares d.qtke L (normalizer (L : Set G))
    (by decide) chosen.le_sylow chosen.normalizes (h.sylow_normalizes_at structural)
    h.residual (fun _ => ⟨h.naturalMarking⟩) (h.flag_escape_at F alternatives)).1
  let B := F.localKernel_markedForm (by decide) htwo hphi hc
  have haI : l⁻¹ * e * l ∈ Chapter12.Section08.centerIn (conjugate (F.I₂ L) l) := by
    rw [centerIn_conjugate]
    simpa only [conjugate, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      mem_map_of_mem (MulAut.conj l⁻¹).toMonoidHom heI
  refine ⟨helem, B.form, B.alternating, B.nondegenerate, ?_,
    source_shifted_displacement_eq_seed_at d earlier hq chosen structural alternatives F hne
      htwo hphi hc g l hgP hgH (chosen.normalizes hlL) hl hspace ⟨_, haH⟩ haI hfaith,
    source_shifted_alternating_displacement_at d earlier hq chosen structural alternatives F hne
      htwo hphi hc g l hgP hgH (chosen.normalizes hlL) hl hspace ⟨_, haH⟩ haI⟩
  intro h x y
  change F.uhatBilinearForm (by decide) htwo hphi
    (Additive.ofMul (F.uhatAction h x)) (Additive.ofMul (F.uhatAction h y)) = _
  rw [F.uhatBilinearForm_apply, F.uhatCommutator_invariant (by decide) htwo hphi]
  rfl
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless

end
