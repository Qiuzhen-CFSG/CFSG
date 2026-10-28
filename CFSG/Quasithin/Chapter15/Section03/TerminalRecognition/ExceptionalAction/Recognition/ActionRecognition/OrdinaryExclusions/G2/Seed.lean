module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.Recognition.ActionRecognition.OrdinaryExclusions.Reduction
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# The marked terminal seed in central sections

The first local factor normalizes V, its two-core centralizes V, and its
quotient by that core is cyclic of order three. A Sylow three-subgroup
therefore has the same commutators on V as the whole factor. Coprime
splitting and V = [V,Y_F] show that V has no Y_F-fixed vector.

Consequently the four-dimensional seed embeds into every section containing
it with a Y_F-fixed kernel. Its image is still fixed by the actual O₂(Ẏ_F),
restricted to the offender actor. This justifies using an irreducible central
quotient without imposing a split extension or discarding fixed summands.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, B.5.1,
printed p.99, and the final proof of 15.3.1, printed p.1155 (1 March 2004).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2

variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- The marked V has no nonidentity Y_F-fixed element. Its action factors through
the odd quotient of Y_F, so coprime splitting applies to V = [V,Y_F]. -/
theorem seed_inf_centralizer_first : V ⊓ centralizer (d.YF : Set H) = ⊥ := by
  have hnorm : d.YF ≤ normalizer (V : Set H) :=
    le_normalizer_iff_commutator_le_left.mpr d.vector_commutator.ge
  let A : Sylow 3 d.YF := Classical.choice (inferInstance : Nonempty (Sylow 3 d.YF))
  let B : Subgroup H := (A : Subgroup d.YF).map d.YF.subtype
  have hBY : B ≤ d.YF := map_subtype_le _
  have hC : d.YF.pCoreIn 2 ≤ centralizer (V : Set H) :=
    le_sup_right.trans (d.core_bound.trans d.centralizer_eq.le)
  obtain ⟨e⟩ := d.first_odd_quotient
  have hq : IsPGroup 3 (d.YF ⧸ pCore 2 d.YF) := by
    apply IsPGroup.of_equiv _ e.symm
    apply IsPGroup.of_card (n := 1)
    simp
  have hres : pResidual 3 d.YF ≤ pCore 2 d.YF := sInf_le ⟨inferInstance, hq⟩
  have hgen : d.YF.pCoreIn 2 ⊔ B = d.YF := by
    have heq : pCore 2 d.YF ⊔ (A : Subgroup d.YF) = ⊤ :=
      top_unique ((pResidual_sup_sylow_eq_top A).symm.trans_le (sup_le_sup_right hres _))
    simpa only [pCoreIn, B, Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] using
      congrArg (fun K : Subgroup d.YF => K.map d.YF.subtype) heq
  have hVB : ⁅V, B⁆ = V :=
    (commutator_eq_of_centralizing_sup hgen hC (hBY.trans hnorm)).trans
      d.vector_commutator.symm
  have hV : IsPGroup 2 V := (pCore_isPGroup (p := 2) (G := H)).of_injective
    (inclusion d.vector_le_core) (inclusion_injective _)
  let : IsMulCommutative V := ⟨⟨fun x y => by
    apply Subtype.ext
    exact congrArg (fun z : moduleClosure V => (z : H)) (mul_comm
      (⟨x, le_normalClosure x.property⟩ : moduleClosure V)
      (⟨y, le_normalClosure y.property⟩ : moduleClosure V))⟩⟩
  have hd := commutator_disjoint_centralizer_of_coprime V B (hBY.trans hnorm)
    (IsPGroup.coprime_card_of_ne 3 2 (by decide) B V (A.isPGroup'.map _) hV)
  rw [hVB] at hd
  have hdz : V ⊓ centralizer (B : Set H) = ⊥ :=
    hd.symm.eq_bot_of_le inf_le_left
  exact le_bot_iff.mp ((inf_le_inf_left V (centralizer_le hBY)).trans hdz.le)
/-- The marked seed avoids the fixed space of every offender subgroup containing
the actual image of Y_F. -/
theorem seed_disjoint_fixedSpace (L : Subgroup d.offenderGroup)
    (hYL : d.YF.map coreProjection ≤ L.map d.offenderGroup.subtype) :
    Disjoint (planeSubspace V V) (fixedSpace d.offenderAction L) := by
  apply Submodule.disjoint_def.mpr
  intro v hv hc
  have hz : (v.toMul : H) ∈ V ⊓ centralizer (d.YF : Set H) := by
    refine ⟨hv, mem_centralizer_iff.mpr ?_⟩
    intro y hy
    obtain ⟨a, ha, hea⟩ := hYL (mem_map_of_mem coreProjection hy)
    have he := hc ⟨a, ha⟩
    have heq : a = (⟨coreProjection y, d.first_image_le
        (mem_map_of_mem coreProjection hy)⟩ : d.offenderGroup) := Subtype.ext hea
    change d.offenderAction a v = v at he
    rw [heq] at he
    have he' := congrArg (fun w : Additive (moduleClosure V) => (w.toMul : H)) he
    change ((quotientAction V d.centralizer_isTwoGroup d.core_centralizes
      (coreProjection y) v).toMul : H) = (v.toMul : H) at he'
    rw [quotientAction_apply] at he'
    exact mul_inv_eq_iff_eq_mul.mp he'
  rw [seed_inf_centralizer_first d] at hz
  exact Additive.toMul.injective (Subtype.ext hz)

/-- The image of Y_F, restricted through its actual inclusion in the offender actor. -/
noncomputable abbrev firstInOffender : Subgroup d.offenderGroup :=
  (d.YF.map coreProjection).subgroupOf d.offenderGroup

/-- Mapping back to the full quotient recovers precisely the image of Y_F. -/
theorem firstInOffender_map :
    (firstInOffender d).map d.offenderGroup.subtype = d.YF.map coreProjection :=
  map_subgroupOf_eq_of_le d.first_image_le

/-- The source identity V = [V,Y_F] puts the seed in every moved space whose
actor contains the actual image of Y_F. -/
theorem seed_le_moved (L : Subgroup d.offenderGroup)
    (hL : firstInOffender d ≤ L) : planeSubspace V V ≤ moved d.offenderAction L := by
  let C : Subgroup (moduleClosure V) :=
    (moved d.offenderAction L).toAddSubgroup.toSubgroup'
  have hVC : V ≤ C.map (moduleClosure V).subtype := by
    conv_lhs => rw [d.vector_commutator, commutator_comm]
    apply commutator_le.mpr
    intro y hy v hv
    let w : Additive (moduleClosure V) := Additive.ofMul ⟨v, le_normalClosure hv⟩
    let a : d.offenderGroup := ⟨coreProjection y,
      d.first_image_le (mem_map_of_mem coreProjection hy)⟩
    have ha : a ∈ L := hL (mem_map_of_mem coreProjection hy)
    refine ⟨(d.offenderAction a w - w).toMul, ?_, ?_⟩
    · change d.offenderAction a w - w ∈ moved d.offenderAction L
      exact Submodule.subset_span ⟨a, ha, w, Submodule.mem_top, rfl⟩
    · change ((quotientAction V d.centralizer_isTwoGroup d.core_centralizes
        (coreProjection y) w).toMul : H) / v = ⁅y, v⁆
      rw [quotientAction_apply, div_eq_mul_inv]
      rfl
  intro v hv
  obtain ⟨w, hw, he⟩ := hVC hv
  have heq : w = v.toMul := Subtype.ext he
  subst w
  exact hw

/-- Inclusion of the marked seed followed by the actual central-section projection. -/
noncomputable def seedSectionMap (S : Subrepresentation d.offenderAction)
    (C : Subrepresentation S.toRepresentation)
    (hS : planeSubspace V V ≤ S.toSubmodule) :
    planeSubspace V V →ₗ[ZMod 2] (S.toSubmodule ⧸ C.toSubmodule) :=
  C.toSubmodule.mkQ.comp (Submodule.inclusion hS)

/-- A kernel fixed by Y_F loses no vector of the marked seed. No splitting
or bound on the dimension of the entire kernel is required. -/
theorem seedSectionMap_injective (S : Subrepresentation d.offenderAction)
    (C : Subrepresentation S.toRepresentation)
    (hS : planeSubspace V V ≤ S.toSubmodule)
    (hC : C.toSubmodule ≤ fixedSpace S.toRepresentation (firstInOffender d)) :
    Function.Injective (seedSectionMap d S C hS) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hc : (Submodule.inclusion hS v) ∈ C.toSubmodule :=
    (Submodule.Quotient.mk_eq_zero C.toSubmodule).mp hv
  have hfixed : (v : Additive (moduleClosure V)) ∈
      fixedSpace d.offenderAction (firstInOffender d) := by
    intro a
    exact congrArg Subtype.val (hC hc a)
  apply Subtype.ext
  exact Submodule.disjoint_def.mp
    (seed_disjoint_fixedSpace d (firstInOffender d) (firstInOffender_map d).ge)
    v v.property hfixed

/-- The actual local core fixes the image of the seed in the section. -/
theorem seedSectionMap_fixed (S : Subrepresentation d.offenderAction)
    (C : Subrepresentation S.toRepresentation)
    (hS : planeSubspace V V ≤ S.toSubmodule) (v : planeSubspace V V) :
    seedSectionMap d S C hS v ∈
      fixedSpace C.quotientRepresentation d.firstCoreInOffender := by
  intro a
  change C.toSubmodule.mkQ (S.toRepresentation a.val (Submodule.inclusion hS v)) =
    C.toSubmodule.mkQ (Submodule.inclusion hS v)
  congr 1
  apply Subtype.ext
  exact d.vector_fixed_offender v.property a

/-- The four-dimensional fixed seed survives any section containing it whose
kernel is fixed by the image of Y_F. -/
theorem section_firstCore_fixed_finrank_ge_four (S : Subrepresentation d.offenderAction)
    (C : Subrepresentation S.toRepresentation)
    (hS : planeSubspace V V ≤ S.toSubmodule)
    (hC : C.toSubmodule ≤ fixedSpace S.toRepresentation (firstInOffender d)) :
    4 ≤ Module.finrank (ZMod 2)
      (fixedSpace C.quotientRepresentation d.firstCoreInOffender) := by
  let f := (seedSectionMap d S C hS).codRestrict
    (fixedSpace C.quotientRepresentation d.firstCoreInOffender)
    (seedSectionMap_fixed d S C hS)
  have hf : Function.Injective f := by
    intro v w he
    exact seedSectionMap_injective d S C hS hC (congrArg Subtype.val he)
  rw [← d.vector_finrank]
  exact LinearMap.finrank_le_finrank_of_injective hf

end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.ExceptionalAction.ActionRecognition.OrdinaryExclusions.G2
