module

public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Contract
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.FullAction.ActionImage
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families
public import CFSG.Quasithin.ChapterA.Section04.Modules
public import Theory.GroupTheory.CComponent.SimpleImage
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Selecting the component in the full moved-space action

The source's earlier Proposition 1.2.1(1) is retained as a universal input
on groups with nontrivial two-core. The moved elementary eight-group proves
that this input applies to LX. Residual generation then constructs an actual
C-component covering the literal conjugation image, without assuming the
action kernel solvable. Subnormal transport and the same moved group prove
membership in the canonical local family over the specified Sylow subgroup.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemma 14.4.8(2), printed p.1009. The source projection and generator placement
are separate obligations; the earlier inputs must be discharged by the
outer source assembly.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components
open ChapterA.Section04
variable {G : Type*} [Group G] [Finite G]

/-- The exact generation clause of the earlier Proposition 1.2.1(1). -/
@[expose] def EarlierComponentGeneration (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ A : Subgroup G, A ∈ Chapter1.H G →
    cComponentLayer A = solvableResidual A

private theorem elementaryEight_simple_perfect {W : Type*} [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 8) :
    IsSimpleGroup (MulAut W) ∧ Group.IsPerfect (MulAut W) := by
  obtain ⟨e⟩ := MulAut.elementaryEight_equiv_PSL3 hW
  let : IsSimpleGroup Matrix.PSL3Two.PSL :=
    Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : Group.IsPerfect Matrix.PSL3Two.PSL := Atlas.psl_perfect 3 (by decide)
  exact ⟨e.isSimpleGroup,
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

omit [Finite G] in
/-- A normal elementary eight-group witnesses membership in the source H-family. -/
theorem mem_H_of_normalized_eight {A W : Subgroup G}
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 8) (hWA : W ≤ A)
    (hn : A ≤ normalizer (W : Set G)) : A ∈ Chapter1.H G := by
  have hc : W ≤ A.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 W) hWA hn
  intro he
  have hw : W = ⊥ := le_bot_iff.mp (he ▸ hc)
  have hcard : Nat.card W = 1 := by rw [hw, card_bot]
  omega

omit [Finite G] in
/-- A component of a T-invariant group remains a component after adjoining T. -/
theorem cComponent_join_sylow {A C T : Subgroup G}
    (hC : C ∈ Chapter1.cComponentsIn A) (hT : T ≤ normalizer (A : Set G)) :
    C ∈ Chapter1.cComponentsIn (A ⊔ T) := by
  have hA : (A.subgroupOf (A ⊔ T)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hT)
  have he : (C.subgroupOf A).map
      (inclusion (show A ≤ A ⊔ T from le_sup_left)) = C.subgroupOf (A ⊔ T) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hC.1 hx⟩, hx, rfl⟩
  have hcomp := (hC.2.map_equiv (subgroupOfEquivOfLe
    (show A ≤ A ⊔ T from le_sup_left)).symm).map_subtype hA.isSubnormal
  refine ⟨hC.1.trans le_sup_left, ?_⟩
  have hfun : (A.subgroupOf (A ⊔ T)).subtype.comp
      (subgroupOfEquivOfLe (show A ≤ A ⊔ T from le_sup_left)).symm.toMonoidHom =
      inclusion (show A ≤ A ⊔ T from le_sup_left) := by ext; rfl
  simpa only [map_map, hfun, he] using hcomp

/-- Select an actual component covering the full conjugation image, and
prove the Sylow and nontrivial-core conditions for its canonical membership. -/
theorem exists_covering_local_component
    (earlier : EarlierComponentGeneration G) (T : Sylow 2 G)
    {A W : Subgroup G} [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 8) (hWA : W ≤ A)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hn : A ⊔ (T : Subgroup G) ≤ normalizer (W : Set G))
    (hs : Function.Surjective (conjugation A W (le_sup_left.trans hn))) :
    ∃ (C : Subgroup G) (hC : C ∈ Chapter1.cComponentsIn A),
      C ∈ Chapter1.L G T ∧
      Function.Surjective (conjugation C W (hC.1.trans (le_sup_left.trans hn))) ∧
      C ⊔ (A ⊓ centralizer (W : Set G)) = A := by
  obtain ⟨hsi, hpe⟩ := elementaryEight_simple_perfect hW
  let := hsi
  let := hpe
  let f := conjugation A W (le_sup_left.trans hn)
  obtain ⟨D, hD, hm⟩ := exists_cComponent_surjects_of_layer_eq_residual
    (earlier A (mem_H_of_normalized_eight hW hWA (le_sup_left.trans hn))) f hs
  let C := D.map A.subtype
  have hCA : C ≤ A := map_subtype_le D
  have hC : C ∈ Chapter1.cComponentsIn A :=
    ⟨hCA, by simpa only [C, subgroupOf, comap_map_eq_self_of_injective A.subtype_injective] using hD⟩
  have hCJ := cComponent_join_sylow hC hTA
  have hJH := mem_H_of_normalized_eight hW (hWA.trans le_sup_left) hn
  have hlocal : C ∈ Chapter1.L G T :=
    (Chapter1.lemma_1_2_6 T ⟨hJH,
      fun _ hx => (show (T : Subgroup G) ≤ A ⊔ T from le_sup_right) hx⟩).1 hCJ |>.2
  have hsurj : Function.Surjective (conjugation C W (hCA.trans (le_sup_left.trans hn))) := by
    intro a
    obtain ⟨d, hd, he⟩ := show a ∈ D.map f by rw [hm]; trivial
    refine ⟨⟨d, mem_map.mpr ⟨d, hd, rfl⟩⟩, ?_⟩
    have hr := DFunLike.congr_fun
      (conjugation_restrict (hCA.trans (le_sup_left.trans hn))
        (le_sup_left.trans hn) hCA)
      (⟨d, mem_map.mpr ⟨d, hd, rfl⟩⟩ : C)
    exact hr.symm.trans he
  refine ⟨C, hC, hlocal, hsurj, ?_⟩
  have hc := congrArg (map A.subtype) (sup_ker_eq_top_of_map_eq_top f hm)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hc
  have hk : f.ker.map A.subtype = A ⊓ centralizer (W : Set G) := by
    rw [conjugation_ker, subgroupOf_map_subtype, inf_comm]
  rwa [hk] at hc

private theorem full_action_core_le_ker {C W : Type*} [Group C] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 8)
    (f : C →* MulAut W) (hf : Function.Surjective f) : pCore 2 C ≤ f.ker := by
  obtain ⟨e⟩ := MulAut.elementaryEight_equiv_PSL3 hW
  have hzero : pCore 2 (MulAut W) = ⊥ := by
    apply ((pCore 2 (MulAut W)).map_eq_bot_iff_of_injective
      (f := e.toMonoidHom) e.injective).mp
    rw [pCore_map_iso, Matrix.PSL3Two.pCore_two_PSL_eq_bot]
  have hn : ((pCore 2 C).map f).Normal := Normal.map inferInstance f hf
  have hc : (pCore 2 C).map f ≤ pCore 2 (MulAut W) :=
    le_sSup ⟨hn, pCore_isPGroup.map f⟩
  rw [hzero] at hc
  exact (map_eq_bot_iff (pCore 2 C)).mp (le_bot_iff.mp hc)

/-- The component's full action makes its intrinsic signalizer module
nontrivial. Faithfulness is proved, before using any 14.3.4 conclusion. -/
theorem covering_component_isFaithful
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    {A C W : Subgroup G} [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 8) (hWA : W ≤ A)
    (hn : A ≤ normalizer (W : Set G))
    (hC : C ∈ Chapter1.cComponentsIn A) (hlocal : C ∈ Chapter1.L G T)
    (hs : Function.Surjective (conjugation C W (hC.1.trans hn))) :
    IsFaithfulSignalizerType C := by
  have hCW := hC.1.trans hn
  have hp := Chapter1.Section02.Adequate.mem_L_isPPerfect hlocal
  have hDC : ⁅C, W⁆ ≤ C := by
    let : (W.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer hn
    let : Group.IsNilpotent (W.subgroupOf A) :=
      (IsElementaryAbelian.isPGroup 2 W).comap_subtype.isNilpotent
    have hc := hC.2.commutator_le_of_solvable (W.subgroupOf A) le_normalizer_of_normal
    simpa only [map_commutator, map_subgroupOf_eq_of_le hC.1,
      map_subgroupOf_eq_of_le hWA] using map_mono (f := A.subtype) hc
  have hDW : ⁅C, W⁆ ≤ W := le_normalizer_iff_commutator_le_right.mp hCW
  have hDcore : ⁅C, W⁆ ≤ C.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((IsElementaryAbelian.isPGroup 2 W).to_le hDW)
      hDC (normalizer_commutator_ge_left C W)
  have hcoreW : C.pCoreIn 2 ≤ centralizer (W : Set G) := by
    have hk := full_action_core_le_ker hW (conjugation C W hCW) hs
    rw [conjugation_ker] at hk
    exact map_le_iff_le_comap.mpr hk
  have hDomega : ⁅C, W⁆ ≤ Stellmacher.omegaOneCenterAmbient (C.pCoreIn 2) := by
    intro d hd
    apply (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨hDcore hd, elemPow_eq_one_of_isElementaryAbelian d (hDW hd),
      fun q hq => (mem_centralizer_iff.mp (hcoreW hq) d (hDW hd)).symm⟩
  have hidem : ⁅⁅C, W⁆, C⁆ = ⁅C, W⁆ := by
    have hr : BenderSuzuki.External.hktPResidual 2 C = ⊤ :=
      hp _ BenderSuzuki.External.hktPResidual_normal
        BenderSuzuki.External.hktPResidual_quotient_isPGroup
    have hm : (BenderSuzuki.External.hktPResidual 2 C).map C.subtype = C := by
      rw [hr, ← MonoidHom.range_eq_map, range_subtype]
    have hh := BenderSuzuki.External.commutator_map_pResidual_idempotent_of_isPGroup
      2 W C (IsElementaryAbelian.isPGroup 2 W) hCW
    dsimp only at hh
    rw [hm, commutator_comm W C] at hh
    exact hh
  have hnon : ⁅C, W⁆ ≠ ⊥ := by
    intro he
    have hz : C ≤ centralizer (W : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp he
    have hk : (conjugation C W hCW).ker = ⊤ := by
      rw [conjugation_ker]
      exact top_unique (fun c _ => hz c.property)
    have heq := MonoidHom.ker_eq_top_iff.mp hk
    have hsub : Subsingleton (MulAut W) := ⟨by
      intro a b
      obtain ⟨c, rfl⟩ := hs a
      obtain ⟨d, rfl⟩ := hs b
      rw [heq]
      rfl⟩
    let := hsub
    have hc : Nat.card (MulAut W) = 1 := Nat.card_unique
    rw [card_mulAut_of_elementary_eight W hW] at hc
    omega
  refine ⟨Chapter1.Section02.Adequate.mem_L_isSignalizerType T hE hlocal, ?_⟩
  intro he
  apply hnon
  apply le_bot_iff.mp
  have hle := commutator_mono hDomega (le_refl C)
  rw [hidem] at hle
  have hm : ⁅Stellmacher.omegaOneCenterAmbient (C.pCoreIn 2), C⁆ =
      intrinsicSignalizerModule C := by
    rw [intrinsicSignalizerModule, signalizerModule_eq_commutator_omegaCenter,
      commutator_comm]
    rfl
  rwa [hm, he] at hle

/-- The actual action excludes the A5 branch of 14.3.4(1): its order has
no factor seven, whereas the full automorphism group has order 168. -/
theorem not_alternatingFive_coreQuotient_of_full_action
    {C W : Type*} [Group C] [Finite C] [Group W] [Finite W]
    [IsElementaryAbelian 2 W] (hW : Nat.card W = 8)
    (f : C →* MulAut W) (hf : Function.Surjective f) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨e⟩
  have hq : Nat.card (C ⧸ pCore 2 C) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp
    (pCore_isPGroup : IsPGroup 2 (pCore 2 C))
  have hd := card_dvd_of_surjective f hf
  rw [card_mulAut_of_elementary_eight W hW,
    card_eq_card_quotient_mul_card_subgroup (pCore 2 C), hq, hn] at hd
  have hseven : 7 ∣ 60 * 2 ^ n := (by decide : 7 ∣ 168).trans hd
  rcases (by decide : Nat.Prime 7).dvd_mul.mp hseven with h | h
  · norm_num at h
  · have ht := (by decide : Nat.Prime 7).dvd_of_dvd_pow h
    norm_num at ht

/-- The selected source component, with its actual embedding and action.
This is an output of selection, not an assumption about the generators. -/
structure SelectedComponent (A W T : Subgroup G)
    (hn : A ≤ normalizer (W : Set G)) where
  carrier : Subgroup G
  component : carrier ∈ Chapter1.cComponentsIn A
  maximal : carrier ∈ Chapter1.LStar G T
  faithful : IsFaithfulSignalizerType carrier
  normal_join : (carrier.subgroupOf (carrier ⊔ T)).Normal
  surjective : Function.Surjective (conjugation carrier W (component.1.trans hn))
  quotient : Nonempty (coreQuotient carrier ≃* Matrix.PSL3Two.PSL)
  cover : carrier ⊔ (A ⊓ centralizer (W : Set G)) = A

/-- Selection and the application of 14.3.4 for the literal source family.
The moved space supplies the nontrivial core; the full action proves
faithfulness and excludes A5. No component placement is an input. -/
theorem exists_selectedComponent_of_Y
    (earlier : EarlierComponentGeneration G)
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    {H V₂ E X L₂ : Subgroup G} (hX : X ∈ YFamily H T V₂ E)
    [IsElementaryAbelian 2 (movedSpace V₂ X)]
    (hV₂T : V₂ ≤ T) (hTL₂ : (T : Subgroup G) ≤ normalizer (L₂ : Set G))
    (hn : localJoin L₂ X ⊔ (T : Subgroup G) ≤ normalizer (movedSpace V₂ X : Set G))
    (hs : Function.Surjective (conjugation (localJoin L₂ X) (movedSpace V₂ X)
      (le_sup_left.trans hn))) :
    Nonempty (SelectedComponent (localJoin L₂ X) (movedSpace V₂ X) T
      (le_sup_left.trans hn)) := by
  have hWA : movedSpace V₂ X ≤ localJoin L₂ X :=
    (le_normalizer_iff_commutator_le_right.mp (hV₂T.trans hX.1.T_normalizes)).trans
      le_sup_right
  have hTA : (T : Subgroup G) ≤ normalizer (localJoin L₂ X : Set G) :=
    (le_inf hTL₂ hX.1.T_normalizes).trans
      (normalizer_inf_normalizer_le_normalizer_sup L₂ X)
  obtain ⟨C, hC, hlocal, hsurj, hcover⟩ :=
    exists_covering_local_component earlier T hX.2.1 hWA hTA hn hs
  have hfaith := covering_component_isFaithful T hE hX.2.1 hWA
    (le_sup_left.trans hn) hC hlocal hsurj
  obtain ⟨halt, hnormal, hmax⟩ := classification C hlocal hfaith
  have hquot := halt.resolve_left
    (not_alternatingFive_coreQuotient_of_full_action hX.2.1 _ hsurj)
  exact ⟨⟨C, hC, hmax, hfaith, hnormal, hsurj, hquot, hcover⟩⟩

/-- Consume the full LXT action constructed from the earlier extraspecial
geometry. Residual functoriality first obtains the full LX action; the
selection theorem then proves the component and classification conclusions. -/
theorem exists_selectedComponent_of_full_join_action
    (earlier : EarlierComponentGeneration G)
    (T : Sylow 2 G) (hE : IsEvenCharacteristicAt T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    {H V₂ E X L₂ : Subgroup G} (hX : X ∈ YFamily H T V₂ E)
    [IsElementaryAbelian 2 (movedSpace V₂ X)]
    (hV₂T : V₂ ≤ T) (hL₂ : twoResidual L₂ = L₂)
    (hTL₂ : (T : Subgroup G) ≤ normalizer (L₂ : Set G))
    (hn : localJoin L₂ X ⊔ (T : Subgroup G) ≤ normalizer (movedSpace V₂ X : Set G))
    (hs : Function.Surjective
      (conjugation (localJoin L₂ X ⊔ (T : Subgroup G)) (movedSpace V₂ X) hn)) :
    Nonempty (SelectedComponent (localJoin L₂ X) (movedSpace V₂ X) T
      (le_sup_left.trans hn)) :=
  exists_selectedComponent_of_Y earlier T hE classification hX hV₂T hTL₂ hn
    (localJoin_action_surjective_of_join_T hX hL₂ hTL₂ T.isPGroup' hn hs)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.LocalAction.Components
