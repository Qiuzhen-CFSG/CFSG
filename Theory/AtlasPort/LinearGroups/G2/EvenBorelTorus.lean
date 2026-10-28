module

public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.PResidual.FiniteImage
public import Mathlib.GroupTheory.Complement

/-!
# The intrinsic Borel quotient of even G₂

The six positive root groups and the two-parameter diagonal torus are
complements in the actual octonion Borel. The normal unipotent Sylow is
its two-core, so the quotient is multiplicatively isomorphic to Fˣ × Fˣ.
Sylow conjugacy transports this identification to any specified Sylow.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954. The root matrices,
normal forms and torus normalization are from the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

namespace Atlas.G2.EvenBorelTorus
open Subgroup LieParabolicSetup
variable {F : Type*} [Field F]

/-- The unipotent subgroup, viewed inside the actual Borel. -/
abbrev radical : Subgroup (borel (K := F)) := unipotent.subgroupOf borel

/-- The split torus, viewed inside the actual Borel. -/
abbrev complement : Subgroup (borel (K := F)) := splitTorus.subgroupOf borel

theorem torus_le_normalizer :
    splitTorus (K := F) ≤ normalizer (unipotent (K := F) : Set (Model F)) :=
  le_normalizer_iff.mpr (fun _ ht _ hu => torus_normalizes_unipotent ht hu)

instance radical_normal : (radical (F := F)).Normal :=
  normal_subgroupOf_of_le_normalizer (sup_le unipotent.le_normalizer torus_le_normalizer)

theorem radical_isComplement : (radical (F := F)).IsComplement' complement := by
  apply isComplement'_of_disjoint_and_mul_eq_univ
  · apply disjoint_def.mpr
    intro x hx hy
    apply Subtype.ext
    exact disjoint_def.mp unipotent_disjoint_torus hx hy
  · rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨⟨u,t⟩,h⟩ := (borelProductEquiv (K := F)).surjective x
    exact ⟨⟨u, (le_sup_left : unipotent ≤ borel) u.property⟩, u.property,
      ⟨t, (le_sup_right : splitTorus ≤ borel) t.property⟩, t.property,
      Subtype.ext (congrArg Subtype.val h)⟩

/-- The quotient torus is an actual multiplicative equivalence. -/
noncomputable def quotientRadicalEquiv :
    borel (K := F) ⧸ radical ≃* (Fˣ × Fˣ) :=
  radical_isComplement.symm.QuotientMulEquiv.trans
    ((subgroupOfEquivOfLe (show splitTorus (K := F) ≤ borel from le_sup_right)).trans
      torusParameterEquiv.symm)

/-- The torus coordinates of a Borel element. -/
noncomputable def projection : borel (K := F) →* (Fˣ × Fˣ) :=
  quotientRadicalEquiv.toMonoidHom.comp (QuotientGroup.mk' radical)

/-- The actual split torus embedded in the Borel. -/
def torusSection : (Fˣ × Fˣ) →* borel (K := F) :=
  torusHom.codRestrict borel (fun p => (le_sup_right : splitTorus ≤ borel) ⟨p,rfl⟩)

theorem projection_surjective : Function.Surjective (projection (F := F)) :=
  quotientRadicalEquiv.surjective.comp (QuotientGroup.mk'_surjective radical)

theorem projection_ker : (projection (F := F)).ker = radical := by
  ext x
  change quotientRadicalEquiv (QuotientGroup.mk' radical x) = 1 ↔ x ∈ radical
  rw [MulEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

/-- The torus projection has the specified values on the split complement. -/
theorem projection_torus (p : Fˣ × Fˣ) :
    projection (⟨torusHom p, (le_sup_right : splitTorus ≤ borel) ⟨p,rfl⟩⟩ : borel) = p := by
  let t : complement (F := F) :=
    ⟨⟨torusHom p, (le_sup_right : splitTorus ≤ borel) ⟨p,rfl⟩⟩, ⟨p,rfl⟩⟩
  have h := radical_isComplement.symm.QuotientMulEquiv.apply_symm_apply t
  change radical_isComplement.symm.QuotientMulEquiv (QuotientGroup.mk t.val) = t at h
  change torusParameterEquiv.symm
    (subgroupOfEquivOfLe (show splitTorus (K := F) ≤ borel from le_sup_right)
      (radical_isComplement.symm.QuotientMulEquiv (QuotientGroup.mk t.val))) = p
  rw [h]
  exact torusParameterEquiv.symm_apply_apply p

variable [Finite F] [CharP F 2]

theorem card_torus_odd : Odd (Nat.card (splitTorus (K := F))) := by
  obtain ⟨n,hn,hF⟩ := field_card (F := F)
  rw [card_splitTorus, hF]
  apply Odd.pow
  exact Nat.Even.sub_odd (Nat.one_le_two_pow) (even_two.pow_of_ne_zero (by omega)) odd_one

theorem radical_isTwoGroup : IsPGroup 2 (radical (F := F)) :=
  unipotent_isTwoGroup.of_injective
    (subgroupOfEquivOfLe (show unipotent (K := F) ≤ borel from le_sup_left)).toMonoidHom
    (subgroupOfEquivOfLe (show unipotent (K := F) ≤ borel from le_sup_left)).injective

theorem twoCore_eq_radical : pCore 2 (borel (K := F)) = radical := by
  have hi : ¬ 2 ∣ (radical (F := F)).index := by
    rw [radical_isComplement.symm.index_eq_card,
      Nat.card_congr (subgroupOfEquivOfLe
        (show splitTorus (K := F) ≤ borel from le_sup_right)).toEquiv]
    exact card_torus_odd.not_two_dvd_nat
  exact le_antisymm
    (pCore_isPGroup.le_sylow_of_normal (radical_isTwoGroup.toSylow hi))
    (le_sSup ⟨inferInstance, radical_isTwoGroup⟩)

theorem twoCoreIn_eq_unipotent : (borel (K := F)).pCoreIn 2 = unipotent := by
  rw [pCoreIn, twoCore_eq_radical, map_subgroupOf_eq_of_le
    (show unipotent (K := F) ≤ borel from le_sup_left)]

noncomputable def quotientTorusEquiv :
    borel (K := F) ⧸ pCore 2 borel ≃* (Fˣ × Fˣ) :=
  (QuotientGroup.quotientMulEquivOfEq twoCore_eq_radical).trans quotientRadicalEquiv

/-- Conjugacy aligns both a specified Sylow and its normalizer. -/
theorem sylow_normalizer_conjugate (S : Sylow 2 (Model F)) :
    ∃ g : Model F,
      unipotent.map (MulAut.conj g).toMonoidHom = (S : Subgroup (Model F)) ∧
      borel.map (MulAut.conj g).toMonoidHom = normalizer (S : Set (Model F)) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model F) (sylow (F := F)) S
  have he : unipotent.map (MulAut.conj g).toMonoidHom = (S : Subgroup (Model F)) :=
    congrArg Sylow.toSubgroup hg
  refine ⟨g,he,?_⟩
  rw [← SylowNormalizer.normalizer_unipotent, map_equiv_normalizer_eq, he]
  rfl

noncomputable def sylowNormalizerEquiv (S : Sylow 2 (Model F)) :
    normalizer (S : Set (Model F)) ≃* borel (K := F) := by
  classical
  let g := Classical.choose (sylow_normalizer_conjugate S)
  have hg := (Classical.choose_spec (sylow_normalizer_conjugate S)).2
  exact ((equivMapOfInjective borel (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hg)).symm

omit [Finite F] [CharP F 2] in
/-- The intrinsic two-core of the specified Sylow normalizer is that Sylow. -/
theorem sylowNormalizer_twoCoreIn (S : Sylow 2 (Model F)) :
    (normalizer (S : Set (Model F))).pCoreIn 2 = S := by
  apply S.is_maximal' (isPGroup_pCoreIn 2 _)
  exact le_pCoreIn_of_normalizes S.isPGroup' (S : Subgroup (Model F)).le_normalizer le_rfl

/-- The quotient equivalence is available in every Sylow marking. -/
noncomputable def sylowNormalizerQuotientEquiv (S : Sylow 2 (Model F)) :
    normalizer (S : Set (Model F)) ⧸ pCore 2 (normalizer (S : Set (Model F))) ≃*
      (Fˣ × Fˣ) :=
  (QuotientGroup.congr _ _ (sylowNormalizerEquiv S)
    (pCore_map_iso 2 (sylowNormalizerEquiv S))).trans quotientTorusEquiv

end Atlas.G2.EvenBorelTorus
