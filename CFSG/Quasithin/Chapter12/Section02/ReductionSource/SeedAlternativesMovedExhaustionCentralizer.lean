module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionStabilization
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionCentralizer

/-!
# The actual component centralizer on the chosen Sylow orbit

Write M = N_G(L), U = componentOrbit V M, and W = componentOrbit V T.
The image K of L on U is quasisimple with its central cover retained.
The centralizer of K in the original Sylow image preserves the seed type,
hence the seed by its homogeneous selection in W. Its two-group action
therefore fixes V, and normality propagates fixation to W.

For every subgroup A of that Sylow image, this proves C_A(V) = C_A(W) = C_A(K).
The original ambient preimages and the exact rank quotient give the source
ratio on W. The D.3.19 consequence is conditional only on the nontriviality
and properness of this component centralizer. Those D.3.13--18 assertions,
the model bounds and the final exclusion U > W remain with qt-baumann-fsu;
this module does not claim normalizer-orbit exhaustion or Source325.
Source: Aschbacher--Smith, D.3.13--19 and 3.2.5,
printed pp.202--204 and580.
-/

public noncomputable section
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Chapter3.Section02.ChosenSource325 ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal internal seed is not centralized by the full image of L. -/
theorem normalizer_seed_not_fixed
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let K := (L.subgroupOf M).map (internalHom M U hn)
    ¬ internalSection U V ≤ fixedSpace (UniqueFactor.imageRepresentation M U hn) K := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  dsimp only
  intro hfix
  apply D.ne_bot
  apply bot_unique
  intro v hv
  apply hc.le
  refine ⟨hv,?_⟩
  intro l hl
  let l' : M := ⟨l,L.le_normalizer hl⟩
  have he := congrArg (fun z : Additive U => z.toMul.val)
    (hfix (show Additive.ofMul (⟨v,le_componentOrbit V M hv⟩ : U) ∈ internalSection U V from hv)
      ⟨f l',⟨l',hl,rfl⟩⟩)
  change l * v * l⁻¹ = v at he
  exact mul_inv_eq_iff_eq_mul.mp he

/-- The component in the faithful full normalizer action is quasisimple.
This retains its central cover; only its intrinsic two-core is killed. -/
theorem normalizer_component_quasisimple
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    IsQuasisimple ((L.subgroupOf (normalizer (L : Set G))).map
      (internalHom (normalizer (L : Set G))
        (componentOrbit V (normalizer (L : Set G))) (le_normalizer_componentOrbit _ _))) := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let f := internalHom M U hn
  let N := L.subgroupOf M
  let : N.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let e : N ≃* L := subgroupOfEquivOfLe L.le_normalizer
  let q := QuotientGroup.congr (pCore 2 N) (pCore 2 L) e (pCore_map_iso 2 e)
  let := h.quasisimple
  have hq : IsQuasisimple (N ⧸ pCore 2 N) := IsQuasisimple.of_mulEquiv q.symm
  apply quasisimple_image_of_twoCore_eq_bot f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective N hq
    _ (D.normalizerActor_twoCore_eq_bot h)
  intro hz
  have hnfix := D.normalizer_seed_not_fixed h hc
  change ¬ internalSection U V ≤ fixedSpace (UniqueFactor.imageRepresentation M U hn) (N.map f) at hnfix
  rw [hz,fixedSpace_bot] at hnfix
  exact hnfix le_top

/-- The Sylow centralizer of the component image fixes the literal seed and
its entire Sylow orbit. No full-orbit exhaustion or actor faithfulness is used. -/
theorem normalizer_sylow_component_centralizer_fixes
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    let S := (internalSylow T M U hn D.sylow_normalizes_component : Subgroup (internalActionImage M U hn))
    internalSection U V ≤ fixedSpace ρ (S ⊓ centralizer (K : Set (internalActionImage M U hn))) ∧
      internalSection U (componentOrbit V (T : Subgroup G)) ≤
        fixedSpace ρ (S ⊓ centralizer (K : Set (internalActionImage M U hn))) := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let f := internalHom M U hn
  let N := L.subgroupOf M
  let K := N.map f
  let S := (internalSylow T M U hn D.sylow_normalizes_component : Subgroup (internalActionImage M U hn))
  let C := centralizer (K : Set (internalActionImage M U hn))
  let I := internalImageSubrepresentation hn D.normalizes
  let : N.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  have hi := internalImageSubrepresentation_irreducible hn D.normalizes
    (internalSubrepresentation_irreducible hn L.le_normalizer
      (le_componentOrbit V M) D.normalizes D.ne_bot (D.seed_invariant_subgroup_eq hc))
  have hstable : S ⊓ C ≤ subspaceStabilizer ρ I.toSubmodule := by
    intro a ha
    apply D.normalizer_sylow_type_stabilizer_le_seed h hc
    refine ⟨ha.1,?_⟩
    obtain ⟨g,rfl⟩ := (UniqueFactor.actionHom M U hn).rangeRestrict_surjective a
    exact (subspace_map_eq_iff ρ _ (f g)).mp
      (typePart_map_eq_of_image_centralizer ρ f N (internalSubrepresentation hn D.normalizes) g ha.2)
  have hfix : internalSection U V ≤ fixedSpace ρ (S ⊓ C) :=
    centralizing_twoGroup_fixes_irreducible ρ K (S ⊓ C) I hi
      ((internalSylow T M U hn D.sylow_normalizes_component).isPGroup'.to_le inf_le_left)
      inf_le_right hstable
  exact ⟨hfix,(internalSection_componentOrbit_le_orbitSpan hn (T : Subgroup G)
    D.sylow_normalizes_component (le_componentOrbit V M)).trans
      (orbitSpan_fixed_of_normal_intersection ρ S C _ hfix)⟩

/-- The kernels on the seed and its Sylow orbit are the same actual component
centralizer, for every subgroup of the original Sylow image. -/
theorem normalizer_sylow_seed_orbit_kernels
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component →
      subspaceKernel ρ (internalSection U V) A = A ⊓ centralizer (K : Set (internalActionImage M U hn)) ∧
      subspaceKernel ρ (internalSection U (componentOrbit V (T : Subgroup G))) A =
        A ⊓ centralizer (K : Set (internalActionImage M U hn)) := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  let f := internalHom M U hn
  let K := (L.subgroupOf M).map f
  let : (L.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : K.Normal := Normal.map inferInstance f
    (UniqueFactor.actionHom M U hn).rangeRestrict_surjective
  let := D.normalizer_component_quasisimple h hc
  have hKI : K ≤ subspaceStabilizer ρ (internalSection U V) :=
    internalSection_stable M U V L hn D.normalizes
  have hnon := D.normalizer_seed_not_fixed h hc
  obtain ⟨hseed,horbit⟩ := D.normalizer_sylow_component_centralizer_fixes h hc
  dsimp only
  intro A hAS
  have hle := subspaceKernel_le_component_centralizer ρ K _ hKI hnon A
  have heq : subspaceKernel ρ (internalSection U V) A = A ⊓ centralizer (K : Set (internalActionImage M U hn)) := by
    apply le_antisymm (le_inf (subspaceKernel_le _ _ _) hle)
    exact fun a ha => ⟨ha.1,fun v hv => hseed hv ⟨a,hAS ha.1,ha.2⟩⟩
  refine ⟨heq,le_antisymm ?_ ?_⟩
  · intro a ha
    exact heq.le ⟨ha.1,fun v hv => ha.2 v (le_componentOrbit V T hv)⟩
  · exact fun a ha => ⟨ha.1,fun v hv => horbit hv ⟨a,hAS ha.1,ha.2⟩⟩

/-- The centralizer kernels retain the original ambient preimage maps. -/
theorem normalizer_sylow_centralizer_images
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let W := componentOrbit V (T : Subgroup G)
    let hn := le_normalizer_componentOrbit V M
    let f := internalHom M U hn
    let K := (L.subgroupOf M).map f
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component →
      (A.comap f ⊓ (centralizer (V : Set G)).subgroupOf M).map f =
        A ⊓ centralizer (K : Set (internalActionImage M U hn)) ∧
      (A.comap f ⊓ (centralizer (W : Set G)).subgroupOf M).map f =
        A ⊓ centralizer (K : Set (internalActionImage M U hn)) := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let W := componentOrbit V (T : Subgroup G)
  let hn := le_normalizer_componentOrbit V M
  dsimp only
  intro A hAS
  have hWU : W ≤ U := iSup_conjugates_le_of_le_normalizer V T U
    (le_componentOrbit V M) (D.sylow_normalizes_component.trans hn)
  have hh := D.normalizer_sylow_seed_orbit_kernels h hc A hAS
  rw [internalSection_kernel M U V hn (le_componentOrbit V M),
    internalSection_kernel M U W hn hWU] at hh
  exact hh

/-- The exact source ratio on W uses the same actor A and its component
centralizer; numerator and denominator come from the literal action maps. -/
theorem normalizer_sylow_section_ratio
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let W := componentOrbit V (T : Subgroup G)
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let f := internalHom M U hn
    let K := (L.subgroupOf M).map f
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component →
      actionRatio (subspaceImageRepresentation ρ (internalSection U W))
        (restrictedSubgroup ρ (internalSection U W) A) =
      ((rank W - rank (W ⊓ centralizer (((A.comap f).map M.subtype : Subgroup G) : Set G)) : ℕ) : ℝ≥0∞) /
        ((rank A - rank (A ⊓ centralizer (K : Set (internalActionImage M U hn))) : ℕ) : ℝ≥0∞) := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let W := componentOrbit V (T : Subgroup G)
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  dsimp only
  intro A hAS
  have hs := hAS.trans (internalSylow_section_stable T M U W hn
    D.sylow_normalizes_component (le_normalizer_componentOrbit V T))
  have hWU : W ≤ U := iSup_conjugates_le_of_le_normalizer V T U
    (le_componentOrbit V M) (D.sylow_normalizes_component.trans hn)
  have hr := rank_subspaceKernel_add_image ρ (internalSection U W) A hs
    ((internalSylow T M U hn D.sylow_normalizes_component).isPGroup'.to_le hAS)
  rw [(D.normalizer_sylow_seed_orbit_kernels h hc A hAS).2] at hr
  rw [actionRatio,internalSection_fixedCodim M U W hn hWU A hs,←hr]
  simp only [Nat.add_sub_cancel_left]
  rfl

/-- D.3.19 after the two structural centralizer assertions. Their proof is
the remaining D.3.13--18 obligation of qt-baumann-fsu, not a consequence of
the numerical cubic bound. -/
theorem normalizer_starred_section_strict_of_component_centralizer
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let W := componentOrbit V (T : Subgroup G)
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let K := (L.subgroupOf M).map (internalHom M U hn)
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      A ⊓ centralizer (K : Set (internalActionImage M U hn)) ≠ ⊥ → ¬ A ≤ centralizer (K : Set (internalActionImage M U hn)) →
      restrictedSubgroup ρ (internalSection U W) A ∈
        Qhat (subspaceImageRepresentation ρ (internalSection U W)) ∧
      actionRatio (subspaceImageRepresentation ρ (internalSection U W))
        (restrictedSubgroup ρ (internalSection U W) A) < 2 := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let W := componentOrbit V (T : Subgroup G)
  let hn := le_normalizer_componentOrbit V M
  let ρ := UniqueFactor.imageRepresentation M U hn
  dsimp only
  intro A hAS hA hk hm
  have he := (D.normalizer_sylow_seed_orbit_kernels h hc A hAS).2
  apply starred_restriction_strict_of_kernel ρ hA (internalSection U W)
    (hAS.trans (internalSylow_section_stable T M U W hn
      D.sylow_normalizes_component (le_normalizer_componentOrbit V T))) _ (he.symm ▸ hk)
  intro hf
  apply hm
  intro a ha
  exact (he.le ⟨ha,fun v hv => hf hv ⟨a,ha⟩⟩).2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
