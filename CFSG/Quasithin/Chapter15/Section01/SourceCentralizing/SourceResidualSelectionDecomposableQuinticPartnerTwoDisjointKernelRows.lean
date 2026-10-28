module

import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoKernelRows
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticPartnerTwoDisjointStrong

/-!
# Canonical commutator rows for the disjoint-support branch

The actual disjoint marked denominator supplies nonsolvability without a
three-dimensional seed assumption. The canonical perfect lift therefore
supplies the same literal rows for both kernel intersections. The private
coordinate descent from KernelRows is intentionally reused without editing
that frozen owner.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u v
variable {G : Type u} [Group G] [Finite G]

/-- Literal perfect-lift kernel rows on the entire actual disjoint-support
branch, including both possible dimensions of the marked seed image. -/
theorem PreparedChosenModule.decomposable_five_partner_two_disjoint_kernel_rows
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          D ⊓ thompsonPlane T V (c.ambientFactor d s.first).space = ⊥ →
          let N := normalClosure (V.subgroupOf Mc : Set Mc)
          let L := ((solvableResidual N).map N.subtype).map Mc.subtype
          let K := commutatorPreimage Mc F D
          let B := K ⊓ L
          let hLMc : L ≤ Mc := map_subtype_le ((solvableResidual N).map N.subtype)
          let ψ := ρ.comp (Subgroup.inclusion hLMc)
          Group.IsPerfect L ∧ L ≤ normalizer (B : Set G) ∧
            L ≤ centralizer (D : Set G) ∧ ⁅F,L⁆ = F ∧ ⁅B,F⁆ ≤ D ∧
            ∃ heD : IsElementaryAbelian 2 D,
              letI := heD
              ∃ row : B →* (Multiplicative W →* D),
                (∀ (b : B) (f : F), (row b (dF.coordinates f) : G) = ⁅(b : G),(f : G)⁆) ∧
                row.ker = (centralizer (F : Set G)).subgroupOf B ∧
                (∀ (l : L) (b b' : B), (b' : G) = (l : G) * (b : G) * (l : G)⁻¹ →
                  ∀ w : W, row b' (Multiplicative.ofAdd w) =
                    row b (Multiplicative.ofAdd (ψ l⁻¹ w))) ∧
                (⨆ b : B, (row b).range).map D.subtype = ⁅B,F⁆ := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF hDZ
  let N := normalClosure (V.subgroupOf Mc : Set Mc)
  let L := ((solvableResidual N).map N.subtype).map Mc.subtype
  let K := commutatorPreimage Mc F D
  let B := K ⊓ L
  have hLMc : L ≤ Mc := map_subtype_le ((solvableResidual N).map N.subtype)
  have hnsolv := (((h.decomposable_five_partner_two_disjoint_strong
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
      ρ dF hDZ).2.2
  obtain ⟨hperfect,_,_,hLD,hFL,_,_⟩ :=
    (h.decomposable_five_canonical_perfect_lift
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hVQ ρ dF).resolve_left hnsolv
  obtain ⟨_,_,_,hnD,_⟩ := (h.decomposable_five_partner_two_core_or_canonical_action
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  have hMcK : Mc ≤ normalizer (K : Set G) :=
    commutatorPreimage_normalized Mc F D Mc hnD Mc.le_normalizer dF.normalized hnD
  have hnB : L ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro l hl b hb
    exact ⟨le_normalizer_iff.mp hMcK l (hLMc hl) b hb.1,
      L.mul_mem (L.mul_mem hl hb.2) (L.inv_mem hl)⟩
  have hBF : ⁅B,F⁆ ≤ D := (commutator_mono (show B ≤ K from inf_le_left) le_rfl).trans
    (commutator_commutatorPreimage_le Mc F D hnD)
  let heF : IsElementaryAbelian 2 F := (h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2.2.1
  let := heF
  let heD : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le dF.kernel_le
  let := heD
  exact ⟨hperfect,hnB,hLD,hFL,hBF,heD,
    exists_central_section_rows Mc F D L B ρ dF hLMc (inf_le_right.trans hLD) hLD hBF⟩

/-- The same literal rows for the section kernel inside the normal closure
of the original module. This retains the original actors before passing
to the canonical perfect lift. -/
theorem PreparedChosenModule.decomposable_five_partner_two_disjoint_normal_kernel_rows
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      Nat.card (localModule T Mc) = 2 →
      let E := thompsonFixed T V
      let C := centralizer (localModule T Mc : Set G)
      let F := conjugateSpanBy E C
      let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
      V ≤ Mc.pCoreIn 2 ∨
        ∀ {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
          (ρ : Representation (ZMod 2) Mc W) (dF : BinaryConjugationSection Mc F D ρ),
          D ⊓ thompsonPlane T V (c.ambientFactor d s.first).space = ⊥ →
          let N := normalClosure (V.subgroupOf Mc : Set Mc)
          let L := ((solvableResidual N).map N.subtype).map Mc.subtype
          let K := commutatorPreimage Mc F D
          let B := K ⊓ N.map Mc.subtype
          let hLMc : L ≤ Mc := map_subtype_le ((solvableResidual N).map N.subtype)
          let ψ := ρ.comp (Subgroup.inclusion hLMc)
          Group.IsPerfect L ∧ L ≤ normalizer (B : Set G) ∧
            L ≤ centralizer (D : Set G) ∧ L ≤ N.map Mc.subtype ∧
            N.map Mc.subtype ≤ centralizer (D : Set G) ∧ ⁅F,L⁆ = F ∧ ⁅B,F⁆ ≤ D ∧
            ∃ heD : IsElementaryAbelian 2 D,
              letI := heD
              ∃ row : B →* (Multiplicative W →* D),
                (∀ (b : B) (f : F), (row b (dF.coordinates f) : G) = ⁅(b : G),(f : G)⁆) ∧
                row.ker = (centralizer (F : Set G)).subgroupOf B ∧
                (∀ (l : L) (b b' : B), (b' : G) = (l : G) * (b : G) * (l : G)⁻¹ →
                  ∀ w : W, row b' (Multiplicative.ofAdd w) =
                    row b (Multiplicative.ofAdd (ψ l⁻¹ w))) ∧
                (⨆ b : B, (row b).range).map D.subtype = ⁅B,F⁆ := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive hcU
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let F := conjugateSpanBy E C
  let D := (((F ⊓ centralizer (V : Set G)).subgroupOf Mc).normalCore).map Mc.subtype
  by_cases hVQ : V ≤ Mc.pCoreIn 2
  · exact Or.inl hVQ
  right
  intro W _ _ ρ dF hDZ
  let N := normalClosure (V.subgroupOf Mc : Set Mc)
  let L := ((solvableResidual N).map N.subtype).map Mc.subtype
  let K := commutatorPreimage Mc F D
  let B := K ⊓ N.map Mc.subtype
  have hLMc : L ≤ Mc := map_subtype_le ((solvableResidual N).map N.subtype)
  have hnsolv := (((h.decomposable_five_partner_two_disjoint_strong
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ)
      ρ dF hDZ).2.2
  obtain ⟨hperfect,_,_,hLD,hFL,_,_⟩ :=
    (h.decomposable_five_canonical_perfect_lift
      hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hVQ ρ dF).resolve_left hnsolv
  obtain ⟨_,_,hDC,hnD,_⟩ := (h.decomposable_five_partner_two_core_or_canonical_action
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive hcU).resolve_left hVQ
  have hUE := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2
  have hVMc : V ≤ Mc := (V.le_centralizer.trans
    (centralizer_le (hUE.trans inf_le_left))).trans (localModule_centralizer_le_partner T Mc hu)
  have hNmap : N.map Mc.subtype = conjugateSpanBy V Mc := by
    rw [map_normalClosure_eq_conjugateSpanBy_range,
      map_subgroupOf_eq_of_le hVMc,range_subtype]
  have hND : N.map Mc.subtype ≤ centralizer (D : Set G) := by
    rw [hNmap]
    exact conjugateSpanBy_le (le_centralizer_iff.mp hDC)
      (hnD.trans (normalizer_le_normalizer_centralizer D))
  have hLN : L ≤ N.map Mc.subtype := map_mono (map_subtype_le (solvableResidual N))
  have hMcK : Mc ≤ normalizer (K : Set G) :=
    commutatorPreimage_normalized Mc F D Mc hnD Mc.le_normalizer dF.normalized hnD
  have hMcN : Mc ≤ normalizer (N.map Mc.subtype : Set G) := by
    apply le_normalizer_iff.mpr
    rintro m hm _ ⟨n,hn,rfl⟩
    exact mem_map_of_mem Mc.subtype ((inferInstance : N.Normal).conj_mem n hn ⟨m,hm⟩)
  have hnB : L ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro l hl b hb
    exact ⟨le_normalizer_iff.mp hMcK l (hLMc hl) b hb.1,
      le_normalizer_iff.mp hMcN l (hLMc hl) b hb.2⟩
  have hBF : ⁅B,F⁆ ≤ D := (commutator_mono (show B ≤ K from inf_le_left) le_rfl).trans
    (commutator_commutatorPreimage_le Mc F D hnD)
  let heF : IsElementaryAbelian 2 F := (h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive).2.2.2.1
  let := heF
  let heD : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le dF.kernel_le
  let := heD
  exact ⟨hperfect,hnB,hLD,hLN,hND,hFL,hBF,heD,
    exists_central_section_rows Mc F D L B ρ dF hLMc (inf_le_right.trans hND) hLD hBF⟩

end CFSG.Quasithin.Chapter15.Section01
