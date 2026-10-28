module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuEscape
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuSourceAt.Ambient

/-!
# Triple-Mathieu escape at the original G,T

This replays the source 14.7.36 argument using only same-G,T earlier
structural and alternative results. The original groups, quotients and
actions are retained; no later 14.7.47 input is assumed.
Source: Aschbacher–Smith, printed p.1059, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuSourceAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter14.Section06.OddCriticalPair.Selection
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}
open Sporadic.Mathieu.M22TripleCover.Ambient
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open Sporadic.Mathieu.M22TripleCover.Escape
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu

theorem reduced_triple_mathieu_solvable_escape_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf I = ⊤) :
    let q := QuotientGroup.mk' (pCore 2 I)
    let X := ((F.Li L 1).subgroupOf I).map q
    let S := ((T : Subgroup G).subgroupOf I).map q
    ∃ hU : IsElementaryAbelian 2 (F.UH I), let := hU
      ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
        Module.finrank (ZMod 2) (fixedSpace a.representation S) = 1 ∧
        ∃ D : Subgroup (HStar I), Group.IsSolvable D ∧ X ⊔ S ≤ D ∧
          ∃ v : Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)),
            v ≠ 0 ∧ v ∈ fixedSpace a.representation S ∧
            ∃ x ∈ D, a.representation x v ∉
              Submodule.span (ZMod 2) (Set.range (fun z : X => a.representation z v)) := by
  obtain ⟨hU,a,j,E,hint,hB,hX,hd,S,hS,hR⟩ := reduced_triple_mathieu_ambient_action_at
    d h hab structural previous faithful earlier I hI C hC e hgen
  let := hU
  let ρ := a.representation
  let X := ((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))
  let S₀ := ((T : Subgroup G).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))
  have hP : S₀.map j.toMonoidHom = (S : Subgroup actionGroup) := hS.symm
  have escape : ∃ D : Subgroup (HStar I), Group.IsSolvable D ∧ X ⊔ S₀ ≤ D ∧
      ∃ v : Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)),
        v ≠ 0 ∧ v ∈ fixedSpace ρ S₀ ∧
        ∃ x ∈ D, ρ x v ∉ Submodule.span (ZMod 2) (Set.range (fun z : X => ρ z v)) := by
    obtain ⟨B,hB,hBS,w,hw,hfix,x,hx,hmove⟩ := exists_solvable_escape S
    let D := B.comap j.toMonoidHom
    let f : D →* B := (j.toMonoidHom.comp D.subtype).codRestrict B (fun y => y.property)
    have hs : Group.IsSolvable D := by
      let := hB
      exact Group.isSolvable_of_isSolvable_injective (f := f)
        (fun a b he => Subtype.ext (j.injective (congrArg Subtype.val he)))
    have hXD : X ≤ D := by
      intro z hz
      apply (le_sup_left.trans hBS)
      rw [←hX]
      exact mem_map_of_mem _ hz
    have hSD : S₀ ≤ D := by
      intro z hz
      apply (le_sup_right.trans hBS)
      rw [←hP]
      exact mem_map_of_mem _ hz
    refine ⟨D,hs,sup_le hXD hSD,E.symm w,?_,?_,j.symm x,?_,?_⟩
    · intro hz
      have hh := congrArg E hz
      rw [E.apply_symm_apply,map_zero] at hh
      exact hw hh
    · intro z
      apply E.injective
      change E (ρ (z : HStar I) (E.symm w)) = E (E.symm w)
      rw [hint,E.apply_symm_apply]
      exact hfix ⟨j z,hP ▸ mem_map_of_mem j.toMonoidHom z.property⟩
    · change j (j.symm x) ∈ B
      rwa [j.apply_symm_apply]
    · intro hm
      have hspan : ∀ y ∈ Submodule.span (ZMod 2) (Set.range (fun z : X => ρ z (E.symm w))),
          E y ∈ scalarSpan w := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨z,rfl⟩ := hy
          change E (ρ (z : HStar I) (E.symm w)) ∈ scalarSpan w
          rw [hint,E.apply_symm_apply]
          exact Submodule.subset_span ⟨⟨j z,hX ▸ mem_map_of_mem j.toMonoidHom z.property⟩,rfl⟩
        | zero => simp
        | add y z hy hz ihy ihz => simpa using (scalarSpan w).add_mem ihy ihz
        | smul a y hy ih => simpa using (scalarSpan w).smul_mem a ih
      have hh := hspan _ hm
      rw [hint,E.apply_symm_apply,j.apply_symm_apply] at hh
      exact hmove hh
  exact ⟨hU,a,hd,escape⟩

theorem reduced_triple_mathieu_trapped_escape_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf I = ⊤) :
    let q := QuotientGroup.mk' (pCore 2 I)
    let X := ((F.Li L 1).subgroupOf I).map q
    let S := ((T : Subgroup G).subgroupOf I).map q
    ∃ hU : IsElementaryAbelian 2 (F.UH I), let := hU
      ∃ a : LocalQuotientAction I (F.UH I) (F.Vi 1),
        Module.finrank (ZMod 2) (fixedSpace a.representation S) = 1 ∧
        ∃ D : Subgroup (HStar I), let B := (D.comap q).map I.subtype
          Group.IsSolvable D ∧ X ⊔ S ≤ D ∧
          B ≤ I ∧ F.Li L 1 ⊔ (T : Subgroup G) ≤ B ∧
          Group.IsSolvable B ∧ B ≤ normalizer (L : Set G) ∧
          (B.subgroupOf I).map q = D ∧
          ∃ v : Additive (F.UH I ⧸ (F.Vi 1).subgroupOf (F.UH I)),
            v ≠ 0 ∧ v ∈ fixedSpace a.representation S ∧
            ∃ x ∈ D, a.representation x v ∉
              Submodule.span (ZMod 2) (Set.range (fun z : X => a.representation z v)) := by
  let q := QuotientGroup.mk' (pCore 2 I)
  obtain ⟨hU,a,hd,D,hD,hDS,v,hv,hfix,x,hx,hmove⟩ := reduced_triple_mathieu_solvable_escape_at
    d h hab structural previous faithful earlier I hI C hC e hgen
  let := hU
  let := hD
  let B := (D.comap q).map I.subtype
  have hBI : B ≤ I := map_subtype_le _
  have hLB : F.Li L 1 ⊔ (T : Subgroup G) ≤ B := by
    apply sup_le
    · intro g hg
      refine ⟨⟨g,F.Li_one_le_of_mem_Hz hI hg⟩,?_,rfl⟩
      exact (le_sup_left.trans hDS) (mem_map_of_mem q hg)
    · intro g hg
      refine ⟨⟨g,F.sylow_le_of_mem_Hz hI hg⟩,?_,rfl⟩
      exact (le_sup_right.trans hDS) (mem_map_of_mem q hg)
  have hsol : Group.IsSolvable B := by
    let := pCore_isNilpotent (p := 2) (G := I)
    let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
    let : Group.IsSolvable (D.comap q) := isSolvable_comap_of_solvable_ker q D
    exact Group.isSolvable_of_surjective (I.subtype.subgroupMap_surjective (D.comap q))
  have hBM : B ≤ normalizer (L : Set G) :=
    WholeResidualAssembly.GuardedSource.solvable_point_overgroup_le_normalizer d h hab structural previous faithful earlier
      B (hBI.trans hI.2.1) hLB hsol
  have him : (B.subgroupOf I).map q = D := by
    change ((D.comap q).map I.subtype |>.comap I.subtype).map q = D
    rw [comap_map_eq_self_of_injective I.subtype_injective,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  exact ⟨hU,a,hd,D,hD,hDS,hBI,hLB,hsol,hBM,him,v,hv,hfix,x,hx,hmove⟩

theorem reduced_triple_mathieu_component_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent)
    (hgen : C ⊔ (T : Subgroup G).subgroupOf I = ⊤) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover) := by
  rintro ⟨e⟩
  let q := QuotientGroup.mk' (pCore 2 I)
  let X := ((F.Li L 1).subgroupOf I).map q
  let S := ((T : Subgroup G).subgroupOf I).map q
  obtain ⟨hU,a,hd,D,hD,hDS,hBI,hLB,hsol,hBM,him,v,hv,hfix,x,hx,hmove⟩ :=
    reduced_triple_mathieu_trapped_escape_at d h hab structural previous faithful earlier I hI C hC e hgen
  let := hU
  let : IsElementaryAbelian 2 (Chapter13.Section08.Source.UH I V) := hU
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let B := (D.comap q).map I.subtype
  let act : SourceAction I V (F.Vi 1) := {
    representation := a.representation
    conjugation := a.conjugation }
  let Q := seedSpace I V (F.Vi 1)
  have hQ : Module.finrank (ZMod 2) Q = 2 := by
    apply source_seed_finrank
    have hc := ((F.Vi 1).subgroupOf V).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 1)).toEquiv] at hc
    have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    have hV : Nat.card V = 8 := by simpa only [F.last,Nat.reducePow] using F.card 3 (by decide)
    rw [hp,hV] at hc
    omega
  have hstable (P : Subgroup G) (hP : P ≤ normalizer (V : Set G)) :
      ∀ z : (P.subgroupOf I).map q, ∀ w ∈ Q, a.representation z w ∈ Q := by
    intro z w hw
    obtain ⟨p,hp,he⟩ := z.property
    have hh := source_seed_stable act P hP ⟨p,hp⟩ w hw
    change a.representation (q p) w ∈ Q at hh
    rwa [he] at hh
  have hS : IsPGroup 2 S := T.isPGroup'.comap_subtype.map q
  have hST : ∀ z : S, ∀ w ∈ Q, a.representation z w ∈ Q :=
    hstable T (by simpa only [F.last] using F.invariant 3)
  have hXT : ∀ z : X, ∀ w ∈ Q, a.representation z w ∈ Q :=
    hstable (F.Li L 1) ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
  obtain ⟨_,_,_,_,hpn,_⟩ := reduced_triple_mathieu_star_structure_at
    d h hab structural previous faithful earlier I hI C hC e hgen
  have hfree : fixedSpace a.representation X = ⊥ :=
    WholeResidualAssembly.GuardedSource.local_point_fixedSpace_eq_bot h structural I (F.Li_one_le_of_mem_Hz hI) hpn a
  have hplane := orbit_span_eq_binary_plane_of_fixed_line a.representation S X hS Q hQ hST hXT hd hfree v hv hfix
  have hvQ : v ∈ Q := by
    have hvspan : v ∈ Submodule.span (ZMod 2)
        (Set.range (fun z : X => a.representation z v)) :=
      Submodule.subset_span ⟨1,by simp⟩
    exact hplane ▸ hvspan
  have hpne : F.Vi 1 ≠ ⊥ := by
    intro he
    have hc := F.card 1 (by decide)
    rw [he,card_bot] at hc
    norm_num at hc
  have hBN : B ≤ normalizer (V : Set G) := by
    apply le_trans (le_inf hBM (hBI.trans hI.2.1))
    exact inf_normalizer_le_of_trivial_intersections (((structural L h.source).2.2 V h.chosen).2.2.1) hpne (F.le_seed 1)
  have hDstable : ∀ z : D, ∀ w ∈ Q, a.representation z w ∈ Q := by
    intro z w hw
    have hz : (z : HStar I) ∈ (B.subgroupOf I).map q := by
      rw [him]
      exact z.property
    exact hstable B hBN ⟨z,hz⟩ w hw
  apply hmove
  rw [hplane]
  exact hDstable ⟨x,hx⟩ v hvQ

theorem local_triple_mathieu_component_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I C : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hCI : C ≤ I) (hC : (C.subgroupOf I).IsCComponent) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover) := by
  rintro ⟨e⟩
  let J := C ⊔ (T : Subgroup G)
  obtain ⟨_,hJ,hCJ,_,_,_,_,_,_,_,_⟩ :=
    local_triple_mathieu_reduced_residual_at d h hab structural previous faithful earlier I C hI hCI hC e
  let b := subgroupOfEquivOfLe (show C ≤ J from le_sup_left)
  let eJ := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans e
  have hg : C.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup (show C ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  exact reduced_triple_mathieu_component_impossible_at
    d h hab structural previous faithful earlier J hJ (C.subgroupOf J) hCJ hg ⟨eJ⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuSourceAt
