module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.TripleMathieuAmbient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.MathieuExclusion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.CoverModels
public import Theory.Representation.Mathieu.M22James.SolvableOvergroup
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.Representation.BinaryFixedLineOrbit

/-!
# The triple-Mathieu contradiction in 14.7.36

The certified native solvable overgroup contains the point cubic and the
whole Sylow image, but moves a vector outside its scalar orbit plane.
The marked group and linear equivalences transport this witness to the
literal local section. Pulling the overgroup back through the actual
two-core map preserves solvability and contains the entire original L₁T.
The proved 14.7.29 therefore places the lift in M.

The original binary seed plane is stable under the Sylow and point actions.
The unique Sylow fixed line lies in this plane, and the fixed-free cubic
generates the plane from any nonzero vector on that line. Meanwhile the
lift lies in M and normalizes V₁; the source TI property makes it normalize
V. Its action on the literal seed section cannot perform the certified
escape. This proves the reduced contradiction and, through the original
CT reduction, excludes the triple cover in every original local.

The component-selection application removes both Mathieu alternatives from
F.9.18 using the proved identification of the intrinsic triple cover. All
remaining quotient models and the alternating-cover exclusion are retained.
The genuine earlier structural, faithful and 14.7.10 inputs remain explicit.

Source: Aschbacher–Smith, 14.7.36, printed p.1059, using 14.7.29,
14.3.3(6) and H.12.1; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Sporadic.Mathieu.M22TripleCover.Ambient
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open Sporadic.Mathieu.M22TripleCover.Escape
open Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Mathieu
universe u
private theorem marked_solvable_escape
    {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (j : A ≃* actionGroup)
    (E : W ≃ₗ[ZMod 2] Sporadic.Mathieu.M22TripleCover.BinarySpace)
    (hint : ∀ g v, E (ρ g v) = binaryAction (j g) (E v))
    (X S : Subgroup A) (hX : X.map j.toMonoidHom = scalarSubgroup)
    (P : Sylow 2 actionGroup) (hP : S.map j.toMonoidHom = (P : Subgroup actionGroup)) :
    ∃ D : Subgroup A, Group.IsSolvable D ∧ X ⊔ S ≤ D ∧
      ∃ v : W, v ≠ 0 ∧ v ∈ fixedSpace ρ S ∧
        ∃ x ∈ D, ρ x v ∉ Submodule.span (ZMod 2) (Set.range (fun z : X => ρ z v)) := by
  obtain ⟨B,hB,hBS,w,hw,hfix,x,hx,hmove⟩ := exists_solvable_escape P
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
  have hSD : S ≤ D := by
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
    change E (ρ (z : A) (E.symm w)) = E (E.symm w)
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
        change E (ρ (z : A) (E.symm w)) ∈ scalarSpan w
        rw [hint,E.apply_symm_apply]
        exact Submodule.subset_span ⟨⟨j z,hX ▸ mem_map_of_mem j.toMonoidHom z.property⟩,rfl⟩
      | zero => simp
      | add y z hy hz ihy ihz => simpa using (scalarSpan w).add_mem ihy ihz
      | smul a y hy ih => simpa using (scalarSpan w).smul_mem a ih
    have hh := hspan _ hm
    rw [hint,E.apply_symm_apply,j.apply_symm_apply] at hh
    exact hmove hh

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original reduced triple-cover local has a genuine solvable star
 overgroup of its point cubic and entire Sylow image which moves the cubic
 orbit plane on the original Sylow fixed line. -/
theorem reduced_triple_mathieu_solvable_escape
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  obtain ⟨hU,a,j,E,hint,hB,hX,hd,S,hS,hR⟩ := reduced_triple_mathieu_ambient_action
    d h hab structural previous faithful earlier I hI C hC e hgen
  let := hU
  exact ⟨hU,a,hd,marked_solvable_escape a.representation j E hint _ _ hX S hS.symm⟩

/-- Lift the escaping native overgroup through the literal two-core map.
It contains the whole original point group and is solvable, so 14.7.29
places it in M. The plane comparison below identifies its moved cubic
plane with the original seed section and gives the contradiction. -/
theorem reduced_triple_mathieu_trapped_escape
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
  obtain ⟨hU,a,hd,D,hD,hDS,v,hv,hfix,x,hx,hmove⟩ := reduced_triple_mathieu_solvable_escape
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
    solvable_point_overgroup_le_normalizer d h hab structural previous faithful earlier
      B (hBI.trans hI.2.1) hLB hsol
  have him : (B.subgroupOf I).map q = D := by
    change ((D.comap q).map I.subtype |>.comap I.subtype).map q = D
    rw [comap_map_eq_self_of_injective I.subtype_injective,
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  exact ⟨hU,a,hd,D,hD,hDS,hBI,hLB,hsol,hBM,him,v,hv,hfix,x,hx,hmove⟩

/-- The constructed reduction of the original component carries the same
solvable lifted overgroup and escaping Sylow-fixed scalar plane. -/
theorem original_triple_mathieu_trapped_escape
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) (hC : C.IsCComponent)
    (e : (C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover) :
    let D := C.map F.H.subtype
    let J := D ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 J)
    let X := ((F.Li L 1).subgroupOf J).map q
    let S := ((T : Subgroup G).subgroupOf J).map q
    J ≤ F.H ∧ J ∈ F.Hz L (normalizer (L : Set G)) ∧
    ∃ hU : IsElementaryAbelian 2 (F.UH J), let := hU
      ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
        Module.finrank (ZMod 2) (fixedSpace a.representation S) = 1 ∧
        ∃ D : Subgroup (HStar J), let B := (D.comap q).map J.subtype
          Group.IsSolvable D ∧ X ⊔ S ≤ D ∧
          B ≤ J ∧ F.Li L 1 ⊔ (T : Subgroup G) ≤ B ∧
          Group.IsSolvable B ∧ B ≤ normalizer (L : Set G) ∧
          (B.subgroupOf J).map q = D ∧
          ∃ v : Additive (F.UH J ⧸ (F.Vi 1).subgroupOf (F.UH J)),
            v ≠ 0 ∧ v ∈ fixedSpace a.representation S ∧
            ∃ x ∈ D, a.representation x v ∉
              Submodule.span (ZMod 2) (Set.range (fun z : X => a.representation z v)) := by
  let D := C.map F.H.subtype
  let J := D ⊔ (T : Subgroup G)
  obtain ⟨hJH,hJ,hDJ,_,_,_,_,_,_,_,_⟩ :=
    original_triple_mathieu_reduced_residual d h hab structural previous faithful earlier C hC e
  let b := equivMapOfInjective C F.H.subtype F.H.subtype_injective
  let eD := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans e
  let c := subgroupOfEquivOfLe (show D ≤ J from le_sup_left)
  let eJ := (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans eD
  have hg : D.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup (show D ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  exact ⟨hJH,hJ,reduced_triple_mathieu_trapped_escape
    d h hab structural previous faithful earlier J hJ (D.subgroupOf J) hDJ eJ hg⟩


/-- Source 14.7.36 excludes the triple Mathieu cover in the reduced original
local: its native solvable overgroup escapes the literal seed plane, whereas
14.7.29 and the seed TI property force it to preserve that same plane. -/
theorem reduced_triple_mathieu_component_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
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
    reduced_triple_mathieu_trapped_escape d h hab structural previous faithful earlier I hI C hC e hgen
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
  obtain ⟨_,_,_,_,hpn,_⟩ := reduced_triple_mathieu_star_structure
    d h hab structural previous faithful earlier I hI C hC e hgen
  have hfree : fixedSpace a.representation X = ⊥ :=
    local_point_fixedSpace_eq_bot h structural I (F.Li_one_le_of_mem_Hz hI) hpn a
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
    exact inf_normalizer_le_of_trivial_intersections (h.seed_TI structural) hpne (F.le_seed 1)
  have hDstable : ∀ z : D, ∀ w ∈ Q, a.representation z w ∈ Q := by
    intro z w hw
    have hz : (z : HStar I) ∈ (B.subgroupOf I).map q := by
      rw [him]
      exact z.property
    exact hstable B hBN ⟨z,hz⟩ w hw
  apply hmove
  rw [hplane]
  exact hDstable ⟨x,hx⟩ v hvQ

/-- The triple Mathieu cover is excluded in every original local, after
reducing that same component to its join with the original Sylow subgroup. -/
theorem local_triple_mathieu_component_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I C : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hCI : C ≤ I) (hC : (C.subgroupOf I).IsCComponent) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover) := by
  rintro ⟨e⟩
  let J := C ⊔ (T : Subgroup G)
  obtain ⟨_,hJ,hCJ,_,_,_,_,_,_,_,_⟩ :=
    local_triple_mathieu_reduced_residual d h hab structural previous faithful earlier I C hI hCI hC e
  let b := subgroupOfEquivOfLe (show C ≤ J from le_sup_left)
  let eJ := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans e
  have hg : C.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup (show C ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  exact reduced_triple_mathieu_component_impossible
    d h hab structural previous faithful earlier J hJ (C.subgroupOf J) hCJ hg ⟨eJ⟩

/-- The reduced-local contradiction applies to every actual triple Mathieu
C-component of the original point normalizer, with the original markings. -/
theorem original_triple_mathieu_component_impossible
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (C : Subgroup F.H) (hC : C.IsCComponent) :
    ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover) := by
  rintro ⟨e⟩
  let D := C.map F.H.subtype
  have hD : (D.subgroupOf F.H).IsCComponent := by
    simpa only [D,subgroupOf,comap_map_eq_self_of_injective F.H.subtype_injective] using hC
  let b := equivMapOfInjective C F.H.subtype F.H.subtype_injective
  let eD := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).symm.trans e
  exact local_triple_mathieu_component_impossible d h hab structural previous faithful earlier
    F.H D (F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)) (map_subtype_le _) hD ⟨eD⟩

/-- The original escaping component retains the full F.9.18 catalogue,
with both ordinary and triple Mathieu alternatives excluded. -/
theorem original_exists_non_mathieu_cover_component_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u}) :
    ∃ C : Subgroup G, C ≤ F.H ∧ (C.subgroupOf F.H).IsCComponent ∧
      (C.subgroupOf F.H).Normal ∧ ¬ C ≤ normalizer (L : Set G) ∧
      (T : Subgroup G) ≤ normalizer (C : Set G) ∧
      C ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∈ F.Hz L (normalizer (L : Set G)) ∧
      Chapter13.Section08.Components.Models.F918Models (C ⧸ pCore 2 C) ∧
      SylowOvergroupComponentUnique C ∧ ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22) ∧
      ¬ Nonempty ((C ⧸ pCore 2 C) ≃* Sporadic.Mathieu.M22TripleCover) := by
  obtain ⟨C,hCH,hC,hn,he,hT,hJ,hm,hu,hM⟩ := original_exists_non_mathieu_component_reduction
    d h hab structural previous faithful earlier (F := F)
  refine ⟨C,hCH,hC,hn,he,hT,hJ,hm,hu,hM,?_⟩
  rintro ⟨e⟩
  let b := subgroupOfEquivOfLe hCH
  let eC := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans e
  exact original_triple_mathieu_component_impossible d h hab structural previous faithful earlier
    (C.subgroupOf F.H) hC ⟨eC⟩

/-- Removing both Mathieu branches from F.9.18 leaves its literal central
quotient models for the original escaping component. The two-core quotient
and its center are retained, as is the exclusion of the alternating cover. -/
theorem original_exists_quotient_component_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u}) :
    ∃ C : Subgroup G, C ≤ F.H ∧ (C.subgroupOf F.H).IsCComponent ∧
      (C.subgroupOf F.H).Normal ∧ ¬ C ≤ normalizer (L : Set G) ∧
      (T : Subgroup G) ≤ normalizer (C : Set G) ∧
      C ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∈ F.Hz L (normalizer (L : Set G)) ∧
      Chapter13.Section08.Components.Models.F918QuotientModel
        ((C ⧸ pCore 2 C) ⧸ center (C ⧸ pCore 2 C)) ∧
      ¬ Chapter1.Section02.LocalModels.IsAlternatingCover (C ⧸ pCore 2 C) 7 ∧
      SylowOvergroupComponentUnique C := by
  obtain ⟨C,hCH,hC,hn,he,hT,hJ,hm,hu,hM,hMt⟩ :=
    original_exists_non_mathieu_cover_component_reduction
      d h hab structural previous faithful earlier (F := F)
  rcases hm with ⟨hquot,hA⟩ | hM' | hMt'
  · exact ⟨C,hCH,hC,hn,he,hT,hJ,hquot,hA,hu⟩
  · exact (hM hM').elim
  · exact (hMt (Chapter13.Section08.Components.CoverModels.m22Triple_nonempty_mulEquiv_of_source hMt')).elim

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
