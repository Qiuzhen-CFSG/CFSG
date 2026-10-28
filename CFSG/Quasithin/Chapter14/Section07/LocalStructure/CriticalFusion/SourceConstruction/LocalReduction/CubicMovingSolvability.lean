module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicQuotientReduction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicSolvability

/-!
# Solvability of cubic completions that move the flag plane

For the original cubic actor Y, suppose Y moves V₂ and escapes N_G(L).
The residual obstruction from `CubicMovingPlane` excludes a normal A₅
component of the faithful action quotient. A PSL₃(2) component would be the
whole quotient and give natural coordinates on E = ⟨V₁ᴰ⟩, where
D = ⟨L₂,Y,T⟩. Its full two-core is exactly C_D(E).

The natural seed E and the original V have the same abelian point span U.
Intersecting conjugates of the mixed seed family therefore commute. The
coset-geometry argument puts their normal span in O₂(LT), and uniqueness
of the maximal two-local over LT contradicts the escape of Y. Hence D is
solvable. Plane movement replaces point-residual normalization throughout;
no normalization of L₁ by Y is assumed.

The final theorem applies this to the literal proper invariant quotient
of U/V₁, deriving escape by seed separation. It discharges the nonsolvable
branch of `original_quotient_plane_lifting_reduction`. The solvable
countercase of 14.7.2(3) remains, as do the subsequent residual alternatives.
The independent earlier structural and faithful-classification inputs are
retained explicitly with their original statements.

Source: Aschbacher–Smith, 14.5.5–8, printed pp.1013–1015, and 14.7.2(3),
printed p.1043, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
universe u
private theorem alternating_normal_sylow_intersection
    {D : Type*} [Group D] [Finite D]
    (S : Sylow 2 D) (J A : Subgroup D) [J.Normal] [Group.IsSolvable A]
    (e : J ≃* alternatingGroup (Fin 5)) (hSA : (S : Subgroup D) ≤ A) :
    A ≤ normalizer (((S : Subgroup D) ⊓ J : Subgroup D) : Set D) := by
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal J
  let B := A.subgroupOf J
  have hRB : (R : Subgroup J) ≤ B := by rw [hR]; exact comap_mono hSA
  have hBA : B.map J.subtype ≤ A := (subgroupOf_map_subtype A J).le.trans inf_le_left
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := (inclusion hBA).comp
      (B.equivMapOfInjective J.subtype J.subtype_injective).toMonoidHom)
    ((inclusion_injective hBA).comp (B.equivMapOfInjective J.subtype J.subtype_injective).injective)
  have hBN := alternatingGroup.solvable_sylow_overgroup_le_normalizer_of_equiv e R B hRB
  have hcore : B.pCoreIn 2 = (R : Subgroup J) := by
    apply le_antisymm
    · have hh := pCoreIn_le_sylow B (R.subtype hRB)
      simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hRB] using hh
    · exact le_pCoreIn_of_normalizes R.isPGroup' hRB hBN
  have he : (A ⊓ J).pCoreIn 2 = (S : Subgroup D) ⊓ J := by
    have hh := congrArg (map J.subtype) hcore
    rw [map_pCoreIn_of_injective 2 _ _ J.subtype_injective,
      subgroupOf_map_subtype,hR,subgroupOf_map_subtype] at hh
    exact hh
  rw [←he]
  exact ((le_inf A.le_normalizer le_normalizer_of_normal).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (A ⊓ J) (pCore 2 (A ⊓ J : Subgroup D)))

private theorem goldschmidt_no_alternating_normal
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : CFSG.Quasithin.ChapterF.IsGoldschmidtTriple A B)
    (hcore : pCore 2 D = ⊥) (J : Subgroup D) [J.Normal]
    (e : J ≃* alternatingGroup (Fin 5)) : False := by
  let : Group.IsSolvable A := SymmetricThreeTwoCore.solvable ht.quotient_left.some
  let : Group.IsSolvable B := SymmetricThreeTwoCore.solvable ht.quotient_right.some
  obtain ⟨S,hS⟩ := ht.intersection_sylow
  have hSA : (S : Subgroup D) ≤ A := hS.symm.le.trans inf_le_left
  have hSB : (S : Subgroup D) ≤ B := hS.symm.le.trans inf_le_right
  have hA := alternating_normal_sylow_intersection S J A e hSA
  have hB := alternating_normal_sylow_intersection S J B e hSB
  have hbot : (S : Subgroup D) ⊓ J = ⊥ :=
    ht.common_normal_eq_bot hcore _ (inf_le_left.trans hS.ge)
      (normal_subgroupOf_of_le_normalizer hA) (normal_subgroupOf_of_le_normalizer hB)
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal J
  have hRbot : (R : Subgroup J) = ⊥ := by
    apply map_injective J.subtype_injective
    rw [hR,subgroupOf_map_subtype,hbot,Subgroup.map_bot]
  have hc := Theory.PSL2.SylowFixedQuotients.alternating_sylow_card
    (R.mapSurjective (f := e.toMonoidHom) e.surjective)
  change Nat.card ((R : Subgroup J).map e.toMonoidHom) = 4 at hc
  simp [hRbot] at hc

private theorem goldschmidt_linear_marking
    {D : Type*} [Group D] [Finite D] {A B : Subgroup D}
    (ht : ChapterF.IsGoldschmidtTriple A B) (e : D ≃* Matrix.PSL3Two.PSL) :
    ∃ f : D ≃* Matrix.PSL3Two.SL,
      A.map f.toMonoidHom = Matrix.PSL3Two.lineParabolicSL ∧
      B.map f.toMonoidHom = Matrix.PSL3Two.pointParabolicSL := by
  let : Group.IsSolvable A := SymmetricThreeTwoCore.solvable ht.quotient_left.some
  let : Group.IsSolvable B := SymmetricThreeTwoCore.solvable ht.quotient_right.some
  have hns : ¬ Group.IsSolvable D := by
    intro hs
    let := hs
    exact not_isSolvable_psl3_two
      (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)
  have hproper (P : Subgroup D) [Group.IsSolvable P] : P ≠ ⊤ := by
    intro he
    have hp : Function.Surjective P.subtype := by
      intro x
      exact ⟨⟨x,he ▸ mem_top x⟩,rfl⟩
    exact hns (Group.isSolvable_of_surjective (f := P.subtype) hp)
  obtain ⟨S,hS⟩ := ht.intersection_sylow
  have hSA : (S : Subgroup D) ≤ A := hS.symm.le.trans inf_le_left
  have hSB : (S : Subgroup D) ≤ B := hS.symm.le.trans inf_le_right
  have hnot (P : Subgroup D) (hSP : (S : Subgroup D) ≤ P)
      (he : Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))) : ¬ IsPGroup 2 P := by
    intro hp
    have hPS := S.is_maximal' hp hSP
    have hi := SymmetricThreeTwoCore.sylow_index_three he.some (S.subtype hSP)
    change (S : Subgroup D).relIndex P = 3 at hi
    rw [hPS,relIndex_self] at hi
    omega
  obtain ⟨f,hSf,hAf⟩ := Matrix.PSL3Two.exists_sylow_line_marking e S A hSA
    (hproper A) (hnot A hSA ht.quotient_left)
  have hBf : B.map f.toMonoidHom = Matrix.PSL3Two.pointParabolicSL := by
    have hBP : B.map f.toMonoidHom ≠ ⊤ := by
      intro hz
      apply hproper B
      exact f.mapSubgroup.injective (hz.trans f.mapSubgroup.map_top.symm)
    have hBtwo : ¬ IsPGroup 2 (B.map f.toMonoidHom) := fun hh =>
      hnot B hSB ht.quotient_right (hh.of_equiv (f.subgroupMap B).symm)
    rcases Matrix.PSL3Two.parabolic_of_borel_le_of_not_two _
      (hSf ▸ map_mono hSB) hBP hBtwo with hh | hh
    · exact hh
    · have heq : A = B := f.mapSubgroup.injective (hAf.trans hh.symm)
      have hAtop : A = ⊤ := by simpa only [←heq,sup_idem] using ht.generated
      exact (hproper A hAtop).elim
  exact ⟨f,hAf,hBf⟩

open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The moving-plane action quotient cannot have an A₅ component. -/
theorem cubic_generated_component_not_alternating_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    ¬ Nonempty ((J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 5)) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨_,⟨e⟩⟩ := cubic_generated_component_action_kernel_of_moving_plane h hab structural previous faithful Y hYH hm hYp hYT he J hJ
  obtain ⟨_,_,hnq,_⟩ := cubic_generated_component_action_reduction_of_moving_plane h hab structural previous faithful Y hYH hm hYp hYT he J hJ
  let : (J.map q).Normal := hnq
  obtain ⟨_,ht,hcore⟩ := cubic_generated_action_triple_of_moving_plane h hab structural previous Y hYH hm hYp hYT he
  rintro ⟨a⟩
  exact goldschmidt_no_alternating_normal ht hcore (J.map q) (e.symm.trans a)

/-- The surviving component has its actual PSL₃(2) two-core quotient. -/
theorem cubic_generated_component_linear_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    Nonempty ((J ⧸ pCore 2 J) ≃* Matrix.PSL3Two.PSL) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  obtain ⟨hJL,hJf⟩ := cubic_generated_component_faithful_of_moving_plane h hab structural previous Y hYH hm hYp hYT he J hJ
  let eJ := J.equivMapOfInjective D.subtype D.subtype_injective
  let eQ := QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ)
  rcases (faithful (J.map D.subtype) hJL hJf).1 with a | a
  · exact (cubic_generated_component_not_alternating_of_moving_plane h hab structural previous faithful Y hYH hm hYp hYT he J hJ ⟨eQ.trans a.some⟩).elim
  · exact ⟨eQ.trans a.some⟩

/-- The entire faithful action quotient is PSL₃(2), with the original kernel. -/
theorem cubic_generated_component_action_quotient_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    Nonempty ((D ⧸ C) ≃* Matrix.PSL3Two.PSL) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨a⟩ := cubic_generated_component_linear_of_moving_plane
    h hab structural previous faithful Y hYH hm hYp hYT he J hJ
  obtain ⟨_,⟨e⟩⟩ := cubic_generated_component_action_kernel_of_moving_plane
    h hab structural previous faithful Y hYH hm hYp hYT he J hJ
  obtain ⟨_,hj,hnj,hcases⟩ := cubic_generated_component_action_reduction_of_moving_plane
    h hab structural previous faithful Y hYH hm hYp hYT he J hJ
  let : (J.map q).Normal := hnj
  let : IsQuasisimple (J.map q) := hj.2
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup (J.map q) := (e.symm.trans a).isSimpleGroup
  obtain ⟨_,ht,hcore⟩ := cubic_generated_action_triple_of_moving_plane
    h hab structural previous Y hYH hm hYp hYT he
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  have ha : (pResidual 2 (((F.P L).subgroupOf D).map q)).map
      (((F.P L).subgroupOf D).map q).subtype = ((F.Li L 2).subgroupOf D).map q := by
    rw [←map_embedded_pResidual,hr.1]
  have hb : (pResidual 2 (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q)).map
      (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q).subtype = (Y.subgroupOf D).map q := by
    rw [←map_embedded_pResidual,hr.2]
  have hout := cubic_generated_action_normalizer_obstruction_of_moving_plane
    h structural Y hYH hm hYp
  have hjtop := goldschmidt_linear_completion ht hcore (J.map q) (e.symm.trans a)
    (by rwa [ha,hb]) (by rwa [ha,hb])
  exact ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr hjtop.symm).trans (e.symm.trans a))⟩

/-- Natural coordinates identify both literal cubic vertices and their action. -/
theorem cubic_generated_component_natural_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    letI : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
      (le_normalizer_conjugateSpanBy _ _)
    let C := centralizer (W.subgroupOf D : Set D)
    let q := QuotientGroup.mk' C
    ∃ (e : (D ⧸ C) ≃* Matrix.PSL3Two.SL)
      (f : W ≃* Multiplicative BinaryLinearThree.Vector),
      (((F.P L).subgroupOf D).map q).map e.toMonoidHom = Matrix.PSL3Two.lineParabolicSL ∧
      (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q).map e.toMonoidHom =
        Matrix.PSL3Two.pointParabolicSL ∧
      ∀ (g : D) (w : W),
        (f (W.normalizerMonoidHom
          (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) w)).toAdd =
          BinaryLinearThree.W (e (q g)) (f w).toAdd := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨e₀⟩ := cubic_generated_component_action_quotient_of_moving_plane h hab structural previous faithful Y hYH hm hYp hYT he J hJ
  obtain ⟨_,ht,_⟩ := cubic_generated_action_triple_of_moving_plane h hab structural previous Y hYH hm hYp hYT he
  obtain ⟨e,hA,hB⟩ := goldschmidt_linear_marking ht e₀
  let π := e.toMonoidHom.comp q
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective C)
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hZD : F.Vi 1 ≤ D := (F.le_seed 1).trans (h.chosen.le_sylow.trans hTD)
  have hWD : W ≤ D := conjugateSpanBy_le_self hZD
  let : IsElementaryAbelian 2 W :=
    (cubic_generated_local_structure h hab structural previous Y hYH he).2.2.1
  have hker : π.ker ≤ (centralizer (W : Set G)).subgroupOf D := by
    intro g hg
    have hq : q g = 1 := e.injective (show e (q g) = e 1 from hg.trans e.map_one.symm)
    have hgC : g ∈ C := (QuotientGroup.eq_one_iff g).mp hq
    apply mem_centralizer_iff.mpr
    intro w hw
    have hc := mem_centralizer_iff.mp hgC (⟨w,hWD hw⟩ : D) hw
    exact congrArg Subtype.val hc
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  let := h.chosen.elementary
  obtain ⟨z,hz1,hZ⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hplane : conjugateSpanBy (F.Vi 1) (F.P L) = F.Vi 2 := by
    apply le_antisymm
    · exact conjugateSpanBy_le (F.monotone (by decide : 1 ≤ 2))
        (F.P_le_G₂ (by decide) L h.chosen.normalizes)
    · rw [←plane_eq_point_residual_span h structural]
      apply conjugateSpanBy_mono le_rfl
      rw [plane_parabolic_eq_join h structural]
      exact le_sup_left
  have hBZ : Y ⊔ (T : Subgroup G) ≤ centralizer (F.Vi 1 : Set G) :=
    (sup_le hYH (F.invariant 1)).trans (normalizer_le_centralizer_of_card_two _ hc)
  obtain ⟨f,hf⟩ := Representation.ConjugatePointNatural.exists_natural_coordinates
    D W (F.Vi 1) (F.P L) (Y ⊔ (T : Subgroup G))
    (le_normalizer_conjugateSpanBy _ _) (le_conjugateSpanBy _ _) z hZ hz1
    π hπ hker le_sup_left (by rwa [←map_map]) (by rwa [←map_map]) hBZ rfl
    (by rw [hplane]; simpa using F.card 2 (by decide))
  exact ⟨e,f,hA,hB,hf⟩

/-- The natural point span is the Y-span of V₂ and has the same full span U. -/
theorem cubic_generated_component_span_geometry_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    Nat.card W = 8 ∧ W = conjugateSpanBy (F.Vi 2) Y ∧
      W ≤ F.U ∧ conjugateSpanBy W F.H = F.U ∧
      IsMulCommutative (conjugateSpanBy W F.H) ∧
      ∀ g : G, W ⊓ W.map (MulAut.conj g).toMonoidHom ≠ ⊥ →
        ⁅W,W.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  let := h.chosen.elementary
  let := hab
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨e,f,_,_,hf⟩ := cubic_generated_component_natural_of_moving_plane h hab structural previous faithful Y hYH hm hYp hYT he J hJ
  have hW8 : Nat.card W = 8 := by
    rw [Nat.card_congr f.toEquiv]
    change Nat.card (Fin 3 → ZMod 2) = 8
    norm_num [Nat.card_fun]
  have hYD : Y ≤ D := le_sup_left.trans le_sup_right
  have hPW : F.Vi 2 ≤ W := by
    rw [←plane_eq_point_residual_span h structural]
    apply conjugateSpanBy_mono le_rfl
    change F.Li L 2 ≤ F.P L ⊔ (Y ⊔ (T : Subgroup G))
    rw [plane_parabolic_eq_join h structural]
    exact le_sup_left.trans le_sup_left
  let S := conjugateSpanBy (F.Vi 2) Y
  have hSW : S ≤ W := conjugateSpanBy_le hPW
    (hYD.trans (le_normalizer_conjugateSpanBy _ _))
  have h4 : 4 ≤ Nat.card S := by
    simpa only [F.card 2 (by decide), show (2 : ℕ) ^ 2 = 4 from rfl] using
      card_le_of_le (le_conjugateSpanBy (F.Vi 2) Y)
  have hn4 : Nat.card S ≠ 4 := by
    intro hc
    have hPS : F.Vi 2 = S := eq_of_le_of_card_ge (le_conjugateSpanBy _ _)
      (by rw [hc,F.card 2 (by decide)]; rfl)
    apply hm
    apply moving_plane_centralized_of_normalized Y hYH hYp
    change Y ≤ normalizer (F.Vi 2 : Set G)
    rw [hPS]
    exact le_normalizer_conjugateSpanBy _ _
  have hS8 : Nat.card S = 8 := by
    have hd : Nat.card S ∣ 8 := hW8 ▸ card_dvd_of_le hSW
    have hm : Nat.card S ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hd,by decide⟩
    have heq : Nat.divisors 8 = {1,2,4,8} := by decide
    rw [heq] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    omega
  have hWS : W = S := (eq_of_le_of_card_ge hSW (by rw [hW8,hS8])).symm
  have hWU : W ≤ F.U := by
    rw [hWS]
    exact conjugateSpanBy_le ((F.le_seed 2).trans (le_conjugateSpanBy _ _))
      (hYH.trans (le_normalizer_conjugateSpanBy _ _))
  let := F.localKernel_tilde_seed_elementary
  have hspan : conjugateSpanBy W F.H = F.U := by
    apply le_antisymm
    · exact conjugateSpanBy_le hWU (le_normalizer_conjugateSpanBy _ _)
    · rw [F.U_eq_plane_span L (by decide) h.chosen.normalizes
        (F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide))]
      exact conjugateSpanBy_mono hPW le_rfl
  have habW : IsMulCommutative (conjugateSpanBy W F.H) := hspan.symm ▸ hab
  refine ⟨hW8,hWS,hWU,hspan,habW,?_⟩
  obtain ⟨z,hz1,hZ⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzW : z ∈ W := le_conjugateSpanBy _ _ (hZ ▸ mem_zpowers z)
  have htrans : ∀ x ∈ W, x ≠ 1 → ∃ n ∈ normalizer (W : Set G),
      (MulAut.conj n) z = x := by
    intro x hx hx1
    let zW : W := ⟨z,hzW⟩
    let xW : W := ⟨x,hx⟩
    have hzn : (f zW).toAdd ≠ 0 := by
      intro hh
      have hfz : f zW = 1 := hh
      exact hz1 (congrArg Subtype.val (f.injective (hfz.trans f.map_one.symm)))
    have hxn : (f xW).toAdd ≠ 0 := by
      intro hh
      have hfx : f xW = 1 := hh
      exact hx1 (congrArg Subtype.val (f.injective (hfx.trans f.map_one.symm)))
    obtain ⟨a,ha⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ hzn hxn
    obtain ⟨g,hg⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective C)) a
    refine ⟨g,(le_normalizer_conjugateSpanBy _ _) g.property,?_⟩
    have hh := hf g zW
    change e (q g) = a at hg
    change (f (W.normalizerMonoidHom
      (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) zW)).toAdd =
        BinaryLinearThree.W (e (q g)) (f zW).toAdd at hh
    rw [hg] at hh
    have hfx : f (W.normalizerMonoidHom
        (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) zW) = f xW :=
      Multiplicative.toAdd.injective (hh.trans ha)
    exact congrArg Subtype.val (f.injective hfx)
  have hc := (point_span_abelian_iff_intersecting_conjugates_commute W hzW hz1 htrans).mp
    (show IsMulCommutative (conjugateSpanBy W (centralizer ({z} : Set G))) from
      (F.H_eq_centralizer (by decide) z hZ) ▸ habW)
  exact hc

/-- The entire two-core quotient is PSL₃(2). -/
theorem cubic_generated_component_core_quotient_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    Nonempty ((D ⧸ pCore 2 D) ≃* Matrix.PSL3Two.PSL) := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let Q := pCore 2 D
  let q := QuotientGroup.mk' Q
  let qC := QuotientGroup.mk' C
  have ht := cubic_goldschmidt_triple h structural Y hYH he
  have hQC : Q ≤ C := (cubic_generated_action_kernel_of_moving_plane h hab structural previous Y hYH hm hYp hYT he).1.symm.le.trans inf_le_right
  let r : (D ⧸ Q) →* (D ⧸ C) := QuotientGroup.map Q C (MonoidHom.id D) hQC
  have hcomp : r.comp q = qC := by
    ext x
    rfl
  have hk : (q.subgroupMap J).ker = pCore 2 J := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hJ.subnormal).symm
  let eJ : (J ⧸ pCore 2 J) ≃* J.map q :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (q.subgroupMap_surjective J))
  obtain ⟨e₀⟩ := cubic_generated_component_linear_of_moving_plane h hab structural previous faithful Y hYH hm hYp hYT he J hJ
  let e := eJ.symm.trans e₀
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup (J.map q) := e.isSimpleGroup
  let := hJ.perfect
  let : Group.IsPerfect (J.map q) := Group.IsPerfect.map q
  have hz : center (J.map q) = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (J.map q)) inferInstance).resolve_right
      (fun hh => Group.IsPerfect.not_isMulCommutative (J.map q) (center_eq_top_iff.mp hh))
  let : IsQuasisimple (J.map q) := ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  have hj : IsComponent (D ⧸ Q) (J.map q) :=
    ⟨hJ.subnormal.map (QuotientGroup.mk'_surjective Q),inferInstance⟩
  have hSQ := (cubic_generated_local_structure h hab structural previous Y hYH he).2.1
  obtain ⟨hJn,hcases⟩ := ChapterF.SourceAssembly.source_component_reduction
    (ChapterA.Section02.theoremA_knownSimple (G := D)) hSQ q (QuotientGroup.mk'_surjective Q)
    ht.quotient_twoCore ht.quotient_twoCore_eq_bot hj
  let : (J.map q).Normal := hJn
  have hr := cubic_action_residuals (F := F) h structural Y hYp hYT
  have hnot : ¬ (pResidual 2 (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q)).map
      (((Y ⊔ (T : Subgroup G)).subgroupOf D).map q).subtype ≤
      normalizer ((pResidual 2 (((F.P L).subgroupOf D).map q)).map
        (((F.P L).subgroupOf D).map q).subtype : Set (D ⧸ Q)) := by
    rw [←map_embedded_pResidual,←map_embedded_pResidual,hr.1,hr.2]
    intro hh
    have hmap := (map_mono (f := r) hh).trans (le_normalizer_map r)
    rw [map_map,map_map,hcomp] at hmap
    exact cubic_generated_action_normalizer_obstruction_of_moving_plane h structural Y hYH hm hYp hmap
  have htop := goldschmidt_linear_completion ht.quotient_twoCore
    ht.quotient_twoCore_eq_bot (J.map q) e hcases hnot
  exact ⟨topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans e)⟩

/-- The full two-core is exactly the centralizer of the original point span. -/
theorem cubic_generated_component_kernel_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    centralizer (W.subgroupOf D : Set D) = pCore 2 D := by
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let Q := pCore 2 D
  have hQC : Q ≤ C := (cubic_generated_action_kernel_of_moving_plane h hab structural previous Y hYH hm hYp hYT he).1.symm.le.trans inf_le_right
  obtain ⟨eQ⟩ := cubic_generated_component_core_quotient_of_moving_plane h hab structural previous faithful Y hYH hm hYp hYT he J hJ
  obtain ⟨eC⟩ := cubic_generated_component_action_quotient_of_moving_plane h hab structural previous faithful Y hYH hm hYp hYT he J hJ
  let r : (D ⧸ Q) →* (D ⧸ C) := QuotientGroup.map Q C (MonoidHom.id D) hQC
  have hr : Function.Surjective r := by
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective C x
    exact ⟨QuotientGroup.mk' Q g,rfl⟩
  have hc : Nat.card (D ⧸ C) = Nat.card (D ⧸ Q) := Nat.card_congr (eC.trans eQ.symm).toEquiv
  have hi := (hr.bijective_of_nat_card_le hc.ge).injective
  apply le_antisymm _ hQC
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply hi
  change QuotientGroup.mk' C x = r 1
  rw [r.map_one]
  exact (QuotientGroup.eq_one_iff x).mpr hx

/-- Intersecting conjugates in the mixed original and new seed family commute. -/
theorem cubic_generated_component_seed_family_commutes_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) :
    let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
    let W := conjugateSpanBy (F.Vi 1) D
    let S : Bool → Subgroup G := fun i => if i then W else V
    ∀ i j g k, (S i).conjBy g ⊓ (S j).conjBy k ≠ ⊥ →
      ⁅(S i).conjBy g,(S j).conjBy k⁆ = ⊥ := by
  let := hab
  let := h.chosen.elementary
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let S : Bool → Subgroup G := fun i => if i then W else V
  let : (W.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (le_normalizer_conjugateSpanBy _ _)
  let C := centralizer (W.subgroupOf D : Set D)
  let q := QuotientGroup.mk' C
  obtain ⟨e,f,_,_,hf⟩ := cubic_generated_component_natural_of_moving_plane h hab structural previous faithful Y hYH hm hYp hYT he J hJ
  obtain ⟨_,_,hWU,hspan,_,_⟩ := cubic_generated_component_span_geometry_of_moving_plane
    h hab structural previous faithful Y hYH hm hYp hYT he J hJ
  obtain ⟨z,hz1,hZ⟩ := SetupFlagGeometry.exists_point_generator F (by decide)
  have hzW : z ∈ W := le_conjugateSpanBy _ _ (hZ ▸ mem_zpowers z)
  have hzV : z ∈ V := F.le_seed 1 (hZ ▸ mem_zpowers z)
  have htrans : ∀ i, ∀ x ∈ S i, x ≠ 1 →
      ∃ n ∈ normalizer (S i : Set G), (MulAut.conj n) z = x := by
    intro i x hx hx1
    cases i with
    | false =>
      obtain ⟨l,hl,he⟩ := h.vector_transitive hzV hx hz1 hx1
      exact ⟨l,h.chosen.normalizes hl,he⟩
    | true =>
      let zW : W := ⟨z,hzW⟩
      let xW : W := ⟨x,hx⟩
      have hzn : (f zW).toAdd ≠ 0 := by
        intro hh
        have hfz : f zW = 1 := hh
        exact hz1 (congrArg Subtype.val (f.injective (hfz.trans f.map_one.symm)))
      have hxn : (f xW).toAdd ≠ 0 := by
        intro hh
        have hfx : f xW = 1 := hh
        exact hx1 (congrArg Subtype.val (f.injective (hfx.trans f.map_one.symm)))
      obtain ⟨a,ha⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ hzn hxn
      obtain ⟨g,hg⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective C)) a
      refine ⟨g,(le_normalizer_conjugateSpanBy _ _) g.property,?_⟩
      have hh := hf g zW
      change e (q g) = a at hg
      change (f (W.normalizerMonoidHom
        (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) zW)).toAdd =
          BinaryLinearThree.W (e (q g)) (f zW).toAdd at hh
      rw [hg] at hh
      have hfx : f (W.normalizerMonoidHom
          (inclusion (le_normalizer_conjugateSpanBy (F.Vi 1) D) g) zW) = f xW :=
        Multiplicative.toAdd.injective (hh.trans ha)
      exact congrArg Subtype.val (f.injective hfx)
  have hle : ∀ i, S i ≤ F.U := by
    intro i
    cases i
    · exact le_conjugateSpanBy _ _
    · exact hWU
  have hsp : ∀ i, conjugateSpanBy (S i) (centralizer ({z} : Set G)) ≤ F.U := by
    intro i
    rw [←F.H_eq_centralizer (by decide) z hZ]
    cases i
    · exact le_rfl
    · exact hspan.le
  change ∀ (i j : Bool) (g k : G), (S i).conjBy g ⊓ (S j).conjBy k ≠ ⊥ →
    ⁅(S i).conjBy g,(S j).conjBy k⁆ = ⊥
  intro i j g k hi
  exact mixed_conjugates_commute (S i) (S j)
    (mixed_intersection_commutes (S i) (S j) F.U hz1 (hle i) (hsp j) (htrans i) (htrans j))
    g k hi

/-- The ambient uniqueness argument excludes a component of the moving completion. -/
theorem cubic_generated_no_component_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (J : Subgroup (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G))
    (hJ : J.IsCComponent) : False := by
  let A := L ⊔ (T : Subgroup G)
  let D := F.P L ⊔ (Y ⊔ (T : Subgroup G))
  let W := conjugateSpanBy (F.Vi 1) D
  let E := A ⊔ D
  let S : Bool → Subgroup G := fun i => if i then W else V
  let M : Bool → Subgroup G := fun i => if i then D else A
  let M₀ := ChapterF.Section07.Geometry.family A D
  let S₀ : Bool → Subgroup E := fun i => (S i).subgroupOf E
  have hTD : (T : Subgroup G) ≤ D := le_sup_right.trans le_sup_right
  have hVD : F.Vi 1 ≤ D := (F.le_seed 1).trans (h.chosen.le_sylow.trans hTD)
  have hSE : ∀ i, S i ≤ E := by
    intro i
    cases i
    · exact h.chosen.le_sylow.trans (le_sup_right.trans le_sup_left)
    · exact (conjugateSpanBy_le_self hVD).trans le_sup_right
  have hSM : ∀ i, S i ≤ M i := by
    intro i
    cases i
    · exact h.chosen.le_sylow.trans le_sup_right
    · exact conjugateSpanBy_le_self hVD
  have hnM : ∀ i, M i ≤ normalizer (S i : Set G) := by
    intro i
    cases i
    · exact sup_le h.chosen.normalizes (h.sylow_normalizes_seed structural)
    · exact le_normalizer_conjugateSpanBy _ _
  have hQTA : A.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow A (T.subtype (show (T : Subgroup G) ≤ A from le_sup_right))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ A from le_sup_right)] using hh
  have hQTD : D.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow D (T.subtype hTD)
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTD] using hh
  have hk := cubic_generated_component_kernel_of_moving_plane h hab structural previous faithful Y hYH hm hYp hYT he J hJ
  have hlocalC : ∀ i j, i ≠ j → M i ⊓ centralizer (S i : Set G) ≤ M j := by
    intro i j hij
    cases i <;> cases j
    · exact (hij rfl).elim
    · exact (h.centralizer_LT structural).le.trans (hQTA.trans hTD)
    · intro x hx
      have hxC : (⟨x,hx.1⟩ : D) ∈ centralizer (W.subgroupOf D : Set D) := by
        intro w hw
        apply Subtype.ext
        exact mem_centralizer_iff.mp hx.2 w hw
      have hxQ : (⟨x,hx.1⟩ : D) ∈ pCore 2 D := hk ▸ hxC
      exact (le_sup_right : (T : Subgroup G) ≤ A) (hQTD (mem_map_of_mem D.subtype hxQ))
    · exact (hij rfl).elim
  have hmap (i : Bool) (g : E) :
      ((S₀ i).conjBy g).map E.subtype = (S i).conjBy (g : G) := by
    rw [map_conjBy_hom,map_subgroupOf_eq_of_le (hSE i)]
    rfl
  have hgen := ChapterF.Section07.Geometry.family_generates A D
  have hle₀ : ∀ i, S₀ i ≤ M₀ i := by
    intro i x hx
    have hh : (x : G) ∈ M i := hSM i hx
    cases i <;> exact hh
  have hn₀ : ∀ i, M₀ i ≤ normalizer (S₀ i : Set E) := by
    intro i
    have hh := (comap_mono (f := E.subtype) (hnM i)).trans (le_normalizer_comap E.subtype)
    cases i <;> exact hh
  have hC₀ : ∀ i j, i ≠ j → M₀ i ⊓ centralizer (S₀ i : Set E) ≤ M₀ j := by
    intro i j hij x hx
    have hxM : (x : G) ∈ M i := by cases i <;> exact hx.1
    have hxC : (x : G) ∈ centralizer (S i : Set G) := by
      apply mem_centralizer_iff.mpr
      intro y hy
      exact congrArg Subtype.val (mem_centralizer_iff.mp hx.2 (⟨y,hSE i hy⟩ : E) hy)
    have hh := hlocalC i j hij ⟨hxM,hxC⟩
    cases j <;> exact hh
  have hc := cubic_generated_component_seed_family_commutes_of_moving_plane h hab structural previous faithful Y hYH hm hYp hYT he J hJ
  have hc₀ : ∀ i j (g k : E), (S₀ i).conjBy g ⊓ (S₀ j).conjBy k ≠ ⊥ →
      ⁅(S₀ i).conjBy g,(S₀ j).conjBy k⁆ = ⊥ := by
    intro i j g k hi
    have hi' : (S i).conjBy (g : G) ⊓ (S j).conjBy (k : G) ≠ ⊥ := by
      rw [←hmap i g,←hmap j k,←map_inf _ _ _ E.subtype_injective]
      exact fun hz => hi ((map_eq_bot_iff_of_injective _ E.subtype_injective).mp hz)
    apply (map_eq_bot_iff_of_injective _ E.subtype_injective).mp
    rw [map_commutator,hmap,hmap]
    exact hc i j g k hi'
  obtain ⟨hfix,hcomm⟩ := CosetGeometry.RankTwo.conjugate_seeds_in_overlap M₀ S₀ hgen hle₀ hn₀ hC₀ hc₀
  let N := conjugateSpanBy V E
  have hNA : N ≤ A := by
    apply (closure_le _).mpr
    rintro x ⟨g,hg,v,hv,rfl⟩
    have hh := hfix false (⟨g,hg⟩ : E)
    have hm := map_mono (f := E.subtype) (hh.trans inf_le_left)
    rw [hmap] at hm
    have hMA : (M₀ false).map E.subtype = A := map_subgroupOf_eq_of_le le_sup_left
    rw [hMA] at hm
    exact hm (mem_map_of_mem _ hv)
  have hNC : N ≤ centralizer (V : Set G) := by
    apply (closure_le _).mpr
    rintro x ⟨g,hg,v,hv,rfl⟩
    have hh := congrArg (map E.subtype) (hcomm false false 1 (⟨g,hg⟩ : E))
    rw [map_commutator,hmap,hmap,Subgroup.map_bot] at hh
    change ⁅V.conjBy 1,V.conjBy g⁆ = ⊥ at hh
    rw [conjBy_one] at hh
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hh))
      (mem_map_of_mem _ hv)
  have hNQ : N ≤ A.pCoreIn 2 := (le_inf hNA hNC).trans (h.centralizer_LT structural).le
  have hNp : IsPGroup 2 N := (isPGroup_pCoreIn 2 A).to_le hNQ
  have hNne : N ≠ ⊥ := fun hz => h.chosen.ne_bot (eq_bot_iff.mpr
    ((le_conjugateSpanBy V E).trans hz.le))
  have hu : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro X _ _ hX S M hM
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hX S hM
  have hcontrol : normalizer (N : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal
      (fun M hM hAM => Set.mem_singleton_iff.mp ((h.maximal_unique structural hu).2 ▸
        show M ∈ {M : Subgroup G | IsMaximalTwoLocal M ∧ A ≤ M} from ⟨hM,hAM⟩))
      hNp hNne (le_sup_left.trans (le_normalizer_conjugateSpanBy V E))
  exact hout (((le_sup_left.trans le_sup_right : Y ≤ D).trans le_sup_right).trans
    ((le_normalizer_conjugateSpanBy V E).trans hcontrol))

/-- An escaping cubic actor that moves the plane has a solvable completion. -/
theorem cubic_generated_solvable_of_moving_plane
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (Y : Subgroup G) (hYH : Y ≤ F.H)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hout : ¬ Y ≤ normalizer (L : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    Group.IsSolvable (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G) := by
  classical
  by_contra hs
  obtain ⟨J,hJD,hJ,_⟩ := cubic_generated_nonsolvable_component_of_moving_plane
    h hab structural previous faithful Y hYH hm hYp hYT he hs
  exact cubic_generated_no_component_of_moving_plane h hab structural previous faithful Y hYH hm hYp hYT hout he (J.subgroupOf _) hJ

open Representation in
/-- A failed lift through a proper invariant quotient has a solvable cubic
completion. This discharges both component alternatives of the original
quotient-lifting reduction, using the very same actor and quotient map. -/
theorem original_quotient_plane_lifting_solvable
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    {W X : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) F.H W} {σ : Representation (ZMod 2) F.H X}
    (c : BinaryConjugationSection F.H F.U (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤)
    (Y : Subgroup G) (hYH : Y ≤ F.H) (hYp : IsPPerfect 2 Y)
    (hYT : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (he : Nonempty (((Y ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (Y ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hfix : ∀ y (hy : y ∈ Y) (v : F.U), (v : G) ∈ F.Vi 2 →
      σ ⟨y,hYH hy⟩ (p (c.coordinates v).toAdd) = p (c.coordinates v).toAdd)
    (hm : ⁅F.Vi 2,Y⁆ ≠ ⊥) :
    Group.IsSolvable (F.P L ⊔ (Y ⊔ (T : Subgroup G)) : Subgroup G) := by
  have hout := quotient_plane_moving_actor_escapes_at h (structural G T)
    c p hp Y hYH hYp hfix hm
  exact cubic_generated_solvable_of_moving_plane h hab structural previous faithful
    Y hYH hm hYp hYT hout he

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
