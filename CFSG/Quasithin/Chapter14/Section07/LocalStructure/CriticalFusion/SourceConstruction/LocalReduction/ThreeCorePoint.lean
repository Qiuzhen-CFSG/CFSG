module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ThreeCoreActions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.ElementaryNine.Offender
public import Theory.GroupTheory.CubicSmallAction

/-!
# Cubic point images in the original solvable local groups

For a supercritical elementary-nine subgroup, an SL₂(3) conjugation image
would force every faithful elementary two-actor to have fixed codimension
greater than twice its rank. The original flag supplies an actor with the
opposite bound. Supercritical detection makes that actor faithful, using
the full three-core centralizer bound. Thus the order-24 point-image branch
is impossible: every original solvable J in H_z has |L₁*| = 3, with
exactly O₂(L₁) as the star-map kernel.

The same image obstruction makes the two-residual of J/O₂(J) equal its
three-core in the elementary-nine branch. In the Heisenberg branch,
the full Frattini-action kernel is O₃(J/O₂(J)). The Sylow-normalized
cubic has normal image in GL₂(3), so it too lies in the three-core.
The final theorem applies both arguments to the original selected lift,
placing L₁* inside O₃(J/O₂(J)) without a placement premise.

The proper supercritical lifts and the remaining ambient noncyclic
three-core exclusions are still required for 14.7.27–29. None of these
results asserts nonsolvability or the final residual classification.

Source: Aschbacher–Smith, 14.7.27, printed pp.1054–1055; D.2.17,
pp.186–188; the elementary-nine character bound in 13.8.13, p.951,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Matrix.GeneralLinearGroup PrimeThreeFiveResidual
open Chapter13.Section08.SolvableExclusion.Three.Noncontained.ElementaryNine
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual quadratic actor excludes a special-linear image on a supercritical nine-group. -/
theorem local_solvable_nine_no_special_image
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (c : ConjugationCoordinates (X.map (pCore 3 (HStar J)).subtype)) :
    ¬ threeSpecialLinear ≤ c.action.range := by
  intro hSL
  have uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u} := by
    intro D _ _ hD S N hN
    exact Chapter1.Section02.nonsolvable_uniqueness_knownSimple hD S hN
  let earlier : EarlierSetupResults KnownSimple.IsKnownSimple.{u} :=
    ⟨structural,uniqueness,previous⟩
  obtain ⟨hU,a,hq,A,hAR,hA,hquad,hcod⟩ :=
    Chapter12.Section09.NaturalSource.abelian_local_quadratic_actor h earlier F hab J hJ
  let := hU
  let B := A.map (QuotientGroup.mk' (pCore 2 J))
  let : IsElementaryAbelian 2 B := hA.2
  have hcent := hX.ambient_centralizer_le_pCore (pCore 3 (HStar J)) pCore_isPGroup
    (local_solvable_threeCore_selfCentralizing h hab structural previous faithful J hJ hs)
    X (by decide : Odd 3)
  have hd := (IsElementaryAbelian.isPGroup 2 B).disjoint_of_coprime
    (pCore_isPGroup (p := 3) (G := HStar J)) (by decide : Nat.Coprime 2 3)
  have hb : B ⊓ centralizer (X.map (pCore 3 (HStar J)).subtype : Set (HStar J)) = ⊥ :=
    bot_unique ((inf_le_inf_left B hcent).trans hd.le_bot)
  have hlt := strict_fixedCodim_of_special_image c a.representation a.faithful hSL B hA hb
  exact (not_lt_of_ge hcod) hlt

/-- The elementary-nine branch has exactly the original two-core kernel and cubic point image. -/
theorem local_solvable_nine_point_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e₀ : X ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    ((QuotientGroup.mk' (pCore 2 J)).comp
      (inclusion (F.Li_one_le_of_mem_Hz hJ))).ker = pCore 2 (F.Li L 1) ∧
    Nat.card (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 3 := by
  let : X.Characteristic := hX.characteristic
  let Z := X.map (pCore 3 (HStar J)).subtype
  let : Z.Characteristic := inferInstance
  let q := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion (F.Li_one_le_of_mem_Hz hJ))
  rcases local_solvable_nine_point_action h hab structural previous faithful J hJ hs X hX e₀ with
    hh | ⟨c,e,he,hr,hk,hcard⟩
  · exact ⟨hh.1,by simpa only [MonoidHom.range_comp,inclusion_range] using hh.2⟩
  let coord : ConjugationCoordinates Z := {
    coordinate := c
    action := e.toMonoidHom.comp (MulAut.conjNormal : HStar J →* MulAut Z)
    conjugates := by
      intro k z
      have hh := he (MulAut.conjNormal k) z
      have hh' : Representation.AffineNine.naturalAction (e (MulAut.conjNormal k)) (c z) =
          c (MulAut.conjNormal k z) := hh
      change k * (z : HStar J) * k⁻¹ =
        (c.symm (Representation.AffineNine.naturalAction (e (MulAut.conjNormal k)) (c z)) : Z)
      rw [hh',c.symm_apply_apply]
      rfl }
  apply (local_solvable_nine_no_special_image h hab structural previous faithful J hJ hs X hX coord).elim
  rw [←hr]
  rintro y ⟨x,rfl⟩
  exact ⟨q x,rfl⟩


private def threeCoreLiftEquiv
    (J : Subgroup G) (X : Subgroup (pCore 3 (HStar J))) (Y : Subgroup J)
    (hm : Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype)
    (hk : ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y) :
    (Y ⧸ pCore 2 Y) ≃* X := by
  let f := (QuotientGroup.mk' (pCore 2 J)).comp Y.subtype
  have hr : f.range = X.map (pCore 3 (HStar J)).subtype := by
    rw [MonoidHom.range_comp,range_subtype,hm]
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans
      ((MulEquiv.subgroupCongr hr).trans
        (equivMapOfInjective X (pCore 3 (HStar J)).subtype
          (pCore 3 (HStar J)).subtype_injective).symm))

/-- Both original solvable three-core branches have the same full point kernel and cubic image. -/
theorem local_solvable_point_kernel
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ((QuotientGroup.mk' (pCore 2 J)).comp
      (inclusion (F.Li_one_le_of_mem_Hz hJ))).ker = pCore 2 (F.Li L 1) ∧
    Nat.card (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 3 := by
  obtain ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,he⟩ :=
    local_solvable_threeCore_source h hab structural previous faithful J hJ hs
  let e := threeCoreLiftEquiv J X Y hYm hYk
  rcases he with he | he
  · exact local_solvable_nine_point_kernel h hab structural previous faithful
      J hJ hs X hX (e.symm.trans he.some)
  · exact local_solvable_heisenberg_point_kernel h hab structural previous faithful
      J hJ hs X hX (e.symm.trans he.some)

/-- The original point residual’s two-core lies in the two-core of each solvable local overgroup. -/
theorem local_solvable_point_core_le
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    (F.Li L 1).pCoreIn 2 ≤ J.pCoreIn 2 := by
  have hk := (local_solvable_point_kernel h hab structural previous faithful J hJ hs).1
  rintro x ⟨y,hy,rfl⟩
  have hyk : ((QuotientGroup.mk' (pCore 2 J)).comp
      (inclusion (F.Li_one_le_of_mem_Hz hJ))) y = 1 := by
    change y ∈ ((QuotientGroup.mk' (pCore 2 J)).comp
      (inclusion (F.Li_one_le_of_mem_Hz hJ))).ker
    rwa [hk]
  exact mem_map_of_mem J.subtype ((QuotientGroup.eq_one_iff _).mp hyk)


/-- The entire two-residual is a three-group in the elementary-nine branch. -/
theorem local_solvable_nine_residual_isThreeGroup
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e₀ : X ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    IsPGroup 3 (pResidual 2 (HStar J)) := by
  let : X.Characteristic := hX.characteristic
  let Z := X.map (pCore 3 (HStar J)).subtype
  let : Z.Characteristic := inferInstance
  let eX := equivMapOfInjective X (pCore 3 (HStar J)).subtype
    (pCore 3 (HStar J)).subtype_injective
  let eZ := eX.symm.trans e₀
  let : IsElementaryAbelian 3 Z := IsElementaryAbelian.of_injective eZ.toMonoidHom eZ.injective
  have hc : Nat.card Z = 3 ^ 2 := by
    rw [Nat.card_congr eZ.toEquiv,Nat.card_prod]
    norm_num [Nat.card_zmod]
  let c := conjugationCoordinates Z hc
  have hn := local_solvable_nine_no_special_image h hab structural previous faithful J hJ hs X hX c
  have hcent := hX.ambient_centralizer_le_pCore (pCore 3 (HStar J)) pCore_isPGroup
    (local_solvable_threeCore_selfCentralizing h hab structural previous faithful J hJ hs)
    X (by decide : Odd 3)
  have hk : IsPGroup 3 c.action.ker := by
    rw [c.ker_eq_centralizer]
    exact pCore_isPGroup.to_le hcent
  let R := (pResidual 2 (HStar J)).map c.action
  have hR : IsPGroup 3 R := by
    by_cases hz : R = ⊥
    · rw [hz]
      exact IsPGroup.of_card (n := 0) (by simp)
    have hp : IsPPerfect 2 R := (isPPerfect_pResidual 2).of_surjective
      (c.action.subgroupMap (pResidual 2 (HStar J))) (c.action.subgroupMap_surjective _)
    rcases three_twoPerfect_subgroup R hp hz with hc | he
    · exact IsPGroup.of_card (n := 1) hc
    · exact (hn (he ▸ map_le_range c.action _)).elim
  exact (hR.comap_of_ker_isPGroup c.action hk).to_le (le_comap_map _ _)

/-- The literal two-residual and three-core coincide in the elementary-nine branch. -/
theorem local_solvable_nine_residual_eq_threeCore
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e₀ : X ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    pResidual 2 (HStar J) = pCore 3 (HStar J) := by
  have hp := local_solvable_nine_residual_isThreeGroup h hab structural previous faithful
    J hJ hs X hX e₀
  have hle : pResidual 2 (HStar J) ≤ pCore 3 (HStar J) :=
    le_sSup ⟨inferInstance,hp⟩
  refine le_antisymm hle ?_
  let q := QuotientGroup.mk' (pResidual 2 (HStar J))
  have hz : (pCore 3 (HStar J)).map q = ⊥ := by
    have hd := (pCore_isPGroup (p := 3) (G := HStar J)).map q |>.disjoint_of_coprime
      ((isPGroup_quotient_pResidual 2).to_subgroup ⊤) (by decide : Nat.Coprime 3 2)
    simpa using hd.eq_bot
  simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz

/-- The selected original lift retains its exact kernel. The elementary-nine
branch now has three-group residual; both branches have the same cubic point image. -/
theorem local_solvable_threeCore_point_reduction
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ((QuotientGroup.mk' (pCore 2 J)).comp
      (inclusion (F.Li_one_le_of_mem_Hz hJ))).ker = pCore 2 (F.Li L 1) ∧
    Nat.card (((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) = 3 ∧
    ∃ (X : Subgroup (pCore 3 (HStar J))) (_hX : IsSupercriticalPSubgroup 3 X)
      (Y : Subgroup J),
      Y.Normal ∧ IsPPerfect 2 Y ∧ Y ≤ pResidual 2 J ∧
      Y.map (QuotientGroup.mk' (pCore 2 J)) = X.map (pCore 3 (HStar J)).subtype ∧
      ((QuotientGroup.mk' (pCore 2 J)).comp Y.subtype).ker = pCore 2 Y ∧
      ((Nonempty ((Y ⧸ pCore 2 Y) ≃*
          (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∧
          pResidual 2 (HStar J) = pCore 3 (HStar J)) ∨
        Nonempty ((Y ⧸ pCore 2 Y) ≃* HeisenbergPrime 3)) := by
  have hp := local_solvable_point_kernel h hab structural previous faithful J hJ hs
  refine ⟨hp.1,hp.2,?_⟩
  obtain ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,he⟩ :=
    local_solvable_threeCore_source h hab structural previous faithful J hJ hs
  refine ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,?_⟩
  rcases he with he | he
  · exact Or.inl ⟨he,local_solvable_nine_residual_eq_threeCore h hab structural previous faithful
      J hJ hs X hX ((threeCoreLiftEquiv J X Y hYm hYk).symm.trans he.some)⟩
  · exact Or.inr he

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction


namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Matrix.GeneralLinearGroup PrimeThreeFiveResidual
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original point cubic lies in the three-core through the full Heisenberg Frattini action. -/
theorem local_solvable_heisenberg_point_le_threeCore
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J)
    (X : Subgroup (pCore 3 (HStar J))) (hX : IsSupercriticalPSubgroup 3 X)
    (e₀ : X ≃* HeisenbergPrime 3) :
    ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤ pCore 3 (HStar J) := by
  let : X.Characteristic := hX.characteristic
  let : IsExtraspecial 3 X := IsExtraspecial.of_mulEquiv e₀.symm
    (HeisenbergPrime.isExtraspecial (by decide : 3 ≠ 2))
  let : Fact (IsPGroup 3 X) := ⟨IsExtraspecial.isPGroup 3 X⟩
  let : IsElementaryAbelian 3 (X ⧸ frattini X) := isElementaryAbelian_quotient_frattini
  have hcX : Nat.card X = 27 := by rw [Nat.card_congr e₀.toEquiv,HeisenbergPrime.card]; decide
  have hc : Nat.card (X ⧸ frattini X) = 3 ^ 2 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (frattini X)
    have hf : Nat.card (frattini X) = 3 := by
      rw [IsExtraspecial.frattini_eq_center (p := 3),IsExtraspecial.center_order_p 3 X]
    rw [hcX,hf] at hh
    omega
  obtain ⟨c,e,he⟩ := exists_plane_coordinates hc
  let b := (((quotientAut (frattini X)).comp (MulAut.characteristic X)).comp
    (MulAut.conjNormal : HStar J →* MulAut (pCore 3 (HStar J))))
  let a := e.toMonoidHom.comp b
  have hb : b.ker = pCore 3 (HStar J) :=
    local_solvable_heisenberg_frattini_kernel h hab structural previous faithful J hJ hs X hX e₀
  have ha : a.ker = b.ker := by
    ext x
    change e (b x) = 1 ↔ b x = 1
    rw [←e.map_one,e.injective.eq_iff]
  have hak : IsPGroup 3 a.ker := by rw [ha,hb]; exact pCore_isPGroup
  have hGL : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := by
    rw [Matrix.card_GL_field]
    decide
  have hcard : Nat.card a.range ∣ 48 := hGL ▸ a.range.card_subgroup_dvd_card
  let q := QuotientGroup.mk' (pCore 2 J)
  let S := T.subtype (show (T : Subgroup G) ≤ J from fun x hx => hJ.1.2 (Or.inr hx))
  let S₀ := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  have hn : (S : Subgroup J) ≤ normalizer ((F.Li L 1).subgroupOf J : Set J) := by
    rw [←subgroupOf_normalizer_eq (F.Li_one_le_of_mem_Hz hJ)]
    intro x hx
    exact T_normalizes_L₁ h structural hx
  exact cubic_le_threeCore_of_small_action a hak hcard S₀ _
    (local_solvable_heisenberg_point_kernel h hab structural previous faithful J hJ hs X hX e₀).2
    ((map_mono hn).trans (le_normalizer_map q))

/-- Every original solvable local overgroup has its literal point image contained in its three-core. -/
theorem local_solvable_point_le_threeCore
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (J : Subgroup G) (hJ : J ∈ F.Hz L (normalizer (L : Set G)))
    (hs : Group.IsSolvable J) :
    ((F.Li L 1).subgroupOf J).map (QuotientGroup.mk' (pCore 2 J)) ≤ pCore 3 (HStar J) := by
  obtain ⟨X,hX,Y,hYn,hYp,hYle,hYm,hYk,he⟩ :=
    local_solvable_threeCore_source h hab structural previous faithful J hJ hs
  let e := threeCoreLiftEquiv J X Y hYm hYk
  rcases he with he | he
  · rw [←local_solvable_nine_residual_eq_threeCore h hab structural previous faithful J hJ hs
      X hX (e.symm.trans he.some)]
    have hp : IsPPerfect 2 (F.Li L 1) := by
      simp only [InvariantFlag.Li]
      exact isPPerfect_embedded_pResidual 2 _
    let f := (QuotientGroup.mk' (pCore 2 J)).comp (inclusion (F.Li_one_le_of_mem_Hz hJ))
    have hh := map_pResidual_le 2 f
    rw [(pResidual_eq_top_iff 2 _).mpr hp,←MonoidHom.range_eq_map,
      MonoidHom.range_comp,inclusion_range] at hh
    exact hh
  · exact local_solvable_heisenberg_point_le_threeCore h hab structural previous faithful
      J hJ hs X hX (e.symm.trans he.some)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
