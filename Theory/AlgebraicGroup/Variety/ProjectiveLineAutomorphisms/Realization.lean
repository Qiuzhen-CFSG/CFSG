module
public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.OpenFactorization
public import Theory.AlgebraicGroup.Variety.OpenSubvariety
public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.LocalTriples
public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.PointAction
public import Theory.AlgebraicGroup.Variety.ProjectiveLineAutomorphisms.PointActionGluing
public import Theory.AlgebraicGroup.Variety.AffineGeometricReverse
import all Theory.AlgebraicGroup.Instance.PGL2ProjectiveAction

/-!
# Morphic actions on the projective line

Every morphic action on P¹ comes from a unique algebraic-group morphism to the
actual PGL₂ carrier. Evaluate the action at 0, 1, and ∞. On the eight choices of
affine charts for these images, the determinant formula gives a regular GL₂
matrix, hence a regular PGL₂ point. Three-point rigidity identifies these local
maps and glues them. The group laws follow from the faithful point action.

This is Borel, *Linear Algebraic Groups*, §10.8, in the form used in §13.13.
The argument works in every characteristic and requires no connectedness or
separability hypothesis on the acting group.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
public noncomputable section

private abbrev ChartIndex := Fin 2 × Fin 2 × Fin 2

private def tripleChartOpen {V : Geometric k} (f0 f1 fi : Morphism V (projectiveLine k))
    (c : ChartIndex) : V.toScheme.Opens :=
  f0.hom ⁻¹ᵁ projectiveLineChartOpen k c.1 ⊓
    f1.hom ⁻¹ᵁ projectiveLineChartOpen k c.2.1 ⊓
    fi.hom ⁻¹ᵁ projectiveLineChartOpen k c.2.2

omit [IsAlgClosed k] in
private lemma tripleChartOpen_cover {V : Geometric k} (f0 f1 fi : Morphism V (projectiveLine k)) :
    ⨆ c, tripleChartOpen f0 f1 fi c = ⊤ := by
  apply top_unique
  intro x hx
  have he (z : (projectiveLine k).toScheme) : ∃ i : Fin 2, z ∈ projectiveLineChartOpen k i := by
    apply Opens.mem_iSup.mp
    rw [iSup_projectiveLineChartOpen_eq_top]
    trivial
  obtain ⟨i0, h0⟩ := he (f0.hom x)
  obtain ⟨i1, h1⟩ := he (f1.hom x)
  obtain ⟨ii, hi⟩ := he (fi.hom x)
  exact Opens.mem_iSup.mpr ⟨⟨i0,i1,ii⟩, ⟨⟨h0,h1⟩,hi⟩⟩

omit [IsAlgClosed k] in
private lemma tripleChartOpen_markings {V : Geometric k} (f0 f1 fi : Morphism V (projectiveLine k))
    (c : ChartIndex) (x : Point (openSubvariety V (tripleChartOpen f0 f1 fi c)).toGeometric) :
    let e := (openSubvariety V (tripleChartOpen f0 f1 fi c)).inclusion
    (f0 (e x)).1 (IsLocalRing.closedPoint k) ∈ projectiveLineChartOpen k c.1 ∧
    (f1 (e x)).1 (IsLocalRing.closedPoint k) ∈ projectiveLineChartOpen k c.2.1 ∧
    (fi (e x)).1 (IsLocalRing.closedPoint k) ∈ projectiveLineChartOpen k c.2.2 := by
  have hx := (x.1 (IsLocalRing.closedPoint k)).property
  exact ⟨hx.1.1, hx.1.2, hx.2⟩

private def actionMark {H : Variety k} [AlgebraicGroup H]
    (A : MorphicAction H (projectiveLine k)) (p : Point (projectiveLine k)) :
    Morphism (ofAffine H) (projectiveLine k) := A.orbitMorphismAt p

private lemma actionMark_apply {H : Variety k} [AlgebraicGroup H]
    (A : MorphicAction H (projectiveLine k)) (p : Point (projectiveLine k))
    (x : Point (ofAffine H)) : actionMark A p x = A.toMulAction.smul (affinePointEquiv H x) p := by
  simpa only [actionMark, Equiv.symm_apply_apply] using A.orbitMorphismAt_apply p (affinePointEquiv H x)

local instance tripleCoverPgl2Action : MulAction (Variety.Point (pgl2Variety (k := k)))
    (Point (projectiveLine k)) := pgl2ProjectiveLinePointMulAction

set_option backward.isDefEq.respectTransparency false in
private lemma action_markings_distinct {H : Variety k} [AlgebraicGroup H]
    (A : MorphicAction H (projectiveLine k)) (x : Point (ofAffine H)) :
    actionMark A projectiveLineOne x ≠ actionMark A projectiveLineZero x ∧
    actionMark A projectiveLineInfinity x ≠ actionMark A projectiveLineOne x ∧
    actionMark A projectiveLineInfinity x ≠ actionMark A projectiveLineZero x := by
  have hmark (p : Point (projectiveLine k)) :
      actionMark A p x = pointActionHom A (affinePointEquiv H x) • p := by
    rw [actionMark_apply, pointActionHom_smul]
  simp only [hmark, ne_eq, smul_left_cancel_iff]
  exact ⟨fun he => one_ne_zero (projectiveLineAffinePoint_injective he),
    projectiveLineInfinity_ne_affinePoint (1 : k), projectiveLineInfinity_ne_affinePoint (0 : k)⟩

set_option backward.isDefEq.respectTransparency false in
private lemma exists_local_action_map {H : Variety k} [AlgebraicGroup H]
    (A : MorphicAction H (projectiveLine k)) (c : ChartIndex) :
    let U := tripleChartOpen (actionMark A projectiveLineZero)
      (actionMark A projectiveLineOne) (actionMark A projectiveLineInfinity) c
    ∃ F : Morphism (openSubvariety (ofAffine H) U).toGeometric (ofAffine (pgl2Variety (k := k))),
      ∀ x, affinePointEquiv _ (F x) = pointActionHom A
        (affinePointEquiv H ((openSubvariety (ofAffine H) U).inclusion x)) := by
  let f0 := actionMark A (projectiveLineZero (k := k))
  let f1 := actionMark A (projectiveLineOne (k := k))
  let fi := actionMark A (projectiveLineInfinity (k := k))
  let U := tripleChartOpen f0 f1 fi c
  let e := (openSubvariety (ofAffine H) U).inclusion
  have h0 (x) : ((Morphism.comp e f0) x).1 (IsLocalRing.closedPoint k) ∈ projectiveLineChartOpen k c.1 :=
    (tripleChartOpen_markings f0 f1 fi c x).1
  have h1 (x) : ((Morphism.comp e f1) x).1 (IsLocalRing.closedPoint k) ∈ projectiveLineChartOpen k c.2.1 :=
    (tripleChartOpen_markings f0 f1 fi c x).2.1
  have hi (x) : ((Morphism.comp e fi) x).1 (IsLocalRing.closedPoint k) ∈ projectiveLineChartOpen k c.2.2 :=
    (tripleChartOpen_markings f0 f1 fi c x).2.2
  have h10 (x) : (Morphism.comp e f1) x ≠ (Morphism.comp e f0) x := by
    simpa only [Morphism.comp_apply_point] using (action_markings_distinct A (e x)).1
  have hi1 (x) : (Morphism.comp e fi) x ≠ (Morphism.comp e f1) x := by
    simpa only [Morphism.comp_apply_point] using (action_markings_distinct A (e x)).2.1
  have hi0 (x) : (Morphism.comp e fi) x ≠ (Morphism.comp e f0) x := by
    simpa only [Morphism.comp_apply_point] using (action_markings_distinct A (e x)).2.2
  obtain ⟨F,hF⟩ := exists_pgl2_morphism_on_charts (Morphism.comp e f0) (Morphism.comp e f1)
    (Morphism.comp e fi) c.1 c.2.1 c.2.2 h0 h1 hi h10 hi1 hi0
  refine ⟨F, ?_⟩
  intro x
  obtain ⟨ha,hb,hc⟩ := hF x
  apply pgl2_triple_images_injective
  · exact ha.trans ((Morphism.comp_apply_point e f0 x).trans
      ((actionMark_apply A projectiveLineZero (e x)).trans (pointActionHom_smul A _ _).symm))
  · exact hb.trans ((Morphism.comp_apply_point e f1 x).trans
      ((actionMark_apply A projectiveLineOne (e x)).trans (pointActionHom_smul A _ _).symm))
  · exact hc.trans ((Morphism.comp_apply_point e fi x).trans
      ((actionMark_apply A projectiveLineInfinity (e x)).trans (pointActionHom_smul A _ _).symm))

/-- The actual point homomorphism induced by any morphic projective-line action
is a geometric morphism in the acting parameter. -/
theorem exists_geometric_realization {H : Variety k} [AlgebraicGroup H]
    (A : MorphicAction H (projectiveLine k)) :
    ∃ f : Morphism (ofAffine H) (ofAffine (pgl2Variety (k := k))),
      ∀ p, affinePointEquiv _ (f p) = pointActionHom A (affinePointEquiv H p) := by
  let U := tripleChartOpen (actionMark A (projectiveLineZero (k := k)))
    (actionMark A (projectiveLineOne (k := k))) (actionMark A (projectiveLineInfinity (k := k)))
  have hU : ⨆ c, U c = ⊤ := tripleChartOpen_cover _ _ _
  have hlocal : ∀ c : ChartIndex,
      ∃ F : Morphism (openSubvariety (ofAffine H) (U c)).toGeometric (ofAffine (pgl2Variety (k := k))),
        ∀ p, affinePointEquiv _ (F p) = pointActionHom A
          (affinePointEquiv H ((openSubvariety (ofAffine H) (U c)).inclusion p)) :=
    fun c => exists_local_action_map A c
  choose F hF using hlocal
  exact (pointActionHom_existsUnique_of_local_representatives A U hU F hF).exists

/-- Borel 10.8: every morphic action on the projective line is realized by a
unique algebraic-group morphism to the actual PGL₂ carrier. -/
theorem existsUnique_algebraicGroupMorphism_of_morphicAction {H : Variety k} [AlgebraicGroup H]
    (A : MorphicAction H (projectiveLine k)) :
    ∃! φ : AlgebraicGroup.Morphism H (pgl2Variety (k := k)),
      ∀ h p, (pgl2ProjectiveLineMorphicAction (k := k)).toMulAction.smul (φ.onPoints h) p =
        A.toMulAction.smul h p := by
  obtain ⟨f, hf⟩ := exists_geometric_realization A
  let F := presentedOfGeometric f
  have hF (h : Variety.Point H) : F.toFun h = pointActionHom A h := by
    have he := presentedOfGeometric_apply f ((affinePointEquiv H).symm h)
    rw [Equiv.apply_symm_apply] at he
    exact he.trans (by simpa only [Equiv.apply_symm_apply] using hf ((affinePointEquiv H).symm h))
  let φ : AlgebraicGroup.Morphism H (pgl2Variety (k := k)) :=
    { toVariety := F
      map_one := by rw [hF, map_one]
      map_mul := by intro a b; rw [hF, map_mul, hF, hF] }
  have hφ (h : Variety.Point H) (p : Point (projectiveLine k)) :
      (pgl2ProjectiveLineMorphicAction (k := k)).toMulAction.smul (φ.onPoints h) p =
        A.toMulAction.smul h p := by
    change F.toFun h • p = _
    rw [hF, pointActionHom_smul]
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply Theory.AlgebraicGroup.Morphism.ext
  funext h
  have hψ' := pointActionHom_unique A ψ.onPoints hψ
  have hφ' := pointActionHom_unique A φ.onPoints hφ
  exact DFunLike.congr_fun (hψ'.trans hφ'.symm) h

end
end Theory.AlgebraicGroup.Variety.Geometric.ProjectiveLineAutomorphisms
