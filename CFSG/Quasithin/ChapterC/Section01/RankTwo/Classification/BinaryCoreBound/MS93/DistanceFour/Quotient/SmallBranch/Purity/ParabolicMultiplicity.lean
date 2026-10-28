module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.Criteria
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Parabolics.Residual
public import Theory.GroupTheory.PCoreImage
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.QuadraticQuotient

/-!
# Natural multiplicity at a marked binary parabolic

A nonzero vector fixed by the source-ordered residual O²(O^{2′}(P))
selects the natural orientation at P. Its embedded intrinsic two-core then
has fixed codimension two on each marked natural factor. Fixed codimensions
add over the quotient copies and cannot increase under the equivariant
surjection, giving `2 * m ≤ fixedCodim ρ O₂(P)`. The supplied upper bound
of two therefore gives `m ≤ 1`.

Both point and line parabolics are transported from the standard point
parabolic using the compatible diagram automorphism. After normalizing the
combined marking, the dual orientation is excluded by two explicit elements
of the actual residual. In the natural orientation the point four-group
fixes exactly the first coordinate line. Relative normality and the checked
S₄ core order identify this four-group with the intrinsic parabolic core.

This is a conditional model calculation: existence of `ParabolicBounds`
remains with the geometric source argument. No FF or fixed-space-purity
hypothesis is needed here.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.4), printed p.842, and the opening inference of (4.6.11), p.909.
-/

public section

open Subgroup Matrix Representation Representation.BinaryOffender
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
open Linear

private def t01 : SL := ⟨!![1,1,0; 0,1,0; 0,0,1], by decide⟩
private def t02 : SL := ⟨!![1,0,1; 0,1,0; 0,0,1], by decide⟩
private theorem t01_mem : t01 ∈ pointV := by decide
private theorem t02_mem : t02 ∈ pointV := by decide
private theorem dual_no_fixed (v : W)
    (hv : ∀ k ∈ pointA, dual k v = v) : v = 0 := by
  have htest : ∀ v : W, dual t01 v = v → dual cubic v = v → v = 0 := by
    decide +kernel
  exact htest v (hv _ (pointV_le t01_mem)) (hv _ cubic_mem)

private theorem point_fixed : fixedSpace (specialLinearNatural 3) pointV =
    Submodule.span (ZMod 2) {(![1,0,0] : W)} := by
  apply le_antisymm
  · intro v hv
    have h1 := congrFun (hv ⟨t01, t01_mem⟩) 0
    have h2 := congrFun (hv ⟨t02, t02_mem⟩) 0
    change t01.val.mulVec v 0 = v 0 at h1
    change t02.val.mulVec v 0 = v 0 at h2
    simp [t01, t02, mulVec, dotProduct, Fin.sum_univ_three] at h1 h2
    apply Submodule.mem_span_singleton.mpr
    refine ⟨v 0, ?_⟩
    ext j
    fin_cases j <;> simp [h1, h2]
  · apply Submodule.span_le.mpr
    rintro v (rfl : v = _)
    intro g
    change g.val.val.mulVec ![1,0,0] = _
    have hg : pointCorePred g := g.property
    ext j
    fin_cases j <;> simp [mulVec, dotProduct, Fin.sum_univ_three, hg.1, hg.2.1, hg.2.2.1]

private theorem point_codim : fixedCodim (specialLinearNatural 3) pointV = 2 := by
  have hd := fixedCodim_add_finrank (specialLinearNatural 3) pointV
  rw [point_fixed, finrank_span_singleton (by decide : (![1,0,0] : W) ≠ 0)] at hd
  norm_num [Module.finrank_pi_fintype] at hd ⊢
  omega

private theorem point_parabolic_core : pointParabolicSL.pCoreIn 2 = pointV := by
  have hn : (pointA.subgroupOf pointParabolicSL).Normal := by
    constructor
    intro a ha g
    exact pointA_conj g g.property a ha
  have hle := pCoreIn_mono_of_normalizes (p := 2) pointA_le
    ((normal_subgroupOf_iff_le_normalizer pointA_le).mp hn)
  rw [point_core] at hle
  have hc : Nat.card (pointParabolicSL.pCoreIn 2) = 4 := by
    unfold pCoreIn
    rw [← Nat.card_congr ((pCore 2 pointParabolicSL).equivMapOfInjective
      pointParabolicSL.subtype pointParabolicSL.subtype_injective).toEquiv]
    exact (ParabolicCoreModel.core_data pointEquivSymmetric).2
  exact (eq_of_le_of_card_ge hle (by rw [hc, card_pointV])).symm

private theorem point_model_transport (g : SL) (i : Bool) :
    ∃ e : SL ≃* SL, pointParabolicSL.map e.toMonoidHom = modelParabolic g i := by
  cases i
  · exact ⟨MulAut.conj g, rfl⟩
  · refine ⟨diagram.trans (MulAut.conj g), ?_⟩
    change pointParabolicSL.map ((MulAut.conj g).toMonoidHom.comp diagram.toMonoidHom) = _
    rw [← Subgroup.map_map, pointParabolic_map_diagram]
    rfl

private theorem model_rankOne (g : SL) (i : Bool) :
    rankOne (modelParabolic g i) = residual (modelParabolic g i) := by
  have hk : IsPGroup 2 (MonoidHom.id SL).ker := by
    rw [MonoidHom.ker_id]
    exact IsPGroup.of_bot
  have hr := rankOne_parabolic_eq (MonoidHom.id SL) Function.surjective_id hk g i
  have hp : parabolic (MonoidHom.id SL) g i = modelParabolic g i := comap_id _
  rw [hp] at hr
  exact hr

private theorem marked_core_codim (a : SL ≃* SL) (g : SL) (i : Bool)
    (hw : ∃ w : W, w ≠ 0 ∧ ∀ k ∈ rankOne (modelParabolic g i),
      (a k).val.mulVec w = w) :
    fixedCodim ((specialLinearNatural 3).comp a.toMonoidHom)
      ((modelParabolic g i).pCoreIn 2) = 2 := by
  obtain ⟨f, hf⟩ := point_model_transport g i
  have hr : pointA.map f.toMonoidHom = rankOne (modelParabolic g i) := by
    rw [model_rankOne, ← hf, ← point_residual]
    exact map_embedded_pResidual 2 pointParabolicSL f.toMonoidHom
  have hc : pointV.map f.toMonoidHom = (modelParabolic g i).pCoreIn 2 := by
    rw [← point_parabolic_core, map_pCoreIn_of_injective 2 _ _ f.injective, hf]
  obtain ⟨E, hE | hE⟩ := marking_coordinates (f.trans a)
  · have he : ∀ k v, E.symm ((specialLinearNatural 3) k v) =
        ((specialLinearNatural 3).comp a.toMonoidHom) (f k) (E.symm v) := by
      intro k v
      apply E.injective
      rw [LinearEquiv.apply_symm_apply]
      change k.val.mulVec v = E ((a (f k)).val.mulVec (E.symm v))
      simpa only [MulEquiv.trans_apply, LinearEquiv.apply_symm_apply] using (hE k (E.symm v)).symm
    have hd := fixedCodim_map_equivariant (specialLinearNatural 3)
      ((specialLinearNatural 3).comp a.toMonoidHom) f.toMonoidHom E.symm he pointV
    rw [hc, point_codim] at hd
    exact hd.symm
  · obtain ⟨w, hw, hfix⟩ := hw
    have hz : E w = 0 := dual_no_fixed (E w) (by
      intro k hk
      rw [← hE k w]
      exact congrArg E (hfix (f k) (hr ▸ mem_map_of_mem f.toMonoidHom hk)))
    exact (hw (E.injective (hz.trans E.map_zero.symm))).elim

private def naturalCopies (a : SL ≃* SL) (m : ℕ) :
    Representation (ZMod 2) SL (Fin m → W) where
  toFun g := {
    toFun w i := (specialLinearNatural 3) (a g) (w i)
    map_add' x y := by funext i; exact map_add _ _ _
    map_smul' c x := by funext i; exact map_smul ((specialLinearNatural 3) (a g)) c (x i)
  }
  map_one' := by
    apply LinearMap.ext
    intro w
    funext i
    change (specialLinearNatural 3) (a 1) (w i) = w i
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro w
    funext i
    change (specialLinearNatural 3) (a (g*h)) (w i) =
      (specialLinearNatural 3) (a g) ((specialLinearNatural 3) (a h) (w i))
    rw [map_mul, map_mul]
    rfl

private def fixedCopiesEquiv (a : SL ≃* SL) (m : ℕ) (A : Subgroup SL) :
    fixedSpace (naturalCopies a m) A ≃ₗ[ZMod 2]
      (Fin m → fixedSpace ((specialLinearNatural 3).comp a.toMonoidHom) A) where
  toFun w i := ⟨w.val i, fun k => congrFun (w.property k) i⟩
  invFun w := ⟨fun i => (w i).val, fun k => funext fun i => (w i).property k⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem fixedCodim_naturalCopies (a : SL ≃* SL) (m : ℕ) (A : Subgroup SL) :
    fixedCodim (naturalCopies a m) A =
      m * fixedCodim ((specialLinearNatural 3).comp a.toMonoidHom) A := by
  have he := (fixedCopiesEquiv a m A).finrank_eq
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul] at he
  have hh := fixedCodim_add_finrank (naturalCopies a m) A
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, he] at hh
  have hσ := fixedCodim_add_finrank ((specialLinearNatural 3).comp a.toMonoidHom) A
  simp only [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at hσ
  nlinarith

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]

/-- The residual-fixed vector selects the natural orientation. The same
parabolic's intrinsic two-core moves two dimensions on each marked quotient copy. -/
theorem two_mul_multiplicity_le_fixedCodim
    (ρ : Representation (ZMod 2) SL V) {m : ℕ}
    (q : AbelianCore.QuotientRecognition.ModuleQuotient ρ m) (g : SL) (i : Bool)
    (hw : ∃ w : W, w ≠ 0 ∧ ∀ k ∈ rankOne (modelParabolic g i),
      (q.marking k).val.mulVec w = w) :
    2 * m ≤ fixedCodim ρ
      ((pCore 2 (modelParabolic g i)).map (modelParabolic g i).subtype) := by
  have hle := fixedCodim_le_of_equivariant_surjection ρ (naturalCopies q.marking m)
    q.projection q.surjective (fun k v => funext (q.equivariant k v))
    ((modelParabolic g i).pCoreIn 2)
  rw [fixedCodim_naturalCopies, marked_core_codim q.marking g i hw] at hle
  simpa only [pCoreIn, Nat.mul_comm] using hle

/-- A codimension bound of two at this same parabolic leaves at most one copy.
No FF condition or vanishing of the original fixed space is required. -/
theorem multiplicity_le_one_of_parabolicBounds
    (ρ : Representation (ZMod 2) SL V) {m : ℕ}
    (q : AbelianCore.QuotientRecognition.ModuleQuotient ρ m) (g : SL) (i : Bool)
    (h : ParabolicBounds ρ q.marking g i) : m ≤ 1 := by
  have hl := two_mul_multiplicity_le_fixedCodim ρ q g i h.fixed_vector
  have hu := h.codimension
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
