module
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Cardinality

/-!
# Sylow invariance of the two residual factors

Conjugation by T induces an automorphism on the literal I/O₂(I). A normal
symmetric-three subgroup of S₃ × S₃ is a coordinate factor, so each such
conjugation permutes the two factors. Pullback and O² commute with the actual
ambient conjugation; hence the source residuals are permuted as well.
This supplies the T-invariance step in the center splitting of 15.3.55.

Source: Aschbacher–Smith, 15.3.55, printed p.1146.
-/

@[expose] public noncomputable section
open Subgroup InvertedCubicTensor
open Representation.BinaryQuadraticPair
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry
open CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Chapter15Collapse

private def factor_equiv_left : ProductDecomposition.leftFactor ≃* S₃ :=
  ((Subgroup.prodEquiv _ _).trans MulEquiv.prodUnique).trans Subgroup.topEquiv

private theorem factors_ne : ProductDecomposition.leftFactor ≠ ProductDecomposition.rightFactor := by
  intro he
  have hm : (Equiv.swap 0 1, (1 : S₃)) ∈ ProductDecomposition.leftFactor := ⟨mem_top _, rfl⟩
  rw [he] at hm
  have h : (Equiv.swap (0 : Fin 3) 1 : S₃) = 1 := hm.1
  have h' := congrArg (fun x : S₃ => x 0) h
  norm_num at h'

/-- Every automorphism permutes the two actual coordinate factors. -/
private theorem automorphism_permutates_factors (e : MulAut (S₃ × S₃)) :
    (ProductDecomposition.leftFactor.map e.toMonoidHom = ProductDecomposition.leftFactor ∧
      ProductDecomposition.rightFactor.map e.toMonoidHom = ProductDecomposition.rightFactor) ∨
    (ProductDecomposition.leftFactor.map e.toMonoidHom = ProductDecomposition.rightFactor ∧
      ProductDecomposition.rightFactor.map e.toMonoidHom = ProductDecomposition.leftFactor) := by
  have classify (K : Subgroup (S₃ × S₃)) [K.Normal] (hK : K ≃* S₃) :
      K.map e.toMonoidHom = ProductDecomposition.leftFactor ∨
      K.map e.toMonoidHom = ProductDecomposition.rightFactor := by
    let : (K.map e.toMonoidHom).Normal := (inferInstance : K.Normal).map _ e.surjective
    exact Theory.GroupTheory.PermThreeProduct.normal_subgroup_eq_factor _
      ((e.subgroupMap K).symm.trans hK)
  have hr : ProductDecomposition.rightFactor ≃* S₃ :=
    ((Subgroup.prodEquiv _ _).trans MulEquiv.uniqueProd).trans Subgroup.topEquiv
  have hn : ProductDecomposition.leftFactor.map e.toMonoidHom ≠
      ProductDecomposition.rightFactor.map e.toMonoidHom :=
    fun h => factors_ne (map_injective e.injective h)
  rcases classify ProductDecomposition.leftFactor factor_equiv_left with hl | hl <;>
    rcases classify ProductDecomposition.rightFactor hr with hr | hr
  · exact (hn (hl.trans hr.symm)).elim
  · exact Or.inl ⟨hl,hr⟩
  · exact Or.inr ⟨hl,hr⟩
  · exact (hn (hl.trans hr.symm)).elim

variable {G : Type*} [Group G]

/-- A compatible automorphism carries each marked factor preimage to the
preimage of its literal factor image. -/
theorem actorPreimage_map_conj {I : Subgroup G} (π : I →* S₃ × S₃)
    (t : G) (a : MulAut I) (e : MulAut (S₃ × S₃))
    (ha : ∀ i : I, (a i : G) = t * i * t⁻¹)
    (he : ∀ i : I, e (π i) = π (a i)) (K : Subgroup (S₃ × S₃)) :
    (actorPreimage π K).map (MulAut.conj t).toMonoidHom =
      actorPreimage π (K.map e.toMonoidHom) := by
  ext x
  constructor
  · rintro ⟨v, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨a i, ⟨π i, hi, he i⟩, ha i⟩
  · rintro ⟨i, ⟨k,hk,hki⟩, rfl⟩
    have hj : π (a.symm i) = k := by
      apply e.injective
      rw [he, a.apply_symm_apply]
      exact hki.symm
    refine ⟨(a.symm i : G), ⟨a.symm i, by change π (a.symm i) ∈ K; rw [hj]; exact hk, rfl⟩, ?_⟩
    exact (ha (a.symm i)).symm.trans (congrArg Subtype.val (a.apply_symm_apply i))

/-- The residual functor preserves this same ambient conjugation. -/
theorem oddFactor_map_conj [Finite G] {I : Subgroup G} (π : I →* S₃ × S₃)
    (Y : Subgroup G) (t : G) (a : MulAut I) (e : MulAut (S₃ × S₃))
    (hY : t ∈ normalizer (Y : Set G))
    (ha : ∀ i : I, (a i : G) = t * i * t⁻¹)
    (he : ∀ i : I, e (π i) = π (a i)) (K : Subgroup (S₃ × S₃)) :
    (oddFactor π Y K).map (MulAut.conj t).toMonoidHom =
      oddFactor π Y (K.map e.toMonoidHom) := by
  have hY' : Y.map (MulAut.conj t).toMonoidHom = Y :=
    mem_normalizer_iff_map_conj_eq.mp hY
  unfold oddFactor
  rw [map_embedded_pResidual, map_inf _ _ _ (MulAut.conj t).injective,
    hY', actorPreimage_map_conj π t a e ha he]

/-- The actual source residual factors are preserved or exchanged by every
element of T. No assumption about a chosen factor-exchanging involution is used. -/
theorem residual_factors_permuted [Finite G] {D : CFSG.Quasithin.ChapterG.Section02.Setup G}
    {g : G} (d : Hypothesis D g) (t : G) (ht : t ∈ D.T) :
    let π := moduleProjection d.quotientSymmetricEquiv
    let X₁ := oddFactor π D.L ProductDecomposition.leftFactor
    let X₂ := oddFactor π D.L ProductDecomposition.rightFactor
    ((X₁.map (MulAut.conj t).toMonoidHom = X₁ ∧
      X₂.map (MulAut.conj t).toMonoidHom = X₂) ∨
    (X₁.map (MulAut.conj t).toMonoidHom = X₂ ∧
      X₂.map (MulAut.conj t).toMonoidHom = X₁)) := by
  let a : MulAut (D.I g) := (D.I g).normalizerMonoidHom
    ⟨t, (d.LT_normalizes_I_of_star d.star_I_eq_star_LU) (mem_sup_right ht)⟩
  let e : MulAut (S₃ × S₃) := d.quotientSymmetricEquiv.symm.trans
    ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans d.quotientSymmetricEquiv)
  let π := moduleProjection d.quotientSymmetricEquiv
  have ha (i : D.I g) : (a i : G) = t * i * t⁻¹ := rfl
  have he (i : D.I g) : e (π i) = π (a i) := by
    simp only [e, π, moduleProjection, MulEquiv.trans_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have hmap (K : Subgroup (S₃ × S₃)) :=
    oddFactor_map_conj π D.L t a e (d.base.T_normalizes_L ht) ha he K
  change ((oddFactor π D.L ProductDecomposition.leftFactor).map _ = _ ∧ _) ∨ _
  rcases automorphism_permutates_factors e with hp | hp
  · left
    exact ⟨(hmap _).trans (congrArg (oddFactor π D.L) hp.1),
      (hmap _).trans (congrArg (oddFactor π D.L) hp.2)⟩
  · right
    exact ⟨(hmap _).trans (congrArg (oddFactor π D.L) hp.1),
      (hmap _).trans (congrArg (oddFactor π D.L) hp.2)⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry
