module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.XiFixed
public import Theory.Representation.QuadraticDuality
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# Full movement of the original doubled module by X

The invariant nondegenerate source form identifies the module with its
contragredient. The checked equality C_W(X)=1 therefore makes the literal
commutator [W,X] equal W. Since W lies in T and T normalizes X, W lies in X;
normal elementary containment then gives W <= O₂(X).

The original action projection and module are retained throughout. No MS
premise is used. `Swapped.NormalModule` applies the containment to the
remaining contrary ambient-Sylow configuration. The ambient exclusion,
fusion and closure remain with qt-d-double-natural-pure-fusion; the original
fixed-subgroup MS premise stays with qt-rank-two-ms93 and final assembly
qt-d-double-natural-centralizers.
Source: Aschbacher--Smith 12.1.4, printed p.790, the plane parabolic of
B.4.9(2iii), pp.92,94, and the invariant form of H.9.1, p.389.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative

private theorem moved_eq_top_of_invariant_form
    {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (ρ : Representation (ZMod 2) A E) (q : QuadraticForm (ZMod 2) E)
    (hq : q.polarBilin.Nondegenerate) (hinv : ∀ a v, q (ρ a v) = q v)
    (hfix : ρ.invariants = ⊥) : Coinvariants.ker ρ = ⊤ := by
  let e := LinearMap.BilinForm.toDual q.polarBilin hq
  have hp (a : A) (v w : E) : q.polarBilin (ρ a v) (ρ a w) = q.polarBilin v w := by
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ←map_add, hinv]
  have he (a : A) (v : E) : e (ρ a v) = ρ.dual a (e v) := by
    ext w
    change q.polarBilin (ρ a v) w = q.polarBilin v (ρ a⁻¹ w)
    simpa only [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,
      Module.End.one_apply] using hp a v (ρ a⁻¹ w)
  have hz : ρ.dual.invariants = ⊥ := by
    apply bot_unique
    intro z hz
    have hc : e.symm z ∈ ρ.invariants := by
      intro a
      apply e.injective
      rw [he,e.apply_symm_apply]
      exact hz a
    have h0 : e.symm z = 0 := by simpa only [hfix,Submodule.mem_bot] using hc
    exact e.symm.injective (h0.trans e.symm.map_zero.symm)
  exact Submodule.dualAnnihilator_eq_bot_iff.mp
    ((dualAnnihilator_coinvariantsKer ρ).trans hz)

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {B : DoubledBranch T L V 4}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
/-- The literal Xi residual moves the whole original doubled module. -/
theorem four_xi_module_commutator
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hm : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G)) :
    ⁅componentOrbit V (T : Subgroup G),PureFourXi.residual T L⁆ =
      componentOrbit V (T : Subgroup G) := by
  let W := componentOrbit V (T : Subgroup G)
  let X := PureFourXi.residual T L
  have hXM : X ≤ normalizer (L : Set G) :=
    (map_subtype_le _).trans (inf_le_right.trans (sup_le L.le_normalizer hTM))
  have hXW : X ≤ normalizer (W : Set G) := by
    dsimp only [W]
    rw [B.orbit_eq]
    exact hXM.trans (le_normalizer_componentOrbit _ _)
  let f := B.actionProjection.comp (inclusion hXM)
  let ρ : Representation (ZMod 2) X (Additive W) := S.setup.representation.comp f
  have hf : ρ.invariants = ⊥ := by
    apply bot_unique
    intro w hw
    have hC : w.toMul.val ∈ W ⊓ centralizer (X : Set G) := by
      refine ⟨w.toMul.property,?_⟩
      intro x hx
      have hh := hw ⟨x,hx⟩
      change S.setup.representation (f ⟨x,hx⟩) w = w at hh
      rw [S.representation_eq] at hh
      have he := congrArg (fun z : Additive W => (z.toMul : G)) hh
      change (B.quotientAction (B.actionProjection (inclusion hXM ⟨x,hx⟩)) w.toMul : G) = w.toMul at he
      rw [B.quotientAction_projection_apply] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    have h0 : w.toMul.val = 1 := mem_bot.mp
      ((S.four_xi_centralizer_eq_bot hTM hWT hm) ▸ hC)
    exact Subtype.ext h0
  have hmoved : Coinvariants.ker ρ = ⊤ :=
    moved_eq_top_of_invariant_form ρ S.setup.quadratic S.setup.quadratic_invariant.1
      (fun x v => S.setup.quadratic_invariant.2.2 (f x) v) hf
  have hc := commutator_image_eq S.setup.representation W W X hXW le_rfl f
    (MonoidHom.id W) (fun x v => by rw [S.representation_eq]; rfl) ⊤ (by
      ext x
      simp [binarySubgroup])
  rw [Subgroup.map_id,MonoidHom.range_eq_map,
    ←subspaceCommutator_comp_map,subspaceCommutator_top_eq_coinvariants] at hc
  have he : Coinvariants.ker (ρ.comp (⊤ : Subgroup X).subtype) = Coinvariants.ker ρ := by
    unfold Coinvariants.ker
    congr 1
    ext v
    constructor
    · rintro ⟨⟨a,w⟩,rfl⟩
      exact ⟨(a.val,w),rfl⟩
    · rintro ⟨⟨a,w⟩,rfl⟩
      exact ⟨(⟨a,mem_top a⟩,w),rfl⟩
  rw [he,hmoved] at hc
  have hct : (⁅W,X⁆).subgroupOf W = ⊤ := by simpa [binarySubgroup] using hc
  have hle := le_normalizer_iff_commutator_le_left.mp hXW
  have hz := congrArg (Subgroup.map W.subtype) hct
  simpa only [map_subgroupOf_eq_of_le hle,←MonoidHom.range_eq_map,range_subtype] using hz

include S in
/-- Full movement places the original module in the smaller residual core. -/
theorem four_orbit_le_xi_core
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hm : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G)) :
    componentOrbit V (T : Subgroup G) ≤ (PureFourXi.residual T L).pCoreIn 2 := by
  let W := componentOrbit V (T : Subgroup G)
  let X := PureFourXi.residual T L
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) :=
    (PureFourXi.sylow_le_normalizerJoin T L).trans
      (le_normalizer_embedded_pResidual 2 (PureFourXi.normalizerJoin T L))
  have hWX : W ≤ X := by
    exact (S.four_xi_module_commutator hTM hWT hm).symm.le.trans
      (le_normalizer_iff_commutator_le_right.mp (hWT.trans hTX))
  have hXW : X ≤ normalizer (W : Set G) := by
    dsimp only [W]
    rw [B.orbit_eq]
    exact ((map_subtype_le _).trans
      (inf_le_right.trans (sup_le L.le_normalizer hTM))).trans
        (le_normalizer_componentOrbit _ _)
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 W) hWX hXW

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
