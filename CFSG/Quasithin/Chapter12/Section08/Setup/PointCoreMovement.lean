module

public import CFSG.Quasithin.Chapter12.Section08.Setup.NaturalActions
public import Theory.SpecificGroups.PSL3Two.Parabolics.Actions
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals
public import Theory.GroupTheory.PCoreImage

/-!
# Movement by the original point-parabolic two-core

For a natural L₃(2) action, the two-core of L₁ does not centralize the
seed module. Choose coordinates sending the original flag point to the
standard point. The normalizer then maps onto the standard point parabolic,
its two-residual maps onto A₄, and its two-core maps onto the nontrivial V₄.
The kernel of the original natural action is a two-group, so these core
images refer to the original subgroup and conjugation action.

This supplies the parabolic movement used in Aschbacher–Smith,
Lemma 13.3.14(c), printed pp.891–892, for the natural L₃(2) branch.
-/

public section
noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {V L : Subgroup G}
  (F : InvariantFlag T V 3) [IsElementaryAbelian 2 V]
  {hLV : L ≤ normalizer (V : Set G)} (A : AmbientNaturalMarking L hLV 3)

omit [Finite G] [IsElementaryAbelian 2 V] in
private theorem exists_point :
    ∃ z : Additive V, z ≠ 0 ∧ ∀ v : Additive V,
      (v.toMul : G) ∈ F.Vi 1 ↔ v = 0 ∨ v = z := by
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨u, hu, hall⟩ := (Nat.card_eq_two_iff' (1 : F.Vi 1)).mp hc
  let z : Additive V := Additive.ofMul ⟨u, F.le_seed 1 u.property⟩
  refine ⟨z, ?_, ?_⟩
  · intro he
    apply hu
    exact Subtype.ext (congrArg (fun v : Additive V => (v.toMul : G)) he)
  · intro v
    constructor
    · intro hv
      by_cases he : v = 0
      · exact Or.inl he
      · right
        have heq := hall ⟨v.toMul, hv⟩ (fun h =>
          he (Additive.toMul.injective (Subtype.ext (congrArg (fun a : F.Vi 1 => (a : G)) h))))
        exact Additive.toMul.injective (Subtype.ext (congrArg (fun a : F.Vi 1 => (a : G)) heq))
    · rintro (rfl | rfl)
      · exact one_mem _
      · exact u.property

omit [Finite G] in
private theorem action_apply (l : L) (v : Additive V) :
    A.geometryAction.action l v = Additive.ofMul ⟨(l : G) * v.toMul * (l : G)⁻¹,
      (mem_normalizer_iff.mp (hLV l.property) v.toMul).mp v.toMul.property⟩ := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact A.geometryAction.conjugation l v

omit [Finite G] in
private theorem mem_pointNormalizer_iff (z : Additive V) (hz0 : z ≠ 0)
    (hz : ∀ v : Additive V, (v.toMul : G) ∈ F.Vi 1 ↔ v = 0 ∨ v = z) (l : L) :
    (l : G) ∈ F.H ↔ A.geometryAction.action l z = z := by
  constructor
  · intro hl
    have hmem : ((A.geometryAction.action l z).toMul : G) ∈ F.Vi 1 := by
      rw [action_apply]
      exact (mem_normalizer_iff.mp hl z.toMul).mp ((hz z).mpr (Or.inr rfl))
    rcases (hz _).mp hmem with hzero | heq
    · exact False.elim (hz0 ((A.geometryAction.action l).map_eq_zero_iff.mp hzero))
    · exact heq
  · intro hl
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      have hxV := F.le_seed 1 hx
      let v : Additive V := Additive.ofMul ⟨x, hxV⟩
      have hm : ((A.geometryAction.action l v).toMul : G) ∈ F.Vi 1 := by
        apply (hz _).mpr
        rcases (hz v).mp hx with hv | hv
        · exact Or.inl (by rw [hv, map_zero])
        · exact Or.inr (by rw [hv, hl])
      rw [action_apply] at hm
      exact hm
    · intro hx
      have hxV : x ∈ V :=
        (mem_normalizer_iff.mp (hLV l.property) x).mpr (F.le_seed 1 hx)
      let v : Additive V := Additive.ofMul ⟨x, hxV⟩
      have hm : ((A.geometryAction.action l v).toMul : G) ∈ F.Vi 1 := by
        rw [action_apply]
        exact hx
      apply (hz v).mpr
      rcases (hz _).mp hm with he | he
      · exact Or.inl ((A.geometryAction.action l).map_eq_zero_iff.mp he)
      · exact Or.inr ((A.geometryAction.action l).injective (he.trans hl.symm))

include A in
omit [Finite G] in
private theorem exists_point_coordinates (z : Additive V) (hz : z ≠ 0) :
    ∃ β : Additive V ≃ₗ[ZMod 2] (Fin 3 → ZMod 2), β z = ![1, 0, 0] := by
  let x := A.coordinates z
  let y : Fin 3 → ZMod 2 := ![1, 0, 0]
  have hx : x ≠ 0 := fun he => hz (A.coordinates.map_eq_zero_iff.mp he)
  have hy : y ≠ 0 := by decide
  let ex := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Fin 3 → ZMod 2) x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) (Fin 3 → ZMod 2) y hy
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨A.coordinates.trans g, ?_⟩
  have he := hg (ex 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at he
  simpa [ex, ey, x, y] using he.symm

include A in
/-- The actual embedded two-core of the point residual moves the original
three-dimensional seed module under its natural L₃(2) action. -/
theorem point_core_moves_seed_of_natural :
    ¬ (F.Li L 1).pCoreIn 2 ≤ centralizer (V : Set G) := by
  obtain ⟨z, hz0, hz⟩ := exists_point F
  obtain ⟨β, hβ⟩ := exists_point_coordinates A z hz0
  let d := A.geometryAction
  let e := BinaryLinear.OuterCyclic.slEquivLinear 3
  let b := BinaryLinear.SmallParabolicLevi.linearGroupCongr β
  let f : L →* Matrix.PSL3Two.SL := e.symm.toMonoidHom.comp (b.toMonoidHom.comp d.action)
  have hf : Function.Surjective f := e.symm.surjective.comp (b.surjective.comp d.surjective)
  have hfk : f.ker = pCore 2 L := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective,
      MonoidHom.ker_comp_of_injective _ _ b.injective, d.kernel]
  have hfa (l : L) (v : Additive V) :
      (f l).val.mulVec (β v) = β (d.action l v) := by
    have he := congrArg (fun g : BinaryLinear.OuterCyclic.LinearGroup 3 => g (β v))
      (e.apply_symm_apply (b (d.action l)))
    change (BinaryLinear.OuterCyclic.slEquivLinear 3 (f l)) (β v) =
      (BinaryLinear.SmallParabolicLevi.linearGroupCongr β (d.action l)) (β v) at he
    simpa only [BinaryLinear.OuterCyclic.slEquivLinear_apply,
      BinaryLinear.SmallParabolicLevi.linearGroupCongr_apply, β.symm_apply_apply] using he
  have hfp (l : L) : f l ∈ Matrix.PSL3Two.pointParabolicSL ↔ (l : G) ∈ F.H := by
    rw [← Matrix.PSL3Two.Fano.stabilizer_flagPoint_SL,
      MulAction.mem_stabilizer_iff, Subtype.ext_iff]
    change (f l).val.mulVec ![1, 0, 0] = ![1, 0, 0] ↔ _
    rw [← hβ, hfa, β.injective.eq_iff]
    exact (mem_pointNormalizer_iff F A z hz0 hz l).symm
  let S : Subgroup L := F.H.subgroupOf L
  have hS : S.map f = Matrix.PSL3Two.pointParabolicSL := by
    ext g
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact (hfp l).mpr hl
    · intro hg
      obtain ⟨l, rfl⟩ := hf g
      exact ⟨l, (hfp l).mp hg, rfl⟩
  let K : Subgroup L := (pResidual 2 S).map S.subtype
  have hK : K.map f = Matrix.PSL3Two.MarkedAutomorphisms.pointA := by
    dsimp only [K]
    rw [map_embedded_pResidual, hS]
    exact Matrix.PSL3Two.MarkedAutomorphisms.point_residual
  have hLi : K.map L.subtype = F.Li L 1 := by
    dsimp only [K]
    rw [map_embedded_pResidual]
    have hSL : S.map L.subtype = L ⊓ F.H := by
      simp only [S, subgroupOf_map_subtype, inf_comm]
    rw [hSL]
    simp only [InvariantFlag.Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide, ↓reduceIte]
    rfl
  have hcore : (K.pCoreIn 2).map f = Matrix.PSL3Two.MarkedAutomorphisms.pointV := by
    rw [map_pCoreIn_of_ker_isPGroup f (hfk ▸ pCore_isPGroup) K,
      hK, Matrix.PSL3Two.MarkedAutomorphisms.point_core]
  have hcoreG : (K.pCoreIn 2).map L.subtype = (F.Li L 1).pCoreIn 2 := by
    rw [map_pCoreIn_of_injective 2 K L.subtype L.subtype_injective, hLi]
  intro hcentral
  have hk : K.pCoreIn 2 ≤ f.ker := by
    intro k hk
    have hg : (k : G) ∈ (F.Li L 1).pCoreIn 2 :=
      hcoreG ▸ mem_map_of_mem L.subtype hk
    have hc := hcentral hg
    rw [hfk, ← d.kernel, MonoidHom.mem_ker]
    apply LinearEquiv.ext
    intro v
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((d.action k v).toMul : G) = (v.toMul : G)
    rw [d.conjugation, ← hc v.toMul v.toMul.property, mul_inv_cancel_right]
  have hzcore : Matrix.PSL3Two.MarkedAutomorphisms.pointV = ⊥ :=
    hcore.symm.trans ((Subgroup.map_eq_bot_iff _).mpr hk)
  have hcard := Matrix.PSL3Two.MarkedAutomorphisms.card_pointV
  rw [hzcore, Subgroup.card_bot] at hcard
  norm_num at hcard

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
