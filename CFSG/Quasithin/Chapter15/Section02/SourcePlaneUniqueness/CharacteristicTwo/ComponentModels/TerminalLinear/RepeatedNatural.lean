module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.SeedCentralizer
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.RepeatedNatural.Seed
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.RepeatedNatural.FourExclusion
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.TerminalLinear.OrthogonalExclusion

/-!
# The surviving repeated-natural case in degree five

The original Sylow fixes U∩ZS, which generates U. Its actual pointwise
centralizer is M₁, and the repeated-natural calculation identifies the
image of M₁ with a natural point stabilizer under the same marking.

The literal row consumer combines this identification with the proved
natural-dual, orthogonal-six and degree-four exclusions. It leaves only
repeated-natural degree five and exterior-five. Constructing the final
minimal parabolic and the exterior cubic subgroup remains necessary;
the four-row recognition on U is still an explicit input.

Source: Aschbacher--Smith, 15.2.23, printed pp.1116--1117.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.TerminalLinear
open ChapterB.QuasisimpleSource Section01
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- In row (a), the image of the literal M₁ is the natural point parabolic. -/
theorem M1_image_pointStabilizer_of_repeatedNatural
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G))
    {n r : ℕ} (hdegree : 2 ≤ n) (hr : 0 < r) :
    letI := U_elementary d hI hfit hXI
    ∀ e : ActionEquiv (U_representation d hI hfit hXI hn)
      (repeated (linearNatural BinaryField.two n) r),
    ∃ v : Fin n → ZMod 2, v ≠ 0 ∧
      (((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
        e.groupEquiv.toMonoidHom =
        MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) v := by
  let := U_elementary d hI hfit hXI
  intro e
  let σ := U_representation d hI hfit hXI hn
  let q := QuotientGroup.mk' (pCore 2 X)
  let : (X.subgroupOf I).Normal := normal_subgroupOf_of_le_normalizer hn
  obtain ⟨S,hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (d.sylow_in_escape hI) hXI (inferInstance : (X.subgroupOf I).Normal).isSubnormal
  let P := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let Z := AddSubgroup.toZModSubmodule 2 (ZS.subgroupOf (U X ZS)).toAddSubgroup
  have hZ : Z ≤ fixedSpace σ P := by
    intro u hu p
    obtain ⟨x,hx,he⟩ := p.property
    change σ (p : X ⧸ pCore 2 X) u = u
    rw [← he]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [U_representation_apply]
    have hxc : (x : G) ∈ centralizer (ZS : Set G) :=
      ((hS.le.trans inf_le_left) (mem_map_of_mem X.subtype hx)).2
    have hh : (u.toMul : G) * (x : G) = (x : G) * (u.toMul : G) := hxc _ hu
    rw [← hh, mul_inv_cancel_right]
  rw [M1_image_eq_seedKernel d hI hfit hXI hn]
  exact repeatedNatural_seedKernel σ hdegree hr e P Z hZ
    (U_seed_module_generates d hI hfit hXI hn σ (U_representation_apply d hI hfit hXI hn))

/-- After all completed exclusions, row (a) has degree five and its original
M₁ is marked as the point parabolic. The exterior-five alternative is unchanged. -/
theorem remaining_rows_in_degree_five
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (hXI : X ≤ I) (hn : I ≤ normalizer (X : Set G)) (hout : ¬ X ≤ Mc)
    (hKX : (pResidual 2 H).map H.subtype ≤ X)
    (hpair : Nonempty ((KS H T ZS ⧸ pCore 2 (KS H T ZS)) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    letI := U_elementary d hI hfit hXI
    let σ := U_representation d hI hfit hXI hn
    ModuleRow σ →
      (∃ r : ℕ, 0 < r ∧ r ≤ 4 ∧
        ∃ e : ActionEquiv σ (repeated (linearNatural BinaryField.two 5) r),
        ∃ v : Fin 5 → ZMod 2, v ≠ 0 ∧
          (((M1 X ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
            e.groupEquiv.toMonoidHom =
            MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) v) ∨
      (∃ r : ℕ, (r = 2 ∨ r = 3) ∧ IsIrreducible σ ∧
        Module.finrank (ZMod 2) (Additive (U X ZS)) = 10 ∧
        Nonempty (ActionEquiv σ (Representation.SL5TenDimensional.exteriorAction r))) := by
  let := U_elementary d hI hfit hXI
  dsimp only
  intro hrow
  rcases remaining_rows_after_orthogonal d hI hfit hXI hn hout hKX hpair hrow with h | h
  · obtain ⟨n,r,hd,hp,hb,⟨e⟩⟩ := h
    rcases hd with rfl | rfl
    · exact (not_repeatedNatural_four_canonical d hI hfit hXI hn hKX hpair r hp ⟨e⟩).elim
    · exact Or.inl ⟨r,hp,hb,e,
        M1_image_pointStabilizer_of_repeatedNatural d hI hfit hXI hn (by decide) hp e⟩
  · exact Or.inr h

end CFSG.Quasithin.Chapter15.Section02.TerminalLinear
