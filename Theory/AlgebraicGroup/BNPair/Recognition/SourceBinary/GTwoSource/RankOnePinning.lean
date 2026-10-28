module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.RankOneFaithfulness
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.SimpleCoordinates
public import Theory.SpecificGroups.PSL2.SemilinearCoverage.RootParameters

/-!
# Whole rank-one maps extending the source simple-root coordinates

The existing additive Sylow coordinates are composites of Sylow conjugacies.
Extend those conjugacies to the entire SL₂ group and then invert the faithful
source panel projection. This constructs an actual isomorphism SL₂(F) ≃ Rᵢ
whose upper unipotents are exactly the previously constructed simpleParameter,
including when F has two elements. Its range is the full source Rᵢ.

The literal matrix word, torus action and involution are transported along
this same map. Relabeling by a field automorphism acts on the entire pinning:
it changes both root and torus parameters and fixes the Weyl matrix.

This is the initial rank-one labeling step of Fong--Seitz II §7, printed
p.192, with the change of labeling in §8, printed p.197. Alignment of this
pinning's torus with H ∩ Rᵢ and of its reflection with the source N is still
required. The natural/tensor module comparison of (9.9)--(9.15) and mixed
root equations are not consequences asserted here.
-/

@[expose] public noncomputable section
open Subgroup Theory.PSL2.SemilinearCoverage
open scoped MatrixGroups
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
open MulAction in
private theorem sylow_equiv_conjugation {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] [Finite (Sylow p G)]
    (P Q : Sylow p G) :
    ∃ g : G, ∀ x : P, (P.equiv Q x : G) = g * x * g⁻¹ := by
  classical
  let g := Classical.choose (exists_smul_eq G P Q)
  have hg : g • P = Q := Classical.choose_spec (exists_smul_eq G P Q)
  refine ⟨g, ?_⟩
  have hh (Q' : Sylow p G) (he : g • P = Q') (x : P) :
      ((Eq.mpr (congrArg (fun T : Sylow p G => P ≃* T) he.symm)
        (P.equivSMul g)) x : G) = g * x * g⁻¹ := by
    cases he
    rfl
  intro x
  exact hh Q hg x

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
theorem exists_linear_sylow_extension (T : Sylow 2 PSL(2,F)) :
    ∃ e : SL2 F ≃* PSL(2,F), ∀ a : F,
      e (uni a) = (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive T (.ofAdd a) : PSL(2,F)) := by
  let U := Matrix.SpecialLinearGroup.upperUnipotentSylow F 2
  let e := BenderSuzuki.ZD.Linear.sl2QuotientEquiv F
  let V := U.mapSurjective e.surjective
  obtain ⟨c,hc⟩ := sylow_equiv_conjugation U U
  obtain ⟨b,hb⟩ := sylow_equiv_conjugation V T
  refine ⟨((MulAut.conj c).trans e).trans (MulAut.conj b), ?_⟩
  intro a
  dsimp only [BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive, MulEquiv.trans_apply]
  rw [hb]
  change b * e (c * uni a * c⁻¹) * b⁻¹ = _
  apply congrArg (fun x : PSL(2,F) => b*x*b⁻¹)
  change e (c * uni a * c⁻¹) =
    e (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 U (.ofAdd a))
  congr 1
  exact (hc ⟨uni a, ⟨.ofAdd a,rfl⟩⟩).symm

open RootCoordinates HexagonStructure
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (i : Fin 2) (hV : simpleRemainder Q split i ≤ localKernel Q i)
  (μ : localGroup Q split i ≃* PSL(2,F))

/-- Extend the already chosen additive simple-root coordinates to all of SL₂. -/
def sourcePinning : SL2 F ≃* rankOne Q split i :=
  (((exists_linear_sylow_extension (linearSylow Q split i μ)).choose).trans μ.symm).trans
    (rankOnePanelEquiv Q split i hV μ).symm

theorem sourcePinning_panel (g : SL2 F) :
    μ (RootLocalCover.projection Q split i (sourcePinning Q split i hV μ g)) =
      (exists_linear_sylow_extension (linearSylow Q split i μ)).choose g := by
  change μ (rankOnePanelEquiv Q split i hV μ (sourcePinning Q split i hV μ g)) = _
  simp only [sourcePinning, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]

private theorem projection_simple (u : simpleRoot Q split i) :
    RootLocalCover.projection Q split i (inclusion (show simpleRoot Q split i ≤
      rankOne Q split i from le_sup_left) u) = simpleRootLocalMap Q split i u := by
  apply Subtype.ext
  rw [RootLocalCover.projection_apply, localAction_eq_panelAction, simpleRootLocalMap_apply]
  rfl

theorem sourcePinning_root (a : F) :
    (sourcePinning Q split i hV μ (uni a) : X ⧸ Q.D) =
      simpleParameter Q split i hV μ (.ofAdd a) := by
  let u := simpleRootFieldEquiv Q split i hV μ (.ofAdd a)
  suffices sourcePinning Q split i hV μ (uni a) =
      inclusion (show simpleRoot Q split i ≤ rankOne Q split i from le_sup_left) u by
    exact congrArg Subtype.val this
  apply rankOne_projection_injective Q split i hV μ
  apply μ.injective
  rw [sourcePinning_panel, projection_simple]
  exact ((exists_linear_sylow_extension (linearSylow Q split i μ)).choose_spec a).trans
    (simpleRootFieldEquiv_model Q split i hV μ (.ofAdd a)).symm

def sourcePinningHom : SL2 F →* X ⧸ Q.D :=
  (rankOne Q split i).subtype.comp (sourcePinning Q split i hV μ).toMonoidHom

@[simp] theorem sourcePinningHom_root (a : F) :
    sourcePinningHom Q split i hV μ (uni a) = simpleParameter Q split i hV μ (.ofAdd a) :=
  sourcePinning_root Q split i hV μ a

theorem sourcePinningHom_injective : Function.Injective (sourcePinningHom Q split i hV μ) :=
  Subtype.val_injective.comp (sourcePinning Q split i hV μ).injective

theorem sourcePinningHom_range : (sourcePinningHom Q split i hV μ).range = rankOne Q split i := by
  rw [sourcePinningHom, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (sourcePinning Q split i hV μ).surjective,
    ← MonoidHom.range_eq_map, range_subtype]

def pinnedReflection : X ⧸ Q.D := sourcePinningHom Q split i hV μ (weyl F)
def pinnedTorus (a : Fˣ) : X ⧸ Q.D := sourcePinningHom Q split i hV μ (tor a)

theorem pinnedReflection_mem : pinnedReflection Q split i hV μ ∈ rankOne Q split i :=
  (sourcePinning Q split i hV μ (weyl F)).property

theorem pinnedReflection_sq : pinnedReflection Q split i hV μ * pinnedReflection Q split i hV μ = 1 := by
  rw [pinnedReflection, ← map_mul, weyl_sq, map_one]

omit [Finite F] in
private theorem matrix_rankOne_word (a : Fˣ) :
    uni (a : F) * (weyl F * uni (↑a⁻¹ : F) * (weyl F)⁻¹) * uni (a : F) =
      tor a * weyl F := by
  rw [show (weyl F)⁻¹ = weyl F from inv_eq_of_mul_eq_one_right weyl_sq]
  apply Subtype.ext
  ext j k
  fin_cases j <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]

theorem pinned_rankOne_word (a : Fˣ) :
    simpleParameter Q split i hV μ (.ofAdd (a : F)) *
      (pinnedReflection Q split i hV μ * simpleParameter Q split i hV μ (.ofAdd (↑a⁻¹ : F)) *
        (pinnedReflection Q split i hV μ)⁻¹) * simpleParameter Q split i hV μ (.ofAdd (a : F)) =
      pinnedTorus Q split i hV μ a * pinnedReflection Q split i hV μ := by
  simp only [← sourcePinningHom_root, pinnedReflection, pinnedTorus,
    ← map_inv, ← map_mul, matrix_rankOne_word]

theorem pinnedTorus_root (a : Fˣ) (b : F) :
    pinnedTorus Q split i hV μ a * simpleParameter Q split i hV μ (.ofAdd b) *
      (pinnedTorus Q split i hV μ a)⁻¹ =
        simpleParameter Q split i hV μ (.ofAdd ((a : F)^2*b)) := by
  simp only [← sourcePinningHom_root, pinnedTorus, ← map_inv, ← map_mul]
  apply congrArg (sourcePinningHom Q split i hV μ)
  exact Borel_conj_uni (by rw [mem_Borel_iff]; rfl) b

/-- A field change is applied to the entire rank-one isomorphism. -/
def relabeledPinning (σ : F ≃+* F) : SL2 F ≃* rankOne Q split i :=
  (Theory.PSL2.sl2FieldAut σ).trans (sourcePinning Q split i hV μ)

theorem relabeledPinning_root (σ : F ≃+* F) (a : F) :
    (relabeledPinning Q split i hV μ σ (uni a) : X ⧸ Q.D) =
      simpleParameter Q split i hV μ (.ofAdd (σ a)) := by
  simp only [relabeledPinning, MulEquiv.trans_apply, sl2FieldAut_uni, sourcePinning_root]

theorem relabeledPinning_weyl (σ : F ≃+* F) :
    (relabeledPinning Q split i hV μ σ (weyl F) : X ⧸ Q.D) =
      pinnedReflection Q split i hV μ := by
  simp only [relabeledPinning, MulEquiv.trans_apply, sl2FieldAut_weyl]
  rfl

theorem relabeledPinning_torus (σ : F ≃+* F) (a : Fˣ) :
    (relabeledPinning Q split i hV μ σ (tor a) : X ⧸ Q.D) =
      pinnedTorus Q split i hV μ (Units.map σ.toMonoidHom a) := by
  have ht : Theory.PSL2.sl2FieldAut σ (tor a) = tor (Units.map σ.toMonoidHom a) := by
    ext j k
    fin_cases j <;> fin_cases k <;> simp [Theory.PSL2.sl2FieldAut]
  simp only [relabeledPinning, MulEquiv.trans_apply, ht]
  rfl
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
