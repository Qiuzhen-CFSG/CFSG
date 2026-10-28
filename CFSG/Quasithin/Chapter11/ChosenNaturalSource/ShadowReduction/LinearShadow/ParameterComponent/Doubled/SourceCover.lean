module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Extension
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Doubled.Cover
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.NaturalSource.Recognition.Action

/-!
# Orthogonal coordinates on the literal source action

The maximal-cover comparison is applied to the binary action of the actual
residual star group on V_H. The resulting coordinates intertwine the original
conjugation action and keep the exact projection of the chosen actor.
The cover property and the Sylow commutator rank are explicit here; they must
still be constructed from the reciprocal doubled-module geometry.

Source: Aschbacher--Smith, 11.3.6, printed pp.772--773.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.OneCohomology
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
open CommonCore
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {H A : Subgroup G}
    [IsElementaryAbelian 2 (omegaClosure T H)]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance sourceCoverFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Construct the orthogonal marking from the literal source cover and its
Sylow commutator dimension. Neither a marking nor disjointness is assumed. -/
theorem source_orthogonalMarking_of_cover
    (e : residualStar T H ≃* SL(2,F)) (hAH : A ≤ H)
    (hAK : (A.subgroupOf H).map (starProjection T H) ≤ residualStar T H)
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (p : (NaturalRecognition.binaryAction T H e).IntertwiningMap
      (SL2OrthogonalCover.binaryNatural (F := F))) (hp : IsCover p)
    (P : Sylow 2 SL(2,F))
    (hmove : Module.finrank (ZMod 2)
      (Coinvariants.ker ((NaturalRecognition.binaryAction T H e).comp P.toSubgroup.subtype)) =
        2 * n) :
    ∃ c : OrthogonalMarking T H A F, ∀ a : A,
      c.parameter a = e ⟨starProjection T H (inclusion hAH a),
        hAK (mem_map_of_mem (starProjection T H) a.property)⟩ := by
  obtain ⟨j,hj,_⟩ := orthogonal_equiv_of_sylow_moved_dimension n hn hF
    (NaturalRecognition.binaryAction T H e) p hp P hmove
  let f : A →* residualStar T H :=
    { toFun a := ⟨starProjection T H (inclusion hAH a),
        hAK (mem_map_of_mem (starProjection T H) a.property)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' a b := Subtype.ext (by simp) }
  let q : omegaClosure T H →* Multiplicative (SL2OrthogonalCover.Space F) :=
    { toFun w := Multiplicative.ofAdd (j.symm (Additive.ofMul w))
      map_one' := j.symm.map_zero
      map_mul' a b := j.symm.map_add (Additive.ofMul a) (Additive.ofMul b) }
  have hq : Function.Injective q := by
    intro a b hab
    exact Additive.ofMul.injective (j.symm.injective (Multiplicative.ofAdd.injective hab))
  have hker : q.ker = ⊥ := (MonoidHom.ker_eq_bot_iff q).mpr hq
  let c : OrthogonalMarking T H A F :=
    { le_local := hAH
      parameter := e.toMonoidHom.comp f
      coordinates := q
      kernel_disjoint := by rw [hker]; exact disjoint_bot_left
      intertwines := by
        intro a w
        change j.symm (Additive.ofMul (localAction T H (inclusion hAH a) w)) =
          SL2OrthogonalCover.action (e (f a)) (j.symm (Additive.ofMul w))
        apply j.injective
        rw [j.apply_symm_apply]
        change _ = j (SL2OrthogonalCover.binaryAction (e (f a)) (j.symm (Additive.ofMul w)))
        rw [hj,j.apply_symm_apply]
        apply Additive.toMul.injective
        rw [NaturalRecognition.binaryAction_equiv]
        rfl }
  exact ⟨c,fun _ => rfl⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent.Doubled
