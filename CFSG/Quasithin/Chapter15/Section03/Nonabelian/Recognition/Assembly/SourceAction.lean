module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.NormalReduction
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve

/-!
# The earlier action inputs for the recognition assembly

Only the orthogonal form and marked elementary actor from 15.3.56 are added
to the normal reduction's earlier-source inputs. The Sylow subgroup is the
image of the original T in H/O₂(H). Its fixed line, the marked central
involution, and all three prime-to-three restrictions are constructed from
those inputs; none is replaced by a model-exclusion premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1147–1149,
15.3.48, 15.3.53 and 15.3.56.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction
variable {G : Type*} [Group G] [Finite G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {C : GroupClass} {v : ActorQuotient Z} {s : ℕ}

/-- The additional genuine 15.3.56 inputs used by both recognition branches.
The elementary actor is the image of the specified ambient X, containing V* in the actor quotient. -/
structure EarlierActionInputs (d : EarlierSourceInputs Z ZS V M C v s) where
  X : Subgroup G
  X_le_T : X ≤ (d.T : Subgroup G)
  Vstar_le_Xstar : actorImage Z V ≤ actorImage Z X
  elementary : IsElementaryAbelian 2 (actorImage Z X)
  card_actor : Nat.card (actorImage Z X) = 2 ^ (s + 1)
  quadratic : QuadraticForm (ZMod 2) (Space Z ZS)
  nondegenerate : quadratic.polarBilin.Nondegenerate
  invariant : ∀ a w, quadratic (actorRepresentation Z ZS d.kernel a w) = quadratic w

namespace NormalReduction.EarlierSourceInputs

/-- The genuine Sylow image T* in H/O₂(H). -/
noncomputable def actorSylow (d : EarlierSourceInputs Z ZS V M C v s) :
    Sylow 2 (ActorQuotient Z) :=
  (d.T.subtype d.T_le_H).mapSurjective (QuotientGroup.mk'_surjective _)

/-- This Sylow is exactly the image under the specified quotient map. -/
theorem actorSylow_coe (d : EarlierSourceInputs Z ZS V M C v s) :
    (d.actorSylow : Subgroup (ActorQuotient Z)) = actorImage Z (d.T : Subgroup G) := rfl

/-- Transport the earlier paired fixed-line equality to the linear quotient
representation and the full Sylow image. -/
theorem actorSylow_fixedSpace (d : EarlierSourceInputs Z ZS V M C v s) :
    IrreducibleSieve.sylowFixedSpace (actorRepresentation Z ZS d.kernel) d.actorSylow =
      LocalRestrictions.vectorSubspace Z ZS ZS := by
  let := MulDistribMulAction.compHom (VectorQuotient Z ZS) (quotientAction Z ZS)
  have hf := fixedPoints_eq_distinguishedLine Z ZS (d.T : Subgroup G)
    d.ZS_commutator_T d.J d.J_le_T d.fixed_line
  ext w
  change (∀ t : actorImage Z (d.T : Subgroup G),
      actorRepresentation Z ZS d.kernel t w = w) ↔
    w.toMul ∈ distinguishedLine Z ZS
  rw [← hf]
  constructor
  · intro hw t
    exact congrArg Additive.toMul (hw
      ⟨QuotientGroup.mk' _ t.val, mem_map.mpr ⟨t.val, t.property, rfl⟩⟩)
  · intro hw t
    obtain ⟨a, ha, he⟩ := mem_map.mp t.property
    rw [← he]
    exact congrArg Additive.ofMul (hw ⟨a, ha⟩)

/-- The Sylow-fixed subspace really has binary dimension one. -/
theorem actorSylow_fixedDimension (d : EarlierSourceInputs Z ZS V M C v s) :
    Module.finrank (ZMod 2)
      (IrreducibleSieve.sylowFixedSpace (actorRepresentation Z ZS d.kernel) d.actorSylow) = 1 := by
  rw [d.actorSylow_fixedSpace]
  let e : LocalRestrictions.vectorSubspace Z ZS ZS ≃ distinguishedLine Z ZS := {
    toFun w := ⟨w.val.toMul, w.property⟩
    invFun w := ⟨Additive.ofMul w.val, w.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hc : Nat.card (LocalRestrictions.vectorSubspace Z ZS ZS) = 2 :=
    (Nat.card_congr e).trans (card_distinguishedLine Z ZS d.Z_le_ZS d.Z_card d.ZS_card)
  have hh := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := LocalRestrictions.vectorSubspace Z ZS ZS)
  rw [hc, Nat.card_zmod] at hh
  exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hh.symm)

end NormalReduction.EarlierSourceInputs

/-- Construct every local input of the exhaustive irreducible sieve from the
literal earlier source data. In particular positivity and the three-prime
restrictions are proved by the normal reduction. -/
theorem EarlierActionInputs.sieveData {d : EarlierSourceInputs Z ZS V M C v s}
    (a : EarlierActionInputs d) :
    IrreducibleSieve.SourceData (actorRepresentation Z ZS d.kernel)
      (actorImage Z a.X) d.actorSylow v s := by
  have r := normal_reduction_of_earlier_source d
  have hXT : actorImage Z a.X ≤ actorImage Z (d.T : Subgroup G) :=
    map_mono (fun _ hx => a.X_le_T hx)
  have hvV : v ∈ actorImage Z V := d.marking ▸ mem_zpowers v
  have hvX : v ∈ actorImage Z a.X := a.Vstar_le_Xstar hvV
  have hc := LocalRestrictions.marked_commutes_actorImage_T Z V d.T v
    d.V_le_H d.T_normalizes_V d.Vstar_card d.marking
  refine {
    faithful := actorRepresentation_injective Z ZS d.kernel
    positive := r.positive
    dimension := d.dimension
    elementary := a.elementary
    card_actor := a.card_actor
    actor_le_sylow := hXT
    involution := ?_
    marked_mem := hvX
    marked_central := ?_
    displacement_rank := d.displacement_rank
    quadratic := ⟨a.quadratic, a.nondegenerate, a.invariant⟩
    fixed_dimension := d.actorSylow_fixedDimension
    plane_three_free := r.plane_three
    line_three_free := ?_
    centralizer_three_free := ?_ }
  · rw [← Nat.card_zpowers, d.marking, d.Vstar_card]
  · refine mem_map.mpr ⟨⟨v, hXT hvX⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro t
    apply Subtype.ext
    exact (hc t).eq.symm
  · simpa only [d.actorSylow_fixedSpace] using r.line_three
  · simpa only [d.marking] using r.centralizer_three

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
