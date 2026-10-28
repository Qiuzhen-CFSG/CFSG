module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FullCoordinates
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Perpendicular
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import Theory.Representation.BinaryPermutation.EightNormalizer

/-!
# Extending the original orthogonal coordinates to LT

The original L-action surjects onto A₈. Since L is normal in LT, the full
LT-action normalizes that image. The full linear normalizer theorem gives
an actual homomorphism LT → S₈ in the unchanged coordinates, restricting
to the original action-kernel quotient marking on L. Its kernel is exactly
C_LT(V), without assuming faithfulness of the full action.

Point fixation and invariance of the half-weight form then prove that the
original L₁T normalizes the literal perpendicular V₅. Only the earlier
fixed-space vanishing and T-invariance of V and its point remain explicit.
Source: Aschbacher--Smith, setup of 12.6.2 and 12.6.24(7), pp.830--831,
using B.3.1--2 for the permutation normalizer.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06.OrthogonalMarking
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (chosen : Section02.ChosenModule T L V)
  (D : OrthogonalMarking L V chosen.normalizes)
  (hZ : ZV L V = ⊥) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))

omit [Finite G] in
/-- Extend the original quotient marking to LT on the same full module.
The restriction on L and the actual action kernel are both retained. -/
theorem exists_full_permutation_action :
    ∃ f : (L ⊔ (T : Subgroup G) : Subgroup G) →* Equiv.Perm (Fin 8),
      (∀ l : L, f ⟨l.val,mem_sup_left l.property⟩ =
        (D.groupEquiv (QuotientGroup.mk' (conjugation L V chosen.normalizes).ker l)).val) ∧
      (∀ (a : (L ⊔ (T : Subgroup G) : Subgroup G)) (v : V),
        (D.fullCoordinates hZ
          (V.normalizerMonoidHom ⟨a.val,(sup_le chosen.normalizes hTV) a.property⟩ v)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 8) (f a)
          (D.fullCoordinates hZ v).toAdd) ∧
      f.ker = (centralizer (V : Set G)).subgroupOf (L ⊔ (T : Subgroup G)) := by
  let J := L ⊔ (T : Subgroup G)
  let hn : J ≤ normalizer (V : Set G) := sup_le chosen.normalizes hTV
  let A := L.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer chosen.sylow_normalizes_component)
  let e : A ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  let q : L →* alternatingGroup (Fin 8) := D.groupEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (conjugation L V chosen.normalizes).ker)
  have hq : Function.Surjective q :=
    D.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨f,hf,ha,hk⟩ := BinaryPermutation.EightNormalizer.exists_ambient_hom
    (seedRepresentation J V hn) A (q.comp e.toMonoidHom) (hq.comp e.surjective)
    (D.fullLinearCoordinates hZ) (by
      intro l v
      exact D.fullCoordinates_equivariant hZ (e l) v.toMul)
  refine ⟨f,?_,?_,?_⟩
  · intro l
    exact hf ⟨⟨l.val,mem_sup_left l.property⟩,l.property⟩
  · intro a v
    exact ha a (Additive.ofMul v)
  · rw [hk]
    ext a
    change seedRepresentation J V hn a = 1 ↔ a.val ∈ centralizer (V : Set G)
    constructor
    · intro he v hv
      have hh := congrArg (fun F : Module.End (ZMod 2) (Additive V) =>
        ((F (Additive.ofMul ⟨v,hv⟩)).toMul : G)) he
      change a.val * v * a.val⁻¹ = v at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro he
      apply LinearMap.ext
      intro v
      apply Additive.toMul.injective
      apply Subtype.ext
      change a.val * v.toMul.val * a.val⁻¹ = v.toMul.val
      rw [←he v.toMul.val v.toMul.property,mul_inv_cancel_right]
end CFSG.Quasithin.Chapter12.Section06.OrthogonalMarking
namespace CFSG.Quasithin.Chapter12.Section06
open Subgroup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  {K : GroupClass} (S : SourceHypothesis K T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The literal edge group normalizes V₅; its T-action is constructed
from the A₈ marking rather than supplied as a second coordinate system. -/
theorem SourceHypothesis.original_local_normalizes_perpendicular
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G)) :
    (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) ≤
      normalizer ((D.fullSetup hZ T z).V₅ : Set G) := by
  let E := D.fullSetup hZ T z
  have hL1 : E.L₁ ≤ L ⊓ E.Gz := map_subtype_le _
  have hJ : E.L₁ ⊔ (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) :=
    sup_le_sup (hL1.trans inf_le_left) le_rfl
  have hN : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) :=
    hJ.trans (sup_le S.chosen.normalizes hTV)
  have hZ' : E.L₁ ⊔ (T : Subgroup G) ≤ E.Gz :=
    sup_le (hL1.trans inf_le_right) (hTz.trans
      (normalizer_le_centralizer_of_card_two E.V₁ (E.point_card hz)))
  obtain ⟨f,_,ha,_⟩ := D.exists_full_permutation_action S.chosen hZ hTV
  apply E.normalizes_perpendicular (E.L₁ ⊔ (T : Subgroup G)) hN hZ'
  intro a
  exact ⟨f ⟨a.val,hJ a.property⟩,fun v => ha ⟨a.val,hJ a.property⟩ v⟩
end CFSG.Quasithin.Chapter12.Section06
