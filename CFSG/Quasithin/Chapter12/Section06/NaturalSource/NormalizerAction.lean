module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FullAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
/-!
# The full original normalizer action

Local uniqueness gives N_G(V) <= N_G(L). Thus L is normal in the
actual normalizer of V, and the linear normalizer theorem extends the
original A8 action to a permutation action of all N_G(V) on the same
six-space. The construction retains the original L-action kernel quotient
and the fixed-space projection used by the full coordinates.

Source: Aschbacher--Smith, the action used in 12.6.20 and 12.6.24,
printed pp.829--831. Vanishing of C_V(L) remains an earlier-source input.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))

include hTV in
/-- The whole ambient normalizer acts by permutations in the original coordinates. -/
theorem SourceHypothesis.original_normalizer_permutation_action :
    ∃ f : normalizer (V : Set G) →* Equiv.Perm (Fin 8),
      (∀ l : L, f ⟨l.val,S.chosen.normalizes l.property⟩ =
        (D.groupEquiv (QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker l)).val) ∧
      (∀ (a : normalizer (V : Set G)) (v : V),
        (D.fullCoordinates hZ (V.normalizerMonoidHom a v)).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 8) (f a) (D.fullCoordinates hZ v).toAdd) := by
  let J := normalizer (V : Set G)
  have hJL : J ≤ normalizer (L : Set G) :=
    S.chosen.normal_subgroup_normalizer_le S.source.toHypothesis1221
      (S.chosen.le_sylow.trans le_sup_right) S.chosen.ne_bot
      (sup_le S.chosen.normalizes hTV)
  let A := L.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer hJL
  let e : A ≃* L := subgroupOfEquivOfLe S.chosen.normalizes
  let q : L →* alternatingGroup (Fin 8) := D.groupEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (conjugation L V S.chosen.normalizes).ker)
  have hq : Function.Surjective q :=
    D.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨f,hf,ha,_⟩ := BinaryPermutation.EightNormalizer.exists_ambient_hom
    (seedRepresentation J V le_rfl) A (q.comp e.toMonoidHom) (hq.comp e.surjective)
    (D.fullLinearCoordinates hZ) (fun (l : A) (v : Additive V) => D.fullCoordinates_equivariant hZ (e l) v.toMul)
  refine ⟨f,?_,?_⟩
  · intro l
    exact hf ⟨⟨l.val,S.chosen.normalizes l.property⟩,l.property⟩
  · intro a v
    exact ha a (Additive.ofMul v)

end CFSG.Quasithin.Chapter12.Section06
