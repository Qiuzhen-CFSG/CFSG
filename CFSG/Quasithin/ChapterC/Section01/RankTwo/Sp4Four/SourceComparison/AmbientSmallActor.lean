module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.SmallActor
public import Theory.Representation.SemilinearFixedIndex
public import Theory.Representation.ConjugationFixedQuotient
/-!
# The critical images cannot have ambient order two

The exact quotient kernels turn opposite image orders into the original
centralizer indices. Critical noncommutation makes both images nontrivial.
Each faithful semilinear natural action has moving index at least four,
so equivariant natural quotients force both original image orders to be
at least four, before either image is known to be inner.

Source: the reciprocal seed calculation of MS93 (3.3)--(3.4), pp.867--868.
-/

public section
noncomputable section
open Subgroup Representation
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}
  {geometry : Geometry R} {a e : Vertex R}

private theorem image_ne_bot_of_kernel_centralizer
    {G D : Type*} [Group G] [Group D] (A B : Subgroup G)
    (α : A →* D) (hk : α.ker = (centralizer (B : Set G)).subgroupOf A)
    (hn : ⁅A,B⁆ ≠ ⊥) : α.range ≠ ⊥ := by
  intro he
  apply hn
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro a ha
  have hx : α ⟨a,ha⟩ ∈ α.range := ⟨⟨a,ha⟩,rfl⟩
  rw [he] at hx
  have hm : (⟨a,ha⟩ : A) ∈ α.ker := hx
  rw [hk] at hm
  exact hm

theorem critical_ambient_actor_orders_ge_four
    {F K D E : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    [Field K] [Finite K] [Algebra (ZMod 2) K] [Group D] [Group E]
    (path : CriticalPath R geometry a e) (hb : 0 < geometry.b R)
    (hC : EdgeCentralizerCondition R) (hF : Nat.card F=4) (hK : Nat.card K=4)
    (πe : U R e →* Multiplicative (Vector F)) (hpe : Function.Surjective πe)
    (πa : U R a →* Multiplicative (Vector K)) (hpa : Function.Surjective πa)
    (ρe : Representation (ZMod 2) D (Vector F)) (hfaithE : Function.Injective ρe)
    (hsemiE : ∀ d : D, ∃ σ : F ≃+* F, ∀ c v, ρe d (c • v)=σ c • ρe d v)
    (ρa : Representation (ZMod 2) E (Vector K)) (hfaithA : Function.Injective ρa)
    (hsemiA : ∀ d : E, ∃ σ : K ≃+* K, ∀ c v, ρa d (c • v)=σ c • ρa d v)
    (α : Z R a →* D) (β : Z R e →* E)
    (hαker : α.ker = (centralizer (Z R e : Set (FreeAmalgam R))).subgroupOf (Z R a))
    (hβker : β.ker = (centralizer (Z R a : Set (FreeAmalgam R))).subgroupOf (Z R e))
    (hα : ∀ (z : Z R a) (u : U R e),
      πe ⟨z.val*u.val*z.val⁻¹,
        (mem_normalizer_iff.mp (critical_actor_normalizes_moving path z.property) u.val).mp u.property⟩ =
          Multiplicative.ofAdd (ρe (α z) (πe u).toAdd))
    (hβ : ∀ (z : Z R e) (u : U R a),
      πa ⟨z.val*u.val*z.val⁻¹,
        (mem_normalizer_iff.mp (critical_reverse_actor_normalizes_moving path z.property) u.val).mp u.property⟩ =
          Multiplicative.ofAdd (ρa (β z) (πa u).toAdd)) :
    4 ≤ Nat.card α.range ∧ 4 ≤ Nat.card β.range := by
  let := finite_Z R a
  let := finite_Z R e
  let : Finite (U R e) := Finite.of_injective (inclusion (U_le_Z e)) (inclusion_injective _)
  let : Finite (U R a) := Finite.of_injective (inclusion (U_le_Z a)) (inclusion_injective _)
  have hn := critical_noncommutation R geometry hC a path.start_color
    (by rwa [geometry.distance_constant a path.start_color]) path.critical
  have hA := image_ne_bot_of_kernel_centralizer (Z R a) (Z R e) α hαker hn
  have hB := image_ne_bot_of_kernel_centralizer (Z R e) (Z R a) β hβker
    (by rwa [commutator_comm])
  have hia : (centralizer (Z R e : Set (FreeAmalgam R))).relIndex (Z R a) =
      Nat.card α.range := by
    change ((centralizer (Z R e : Set (FreeAmalgam R))).subgroupOf (Z R a)).index = _
    rw [←hαker,index_ker]
  have hie : (centralizer (Z R a : Set (FreeAmalgam R))).relIndex (Z R e) =
      Nat.card β.range := by
    change ((centralizer (Z R a : Set (FreeAmalgam R))).subgroupOf (Z R e)).index = _
    rw [←hβker,index_ker]
  constructor
  · apply (four_le_fixed_quotient_card_of_semilinear hK ρa hfaithA hsemiA β.range hB).trans
    apply (Representation.fixed_quotient_card_le_centralizer_index (U R a) (Z R e)
      (critical_reverse_actor_normalizes_moving path) πa hpa ρa β hβ).trans
    rw [←hia]
    exact relIndex_le_of_le_right (U_le_Z a) index_ne_zero_of_finite
  · apply (four_le_fixed_quotient_card_of_semilinear hF ρe hfaithE hsemiE α.range hA).trans
    apply (Representation.fixed_quotient_card_le_centralizer_index (U R e) (Z R a)
      (critical_actor_normalizes_moving path) πe hpe ρe α hα).trans
    rw [←hie]
    exact relIndex_le_of_le_right (U_le_Z e) index_ne_zero_of_finite
end CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
