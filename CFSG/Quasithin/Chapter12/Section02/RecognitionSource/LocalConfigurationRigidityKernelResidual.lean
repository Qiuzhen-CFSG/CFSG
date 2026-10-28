module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelFixedSupplement
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityKernelThompson
/-!
# The residual normalizes the elementary radical in every dimension

The literal fixed supplement gives C_T(U∩V)=UV×C_T(I). Consequently
R=C_T(U) has index two in this non-elementary hyperplane centralizer.
The literal N_L(U∩V) normalizes that centralizer. Its two-residual fixes
each elementary index-two subgroup, and therefore normalizes R.
This proves the required Y≤N_G(R) also in dimension three, independently
of the cohomological split and without assuming a Thompson calculation.

Source: Aschbacher--Smith, original 12.2.25, printed pp.804--805.
Final source assembly belongs to qt-d-12213-local-rigidity.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d : ℕ}
namespace RigidityKernel
omit [Finite G] in
private theorem fixed_supplement_hyperplane_index
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U) :
    (U ⊓ V : Subgroup G).relIndex V = 2 := by
  have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left, relIndex_bot_left, C.hyperplane, chosen_card A] at hh
  have hd : d = d - 1 + 1 := by have := A.dimension.1; omega
  have hc : 2 ^ d = 2 * 2 ^ (d - 1) := by
    calc
      2 ^ d = 2 ^ (d - 1 + 1) := congrArg (fun n : ℕ => 2 ^ n) hd
      _ = _ := by rw [pow_succ, Nat.mul_comm]
  rw [hc] at hh
  have hp : 0 < 2 ^ (d - 1) := pow_pos (by decide) _
  nlinarith

/-- The hyperplane-centralizer product is internal: the stated map is
multiplication in G, and its two factors have trivial intersection. -/
theorem hyperplane_pair_directProduct
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    ∃ e : ↥(U ⊔ V) × ↥((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) ≃*
      ↥((T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G)),
      ∀ x z, (e (x,z) : G) = (x : G) * (z : G) := by
  let := C.elementary
  let E := (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)
  have hEU : E ≤ centralizer (U : Set G) := inf_le_right.trans
    (centralizer_le (show U ≤ cyclicPairJoin P U V from le_sup_right.trans le_sup_left))
  have hEV : E ≤ centralizer (V : Set G) := inf_le_right.trans
    (centralizer_le (show V ≤ cyclicPairJoin P U V from le_sup_right))
  have hsplit : (U ⊔ V) ⊓ centralizer (U : Set G) = U := by
    rw [inf_centralizer_sup_of_centralizing U V U
      (C.core_le_sylow.trans (((structural G T L h).2.2 V D).1)) (le_centralizer U),
      chosen_centralizer_core A C, sup_eq_left.mpr inf_le_left]
  have hdis : Disjoint (U ⊔ V) E := by
    apply disjoint_def.mpr
    intro x hx hxE
    exact disjoint_def.mp C.core_disjoint_sylow_pair_centralizer
      (hsplit.le ⟨hx,hEU hxE⟩) hxE
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting (U ⊔ V) E hdis
    (sup_le (le_centralizer_iff.mp hEU) (le_centralizer_iff.mp hEV))
  exact ⟨e.trans (MulEquiv.subgroupCongr (hyperplane_pair_split h D structural A C hnone).symm),he⟩

/-- The centralizer R has index two in the hyperplane centralizer in every
dimension. -/
theorem radical_hyperplane_index
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    ((T : Subgroup G) ⊓ centralizer (U : Set G)).relIndex
      ((T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G)) = 2 := by
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let K := (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G)
  have hRV : R ⊓ V = U ⊓ V := by
    rw [inf_assoc, inf_comm (centralizer _) V, chosen_centralizer_core A C,
      inf_eq_right.mpr (inf_le_right.trans D.le_sylow)]
  have hRK : R ≤ K := inf_le_inf_left _ (centralizer_le inf_le_left)
  have hs : R ⊔ V = K := by
    dsimp only [K]
    rw [hyperplane_pair_split h D structural A C hnone]
    dsimp only [R]
    rw [C.sylow_centralizer_core_decomposition (by have := A.dimension.1; omega)
      (((structural G T L h).2.2 V D).1) D.le_sylow hnone]
    ac_rfl
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes R V
    (D.le_sylow.trans ((le_inf (T : Subgroup G).le_normalizer
      (C.sylow_normalizes_core.trans (normalizer_le_normalizer_centralizer U))).trans
        inf_normalizer_le_normalizer_inf))
  rw [hRV,hs] at hp
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) R K bot_le hRK
  rw [relIndex_bot_left,relIndex_bot_left] at hi
  have hv := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ V) V bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,fixed_supplement_hyperplane_index A C] at hv
  have hr := Nat.card_pos (α := R)
  have hw := Nat.card_pos (α := ↥(U ⊓ V))
  change R.relIndex K = 2
  rw [← hi, ← hv] at hp
  have he : Nat.card R * Nat.card ↥(U ⊓ V) * 2 =
      Nat.card R * Nat.card ↥(U ⊓ V) * R.relIndex K := by nlinarith only [hp]
  exact (Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hr hw) he).symm

/-- The two-residual of the literal hyperplane normalizer fixes R. The
index-two elementary argument replaces the source's Thompson calculation
without requiring a complement or self-normalization. -/
theorem residual_normalizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    rigidityHyperplaneResidual L U V ≤
      normalizer (((T : Subgroup G) ⊓ centralizer (U : Set G) : Subgroup G) : Set G) := by
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  let K := (T : Subgroup G) ⊓ centralizer ((U ⊓ V : Subgroup G) : Set G)
  have hUK : U ≤ K := le_inf C.core_le_sylow (by
    let := C.elementary
    exact (le_centralizer U).trans (centralizer_le inf_le_left))
  have hVK : V ≤ K := le_inf D.le_sylow (by
    let := D.elementary
    exact (le_centralizer V).trans (centralizer_le inf_le_right))
  have hnot : ¬ IsElementaryAbelian 2 K := by
    intro hk
    let := hk
    have hu : U ≤ centralizer (V : Set G) :=
      hUK.trans ((le_centralizer K).trans (centralizer_le hVK))
    have hz : U ⊓ V = ⊥ := C.transvections.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr hu)
    have hh := C.hyperplane
    rw [hz,card_bot] at hh
    have hd1 : 0 < d-1 := by have := A.dimension.1; omega
    have hp : 1 < 2^(d-1) := one_lt_pow₀ (by decide) (by omega)
    omega
  exact twoPerfect_le_normalizer_elementary_index_two _ K R
    (isPPerfect_embedded_pResidual 2 _)
    ((map_subtype_le _).trans (hyperplane_normalizer_normalizes_centralizer h D structural A C))
    (inf_le_inf_left _ (centralizer_le inf_le_left))
    (radical_elementary h D structural A C hnone)
    (radical_hyperplane_index h D structural A C hnone) hnot


end RigidityKernel
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
