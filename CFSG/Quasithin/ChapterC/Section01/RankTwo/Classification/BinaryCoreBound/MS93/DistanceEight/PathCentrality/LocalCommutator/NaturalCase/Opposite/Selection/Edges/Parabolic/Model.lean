module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.CyclicNormalization.SmallInvariant.Lifting
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.Verification.CommutatorBounds.CyclicNormalization.SmallInvariant.Overgroups
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.RankOne.SmallInvariant.Algebra

/-!
# Lifting small-subgroup invariance to a binary parabolic

The twelve explicit actors in O²(P) and P have the same orbits on the
binary natural three-space. Thus residual invariance of any natural
subgroup implies full parabolic invariance, for either side and marking.

For a subgroup K of order at most four, two-perfect idempotence gives
[K,O²(P)] = K or 1. In the first case the bound [K,O²(G)] ≤ U puts K
in the actual natural subgroup, where the orbit calculation applies.
In the second case the existing centralizer-index lifting theorem applies.
All assertions concern the original finite group, with no quotient lift
assumed and no fixed-space orientation restriction.

Source: MS93 (4.4.1)(1), printed p.891, normalization by a conjugate of F₂.
This extends the point-fixed normalization argument in FirstPairing/Orientation
using the small-perfect-action dichotomy in FirstPairing/StepThree/RankOne.
-/

@[expose] public section

open Matrix Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Parabolic
open RankOnePairing RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open ModelProof
open Matrix.PSL3Two hiding SL
open Matrix.PSL3Two.MarkedAutomorphisms
private def translation (i : Bool) (a b : ZMod 2) : SL :=
  if i then ⟨!![1,0,a;0,1,b;0,0,1], by simp [det_fin_three]⟩
  else ⟨!![1,a,b;0,1,0;0,0,1], by simp [det_fin_three]⟩
private def levi (i : Bool) : Fin 3 → SL :=
  if i then ![1, ⟨!![0,1,0;1,1,0;0,0,1], by decide⟩,
    ⟨!![1,1,0;1,0,0;0,0,1], by decide⟩]
  else ![1, ⟨!![1,0,0;0,0,1;0,1,1], by decide⟩,
    ⟨!![1,0,0;0,1,1;0,1,0], by decide⟩]
private def actor (i : Bool) (t : ZMod 2 × ZMod 2 × Fin 3) : SL :=
  translation i t.1 t.2.1 * levi i t.2.2
private theorem actor_mem : ∀ i t, actor i t ∈ (if i then lineA else pointA) := by
  intro i
  cases i <;> simp only [Bool.false_eq_true, if_false, if_true] <;> decide +kernel
private theorem orbit_covers : ∀ (i : Bool) (p : SL),
    p ∈ (if i then lineParabolicSL else pointParabolicSL) →
    ∀ v : Fin 3 → ZMod 2, ∃ t : ZMod 2 × ZMod 2 × Fin 3,
      (actor i t).val.mulVec v = p.val.mulVec v := by
  intro i
  cases i <;> simp only [Bool.false_eq_true, if_false, if_true] <;> decide +kernel

/-- The two-residual and the whole binary parabolic have the same vector orbits. -/
theorem invariant_of_residual (i : Bool) (A : Subgroup VectorGroup)
    (hi : ∀ t ∈ residual (if i then lineParabolicSL else pointParabolicSL),
      A.map (vectorAction t).toMonoidHom = A) :
    ∀ p ∈ (if i then lineParabolicSL else pointParabolicSL),
      A.map (vectorAction p).toMonoidHom = A := by
  intro p hp
  apply eq_of_le_of_card_ge
  · rintro _ ⟨v,hv,rfl⟩
    obtain ⟨t,ht⟩ := orbit_covers i p hp v.toAdd
    have hm : actor i t ∈ residual (if i then lineParabolicSL else pointParabolicSL) := by
      cases i
      · simp only [Bool.false_eq_true, if_false, point_residual]
        exact actor_mem false t
      · simp only [if_true, line_residual]
        exact actor_mem true t
    have h := mem_map_of_mem (vectorAction (actor i t)).toMonoidHom hv
    rw [hi _ hm] at h
    have he : vectorAction (actor i t) v = vectorAction p v := ht
    exact he ▸ h
  · exact (Nat.card_congr ((vectorAction p).subgroupMap A).toEquiv).le

/-- Residual invariance implies parabolic invariance under every natural marking. -/
theorem marked_invariant_of_residual (σ : MulAut SL) (flag : SL) (side : Bool)
    (A : Subgroup VectorGroup)
    (hi : ∀ t ∈ residual (markedParabolic σ flag side),
      A.map (vectorAction t).toMonoidHom = A) :
    ∀ p ∈ markedParabolic σ flag side, A.map (vectorAction p).toMonoidHom = A := by
  have transport (k : SL) (i : Bool)
      (hp : markedParabolic σ flag side =
        (if i then lineParabolicSL else pointParabolicSL).map (MulAut.conj k).toMonoidHom) :
      ∀ p ∈ markedParabolic σ flag side, A.map (vectorAction p).toMonoidHom = A := by
    have hr : residual (markedParabolic σ flag side) =
        (residual (if i then lineParabolicSL else pointParabolicSL)).map
          (MulAut.conj k).toMonoidHom := by
      rw [hp, Matrix.PSL3Two.MarkedAutomorphisms.residual, ← map_embedded_pResidual]
      rfl
    have hs := invariant_of_residual i (A.map (vectorAction k⁻¹).toMonoidHom)
      (invariant_pullback k _ A (hr ▸ hi))
    intro p hpm
    rw [hp] at hpm
    obtain ⟨q,hq,rfl⟩ := hpm
    have hh := congrArg (Subgroup.map (vectorAction k).toMonoidHom) (hs q hq)
    rwa [← map_action_conj, map_action_cancel] at hh
  obtain ⟨k, ⟨hp,_⟩ | ⟨hp,_⟩⟩ := marked_pair σ flag side
  · exact transport k false hp
  · exact transport k true hp

/-- A subgroup of the actual natural module normalized by the parabolic
 two-residual is normalized by the full parabolic. -/
theorem natural_normalized_of_residual {G : Type*} [Group G] [Finite G]
    {π : G →* SL} {U : Subgroup G} [U.Normal]
    (hπ : Function.Surjective π) (n : NaturalFactor π ⊤ U ⊥)
    (flag : SL) (side : Bool) (K : Subgroup G) (hKU : K ≤ U)
    (hn : (pResidual 2 (parabolic π flag side)).map (parabolic π flag side).subtype ≤
      normalizer (K : Set G)) :
    parabolic π flag side ≤ normalizer (K : Set G) := by
  let P := parabolic π flag side
  let T := (pResidual 2 P).map P.subtype
  let A := (K.subgroupOf U).map n.coordinates
  have hP : P.map π = modelParabolic flag side := map_comap_eq_self_of_surjective hπ _
  have hT : (T.map π).map n.marking.toMonoidHom =
      residual (markedParabolic n.marking flag side) := by
    rw [map_embedded_pResidual, map_embedded_pResidual, hP]
    rfl
  have hconj (t : G) (z : U) :
      n.coordinates (MulAut.conjNormal t z) =
        vectorAction (n.marking (π t)) (n.coordinates z) :=
    n.action t (mem_top _) z (MulAut.conjNormal t z) rfl
  have hi : ∀ t ∈ residual (markedParabolic n.marking flag side),
      A.map (vectorAction t).toMonoidHom = A := by
    intro t ht
    rw [← hT] at ht
    obtain ⟨_,⟨t,ht,rfl⟩,rfl⟩ := ht
    apply eq_of_le_of_card_ge
    · rintro _ ⟨_,⟨z,hz,rfl⟩,rfl⟩
      exact ⟨MulAut.conjNormal t z, (mem_normalizer_iff.mp (hn ht) z).mp hz, hconj t z⟩
    · exact (Nat.card_congr ((vectorAction (n.marking (π t))).subgroupMap A).toEquiv).le
  have hp := marked_invariant_of_residual n.marking flag side A hi
  apply le_normalizer_iff.mpr
  intro p hpm k hk
  let u : U := ⟨k,hKU hk⟩
  have hu : n.coordinates u ∈ A := ⟨u,hk,rfl⟩
  have hp' : n.marking (π p) ∈ markedParabolic n.marking flag side :=
    mem_map_of_mem _ hpm
  have hmem := mem_map_of_mem (vectorAction (n.marking (π p))).toMonoidHom hu
  rw [hp _ hp'] at hmem
  change vectorAction (n.marking (π p)) (n.coordinates u) ∈ A at hmem
  rw [← hconj] at hmem
  obtain ⟨v,hv,he⟩ := hmem
  have heq := congrArg Subtype.val (n.equivOfBot.injective he)
  change (v : G) = p * k * p⁻¹ at heq
  exact heq ▸ (show (v : G) ∈ K from hv)

private theorem sl_two_perfect : IsPPerfect 2 SL := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  intro N hN hp
  rcases hN.eq_bot_or_eq_top with h | h
  · subst N
    have hSL : IsPGroup 2 SL := hp.of_equiv QuotientGroup.quotientBot
    obtain ⟨n,hn⟩ := hSL.exists_card_eq
    rw [Matrix.PSL3Two.card_SL] at hn
    have h3 : 3 ∣ 2 ^ n := by rw [← hn]; decide
    have hh := (show Nat.Prime 3 by decide).dvd_of_dvd_pow h3
    norm_num at hh
  · exact h

/-- Small displacement invariance lifts from the two-residual to the full
parabolic in the original finite group. The kernel already normalizes K. -/
theorem small_normalized_of_residual {G : Type*} [Group G] [Finite G]
    (π : G →* SL) (hπ : Function.Surjective π) (hker : IsPGroup 2 π.ker)
    (U : Subgroup G) [U.Normal] (n : NaturalFactor π ⊤ U ⊥)
    (flag : SL) (side : Bool) (K : Subgroup G) (hKQ : K ≤ π.ker)
    (hcard : Nat.card K ≤ 4) (hcomm : ⁅K,pResidual 2 G⁆ ≤ U)
    (hQN : π.ker ≤ normalizer (K : Set G))
    (hTN : (pResidual 2 (parabolic π flag side)).map (parabolic π flag side).subtype ≤
      normalizer (K : Set G)) :
    parabolic π flag side ≤ normalizer (K : Set G) := by
  let P := parabolic π flag side
  let T := (pResidual 2 P).map P.subtype
  have hTL : T ≤ pResidual 2 G := map_pResidual_le 2 P.subtype
  rcases Escape.PairingControl.FirstPairing.StepThree.RankOne.SmallInvariant.small_perfect_commutator_eq_or_bot
      K T (hker.to_le hKQ) (isPPerfect_embedded_pResidual 2 P) hTN hcard with he | he
  · apply natural_normalized_of_residual hπ n flag side K _ hTN
    rw [← he]
    exact (commutator_mono le_rfl hTL).trans hcomm
  · have hTK : T ≤ centralizer (K : Set G) := by
      rw [commutator_comm] at he
      exact commutator_eq_bot_iff_le_centralizer.mp he
    have hL : (pResidual 2 G).map π = ⊤ := by
      rw [map_pResidual_of_surjective 2 π hπ,
        (pResidual_eq_top_iff 2 SL).mpr sl_two_perfect]
    have hU : Nat.card U ≤ 8 := by
      rw [Nat.card_congr n.equivOfBot.toEquiv]
      norm_num [Nat.card_eq_fintype_card]
    have hP : P.map π = modelParabolic flag side := map_comap_eq_self_of_surjective hπ _
    have hT : T.map π = residual (modelParabolic flag side) := by
      rw [map_embedded_pResidual, hP]
      rfl
    apply Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.CyclicNormalization.SmallInvariant.Lifting.normalized_of_small_centralizer_overgroups
      π P K (pResidual 2 G) U T 8 hL hTL hQN hcomm hU hTK
    intro A hA hi
    rw [hP]
    apply Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.CyclicNormalization.SmallInvariant.Overgroups.small_index_overgroup
      flag side A _ hi
    rwa [hT] at hA
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Parabolic
