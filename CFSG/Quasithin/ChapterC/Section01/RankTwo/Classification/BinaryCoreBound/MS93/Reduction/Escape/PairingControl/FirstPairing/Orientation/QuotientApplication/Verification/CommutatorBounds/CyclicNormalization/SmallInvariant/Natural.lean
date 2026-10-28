module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Small residual-invariant subgroups of the marked natural three-space

Twelve explicit elements of the point-parabolic two-residual move any vector
outside the fixed line through all six outside vectors. A subgroup of order
at most four therefore lies on the fixed line. The arbitrary marking is
retained: inner-or-graph coverage and the nonzero fixed-space hypothesis
select a conjugate of the point parabolic. Natural coordinates then transport
this result to K ∩ Z, without assuming K ≤ Z or normality of K.

The finite checks only enumerate the eight vectors and twelve named actors.
They extend the full-parabolic calculation in ValueConstruction.ModelProof.Standard
to its two-residual. Source: MS93 (1993), printed pp.847–848 and the small
cyclic-pairing normalization on p.883.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.CyclicNormalization.SmallInvariant.Natural
open Matrix Subgroup
open scoped commutatorElement
open RankOnePairing RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open ModelProof
open Matrix.PSL3Two hiding SL
open Matrix.PSL3Two.MarkedAutomorphisms

private def translation (a b : ZMod 2) : SL :=
  ⟨!![1,a,b;0,1,0;0,0,1], by simp [det_fin_three]⟩
private def levi : Fin 3 → SL := ![
  1,
  ⟨!![1,0,0;0,0,1;0,1,1], by decide⟩,
  ⟨!![1,0,0;0,1,1;0,1,0], by decide⟩]
private def actor (t : ZMod 2 × ZMod 2 × Fin 3) : SL :=
  translation t.1 t.2.1 * levi t.2.2

private theorem actor_mem : ∀ t, actor t ∈ pointA := by decide +kernel

private theorem outside_transitive : ∀ v w : Fin 3 → ZMod 2,
    ¬ (v 1 = 0 ∧ v 2 = 0) → ¬ (w 1 = 0 ∧ w 2 = 0) →
    ∃ t : ZMod 2 × ZMod 2 × Fin 3, (actor t).val.mulVec v = w := by decide +kernel

private def fiveOutside : Fin 5 → VectorGroup := fun i => Multiplicative.ofAdd
  (![![0,1,0], ![1,1,0], ![0,0,1], ![1,0,1], ![0,1,1]] i)

private theorem small_residual_invariant (A : Subgroup VectorGroup) (hc : Nat.card A ≤ 4)
    (hi : ∀ a ∈ pointA, A.map (vectorAction a).toMonoidHom = A) :
    A ≤ pointLine := by
  intro v hv
  by_contra h
  have hm (j : Fin 5) : fiveOutside j ∈ A := by
    have hw : ∀ j : Fin 5, ¬ ((fiveOutside j).toAdd 1 = 0 ∧
        (fiveOutside j).toAdd 2 = 0) := by decide
    obtain ⟨t, ht⟩ := outside_transitive v.toAdd (fiveOutside j).toAdd h (hw j)
    have hh : vectorAction (actor t) v ∈ A := by
      rw [← hi _ (actor_mem t)]
      exact mem_map_of_mem _ hv
    have he : vectorAction (actor t) v = fiveOutside j := ht
    exact he ▸ hh
  let f : Fin 5 → A := fun j => ⟨fiveOutside j, hm j⟩
  have hf : Function.Injective f := by
    intro j k he
    have hinj : Function.Injective fiveOutside := by decide
    exact hinj (congrArg Subtype.val he)
  have hh := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin] at hh
  omega

private theorem small_marked_residual_invariant
    (σ : MulAut SL) (g : SL) (i : Bool)
    (hfixed : fixedSpace (markedParabolic σ g i) ≠ ⊥)
    (A : Subgroup VectorGroup) (hc : Nat.card A ≤ 4)
    (hi : ∀ a ∈ residual (markedParabolic σ g i),
      A.map (vectorAction a).toMonoidHom = A) :
    A ≤ fixedSpace (markedParabolic σ g i) := by
  obtain ⟨k, ⟨hp, hq⟩|⟨hp, hq⟩⟩ := marked_pair σ g i
  · have hr : residual (markedParabolic σ g i) = pointA.map (MulAut.conj k).toMonoidHom := by
      rw [hp, Matrix.PSL3Two.MarkedAutomorphisms.residual, ← map_embedded_pResidual]
      change (residual pointParabolicSL).map _ = _
      rw [point_residual]
    have hc' : Nat.card (A.map (vectorAction k⁻¹).toMonoidHom) ≤ 4 := by
      rw [card_map_of_injective (f := (vectorAction k⁻¹).toMonoidHom)
        (vectorAction k⁻¹).injective]
      exact hc
    have hs := small_residual_invariant _ hc'
      (invariant_pullback k pointA A (hr ▸ hi))
    have hm := map_mono (f := (vectorAction k).toMonoidHom)
      (hs.trans line_fixed_by_point)
    rw [map_action_cancel] at hm
    rwa [hp, fixedSpace_conj]
  · exact False.elim (hfixed (by
      rw [hp, fixedSpace_conj, line_fixed_bot, Subgroup.map_bot]))


variable {G : Type*} [Group G]
    {π : G →* SL} {Z : Subgroup G} [Z.Normal]

private theorem natural_conj (n : NaturalFactor π ⊤ Z ⊥) (g : G) (z : Z) :
    n.coordinates (MulAut.conjNormal g z) =
      vectorAction (n.marking (π g)) (n.coordinates z) :=
  n.action g (mem_top g) z (MulAut.conjNormal g z) rfl

private theorem natural_centralizer_iff (n : NaturalFactor π ⊤ Z ⊥)
    (B : Subgroup G) (z : Z) :
    (z : G) ∈ centralizer (B : Set G) ↔
      n.coordinates z ∈ fixedSpace ((B.map π).map n.marking.toMonoidHom) := by
  constructor
  · intro hc a ha
    obtain ⟨_, ⟨b, hb, rfl⟩, rfl⟩ := ha
    change vectorAction (n.marking (π b)) (n.coordinates z) = n.coordinates z
    rw [← natural_conj n]
    apply congrArg n.coordinates
    apply Subtype.ext
    change b * (z : G) * b⁻¹ = (z : G)
    rw [hc b hb, mul_inv_cancel_right]
  · intro hf b hb
    have hh := hf _ (mem_map_of_mem _ (mem_map_of_mem π hb))
    change vectorAction (n.marking (π b)) (n.coordinates z) = n.coordinates z at hh
    rw [← natural_conj n] at hh
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (n.equivOfBot.injective hh))

private theorem model_fixed_nontrivial (hπ : Function.Surjective π)
    (n : NaturalFactor π ⊤ Z ⊥) (g : SL) (i : Bool)
    (hfixed : Z ⊓ centralizer (parabolic π g i : Set G) ≠ ⊥) :
    fixedSpace (markedParabolic n.marking g i) ≠ ⊥ := by
  have hP : (parabolic π g i).map π = modelParabolic g i :=
    map_comap_eq_self_of_surjective hπ _
  intro hzero
  apply hfixed
  apply eq_bot_iff.mpr
  intro z hz
  have hv := (natural_centralizer_iff n (parabolic π g i) ⟨z, hz.1⟩).mp hz.2
  rw [hP] at hv
  change n.coordinates ⟨z, hz.1⟩ ∈ fixedSpace (markedParabolic n.marking g i) at hv
  rw [hzero] at hv
  have hz1 : (⟨z, hz.1⟩ : Z) = 1 := n.equivOfBot.injective
    ((mem_bot.mp hv).trans (map_one n.coordinates).symm)
  exact congrArg Subtype.val hz1

private theorem intersection_centralizes_of_model [Finite G]
    (hπ : Function.Surjective π) (n : NaturalFactor π ⊤ Z ⊥)
    (g : SL) (i : Bool) (K : Subgroup G)
    (hcard : Nat.card K ≤ 4)
    (hn : (pResidual 2 (parabolic π g i)).map (parabolic π g i).subtype ≤
      normalizer (K : Set G))
    (hmodel : ∀ A : Subgroup VectorGroup, Nat.card A ≤ 4 →
      (∀ a ∈ residual (markedParabolic n.marking g i),
        A.map (vectorAction a).toMonoidHom = A) →
      A ≤ fixedSpace (markedParabolic n.marking g i)) :
    K ⊓ Z ≤ centralizer (parabolic π g i : Set G) := by
  let P := parabolic π g i
  let T := (pResidual 2 P).map P.subtype
  let J := K ⊓ Z
  let A := (J.subgroupOf Z).map n.coordinates
  have hP : P.map π = modelParabolic g i := map_comap_eq_self_of_surjective hπ _
  have hT : (T.map π).map n.marking.toMonoidHom =
      residual (markedParabolic n.marking g i) := by
    rw [map_embedded_pResidual, map_embedded_pResidual, hP]
    rfl
  have hJA : Nat.card A = Nat.card J := by
    rw [card_map_of_injective n.equivOfBot.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv
  have hAJ : Nat.card A ≤ 4 := by
    rw [hJA]
    exact (Nat.card_le_card_of_injective (inclusion (inf_le_left : J ≤ K))
      (inclusion_injective _)).trans hcard
  have hnJ : T ≤ normalizer (J : Set G) :=
    (le_inf hn le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  have hAinv : ∀ a ∈ residual (markedParabolic n.marking g i),
      A.map (vectorAction a).toMonoidHom = A := by
    intro a ha
    rw [← hT] at ha
    obtain ⟨_, ⟨t, ht, rfl⟩, rfl⟩ := ha
    apply eq_of_le_of_card_ge
    · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨MulAut.conjNormal t z, ?_, natural_conj n t z⟩
      exact (mem_normalizer_iff.mp (hnJ ht) z).mp hz
    · exact (Nat.card_congr ((vectorAction (n.marking.toMonoidHom (π t))).subgroupMap A).toEquiv).le
  intro z hz
  apply (natural_centralizer_iff n P ⟨z, hz.2⟩).mpr
  rw [hP]
  exact hmodel A hAJ hAinv ⟨⟨z, hz.2⟩, hz, rfl⟩

/-- A subgroup of the natural Z of order at most four, obtained as K ∩ Z and
normalized by O²(P), is fixed by P when P has a nonzero fixed vector on Z. -/
theorem small_intersection_centralizes [Finite G]
    (hπ : Function.Surjective π) (n : NaturalFactor π ⊤ Z ⊥)
    (g : SL) (i : Bool) (K : Subgroup G)
    (hfixed : Z ⊓ centralizer (parabolic π g i : Set G) ≠ ⊥)
    (hcard : Nat.card K ≤ 4)
    (hn : (pResidual 2 (parabolic π g i)).map (parabolic π g i).subtype ≤
      normalizer (K : Set G)) :
    K ⊓ Z ≤ centralizer (parabolic π g i : Set G) :=
  intersection_centralizes_of_model hπ n g i K hcard hn
    (small_marked_residual_invariant n.marking g i
      (model_fixed_nontrivial hπ n g i hfixed))


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.CyclicNormalization.SmallInvariant.Natural
