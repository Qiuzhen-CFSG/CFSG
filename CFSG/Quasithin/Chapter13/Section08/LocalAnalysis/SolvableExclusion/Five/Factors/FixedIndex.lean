module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.RankTwo

/-!
# The two distinct counts in the order-four alternative

When one involution realizes its full displacement on a subgroup fixed by
the other, their fixed subgroups generate the whole module. The index of
the common fixed subgroup is therefore the product of their individual
indices. Separately, disjoint support planes make the full displacement
have order sixteen. These prove both counts needed in the equality case;
displacement order by itself does not determine a common fixed index.

This is the counting step in Aschbacher–Smith, combined manuscript
(1 March 2004), 13.8.13, printed p.951, before applying F.9.16(2).
The construction of the two involutions and their split support actions
remains an obligation of the actor-alternative argument.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open Subgroup
variable {W : Type*} [CommGroup W]

private def displacement (t : MulAut W) : W →* W where
  toFun w := w⁻¹ * t w
  map_one' := by simp
  map_mul' x y := by
    simp only [mul_inv_rev, map_mul]
    ac_rfl

private theorem two_actor_eq_one_or_eq (A : Subgroup (MulAut W))
    (hA : Nat.card A = 2) (t : A) (ht : t ≠ 1) (b : A) : b = 1 ∨ b = t := by
  by_cases hb : b = 1
  · exact Or.inl hb
  · obtain ⟨s, _, hs⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
    exact Or.inr ((hs b hb).trans (hs t ht).symm)

private theorem displacement_ker (A : Subgroup (MulAut W))
    (hA : Nat.card A = 2) (t : A) (ht : t ≠ 1) :
    (displacement (t : MulAut W)).ker = FixedPoints.subgroup A W := by
  ext w
  constructor
  · intro hw b
    have htfix : (t : MulAut W) w = w := (inv_mul_eq_one.mp hw).symm
    rcases two_actor_eq_one_or_eq A hA t ht b with rfl | rfl
    · exact one_smul A w
    · exact htfix
  · intro hw
    exact inv_mul_eq_one.mpr (hw t).symm

private theorem displacement_map (A : Subgroup (MulAut W))
    (hA : Nat.card A = 2) (t : A) (ht : t ≠ 1) (X : Subgroup W) :
    X.map (displacement (t : MulAut W)) = commutatorSubgroup A W X := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact subset_closure ⟨t, x, hx, rfl⟩
  · rw [commutatorSubgroup, closure_le]
    rintro _ ⟨b, x, hx, rfl⟩
    rcases two_actor_eq_one_or_eq A hA t ht b with rfl | rfl
    · change x⁻¹ * ((1 : A) • x) ∈ X.map (displacement (t : MulAut W))
      simp only [one_smul, inv_mul_cancel]
      exact (X.map (displacement (t : MulAut W))).one_mem
    · exact mem_map_of_mem _ hx

private theorem fixed_sup (A B : Subgroup (MulAut W)) :
    FixedPoints.subgroup (A ⊔ B : Subgroup (MulAut W)) W =
      FixedPoints.subgroup A W ⊓ FixedPoints.subgroup B W := by
  ext w
  constructor
  · intro hw
    exact ⟨fun a => hw ⟨a, (show A ≤ A ⊔ B from le_sup_left) a.property⟩,
      fun b => hw ⟨b, (show B ≤ A ⊔ B from le_sup_right) b.property⟩⟩
  · rintro ⟨hA, hB⟩ b
    have hfix : A ⊔ B ≤ MulAction.stabilizer (MulAut W) w :=
      sup_le (fun a ha => hA ⟨a, ha⟩) (fun a ha => hB ⟨a, ha⟩)
    exact hfix b.property

/-- Full displacement on a subgroup fixed by the other involution makes
the two fixed indices multiply. No common fixed-index assertion follows
from disjoint displacement subgroups alone. -/
theorem fixed_index_mul_of_split_involutions [Finite W]
    (A B : Subgroup (MulAut W)) (X : Subgroup W)
    (hA : Nat.card A = 2) (hB : Nat.card B = 2)
    (hfixed : X ≤ FixedPoints.subgroup B W)
    (hfull : commutatorSubgroup A W X = commutatorAction A W) :
    (FixedPoints.subgroup (A ⊔ B : Subgroup (MulAut W)) W).index =
      Nat.card (commutatorAction A W) * Nat.card (commutatorAction B W) := by
  obtain ⟨t, ht, _⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  obtain ⟨u, hu, _⟩ := (Nat.card_eq_two_iff' (1 : B)).mp hB
  let CA := FixedPoints.subgroup A W
  let CB := FixedPoints.subgroup B W
  have hcover : CA ⊔ CB = ⊤ := by
    apply top_unique
    intro w _
    have hw : displacement (t : MulAut W) w ∈
        X.map (displacement (t : MulAut W)) := by
      rw [displacement_map A hA t ht, hfull]
      exact subset_closure ⟨t, w, mem_top w, rfl⟩
    obtain ⟨x, hx, he⟩ := hw
    have hwx : w * x⁻¹ ∈ CA := by
      dsimp only [CA]
      rw [← displacement_ker A hA t ht]
      change displacement (t : MulAut W) (w * x⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    have hm : (w * x⁻¹) * x ∈ CA ⊔ CB :=
      (CA ⊔ CB).mul_mem ((show CA ≤ CA ⊔ CB from le_sup_left) hwx)
        ((show CB ≤ CA ⊔ CB from le_sup_right) (hfixed hx))
    simpa only [inv_mul_cancel_right] using hm
  have hidx : (CA ⊓ CB).index = CA.index * CB.index := by
    rw [← relIndex_mul_index (show CA ⊓ CB ≤ CB from inf_le_right), inf_relIndex_right,
      ← relIndex_sup_left CB CA, hcover, relIndex_top_right]
  have hidxA : CA.index = Nat.card (commutatorAction A W) := by
    dsimp only [CA]
    rw [← displacement_ker A hA t ht, index_ker, MonoidHom.range_eq_map,
      displacement_map A hA t ht]
  have hidxB : CB.index = Nat.card (commutatorAction B W) := by
    dsimp only [CB]
    rw [← displacement_ker B hB u hu, index_ker, MonoidHom.range_eq_map,
      displacement_map B hB u hu]
  rw [fixed_sup]
  exact hidx.trans (congrArg₂ (· * ·) hidxA hidxB)

theorem fixed_index_sixteen_of_split_planes [Finite W]
    (A B : Subgroup (MulAut W)) (X : Subgroup W)
    (hA : Nat.card A = 2) (hB : Nat.card B = 2)
    (hfixed : X ≤ FixedPoints.subgroup B W)
    (hfull : commutatorSubgroup A W X = commutatorAction A W)
    (hplaneA : Nat.card (commutatorAction A W) = 4)
    (hplaneB : Nat.card (commutatorAction B W) = 4) :
    (FixedPoints.subgroup (A ⊔ B : Subgroup (MulAut W)) W).index = 16 := by
  rw [fixed_index_mul_of_split_involutions A B X hA hB hfixed hfull, hplaneA, hplaneB]

/-- The separate fixed-index and displacement-order calculations for the
two-factor alternative. The two conclusions are proved from the support
actions; neither of the two cardinalities is inferred from the other. -/
theorem split_planes_equality_case [Finite W]
    (A B : Subgroup (MulAut W)) (X Y : Subgroup W)
    (hA : Nat.card A = 2) (hB : Nat.card B = 2)
    (hfixed : X ≤ FixedPoints.subgroup B W)
    (hfull : commutatorSubgroup A W X = commutatorAction A W)
    (hplaneA : Nat.card (commutatorAction A W) = 4)
    (hplaneB : Nat.card (commutatorAction B W) = 4)
    (hAX : commutatorAction A W ≤ X) (hBY : commutatorAction B W ≤ Y)
    (hXY : Disjoint X Y) :
    Nat.card (commutatorAction (A ⊔ B : Subgroup (MulAut W)) W) = 16 ∧
      (FixedPoints.subgroup (A ⊔ B : Subgroup (MulAut W)) W).index = 16 := by
  refine ⟨?_, fixed_index_sixteen_of_split_planes A B X hA hB hfixed hfull hplaneA hplaneB⟩
  rw [commutatorAction_sup,
    card_sup_eq_mul_of_normalizes_of_disjoint _ _ le_normalizer_of_normal
      (hXY.mono hAX hBY), hplaneA, hplaneB]

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
end
