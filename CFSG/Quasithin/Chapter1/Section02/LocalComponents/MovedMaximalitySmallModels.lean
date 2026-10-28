module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalityObstruction
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SmallAlternating
public import Theory.SpecificGroups.PSL2.QuadraticNonsolvableSylowOvergroups

/-!
# The small models in the moved-component embedding restriction

Bender groups, A₅ and A₆ have solvable proper full-Sylow overgroups.
Dickson's theorem makes every nonsolvable proper overgroup in odd-prime
PSL₂ an A₅. In the quadratic-prime case the full Sylow leaves only PSL₂(p)
and PGL₂(p); their nontrivial perfect subnormal subgroups are respectively
the whole PSL₂ and the distinguished PSL₂ derived subgroup. Thus all
these models have at most one C-component in every full-Sylow overgroup.

Applying these facts to the actual simple radical quotient of a normalized
overcomponent removes these families from the moved-component obstruction.
The remaining list retains actual model isomorphisms. Its model exclusions
are still needed for unconditional 1.2.8(3).
Source: Aschbacher--Smith, A.3.12, pp.47--48, and 1.2.8, pp.506--507.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
variable {G : Type*} [Group G] [Finite G]

/-- The three binary rank-one families have unique components in Sylow overgroups. -/
theorem bender_sylow_overgroup_component_unique [IsSimpleGroup G] [Group.IsPerfect G]
    (hm : ClassificationModels.IsBenderModel G) : SylowOvergroupComponentUnique G :=
  SylowOvergroupComponentUnique.of_solvable_proper_overgroups
    (ChapterA.Section03.SourceEmbeddings.bender_solvable_proper_sylow_overgroup hm)

/-- The A₅ and A₆ full-Sylow overgroups have at most one C-component. -/
theorem small_alternating_sylow_overgroup_component_unique
    [IsSimpleGroup G] [Group.IsPerfect G]
    (hm : LocalModels.IsAlternating G 5 ∨ LocalModels.IsAlternating G 6) :
    SylowOvergroupComponentUnique G := by
  apply SylowOvergroupComponentUnique.of_solvable_proper_overgroups
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    exact SolvableSylowOvergroups.of_equiv e (fun _ P _ hP =>
      alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP)
  · obtain ⟨e⟩ := hm
    exact SolvableSylowOvergroups.of_equiv e AlternatingSix.ProperSylowOvergroups.isSolvable

private theorem components_unique_prime_linear
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (ho : Odd p)
    (hm : Nonempty (H ≃* BenderSuzuki.MatrixGroups.PSL2MatrixGroup (GaloisField p 1)) ∨
      Nonempty (H ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p 1)))
    {B C : Subgroup H} (hB : B.IsCComponent) (hC : C.IsCComponent) : B = C := by
  have hcard : Nat.card (GaloisField p 1) = p := by
    simpa using GaloisField.card p 1 (by decide)
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p 1)) :=
    ⟨p,1,Fact.out,ho,by decide,by simpa using hcard⟩
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    have hb := hB.map_equiv e
    have hc := hC.map_equiv e
    apply map_injective (f := e.toMonoidHom) e.injective
    exact (GorensteinWalter.psl2_perfect_subnormal_eq_top _ hodd _
      hb.ne_bot hb.perfect hb.subnormal).2.trans
      (GorensteinWalter.psl2_perfect_subnormal_eq_top _ hodd _
        hc.ne_bot hc.perfect hc.subnormal).2.symm
  · obtain ⟨e⟩ := hm
    have hb := hB.map_equiv e
    have hc := hC.map_equiv e
    apply map_injective (f := e.toMonoidHom) e.injective
    exact (GorensteinWalter.pgl2_perfect_subnormal_eq_commutator _ hodd _
      hb.ne_bot hb.perfect hb.subnormal).2.trans
      (GorensteinWalter.pgl2_perfect_subnormal_eq_commutator _ hodd _
        hc.ne_bot hc.perfect hc.subnormal).2.symm

/-- Both odd PSL₂ rows in Theorem C have unique components in Sylow overgroups. -/
theorem odd_linear_sylow_overgroup_component_unique
    [IsSimpleGroup G] [Group.IsPerfect G]
    {p n : ℕ} (hp : p.Prime) (ho : Odd p) (hn : n = 1 ∨ n = 2)
    (hm : ClassicalGroup.IsPSL G 2 (p ^ n)) : SylowOvergroupComponentUnique G := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) := e.symm.isSimpleGroup
  let : Group.IsPerfect (BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  apply SylowOvergroupComponentUnique.of_equiv e
  apply SylowOvergroupComponentUnique.of_proper_overgroups
  intro S P hSP hP B C hB hC
  have hns : ¬ Group.IsSolvable P := fun h => by
    let := h
    exact hB.not_isSolvable inferInstance
  rcases hn with rfl | rfl
  · rw [pow_one] at hF
    obtain ⟨_,_,⟨a⟩⟩ := Theory.PSL2.prime_nonsolvable_proper_is_alternating_five
      ho hF P hP hns
    have ht (D : Subgroup P) (hD : D.IsCComponent) : D = ⊤ := by
      by_contra hne
      exact hD.not_isSolvable (alternatingGroup.isSolvable_subgroup_of_equiv_five a D hne)
    exact (ht B hB).trans (ht C hC).symm
  · exact components_unique_prime_linear ho
      (Theory.PSL2.quadratic_nonsolvable_proper_sylow_models ho hF S P hSP hP hns) hB hC

/-- The actual remaining simple carriers after the proved small-model exclusions. -/
@[expose] def RemainingSimpleModel (G : Type*) [Group G] : Prop :=
  (LocalModels.IsAlternating G 7 ∨ LocalModels.IsAlternating G 8) ∨
  (∃ (p : ℕ), p.Prime ∧ Odd p ∧ ∃ unitary : Bool, LocalModels.IsPSLSign G unitary 3 p) ∨
  LocalModels.RankTwoTheoremC G ∨
  (ClassicalGroup.IsPSL G 4 2 ∨ ClassicalGroup.IsPSL G 5 2) ∨
  ChapterA.Section02.IsTheoremCSporadicModel G

/-- Failure of component uniqueness eliminates the rank-one and small alternating rows. -/
theorem remaining_simple_model_of_not_unique [IsSimpleGroup G] [Group.IsPerfect G]
    (hm : LocalModels.TheoremCModel G) (hu : ¬ SylowOvergroupComponentUnique G) :
    RemainingSimpleModel G := by
  cases hm with
  | alternating n hn iso =>
    by_cases h5 : n = 5
    · subst n
      exact (hu (small_alternating_sylow_overgroup_component_unique (Or.inl iso))).elim
    by_cases h6 : n = 6
    · subst n
      exact (hu (small_alternating_sylow_overgroup_component_unique (Or.inr iso))).elim
    have hn78 : n = 7 ∨ n = 8 := by omega
    left
    rcases hn78 with rfl | rfl
    · exact Or.inl iso
    · exact Or.inr iso
  | linear_odd p n hp ho hn _ iso =>
    exact (hu (odd_linear_sylow_overgroup_component_unique hp ho hn iso)).elim
  | three_odd p hp ho unitary iso =>
    exact Or.inr (Or.inl ⟨p,hp,ho,unitary,iso⟩)
  | rank_one iso => exact (hu (bender_sylow_overgroup_component_unique iso)).elim
  | rank_two iso => exact Or.inr (Or.inr (Or.inl iso))
  | binary_linear n hn iso =>
    right; right; right; left
    rcases hn with rfl | rfl
    · exact Or.inl iso
    · exact Or.inr iso
  | sporadic name hne iso =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨name,hne,iso⟩))))
  | janko_one iso => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr iso))))

/-- The small-model calculations apply to the literal radical quotient of
the original normalized overcomponent. No new ambient or model hypotheses occur. -/
theorem moved_normalized_remaining_simple_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    IsSimpleGroup Q ∧ ¬ IsMulCommutative Q ∧ RemainingSimpleModel Q ∧
      ¬ SylowOvergroupComponentUnique Q := by
  obtain ⟨hs,hna,hmodel,hu⟩ := moved_normalized_simple_quotient_obstruction
    hG T hB hK hBK hTK hm
  let := hs
  let := hK.1.perfect
  exact ⟨hs,hna,remaining_simple_model_of_not_unique hmodel hu,hu⟩

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
