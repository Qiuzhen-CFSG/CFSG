module

public import CFSG.Quasithin.Chapter2.Section01To03.Bender.ComponentActor
public import Theory.GroupTheory.ThreeCommutingLocalActions
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-!
# The three-component obstruction in the source Bender argument

The source normalizer acts transitively on the nonidentity elements of
Q = U intersect L. Its odd-prime action lifts to the literal L intersect M,
and three conjugate lifts commute when their components commute. Their
independent actions on the three Q-conjugates give rank three inside the
normalizer of the join, which is an actual two-local subgroup.

The final theorem supplies this witness to the existing maximal-component
geometry consumer. Its separate three-component-rank premise is discharged
from the existing size and local-transitivity hypotheses. Component centers
and the full action kernel are retained. The projected splitting, the actual
Bender-model normalizer action and genuine I.3.2 balance remain source inputs.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Proposition 2.2.2, printed p.520 (PDF p.537).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter2.BenderFusion
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizer_action_order_map
    (Q : Subgroup G) (b : G) (hb : b ∈ normalizer (Q : Set G)) (e : G ≃* G)
    (he : e b ∈ normalizer (Q.map e.toMonoidHom : Set G)) :
    orderOf ((Q.map e.toMonoidHom).normalizerMonoidHom ⟨e b, he⟩) =
      orderOf (Q.normalizerMonoidHom ⟨b, hb⟩) := by
  let E : Q ≃* Q.map e.toMonoidHom := e.subgroupMap Q
  let a : MulAut Q := Q.normalizerMonoidHom ⟨b, hb⟩
  let a' : MulAut (Q.map e.toMonoidHom) :=
    (Q.map e.toMonoidHom).normalizerMonoidHom ⟨e b, he⟩
  have hc (q : Q) : a' (E q) = E (a q) := by
    apply Subtype.ext
    change e b * e (q : G) * (e b)⁻¹ = e (b * (q : G) * b⁻¹)
    simp only [map_mul, map_inv]
  have heq : a' = MulAut.congr E a := by
    apply MulEquiv.ext
    intro q
    obtain ⟨q, rfl⟩ := E.surjective q
    change a' (E q) = E (a (E.symm (E q)))
    rw [E.symm_apply_apply]
    exact hc q
  change orderOf a' = orderOf a
  rw [heq]
  exact orderOf_injective (MulAut.congr E).toMonoidHom (MulAut.congr E).injective a

/-- The source three-component rank witness follows from its existing local
transitivity and size hypotheses. All conjugation images and the two-local
normalizer in the conclusion are actual subgroups of the indicated groups. -/
theorem component_three_rank_witness_of_local_transitivity
    {T : Sylow 2 G} {M : Subgroup G} (w : LocalControlWitness T M)
    (L : Subgroup G) (hsize : 2 < Nat.card (w.U ⊓ L : Subgroup G))
    (hlocal : ∀ a ∈ w.U ⊓ L, a ≠ 1 → ∀ b ∈ w.U ⊓ L, b ≠ 1 →
      ∃ l ∈ L ⊓ M, l * a * l⁻¹ = b)
    (x y z : M)
    (hxy : componentConjugate L x ≤ centralizer (componentConjugate L y : Set G))
    (hxz : componentConjugate L x ≤ centralizer (componentConjugate L z : Set G))
    (hyz : componentConjugate L y ≤ centralizer (componentConjugate L z : Set G)) :
    ∃ H : Subgroup G, IsTwoLocal H ∧ ∃ p : ℕ, p.Prime ∧ Odd p ∧ 3 ≤ primeRank p H := by
  let Q : Subgroup G := w.U ⊓ L
  let N : Subgroup G := L ⊓ M
  have hNQ : N ≤ normalizer (Q : Set G) :=
    (le_inf (inf_le_right.trans w.normalizes) (inf_le_left.trans L.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hU : IsPGroup 2 w.U := by
    let _ := w.elementary
    exact IsElementaryAbelian.isPGroup 2 w.U
  have ht : ∀ a : Q, a ≠ 1 → ∀ b : Q, b ≠ 1 →
      ∃ n : N, conjugationAction N Q hNQ n a = b := by
    intro a ha b hb
    obtain ⟨n, hn, hab⟩ := hlocal a a.property (fun he => ha (Subtype.ext he))
      b b.property (fun he => hb (Subtype.ext he))
    exact ⟨⟨n, hn⟩, Subtype.ext hab⟩
  obtain ⟨p, hp, hop, n, hn⟩ := exists_odd_prime_conjugation_action N Q hNQ
    (hU.to_le inf_le_left) hsize ht
  let _ : Fact p.Prime := ⟨hp⟩
  let s : Fin 3 → M := ![x, y, z]
  let e (i : Fin 3) := MulAut.conj ((s i : M) : G)
  let Li (i : Fin 3) := componentConjugate L (s i)
  let Qi (i : Fin 3) := componentConjugate Q (s i)
  let b (i : Fin 3) : G := e i (n : G)
  have hu (i : Fin 3) : componentConjugate w.U (s i) = w.U :=
    mem_normalizer_iff_map_conj_eq.mp (w.normalizes (s i).property)
  have hQU (i : Fin 3) : Qi i ≤ w.U := by
    rw [← hu i]
    exact map_mono inf_le_left
  have hQne : Q ≠ ⊥ := by
    intro he
    change 2 < Nat.card Q at hsize
    rw [he, card_bot] at hsize
    omega
  have hQine : Qi 0 ≠ ⊥ := by
    intro he
    exact hQne ((Q.map_eq_bot_iff_of_injective (e 0).injective).mp he)
  have hQL (i : Fin 3) : Qi i ≤ Li i := map_mono inf_le_right
  have hbL (i : Fin 3) : b i ∈ Li i := mem_map_of_mem (e i).toMonoidHom n.property.1
  have hLi (i j : Fin 3) (hij : i ≠ j) : Li i ≤ centralizer (Li j : Set G) := by
    fin_cases i <;> fin_cases j
    all_goals dsimp only [Li, s] at *
    all_goals first
      | exact (hij rfl).elim
      | exact hxy
      | exact hxz
      | exact hyz
      | exact fun a ha b hb => (hxy hb a ha).symm
      | exact fun a ha b hb => (hxz hb a ha).symm
      | exact fun a ha b hb => (hyz hb a ha).symm
  have hc (i j : Fin 3) : Commute (b i) (b j) := by
    by_cases hij : i = j
    · subst j
      exact Commute.refl _
    · exact (hLi i j hij (hbL i) (b j) (hbL j)).symm
  have hoff (i j : Fin 3) (hij : i ≠ j) : b j ∈ centralizer (Qi i : Set G) :=
    centralizer_le (hQL i) (hLi j i (Ne.symm hij) (hbL j))
  have hdiag (i : Fin 3) : b i ∈ normalizer (Qi i : Set G) :=
    le_normalizer_map (e i).toMonoidHom (mem_map_of_mem _ (hNQ n.property))
  have hnorm (i j : Fin 3) : b i ∈ normalizer (Qi j : Set G) := by
    by_cases hij : i = j
    · subst j
      exact hdiag i
    · exact Subgroup.centralizer_le_normalizer _ (hoff j i (Ne.symm hij))
  have horder (i : Fin 3) :
      orderOf ((Qi i).normalizerMonoidHom ⟨b i, hnorm i i⟩) = p :=
    (normalizer_action_order_map Q n (hNQ n.property) (e i) (hnorm i i)).trans hn
  obtain ⟨H, hH, hr⟩ := three_cyclic_actions_local_rank w.U Qi b hU hQU hQine
    hnorm hc hoff p horder
  exact ⟨H, hH, p, hp, hop, hr⟩

/-- The actual Bender consumer with its former `hthree` premise proved from
the already required source normalizer transitivity and size. -/
theorem false_of_maximal_component_geometry_of_local_transitivity
    {T : Sylow 2 G} {M : Subgroup G} (w : LocalControlWitness T M)
    {C : GroupClass} (hG : IsSimpleQTKE C G)
    (hTM : (T : Subgroup G) ≤ M)
    (L : Subgroup G)
    (hmax : Maximal (fun K => K ∈ badCentralizerComponents w) L)
    (hsplit : w.U = componentFixedSubgroup w L ⊔ (w.U ⊓ L))
    (hbalance : ∀ v ∈ componentFixedSubgroup w L, v ≠ 1 →
      ∃ K : Subgroup G, IsComponentIn K (centralizer ({v} : Set G)) ∧ L ≤ K)
    (hsize : 2 < Nat.card (w.U ⊓ L : Subgroup G))
    (hcyclic : IsCyclic (componentActor w L)) (hodd : Odd (Nat.card (componentActor w L)))
    (hUL : w.U ≤ normalizer (L : Set G))
    (hlocal : ∀ a ∈ w.U ⊓ L, a ≠ 1 → ∀ b ∈ w.U ⊓ L, b ≠ 1 →
      ∃ l ∈ L ⊓ M, l * a * l⁻¹ = b) : False := by
  apply w.false_of_maximal_component_geometry hG hTM L hmax hsplit hbalance
    _ hsize hcyclic hodd hUL hlocal
  intro x y z _ _ _ hxy hxz hyz
  exact component_three_rank_witness_of_local_transitivity w L hsize hlocal x y z hxy hxz hyz

end CFSG.Quasithin.Chapter2.BenderFusion
