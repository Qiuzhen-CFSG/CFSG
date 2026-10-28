module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.FullLevi.Separation

/-!
# A central torus factor for the full triality Levi

An off-subsystem coroot scales every adjacent subsystem root by the inverse
of its parameter. Choose its unique square root in the characteristic-two
field and put that parameter on the subsystem coroots. The two words act
identically on all subsystem generators, so their quotient centralizes the
subsystem. This splits the full Levi into the subsystem and its centralizing
torus. Centerlessness proves uniqueness of the two factors. Both factors
are preserved by the actual graph-field automorphism.

Source: the diagonal actions in GLS3 §2.4 and Theorem 2.6.5(f,g)
(`refs/KGroup/GLS3/chapter2.tex`). No preservation of joins by fixed points
is used.
-/

@[expose] public section

open Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.Standard.RadicalCoordinates
open Parabolics ConcreteBruhat TorusCoordinates
noncomputable section

private theorem conjugate_mul {G : Type*} [Group G] (g h x : G) :
    (g * h) * x * (g * h)⁻¹ = g * (h * x * h⁻¹) * g⁻¹ := by group

private theorem same_conjugation_iff {G : Type*} [Group G] (g h x : G) :
    g * x * g⁻¹ = h * x * h⁻¹ ↔ x * (h⁻¹ * g) = (h⁻¹ * g) * x := by
  constructor <;> intro he
  · calc
      x * (h⁻¹ * g) = h⁻¹ * (h * x * h⁻¹) * g := by group
      _ = h⁻¹ * (g * x * g⁻¹) * g := by rw [he]
      _ = (h⁻¹ * g) * x := by group
  · calc
      g * x * g⁻¹ = h * ((h⁻¹ * g) * x) * g⁻¹ := by group
      _ = h * (x * (h⁻¹ * g)) * g⁻¹ := by rw [he]
      _ = h * x * h⁻¹ := by group

private theorem torusWord_mem_splitLevi (P : Parameters) (a : Node) (i : Fin 4)
    (hi : i ∈ a.support) (t : (ExtensionField P)ˣ) :
    torusWord P i t ∈ splitLevi P a := by
  have hw (u : ExtensionField P) : weylWord P i u ∈ splitLevi P a := by
    have hp (v : ExtensionField P) : positiveRoot P i v ∈ splitLevi P a :=
      Subgroup.subset_closure ⟨i, hi, v, Or.inl rfl⟩
    have hn (v : ExtensionField P) : negativeRoot P i v ∈ splitLevi P a :=
      Subgroup.subset_closure ⟨i, hi, v, Or.inr rfl⟩
    exact (splitLevi P a).mul_mem ((splitLevi P a).mul_mem (hp u) (hn _)) (hp u)
  exact (splitLevi P a).mul_mem (hw _) (hw _)

/-- A common coroot parameter on the subsystem vertices. -/
def leviTorusWord (P : Parameters) (a : Node) (s : (ExtensionField P)ˣ) : SplitGroup P :=
  match a with
  | .arms => torusWord P 0 s * torusWord P 2 s * torusWord P 3 s
  | .central => torusWord P 1 s

lemma leviTorusWord_mem (P : Parameters) (a : Node) (s : (ExtensionField P)ˣ) :
    leviTorusWord P a s ∈ splitLevi P a ⊓ splitTorus P := by
  have hT (i : Fin 4) : torusWord P i s ∈ splitTorus P :=
    Subgroup.subset_closure ⟨i, s, rfl⟩
  cases a
  · exact ⟨(splitLevi P .arms).mul_mem ((splitLevi P .arms).mul_mem
      (torusWord_mem_splitLevi P .arms 0 (by decide : (0 : Fin 4) ≠ 1) s)
      (torusWord_mem_splitLevi P .arms 2 (by decide : (2 : Fin 4) ≠ 1) s))
      (torusWord_mem_splitLevi P .arms 3 (by decide : (3 : Fin 4) ≠ 1) s),
      (splitTorus P).mul_mem ((splitTorus P).mul_mem (hT 0) (hT 2)) (hT 3)⟩
  · exact ⟨torusWord_mem_splitLevi P .central 1 rfl s, hT 1⟩

private lemma leviTorusWord_positive (P : Parameters) (hp : P.prime = 2)
    (a : Node) (i j : Fin 4) (hi : i ∉ a.support) (hj : j ∈ a.support)
    (t s : (ExtensionField P)ˣ) (hs : s.val ^ 2 = t.val⁻¹) (u : ExtensionField P) :
    leviTorusWord P a s * positiveRoot P j u * (leviTorusWord P a s)⁻¹ =
      torusWord P i t * positiveRoot P j u * (torusWord P i t)⁻¹ := by
  cases a <;> fin_cases i <;> fin_cases j
  all_goals simp only [Node.support, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hi hj
  all_goals try contradiction
  all_goals simp only [leviTorusWord, conjugate_mul, torusWord_positiveRoot_conjugate_cartan P hp]
  all_goals simp [typeDCartanMatrix, hs]

private lemma leviTorusWord_negative (P : Parameters) (hp : P.prime = 2)
    (a : Node) (i j : Fin 4) (hi : i ∉ a.support) (hj : j ∈ a.support)
    (t s : (ExtensionField P)ˣ) (hs : s.val ^ 2 = t.val⁻¹) (u : ExtensionField P) :
    leviTorusWord P a s * negativeRoot P j u * (leviTorusWord P a s)⁻¹ =
      torusWord P i t * negativeRoot P j u * (torusWord P i t)⁻¹ := by
  cases a <;> fin_cases i <;> fin_cases j
  all_goals simp only [Node.support, Set.mem_ofPred_eq, Set.mem_singleton_iff] at hi hj
  all_goals try contradiction
  all_goals simp only [leviTorusWord, conjugate_mul, torusWord_negativeRoot_conjugate P hp]
  all_goals simp [typeDCartanMatrix, hs]


/-- The part of the split torus centralizing the subsystem Levi. -/
def splitCentralTorus (P : Parameters) (a : Node) : Subgroup (SplitGroup P) :=
  splitTorus P ⊓ Subgroup.centralizer (splitLevi P a : Set (SplitGroup P))

private lemma torusWord_adjustment (P : Parameters) (hp : P.prime = 2)
    (a : Node) (i : Fin 4) (hi : i ∉ a.support) (t : (ExtensionField P)ˣ) :
    ∃ s : (ExtensionField P)ˣ,
      (leviTorusWord P a s)⁻¹ * torusWord P i t ∈ splitCentralTorus P a := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have hsq : Function.Surjective (fun s : (ExtensionField P)ˣ => s ^ 2) := by
    apply Finite.surjective_of_injective
    intro s u he
    apply Units.ext
    apply CharTwo.sq_injective
    exact congrArg Units.val he
  obtain ⟨s, hs⟩ := hsq t⁻¹
  have hsval : s.val ^ 2 = t.val⁻¹ := by
    simpa only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val] using congrArg Units.val hs
  refine ⟨s, (splitTorus P).mul_mem ((splitTorus P).inv_mem (leviTorusWord_mem P a s).2)
    (Subgroup.subset_closure ⟨i, t, rfl⟩), ?_⟩
  change (leviTorusWord P a s)⁻¹ * torusWord P i t ∈
    Subgroup.centralizer (splitLevi P a : Set (SplitGroup P))
  rw [splitLevi, Subgroup.centralizer_closure]
  apply Subgroup.mem_centralizer_iff.mpr
  rintro x ⟨j, hj, u, rfl | rfl⟩
  · exact (same_conjugation_iff _ _ _).mp
      (leviTorusWord_positive P hp a i j hi hj t s hsval u).symm
  · exact (same_conjugation_iff _ _ _).mp
      (leviTorusWord_negative P hp a i j hi hj t s hsval u).symm

/-- Unique square roots supply a central torus complement to the subsystem. -/
theorem splitFullLevi_eq_sup_centralTorus (P : Parameters) (hp : P.prime = 2)
    (a : Node) : splitFullLevi P a = splitLevi P a ⊔ splitCentralTorus P a := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, t, rfl⟩
    by_cases hi : i ∈ a.support
    · exact Subgroup.mem_sup_left (torusWord_mem_splitLevi P a i hi t)
    · obtain ⟨s, hs⟩ := torusWord_adjustment P hp a i hi t
      have hm := Subgroup.mul_mem (splitLevi P a ⊔ splitCentralTorus P a)
        (Subgroup.mem_sup_left (leviTorusWord_mem P a s).1) (Subgroup.mem_sup_right hs)
      change torusWord P i t ∈ splitLevi P a ⊔ splitCentralTorus P a
      simpa only [mul_inv_cancel_left] using hm
  · exact sup_le le_sup_left ((show splitCentralTorus P a ≤ splitTorus P from inf_le_left).trans
      le_sup_right)

/-- The centerless subsystem meets its central torus trivially. -/
theorem disjoint_splitLevi_splitCentralTorus (P : Parameters) (hp : P.prime = 2)
    (a : Node) : Disjoint (splitLevi P a) (splitCentralTorus P a) := by
  apply Subgroup.disjoint_def.mpr
  intro g hg hc
  have hh : (⟨g, hg⟩ : splitLevi P a) ∈ Subgroup.center (splitLevi P a) := by
    apply Subgroup.mem_center_iff.mpr
    intro x
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hc.2 x.val x.property)
  rw [splitLevi_center_eq_bot P hp a] at hh
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hh)

/-- The actual graph-field automorphism preserves the central torus factor. -/
theorem graphField_mem_splitCentralTorus (P : Parameters) (a : Node)
    {t : SplitGroup P} (ht : t ∈ splitCentralTorus P a) :
    graphFieldAutomorphism P t ∈ splitCentralTorus P a := by
  refine ⟨(splitTorus_invariant P).le ⟨t, ht.1, rfl⟩, ?_⟩
  apply Subgroup.mem_centralizer_iff.mpr
  intro l hl
  obtain ⟨k, hk, rfl⟩ := (splitLevi_invariant P a).ge hl
  change graphFieldAutomorphism P k * graphFieldAutomorphism P t =
    graphFieldAutomorphism P t * graphFieldAutomorphism P k
  simpa only [map_mul] using congrArg (graphFieldAutomorphism P)
    (Subgroup.mem_centralizer_iff.mp ht.2 k hk)

open scoped Pointwise in
/-- Multiplication gives the full Levi from its subsystem and central torus. -/
theorem splitFullLevi_eq_mul_centralTorus (P : Parameters) (hp : P.prime = 2)
    (a : Node) : (splitFullLevi P a : Set (SplitGroup P)) =
      (splitLevi P a : Set (SplitGroup P)) * splitCentralTorus P a := by
  rw [splitFullLevi_eq_sup_centralTorus P hp a]
  exact Subgroup.coe_mul_of_right_le_normalizer_left _ _
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))

end
end Triality.Standard.RadicalCoordinates
