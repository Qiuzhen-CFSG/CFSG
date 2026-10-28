module

public import Theory.Representation.QuadraticFourGroup.CubicSections.SplitSection
public import Theory.Representation.QuadraticFourGroup.Recognition.OddTranspositions.Definitions
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The diagonal of a split component orbit

For the actual product embedding in `SplitOrbit`, conjugation by the marked
involution sends the first factor onto the second. Unique product coordinates
identify its centralizer in the orbit with the simple diagonal
`x ↦ x xᵃ`. The four-group normalizes this diagonal and acts nontrivially on it:
a diagonal centralizer which preserves the first factor centralizes that factor,
and otherwise differs from the swapping involution by such an element.
The trivial component centralizer would therefore bound the four-group by
its order-two subgroup. Simplicity now gives `[K,B] = K` for this actual diagonal.

Source: GLS, volume 2, Theorem 25.14, Step 3, `refs/KGroup/GLS2/ChapterG.tex`,
lines 850–880. Only the already supplied split orbit is used; no representation
conclusion or additional diagonal hypothesis is assumed.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace Representation.QuadraticFourGroup.SplitOrbit
variable {Q V : Type*} [Group Q] [AddCommGroup V] [Module (ZMod 2) V]
  {τ : Representation (ZMod 2) Q V} {n : ℕ} (d : SplitOrbit τ n)

noncomputable abbrev first : Factor n →* Q := d.embedding.comp (MonoidHom.inl _ _)
noncomputable abbrev second : Factor n →* Q := d.embedding.comp (MonoidHom.inr _ _)

lemma first_injective : Function.Injective d.first :=
  fun _ _ h => congrArg Prod.fst (d.injective h)
lemma second_injective : Function.Injective d.second :=
  fun _ _ h => congrArg Prod.snd (d.injective h)

include d in
lemma factor_simple : IsSimpleGroup (Factor n) := by
  apply Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
  rw [GaloisField.card 2 n (by have := d.one_lt; omega)]
  exact (show 4 = 2 ^ 2 by rfl).le.trans
    (Nat.pow_le_pow_right (by decide) (by have := d.one_lt; omega))

include d in
private lemma factor_center : center (Factor n) = ⊥ := by
  let := d.factor_simple
  let := d.hypotheses.component.2
  let e := MonoidHom.ofInjective d.first_injective
  let : Group.IsPerfect (Factor n) := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  rcases (inferInstance : (center (Factor n)).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative (Factor n) (center_eq_top_iff.mp h)).elim

lemma first_second_commute (x y : Factor n) : Commute (d.first x) (d.second y) := by
  apply Commute.map _ d.embedding
  show (x, 1) * (1, y) = (1, y) * (x, 1)
  simp

private lemma centralizer_first (z : Q) (hz : z ∈ d.embedding.range)
    (hc : z ∈ centralizer (d.first.range : Set Q)) : z ∈ d.second.range := by
  obtain ⟨⟨x,y⟩, rfl⟩ := hz
  have hx : x ∈ center (Factor n) := by
    rw [mem_center_iff]
    intro t
    have he := mem_centralizer_iff.mp hc (d.first t) ⟨t,rfl⟩
    have he' : d.embedding ((t,1) * (x,y)) = d.embedding ((x,y) * (t,1)) := by
      simpa only [first, MonoidHom.comp_apply, MonoidHom.inl_apply, map_mul] using he
    simpa using congrArg Prod.fst (d.injective he')
  have hx1 : x = 1 := by simpa only [d.factor_center, mem_bot] using hx
  exact ⟨y, by simp [hx1, second]⟩

private lemma conjugate_first_le_range {b : Q} (hb : b ∈ d.fourGroup) :
    d.first.range.map (MulAut.conj b).toMonoidHom ≤ d.embedding.range := by
  rw [← d.orbit_eq]
  exact le_iSup (fun b : d.fourGroup =>
    d.first.range.map (MulAut.conj (b : Q)).toMonoidHom) ⟨b,hb⟩

variable [Finite Q]

private lemma conjugate_first_eq_second {b : Q} (hb : b ∈ d.fourGroup)
    (hne : d.first.range.map (MulAut.conj b).toMonoidHom ≠ d.first.range) :
    d.first.range.map (MulAut.conj b).toMonoidHom = d.second.range := by
  apply eq_of_le_of_card_ge
  · intro z hz
    apply d.centralizer_first z (d.conjugate_first_le_range hb hz)
    exact commutator_eq_bot_iff_le_centralizer.mp
      ((d.hypotheses.component.map_conj b).commutator_eq_bot_of_ne
        d.hypotheses.component hne) hz
  · rw [card_map_of_injective (MulAut.conj b).injective]
    exact (Nat.card_congr (MonoidHom.ofInjective d.second_injective).toEquiv).symm.le.trans
      (Nat.card_congr (MonoidHom.ofInjective d.first_injective).toEquiv).le

lemma swap_first : d.first.range.map (MulAut.conj d.involution).toMonoidHom =
    d.second.range := d.conjugate_first_eq_second d.hypotheses.mem d.hypotheses.moves

omit [Finite Q] in
lemma involution_mul : d.involution * d.involution = 1 := by
  simpa only [d.hypotheses.involution, pow_two] using pow_orderOf_eq_one d.involution

noncomputable abbrev swapped : Factor n →* Q :=
  (MulAut.conj d.involution).toMonoidHom.comp d.first

lemma swapped_range : d.swapped.range = d.second.range := by
  rw [MonoidHom.range_comp]
  exact d.swap_first

omit [Finite Q] in
lemma swapped_injective : Function.Injective d.swapped :=
  (MulAut.conj d.involution).injective.comp d.first_injective

lemma first_swapped_commute (x y : Factor n) : Commute (d.first x) (d.swapped y) := by
  obtain ⟨z,hz⟩ := show d.swapped y ∈ d.second.range from d.swapped_range ▸ ⟨y,rfl⟩
  rw [← hz]
  exact d.first_second_commute x z

omit [Finite Q] in
lemma swap_twice (x : Factor n) :
    MulAut.conj d.involution (d.swapped x) = d.first x := by
  change d.involution * (d.involution * d.first x * d.involution⁻¹) * d.involution⁻¹ = _
  calc _ = (d.involution * d.involution) * d.first x *
      (d.involution * d.involution)⁻¹ := by group
       _ = d.first x := by rw [d.involution_mul]; simp

lemma coordinates_unique {x y x' y' : Factor n}
    (h : d.first x * d.swapped y = d.first x' * d.swapped y') : x = x' ∧ y = y' := by
  obtain ⟨z,hz⟩ := show d.swapped y ∈ d.second.range from d.swapped_range ▸ ⟨y,rfl⟩
  obtain ⟨z',hz'⟩ := show d.swapped y' ∈ d.second.range from d.swapped_range ▸ ⟨y',rfl⟩
  rw [← hz, ← hz'] at h
  have hp : (x,z) = (x',z') := d.injective (by simpa [first, second, ← map_mul] using h)
  have hx := congrArg Prod.fst hp
  have hy := congrArg Prod.snd hp
  exact ⟨hx, d.swapped_injective (hz.symm.trans ((congrArg d.second hy).trans hz'))⟩

lemma exists_coordinates {z : Q} (hz : z ∈ d.embedding.range) :
    ∃ x y, d.first x * d.swapped y = z := by
  obtain ⟨⟨x,y⟩,rfl⟩ := hz
  obtain ⟨t,ht⟩ := show d.second y ∈ d.swapped.range from d.swapped_range.symm ▸ ⟨y,rfl⟩
  refine ⟨x,t,?_⟩
  rw [ht]
  change d.embedding (x,1) * d.embedding (1,y) = _
  rw [← map_mul]
  simp



noncomputable def diagonalHom : Factor n →* Q where
  toFun x := d.first x * d.swapped x
  map_one' := by rw [map_one, map_one, mul_one]
  map_mul' x y := by
    simp only [map_mul]
    exact ((d.first_swapped_commute y x).mul_mul_mul_comm _ _)

lemma diagonalHom_injective : Function.Injective d.diagonalHom := by
  intro x y h
  exact (d.coordinates_unique h).1

lemma diagonalHom_range : d.diagonalHom.range =
    d.embedding.range ⊓ centralizer ({d.involution} : Set Q) := by
  apply le_antisymm
  · rintro z ⟨x,rfl⟩
    constructor
    · apply d.embedding.range.mul_mem
      · exact ⟨(x,1),rfl⟩
      · have hz : d.swapped x ∈ d.second.range := d.swapped_range ▸ ⟨x,rfl⟩
        obtain ⟨y,hy⟩ := hz
        exact ⟨(1,y),hy⟩
    · apply mem_centralizer_singleton_iff.mpr
      apply (mul_inv_eq_iff_eq_mul.mp ?_).symm
      change MulAut.conj d.involution (d.first x * d.swapped x) = _
      rw [map_mul, d.swap_twice]
      exact (d.first_swapped_commute x x).eq.symm
  · intro z hz
    obtain ⟨x,y,rfl⟩ := d.exists_coordinates hz.1
    have he : MulAut.conj d.involution (d.first x * d.swapped y) =
        d.first x * d.swapped y :=
      (mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hz.2).symm)
    rw [map_mul, d.swap_twice] at he
    change d.swapped x * d.first y = _ at he
    rw [← (d.first_swapped_commute y x).eq] at he
    have hyx := (d.coordinates_unique he).1
    exact ⟨x, by change d.first x * d.swapped x = _; rw [hyx]⟩

lemma diagonal_simple : IsSimpleGroup d.diagonalHom.range := by
  let := d.factor_simple
  exact (MonoidHom.ofInjective d.diagonalHom_injective).symm.isSimpleGroup

lemma fourGroup_normalizes_diagonal :
    d.fourGroup ≤ normalizer (d.diagonalHom.range : Set Q) := by
  intro b hb
  rw [mem_normalizer_iff]
  intro z
  have hE : b ∈ normalizer (d.embedding.range : Set Q) := by
    rw [← d.orbit_eq]
    exact le_normalizer_componentOrbit _ _ hb
  have hbcomm : Commute b d.involution :=
    mem_centralizer_singleton_iff.mp (d.hypotheses.fourGroup_le_centralizer hb)
  have hc : b ∈ normalizer (centralizer ({d.involution} : Set Q) : Set Q) := by
    exact le_normalizer (d.hypotheses.fourGroup_le_centralizer hb)
  rw [d.diagonalHom_range]
  exact and_congr (mem_normalizer_iff.mp hE z) (mem_normalizer_iff.mp hc z)

private lemma centralizes_diagonal_normalizes_first {b : Q}
    (hb : b ∈ d.fourGroup) (hN : b ∈ normalizer (d.first.range : Set Q))
    (hC : b ∈ centralizer (d.diagonalHom.range : Set Q)) : b = 1 := by
  have hba : Commute b d.involution :=
    mem_centralizer_singleton_iff.mp (d.hypotheses.fourGroup_le_centralizer hb)
  have hconj (x : Factor n) : MulAut.conj b (d.swapped x) =
      MulAut.conj d.involution (MulAut.conj b (d.first x)) := by
    change b * (d.involution * d.first x * d.involution⁻¹) * b⁻¹ =
      d.involution * (b * d.first x * b⁻¹) * d.involution⁻¹
    calc _ = (b * d.involution) * d.first x * (b * d.involution)⁻¹ := by group
         _ = (d.involution * b) * d.first x * (d.involution * b)⁻¹ := by rw [hba.eq]
         _ = _ := by group
  have hfirst : b ∈ centralizer (d.first.range : Set Q) := by
    rw [mem_centralizer_iff]
    rintro z ⟨x,rfl⟩
    obtain ⟨y,hy⟩ := (mem_normalizer_iff.mp hN (d.first x)).mp ⟨x,rfl⟩
    have he : MulAut.conj b (d.diagonalHom x) = d.diagonalHom x := by
      exact mul_inv_eq_iff_eq_mul.mpr
        (mem_centralizer_iff.mp hC _ ⟨x,rfl⟩).symm
    change MulAut.conj b (d.first x * d.swapped x) = _ at he
    change d.first y = MulAut.conj b (d.first x) at hy
    rw [map_mul, hconj, ← hy] at he
    have hyx : y = x := (d.coordinates_unique he).1
    exact (mul_inv_eq_iff_eq_mul.mp (hy.symm.trans (congrArg d.first hyx))).symm
  have hm : b ∈ d.fourGroup ⊓ centralizer (d.first.range : Set Q) := ⟨hb,hfirst⟩
  simpa only [d.hypotheses.centralizer, mem_bot] using hm

private lemma not_centralizes_diagonal : ¬ d.fourGroup ≤ centralizer (d.diagonalHom.range : Set Q) := by
  intro hC
  have hle : d.fourGroup ≤ zpowers d.involution := by
    intro b hb
    by_cases hN : d.first.range.map (MulAut.conj b).toMonoidHom = d.first.range
    · have hb1 := d.centralizes_diagonal_normalizes_first hb
        (mem_normalizer_iff_map_conj_eq.mpr hN) (hC hb)
      rw [hb1]
      exact one_mem _
    · have hR := d.conjugate_first_eq_second hb hN
      have hab : d.involution * b ∈ d.fourGroup := d.fourGroup.mul_mem d.hypotheses.mem hb
      have hNab : d.involution * b ∈ normalizer (d.first.range : Set Q) := by
        apply mem_normalizer_iff_map_conj_eq.mpr
        have he : (MulAut.conj (d.involution * b)).toMonoidHom =
            (MulAut.conj d.involution).toMonoidHom.comp (MulAut.conj b).toMonoidHom := by
          ext z
          simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MulAut.conj_apply]
          group
        change d.first.range.map (MulAut.conj (d.involution * b)).toMonoidHom = _
        rw [he, ← Subgroup.map_map, hR, ← d.swap_first, Subgroup.map_map]
        have he2 : (MulAut.conj d.involution).toMonoidHom.comp
            (MulAut.conj d.involution).toMonoidHom = MonoidHom.id Q := by
          ext z
          change d.involution * (d.involution * z * d.involution⁻¹) * d.involution⁻¹ = z
          calc _ = (d.involution * d.involution) * z * (d.involution * d.involution)⁻¹ := by group
               _ = z := by rw [d.involution_mul]; simp
        rw [he2, Subgroup.map_id]
      have hab1 := d.centralizes_diagonal_normalizes_first hab hNab (hC hab)
      have hbeq : b = d.involution := by
        calc b = d.involution * (d.involution * b) := by rw [← mul_assoc, d.involution_mul, one_mul]
             _ = d.involution := by rw [hab1, mul_one]
      rw [hbeq]
      exact mem_zpowers _
  have hc := card_le_of_le hle
  rw [d.hypotheses.card_four, Nat.card_zpowers, d.hypotheses.involution] at hc
  omega

lemma diagonal_commutator : ⁅d.diagonalHom.range, d.fourGroup⁆ = d.diagonalHom.range := by
  let := d.diagonal_simple
  have hle : ⁅d.diagonalHom.range, d.fourGroup⁆ ≤ d.diagonalHom.range :=
    le_normalizer_iff_commutator_le_left.mp d.fourGroup_normalizes_diagonal
  have hn : (⁅d.diagonalHom.range, d.fourGroup⁆.subgroupOf d.diagonalHom.range).Normal :=
    (normal_subgroupOf_iff_le_normalizer hle).mpr
      (normalizer_commutator_ge_left _ _)
  rcases (Subgroup.isSimpleGroup_iff.mp d.diagonal_simple).2 _ hle hn with hbot | heq
  · exact (d.not_centralizes_diagonal
      (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hbot))).elim
  · exact heq

end Representation.QuadraticFourGroup.SplitOrbit

end
