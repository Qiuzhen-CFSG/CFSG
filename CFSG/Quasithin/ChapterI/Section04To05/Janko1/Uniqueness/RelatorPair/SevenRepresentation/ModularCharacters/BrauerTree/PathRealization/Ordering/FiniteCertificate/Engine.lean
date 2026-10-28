module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Ordering.Arithmetic

/-!
# Sound finite verification of the principal eleven-block paths

`completions` enumerates unused ordinary rows with alternating signs and positive
successive edge degrees, including the last endpoint equation. `admissible_mem`
and `mem_branch` prove exhaustive coverage of every `Admissible` path.

The arithmetic checker uses six-integer tuples to avoid repeated function
extensionality during reduction. `unpack_tupleTensor` proves agreement with
all six coordinates of the published `tensorNumerator`; no period interpretation
or external calculation is assumed. `verify_sound` checks the degree sequence
or an explicit negative witness for every enumerated completion.

Source: the ordinary ATLAS/GAP CTblLib J1 table (Thomas Breuer,
GPL-3.0-or-later), copied from `Ordering.Arithmetic`; see
`../../Source.md`. The modular application is Janko, J. Algebra 3 (1966),
147–186, and Feit, Chapter VII.
-/

public section

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering
namespace FiniteCertificate

abbrev Tuple := ℤ × ℤ × ℤ × ℤ × ℤ × ℤ

@[expose] def unpack (x : Tuple) : Coeff := ![x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, x.2.2.2.2.2]
@[expose] def tupleScalar (n : ℤ) : Tuple := (n,0,0,0,0,0)

@[expose] def triMul (x y : ℤ × ℤ × ℤ) : ℤ × ℤ × ℤ :=
  (x.1*y.1 + 4*x.2.1*y.2.1 - 3*(x.2.1*y.2.2 + x.2.2*y.2.1) + 5*x.2.2*y.2.2,
   x.1*y.2.1 + x.2.1*y.1 - 2*(x.2.1*y.2.2 + x.2.2*y.2.1) + x.2.2*y.2.2,
   x.1*y.2.2 + x.2.2*y.1 - x.2.1*y.2.1 - (x.2.1*y.2.2 + x.2.2*y.2.1) + x.2.2*y.2.2)

@[expose] def tupleMul (x y : Tuple) : Tuple :=
  let x₀ := (x.1,x.2.1,x.2.2.1)
  let x₁ := x.2.2.2
  let y₀ := (y.1,y.2.1,y.2.2.1)
  let y₁ := y.2.2.2
  let u := triMul x₀ y₀ + triMul x₁ y₁
  let v := triMul x₀ y₁ + triMul x₁ y₀ - triMul x₁ y₁
  (u.1,u.2.1,u.2.2,v.1,v.2.1,v.2.2)

@[expose] def tupleTable : Fin 15 → Fin 15 → Tuple :=
  let a : Tuple := (0,0,0,1,0,0)
  let b := -tupleScalar 1 - a
  let c : Tuple := (0,1,0,0,0,0)
  let d : Tuple := (0,0,1,0,0,0)
  let e := -tupleScalar 1 - c - d
  ![![tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar 1],
    ![tupleScalar 56, tupleScalar 0, tupleScalar 2, -(2 • a), -(2 • b), tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar 1, a, b, tupleScalar (-1), tupleScalar (-1), tupleScalar (-1)],
    ![tupleScalar 56, tupleScalar 0, tupleScalar 2, -(2 • b), -(2 • a), tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar 1, b, a, tupleScalar (-1), tupleScalar (-1), tupleScalar (-1)],
    ![tupleScalar 76, tupleScalar 4, tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar (-1), tupleScalar (-1), tupleScalar (-1), tupleScalar (-1), tupleScalar 1, tupleScalar 1, tupleScalar 0, tupleScalar 0, tupleScalar 0],
    ![tupleScalar 76, tupleScalar (-4), tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar (-1), tupleScalar (-1), tupleScalar 1, tupleScalar 1, tupleScalar (-1), tupleScalar 1, tupleScalar 1, tupleScalar 0, tupleScalar 0, tupleScalar 0],
    ![tupleScalar 77, tupleScalar 5, tupleScalar (-1), tupleScalar 2, tupleScalar 2, tupleScalar (-1), tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar (-1), tupleScalar (-1), tupleScalar 1, tupleScalar 1, tupleScalar 1],
    ![tupleScalar 77, tupleScalar (-3), tupleScalar 2, a, b, tupleScalar 0, tupleScalar 0, a, b, tupleScalar 0, a, b, tupleScalar 1, tupleScalar 1, tupleScalar 1],
    ![tupleScalar 77, tupleScalar (-3), tupleScalar 2, b, a, tupleScalar 0, tupleScalar 0, b, a, tupleScalar 0, b, a, tupleScalar 1, tupleScalar 1, tupleScalar 1],
    ![tupleScalar 120, tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar 1, tupleScalar 0, tupleScalar 0, tupleScalar (-1), tupleScalar 0, tupleScalar 0, c, d, e],
    ![tupleScalar 120, tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar 1, tupleScalar 0, tupleScalar 0, tupleScalar (-1), tupleScalar 0, tupleScalar 0, e, c, d],
    ![tupleScalar 120, tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar 1, tupleScalar 0, tupleScalar 0, tupleScalar (-1), tupleScalar 0, tupleScalar 0, d, e, c],
    ![tupleScalar 133, tupleScalar 5, tupleScalar 1, tupleScalar (-2), tupleScalar (-2), tupleScalar (-1), tupleScalar 0, tupleScalar 0, tupleScalar 0, tupleScalar 1, tupleScalar 1, tupleScalar 1, tupleScalar 0, tupleScalar 0, tupleScalar 0],
    ![tupleScalar 133, tupleScalar (-3), tupleScalar (-2), -a, -b, tupleScalar 0, tupleScalar 0, a, b, tupleScalar 1, -a, -b, tupleScalar 0, tupleScalar 0, tupleScalar 0],
    ![tupleScalar 133, tupleScalar (-3), tupleScalar (-2), -b, -a, tupleScalar 0, tupleScalar 0, b, a, tupleScalar 1, -b, -a, tupleScalar 0, tupleScalar 0, tupleScalar 0],
    ![tupleScalar 209, tupleScalar 1, tupleScalar (-1), tupleScalar (-1), tupleScalar (-1), tupleScalar 1, tupleScalar (-1), tupleScalar 1, tupleScalar 1, tupleScalar 0, tupleScalar (-1), tupleScalar (-1), tupleScalar 0, tupleScalar 0, tupleScalar 0]]


@[expose] def tupleTensor (r : Fin 11 → Fin 15) (i j k : Fin 10) : Tuple :=
  ∑ t ∈ (Finset.univ.erase (9 : Fin 15)),
    (175560 / centralizerOrder t : ℕ) •
      tupleMul (tupleMul (edgeTerms (fun v => tupleTable (r v) t) i)
        (edgeTerms (fun v => tupleTable (r v) t) j))
        (tupleTable (r k.castSucc) t + tupleTable (r k.succ) t)

@[expose] def unpackHom : Tuple →+ Coeff where
  toFun := unpack
  map_zero' := by funext i; fin_cases i <;> rfl
  map_add' x y := by funext i; fin_cases i <;> rfl

theorem unpack_tupleMul (x y : Tuple) :
    unpack (tupleMul x y) = coeffMul (unpack x) (unpack y) := by
  funext i
  fin_cases i <;> rfl

theorem unpack_tupleTable : ∀ r t, unpack (tupleTable r t) = coefficientTable r t := by
  decide +kernel

theorem unpack_edgeTerms (v : Fin 11 → Tuple) :
    (fun i => unpack (edgeTerms v i)) = edgeTerms (fun j => unpack (v j)) := by
  funext i c
  fin_cases i <;> fin_cases c <;> rfl

theorem unpack_tupleTensor (r : Fin 11 → Fin 15) (i j k : Fin 10) :
    unpack (tupleTensor r i j k) = tensorNumerator r i j k := by
  change unpackHom _ = _
  unfold tupleTensor tensorNumerator
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [map_nsmul]
  change _ • unpack (tupleMul _ _) = _
  rw [unpack_tupleMul, unpack_tupleMul]
  change _ • coeffMul (coeffMul ((fun i => unpack (edgeTerms _ i)) i)
    ((fun i => unpack (edgeTerms _ i)) j)) (unpackHom (_ + _)) = _
  rw [unpack_edgeTerms, map_add]
  simp only [unpackHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, unpack_tupleTable]

abbrev Row := Fin 15

@[expose] def TailOK (sgn edge : ℤ) : List Row → Prop
  | [] => edge = 0
  | a :: as => ordinarySign a = sgn ∧
      (0 < (ordinaryDegree a : ℤ) - edge ∨ as = []) ∧
      TailOK (-sgn) ((ordinaryDegree a : ℤ) - edge) as

@[expose] def completions : ℕ → ℤ → ℤ → List Row → List (List Row)
  | 0, _, edge, _ => if edge = 0 then [[]] else []
  | n+1, sgn, edge, pool => pool.flatMap fun a =>
      if ordinarySign a = sgn ∧ (0 < (ordinaryDegree a : ℤ) - edge ∨ n = 0) then
        (completions n (-sgn) ((ordinaryDegree a : ℤ) - edge) (pool.erase a)).map (a :: ·)
      else []

theorem mem_completions {as : List Row} {sgn edge : ℤ} {pool : List Row}
    (hn : as.Nodup) (hp : as ⊆ pool) (hv : TailOK sgn edge as) :
    as ∈ completions as.length sgn edge pool := by
  induction as generalizing sgn edge pool with
  | nil => simp_all [TailOK, completions]
  | cons a as ih =>
    obtain ⟨ha, hn⟩ := List.nodup_cons.mp hn
    obtain ⟨hs, he, hv⟩ := hv
    have hcond : ordinarySign a = sgn ∧
        (0 < (ordinaryDegree a : ℤ) - edge ∨ as.length = 0) := by
      simpa only [List.length_eq_zero_iff] using And.intro hs he
    simp only [List.length_cons, completions, List.mem_flatMap]
    refine ⟨a, hp (by simp), ?_⟩
    rw [if_pos hcond, List.mem_map]
    refine ⟨as, ih hn ?_ hv, rfl⟩
    intro b hb
    have hba : b ≠ a := fun h => ha (h ▸ hb)
    exact (List.mem_erase_of_ne hba).mpr (hp (by simp [hb]))

@[expose] def tailRows (r : Fin 11 → Row) : List Row := [r 1,r 2,r 3,r 4,r 5,r 6,r 7,r 8,r 9,r 10]

theorem admissible_tail {r : Fin 11 → Row} (hr : Admissible r) :
    TailOK (-1) 1 (tailRows r) := by
  have hs : ∀ i, ordinarySign (r i) = vertexSign i := hr.alternating
  have he : ∀ i, 0 < edgeTerms (fun j => (ordinaryDegree (r j) : ℤ)) i := hr.positive
  have hl := hr.last
  dsimp [TailOK, tailRows]
  refine ⟨hs 1, Or.inl ?_, hs 2, Or.inl ?_, hs 3, Or.inl ?_,
    hs 4, Or.inl ?_, hs 5, Or.inl ?_, hs 6, Or.inl ?_,
    hs 7, Or.inl ?_, hs 8, Or.inl ?_, hs 9, Or.inl ?_,
    hs 10, Or.inr rfl, ?_⟩
  · simpa [edgeTerms, hr.first, ordinaryDegree] using he 1
  · simpa [edgeTerms, hr.first, ordinaryDegree] using he 2
  · simpa [edgeTerms, hr.first, ordinaryDegree] using he 3
  · simpa [edgeTerms, hr.first, ordinaryDegree] using he 4
  · simpa [edgeTerms, hr.first, ordinaryDegree] using he 5
  · simpa [edgeTerms, hr.first, ordinaryDegree] using he 6
  · simpa [edgeTerms, hr.first, ordinaryDegree] using he 7
  · simpa [edgeTerms, hr.first, ordinaryDegree] using he 8
  · simpa [edgeTerms, hr.first, ordinaryDegree] using he 9
  · apply sub_eq_zero.mpr
    simpa [edgeTerms, hr.first, ordinaryDegree] using hl.symm

-- Every actual tail occurs in the exhaustive search.
theorem admissible_mem {r : Fin 11 → Row} (hr : Admissible r) :
    tailRows r ∈ completions 10 (-1) 1 ((List.finRange 15).erase 0) := by
  have hn : (r 0 :: tailRows r).Nodup := by
    have h := List.nodup_ofFn.mpr hr.injective
    simpa [List.ofFn_succ, tailRows] using h
  apply mem_completions (List.nodup_cons.mp hn).2 _ (admissible_tail hr)
  intro a ha
  apply (List.mem_erase_of_ne ?_).mpr (List.mem_finRange a)
  intro h
  have := (List.nodup_cons.mp hn).1
  apply this
  simpa only [hr.first, h] using ha

@[expose] def rowOf (l : List Row) : Fin 11 → Row := fun i => l.getD i 0

theorem rowOf_actual {r : Fin 11 → Row} (hr : Admissible r) :
    rowOf (0 :: tailRows r) = r := by
  funext i
  fin_cases i <;> simp [rowOf, tailRows, hr.first]


abbrev Witness := Option (Fin 10 × Fin 10 × Fin 10 × ℕ)

@[expose] def Good (r : Fin 11 → Row) : Prop :=
  (fun v => ordinaryDegree (r v)) = orderedVertexDegree ∨
  ∃ i j k : Fin 10, ∃ n : ℕ, 0 < n ∧ tensorNumerator r i j k = scalar (-(n : ℤ))

@[expose] def test (r : Fin 11 → Row) : Witness → Bool
  | none => decide ((fun v => ordinaryDegree (r v)) = orderedVertexDegree)
  | some (i,j,k,n) => decide (0 < n ∧ tupleTensor r i j k = tupleScalar (-(n : ℤ)))

theorem test_sound {r : Fin 11 → Row} {w : Witness} (h : test r w = true) : Good r := by
  cases w with
  | none => exact Or.inl (of_decide_eq_true h)
  | some w =>
    obtain ⟨i,j,k,n⟩ := w
    obtain ⟨hn, he⟩ := of_decide_eq_true h
    refine Or.inr ⟨i,j,k,n,hn,?_⟩
    rw [← unpack_tupleTensor, he]
    rfl

@[expose] def verify (pre : List Row) : List (List Row) → List Witness → Bool
  | [], [] => true
  | p :: ps, w :: ws => test (rowOf (pre ++ p)) w && verify pre ps ws
  | _, _ => false

theorem verify_sound {pre : List Row} {paths : List (List Row)} {ws : List Witness}
    (h : verify pre paths ws = true) : ∀ p ∈ paths, Good (rowOf (pre ++ p)) := by
  induction paths generalizing ws with
  | nil => simp
  | cons p ps ih =>
    cases ws with
    | nil => simp [verify] at h
    | cons w ws =>
      obtain ⟨hp, hs⟩ := Bool.and_eq_true_iff.mp h
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact test_sound hp
      · exact ih hs q hq

/-- Split coverage into bounded checks, without dropping any candidate. -/
theorem cover_split {pre : List Row} {paths : List (List Row)} {n : ℕ}
    (h₁ : ∀ p ∈ paths.take n, Good (rowOf (pre ++ p)))
    (h₂ : ∀ p ∈ paths.drop n, Good (rowOf (pre ++ p))) :
    ∀ p ∈ paths, Good (rowOf (pre ++ p)) := by
  intro p hp
  have hp' : p ∈ paths.take n ++ paths.drop n := by
    simpa only [List.take_append_drop] using hp
  rcases List.mem_append.mp hp' with hp₁ | hp₂
  · exact h₁ p hp₁
  · exact h₂ p hp₂

-- Eight remaining vertices after the initial three.
@[expose] def branch (a b : Row) : List (List Row) :=
  completions 8 (-1) ((ordinaryDegree b : ℤ) - ((ordinaryDegree a : ℤ) - 1))
    ((((List.finRange 15).erase 0).erase a).erase b)

theorem mem_completions_step {a : Row} {as : List Row} {n : ℕ}
    {sgn edge : ℤ} {pool : List Row}
    (h : a :: as ∈ completions (n+1) sgn edge pool) :
    as ∈ completions n (-sgn) ((ordinaryDegree a : ℤ) - edge) (pool.erase a) := by
  rw [completions] at h
  obtain ⟨b, _, hb⟩ := List.mem_flatMap.mp h
  split_ifs at hb
  · obtain ⟨bs, hbs, he⟩ := List.mem_map.mp hb
    obtain ⟨rfl, rfl⟩ := List.cons.inj he
    exact hbs
  · simp at hb

theorem mem_branch {r : Fin 11 → Row} (hr : Admissible r) :
    [r 3,r 4,r 5,r 6,r 7,r 8,r 9,r 10] ∈ branch (r 1) (r 2) := by
  exact mem_completions_step (mem_completions_step (admissible_mem hr))

theorem initial_choices : ∀ a b : Row,
    ordinarySign a = -1 → ordinarySign b = 1 →
    0 < (ordinaryDegree b : ℤ) - ((ordinaryDegree a : ℤ) - 1) →
    (a = 3 ∨ a = 4 ∨ a = 8 ∨ a = 9 ∨ a = 10) ∧
    (b = 11 ∨ b = 12 ∨ b = 13) := by
  decide +kernel

end FiniteCertificate
end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.PathOrdering
