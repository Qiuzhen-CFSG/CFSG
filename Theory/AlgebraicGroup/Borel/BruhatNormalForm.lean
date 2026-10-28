module

public import Theory.AlgebraicGroup.BNPair.Bruhat
public import Theory.AlgebraicGroup.Borel.Defs
public import Theory.AlgebraicGroup.RootData.Realization
public import Theory.AlgebraicGroup.RootSystems.Weyl
public import Theory.AlgebraicGroup.Semisimple.Defs
public import Theory.AlgebraicGroup.Tori.Basic

/-!
# Bruhat normal form and Weyl positivity rigidity

This module supplies the two group- and root-theoretic reductions used in the
proof of Bor1, Lemma 14.23.  A Tits system gives an explicit factorization
`g = b' * n * b` by unpacking its Bruhat double-coset coverage.  In the
semisimple setup, identifying the Tits-system subgroups with a Borel subgroup
and the normalizer of a maximal torus gives the source's normal form.

For the rigidity step, a minimal word in the simple reflections is used.  If
its Weyl element sends the last simple root to a positive root, the preceding
word sends that root to a negative root; the exchange argument then produces a
strictly shorter word, a contradiction.  The exchange proof is repeated here
over the integral root pairing because the older public word-length API assumes
a field.  `IsActualBasedRootDatum` transports this conclusion to the realized
simple and positive roots of the algebraic group.

The normal-form statement is more general than the semisimple application:
opposite-Borel and root-datum geometry are needed to construct the aligned Tits
system, but not to unpack Bruhat coverage once that system is available.

Source: Bor1, Lemma 14.23, using the Bruhat decomposition from 14.12 and the
positive-chamber rigidity consequences of 14.7--14.8.
-/

namespace Theory.AlgebraicGroup

open scoped Pointwise

namespace TitsSystem

variable {X : Type*} [Group X]

/-- Membership in a Bruhat double coset yields an explicit `B N B`
factorization. -/
public theorem exists_bruhat_factorization (T : TitsSystem (X := X)) (x : X) :
    ∃ b' n b : X,
      b' ∈ T.B ∧ n ∈ T.N ∧ b ∈ T.B ∧ x = b' * n * b := by
  obtain ⟨w, hw⟩ := T.exists_mem_doubleCoset x
  obtain ⟨y, hy, b, hb, rfl⟩ := Set.mem_mul.mp hw
  obtain ⟨b', hb', n, ⟨nN, _, rfl⟩, rfl⟩ := Set.mem_mul.mp hy
  exact ⟨b', nN, b, hb', nN.property, hb, rfl⟩

end TitsSystem

section WeylPositivity

variable {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
  {P : RootPairing ι ℤ X Y} [P.IsCrystallographic] [P.IsReduced]

private theorem exists_integral_wordProd_eq
    (base : P.Base) (w : P.weylGroup) :
    ∃ l : List base.support, base.wordProd l = w := by
  suffices ∃ l : List base.support,
      (base.wordProd l : RootPairing.Aut P) = (w : RootPairing.Aut P) by
    rcases this with ⟨l, hl⟩
    exact ⟨l, Subtype.ext hl⟩
  have hw : (w : RootPairing.Aut P) ∈ Subgroup.closure
      (Set.range fun j : base.support => RootPairing.Equiv.reflection P j) := by
    rw [← weylGroup_generated_by_simpleReflections base]
    exact w.property
  refine Subgroup.closure_induction''
    (s := Set.range fun j : base.support => RootPairing.Equiv.reflection P j)
    (p := fun x _ => ∃ l : List base.support,
      (base.wordProd l : RootPairing.Aut P) = x) ?_ ?_ ?_ ?_ hw
  · intro x hx
    rcases hx with ⟨j, rfl⟩
    exact ⟨[j], by rfl⟩
  · intro x hx
    rcases hx with ⟨j, rfl⟩
    refine ⟨[j], ?_⟩
    change RootPairing.Equiv.reflection P j =
      (RootPairing.Equiv.reflection P j)⁻¹
    simp
  · exact ⟨[], by simp⟩
  · intro x y hx hy hx' hy'
    rcases hx' with ⟨l, rfl⟩
    rcases hy' with ⟨m, rfl⟩
    exact ⟨l ++ m, by simp⟩

private lemma simpleReflection_unique_positiveRoot_integral
    (base : P.Base) {j : ι} (hj : j ∈ base.support) :
    ∀ i, base.IsPos i ∧ ¬ base.IsPos (P.reflectionPerm j i) ↔ i = j := by
  let := P.indexNeg
  intro i
  constructor
  · rintro ⟨hi, hneg⟩
    by_contra hij
    exact hneg (hi.reflectionPerm hj hij)
  · rintro rfl
    refine ⟨base.isPos_of_mem_support hj, ?_⟩
    change ¬ base.IsPos (-i)
    rw [base.isPos_iff, base.height_reflectionPerm_self,
      base.height_one_of_mem_support hj]
    norm_num

private theorem exchange_integral_word
    (base : P.Base) (l : List base.support) (j : base.support)
    (hneg : ¬ base.IsPos (P.weylGroupToPerm (base.wordProd l) j)) :
    ∃ l' : List base.support,
      base.wordProd l' = base.wordProd l * base.simpleReflection j ∧
        l'.length < l.length := by
  induction l with
  | nil =>
      exfalso
      apply hneg
      simpa using base.isPos_of_mem_support j.property
  | cons k l ih =>
      have hneg' : ¬ base.IsPos
          (P.reflectionPerm k (P.weylGroupToPerm (base.wordProd l) j)) := by
        rw [base.wordProd_cons] at hneg
        change ¬ base.IsPos
          (P.reflectionPerm k (P.weylGroupToPerm (base.wordProd l) j)) at hneg
        exact hneg
      by_cases hpos : base.IsPos (P.weylGroupToPerm (base.wordProd l) j)
      · have heq : P.weylGroupToPerm (base.wordProd l) j = k :=
          (simpleReflection_unique_positiveRoot_integral
            base k.property _).mp ⟨hpos, hneg'⟩
        refine ⟨l, ?_, by simp⟩
        rw [base.wordProd_cons]
        change base.wordProd l = base.simpleReflection k *
          (base.wordProd l * RootPairing.weylGroup.ofIdx P j)
        rw [base.wordProd_mul_ofIdx]
        rw [← mul_assoc]
        change base.wordProd l = base.simpleReflection k *
          RootPairing.weylGroup.ofIdx P
              (P.weylGroupToPerm (base.wordProd l) j) *
            base.wordProd l
        rw [heq]
        change base.wordProd l =
          (base.simpleReflection k * base.simpleReflection k) * base.wordProd l
        simp
      · rcases ih hpos with ⟨l', hl', hlen⟩
        refine ⟨k :: l', ?_, by simpa using Nat.succ_lt_succ hlen⟩
        rw [base.wordProd_cons, hl', base.wordProd_cons, mul_assoc]

/-- A Weyl-group element sending every simple root to a positive root is
trivial. -/
public theorem _root_.RootPairing.Base.weyl_eq_one_of_maps_simpleRoots_to_positive
    (base : P.Base) (w : P.weylGroup)
    (hpositive : ∀ i : base.support,
      base.IsPos (P.weylGroupToPerm w i)) :
    w = 1 := by
  classical
  have hex : ∃ n : ℕ, ∃ l : List base.support,
      l.length = n ∧ base.wordProd l = w := by
    rcases exists_integral_wordProd_eq base w with ⟨l, hl⟩
    exact ⟨l.length, l, rfl, hl⟩
  let n := Nat.find hex
  obtain ⟨l, hlen, hprod⟩ := Nat.find_spec hex
  by_cases hl : l = []
  · subst l
    simpa using hprod.symm
  · let j : base.support := l.getLast hl
    let p : List base.support := l.dropLast
    have hl_decomp : p ++ [j] = l := List.dropLast_append_getLast hl
    have hw_word : base.wordProd p * base.simpleReflection j = w := by
      change base.wordProd p * base.wordProd [j] = w
      rw [← base.wordProd_append, hl_decomp, hprod]
    have hpneg : ¬ base.IsPos
        (P.weylGroupToPerm (base.wordProd p) j) := by
      let := P.indexNeg
      have hwj : P.weylGroupToPerm w j =
          -(P.weylGroupToPerm (base.wordProd p) j) := by
        rw [← hw_word]
        change P.weylGroupToPerm (base.wordProd p)
            (P.reflectionPerm j j) = _
        change P.weylGroupToPerm (base.wordProd p) (-j) = _
        exact P.weylGroupToPerm_neg (base.wordProd p) j
      have hwjpos := hpositive j
      rw [hwj, RootPairing.Base.IsPos.neg_iff_not base] at hwjpos
      exact hwjpos
    rcases exchange_integral_word base p j hpneg with ⟨l', hl'prod, hl'len⟩
    have hcandidate : ∃ m : List base.support,
        m.length = l'.length ∧ base.wordProd m = w :=
      ⟨l', rfl, hl'prod.trans hw_word⟩
    have hmin : n ≤ l'.length := Nat.find_min' hex hcandidate
    have hp_len : p.length + 1 = l.length := by
      rw [← hl_decomp]
      simp
    omega

/-- A nontrivial Weyl element sends some simple root to a nonpositive root. -/
public theorem _root_.RootPairing.Base.exists_simpleRoot_not_positive_of_ne_one
    (base : P.Base) (w : P.weylGroup) (hw : w ≠ 1) :
    ∃ i : base.support,
      ¬ base.IsPos (P.weylGroupToPerm w i) := by
  by_contra h
  apply hw
  apply RootPairing.Base.weyl_eq_one_of_maps_simpleRoots_to_positive base w
  intro i
  exact Classical.byContradiction fun hi => h ⟨i, hi⟩

/-- A nontrivial Weyl element sends a positive simple root to a nonpositive
root, in the ambient root-index type. -/
public theorem _root_.RootPairing.Base.exists_positive_simpleRoot_not_positive_of_ne_one
    (base : P.Base) (w : P.weylGroup) (hw : w ≠ 1) :
    ∃ i : ι, base.IsPos i ∧
      ¬ base.IsPos (P.weylGroupToPerm w i) := by
  obtain ⟨i, hi⟩ := base.exists_simpleRoot_not_positive_of_ne_one w hw
  exact ⟨i, base.isPos_of_mem_support i.property, hi⟩

end WeylPositivity

section ActualRootAction

universe u

variable {k : Type u} [Field k]
  {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
  {D : RootGroupData K T}
  {ι X Y : Type*} [Finite ι] [AddCommGroup X] [AddCommGroup Y]
  {P : RootPairing ι ℤ X Y} [P.IsCrystallographic] [P.IsReduced]
  {base : P.Base} {e : D.Root ≃ ι}
  {weightEquiv : Multiplicative X ≃* TorusWeight T}
  {positiveRoots : Set D.Root}

omit [P.IsCrystallographic] [P.IsReduced] in
/-- The realized Weyl action is positive exactly when its image index is
base-positive. -/
public theorem IsActualBasedRootDatum.weylImage_mem_positiveRoots_iff
    (hactual : IsActualBasedRootDatum D P base e weightEquiv positiveRoots)
    (w : P.weylGroup) (α : D.Root) :
    e.symm (P.weylGroupToPerm w (e α)) ∈ positiveRoots ↔
      base.IsPos (P.weylGroupToPerm w (e α)) := by
  simpa using hactual.2.2 (e.symm (P.weylGroupToPerm w (e α)))

/-- Positivity of every realized simple-root image forces a Weyl element to be
trivial. -/
public theorem IsActualBasedRootDatum.weyl_eq_one_of_maps_simpleRoots_to_positive
    (hactual : IsActualBasedRootDatum D P base e weightEquiv positiveRoots)
    (w : P.weylGroup)
    (hpositive : ∀ α : D.Root, α ∈ D.simple →
      e.symm (P.weylGroupToPerm w (e α)) ∈ positiveRoots) :
    w = 1 := by
  apply RootPairing.Base.weyl_eq_one_of_maps_simpleRoots_to_positive base w
  intro i
  have hiSimple : e.symm i ∈ D.simple :=
    (hactual.1.2.2.2 (e.symm i)).mpr (by simp [i.property])
  have hi := hpositive (e.symm i) hiSimple
  rw [hactual.weylImage_mem_positiveRoots_iff] at hi
  simpa using hi

end ActualRootAction

section SemisimpleBruhat

universe u

variable {k : Type u} [Field k]
  {K : Variety k} [AlgebraicGroup K]

/-- The explicit Bruhat normal form in the semisimple, opposite-Borel setup.

The geometric hypotheses record the source setting.  The proof itself uses the
aligned Tits system, which is the group-theoretic content constructed from that
geometry. -/
public theorem exists_bruhat_normal_form_of_semisimple_opposite_borel
    (_hK : IsSemisimpleAlgebraicGroup K)
    (T : ClosedSubgroup K) (_hT : IsMaximalTorus T)
    (B Bopp : ClosedSubgroup K)
    (_hB : IsBorelSubgroup B) (_hBopp : IsBorelSubgroup Bopp)
    (_hOpp : B.toSubgroup ⊓ Bopp.toSubgroup = T.toSubgroup)
    (TS : TitsSystem (X := Variety.Point K))
    (hTSB : TS.B = B.toSubgroup)
    (hTSN : TS.N = Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)))
    (g : Variety.Point K) :
    ∃ b' n b : Variety.Point K,
      b' ∈ B.toSubgroup ∧
      n ∈ Subgroup.normalizer (T.toSubgroup : Set (Variety.Point K)) ∧
      b ∈ B.toSubgroup ∧ g = b' * n * b := by
  obtain ⟨b', n, b, hb', hn, hb, hg⟩ := TS.exists_bruhat_factorization g
  exact ⟨b', n, b, hTSB ▸ hb', hTSN ▸ hn, hTSB ▸ hb, hg⟩

end SemisimpleBruhat

end Theory.AlgebraicGroup
