module

public import Theory.SpecificGroups.Triality.TwoLocalCover
public import Theory.SpecificGroups.Triality.FullParabolicActions.CyclicQuotient
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.Quasithin.CoprimeRank
public import Theory.GroupTheory.Commutator.PerfectLocalReduction

/-!
# Perfect subgroups in binary triality two-local normalizers

The full normalizer of a nonidentity two-subgroup is conjugate into a root
parabolic. Its cyclic quotient kills every perfect image, placing that image
in the actual local factor. The local factor has a two-group kernel and a
binary PSL₂ quotient, so every odd-prime rank is at most one.

This uses the literal triality carrier and both root parabolics, including
the field of order two. It supplies the triality local obstruction used in
Aschbacher--Smith C.3.5, printed p.150, from the parabolic structures in
GLS3 §2.6 and Aschbacher--Smith F.1.12(I)(4), printed pp.263–264.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Triality.Standard.PerfectTwoNormalizer
open Parabolics

/-- The two-core quotient of either actual local factor bounds every odd-prime
rank, including the central factor at q = 2. -/
theorem localFactor_odd_primeRank_le_one
    (P : Parameters) (hp : P.prime = 2) (a : Node)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) : primeRank p (localFactor P a) ≤ 1 := by
  rw [← primeRank_quotient_eq_of_isTwoGroup p ho
    (pCore 2 (localFactor P a)) pCore_isPGroup]
  cases a with
  | arms =>
    let : CharP (ExtensionField P) 2 :=
      hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
    rw [primeRank_equiv p (localFactorArmsQuotientEquivPSL2 P hp),
      ← primeRank_equiv p (Theory.PSL2.sl2QuotientEquiv (ExtensionField P))]
    exact Matrix.SL2.binary_odd_primeRank_le_one ho
  | central =>
    let : CharP (GaloisField P.prime P.exponent) 2 :=
      hp ▸ inferInstanceAs (CharP (GaloisField P.prime P.exponent) P.prime)
    rw [primeRank_equiv p (localFactorCentralQuotientEquivPSL2 P hp),
      ← primeRank_equiv p (Theory.PSL2.sl2QuotientEquiv
        (GaloisField P.prime P.exponent))]
    exact Matrix.SL2.binary_odd_primeRank_le_one ho

/-- A faithful perfect actor in either full root parabolic has odd-prime
rank at most one: its projection to the cyclic torus quotient is trivial. -/
theorem perfect_parabolic_embedding_odd_rank_le_one
    (P : Parameters) (hp : P.prime = 2) (a : Node)
    {A : Type*} [_root_.Group A] [Finite A] [Group.IsPerfect A]
    (f : A →* Carrier P) (hf : Function.Injective f)
    (hn : f.range ≤ parabolic P a)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) : primeRank p A ≤ 1 := by
  let D := parabolic P a
  let N := (localFactor P a).subgroupOf D
  let fD : A →* D := f.codRestrict D (fun x => hn ⟨x,rfl⟩)
  let : Group.IsPerfect fD.range := Group.IsPerfect.range fD
  let : IsCyclic (D ⧸ N) := parabolic_quotient_isCyclic P hp a
  let : CommGroup (D ⧸ N) := IsCyclic.commGroup
  have hN : fD.range ≤ N := le_of_isPerfect_of_solvable_quotient _ _
  let j : A →* localFactor P a := f.codRestrict _ (fun x => hN ⟨x,rfl⟩)
  have hj : Function.Injective j := fun x y h => hf (congrArg Subtype.val h)
  exact (Theory.GroupTheory.primeRank_le_of_injective p j hj).trans
    (localFactor_odd_primeRank_le_one P hp a ho)

/-- A faithfully embedded perfect group normalizing a nonidentity
two-subgroup of binary triality has odd-prime rank at most one. -/
theorem perfect_two_normalizer_embedding_odd_rank_le_one
    (n : ℕ) (hn : 0 < n)
    (P : Subgroup (Carrier (binaryParameters n hn)))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    {A : Type*} [_root_.Group A] [Finite A] [Group.IsPerfect A]
    (f : A →* Carrier (binaryParameters n hn)) (hf : Function.Injective f)
    (hN : f.range ≤ normalizer (P : Set (Carrier (binaryParameters n hn))))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) : primeRank p A ≤ 1 := by
  obtain ⟨g,a,hg⟩ := TwoLocalCover.normalizer_cover n hn P hne hp
  let j := (MulAut.conj g).toMonoidHom.comp f
  have hj : j.range ≤ (normalizer (P : Set (Carrier (binaryParameters n hn)))).map
      (MulAut.conj g).toMonoidHom := by
    rw [MonoidHom.range_comp]
    exact map_mono hN
  exact perfect_parabolic_embedding_odd_rank_le_one (binaryParameters n hn) rfl a j
    ((MulAut.conj g).injective.comp hf) (hj.trans hg) ho

/-- The subgroup form of the actual triality two-local bound. -/
theorem perfect_subgroup_two_normalizer_odd_rank_le_one
    (n : ℕ) (hn : 0 < n)
    (P : Subgroup (Carrier (binaryParameters n hn)))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥)
    (A : Subgroup (Carrier (binaryParameters n hn))) [Group.IsPerfect A]
    (hN : A ≤ normalizer (P : Set (Carrier (binaryParameters n hn))))
    {p : ℕ} [Fact p.Prime] (ho : Odd p) : primeRank p A ≤ 1 := by
  apply perfect_two_normalizer_embedding_odd_rank_le_one n hn P hp hne
    A.subtype A.subtype_injective ?_ ho
  simpa only [range_subtype] using hN

end Triality.Standard.PerfectTwoNormalizer
