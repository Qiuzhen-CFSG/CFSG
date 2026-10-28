module

public import Theory.SpecificGroups.GL2.CubicTwoPerfect
public import Theory.GroupTheory.TwoPerfectCubicImages
public import Theory.GroupTheory.TwoPerfectCubicSylow
public import CFSG.Quasithin.ChapterA.Section01.RankActions.AutomorphismQuotient

/-!
# The actual binary-tetrahedral actor on the odd core

Pass from the given action to its literal range. The range retains the
cubic two-core quotient. Its nontrivial two-core excludes every normal odd
subgroup, so A.1.25's small-linear homomorphism is faithful on this range.
The determinant calculation and quaternion recognition give SL₂(3).
The actual image of any original full Sylow is its quaternion two-core.

Source: Aschbacher–Smith, Lemma 13.3.14(d), printed p.892. In particular,
no injectivity of the original action, prescribed actor image, or Sylow
image is a premise.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource

variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
  {A : Type*} [Group A] [Finite A]

omit [Finite A] in
theorem actual_actor_models
    (hp : Odd p) (hP : IsPGroup p P) (hr : primeRank p P ≤ 2)
    (hA : IsPPerfect 2 A) (hthree : Nat.card (A ⧸ pCore 2 A) = 3)
    (a : A →* MulAut P) (hm : (pCore 2 A).map a ≠ ⊥) :
    Nonempty (a.range ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∧
      Nonempty ((pCore 2 a.range) ≃* QuaternionGroup 2) := by
  let B := a.range
  have hB : IsPPerfect 2 B := hA.of_surjective a.rangeRestrict a.rangeRestrict_surjective
  have hm' : (pCore 2 A).map a.rangeRestrict ≠ ⊥ := by
    intro hz
    apply hm
    have hh := congrArg (map a.range.subtype) hz
    rw [map_map, Subgroup.map_bot] at hh
    have he : a.range.subtype.comp a.rangeRestrict = a := by ext; rfl
    rwa [he] at hh
  have hBthree := a.rangeRestrict.twoCore_quotient_card_three
    a.rangeRestrict_surjective hA hthree hm'
  have hBn : ((pCore 2 A).map a.rangeRestrict).Normal :=
    Normal.map inferInstance a.rangeRestrict a.rangeRestrict_surjective
  have hle : (pCore 2 A).map a.rangeRestrict ≤ pCore 2 B :=
    le_sSup ⟨hBn, pCore_isPGroup.map a.rangeRestrict⟩
  have hBcore : pCore 2 B ≠ ⊥ := by
    intro hz
    apply hm'
    exact le_bot_iff.mp (hle.trans hz.le)
  obtain ⟨f, hf⟩ := ChapterA.RankActions.smallRankAutomorphismRepresentation p hp P hP hr
  let g := f.comp a.range.subtype
  have hgker : IsPGroup p g.ker := hf.comap_of_injective a.range.subtype a.range.subtype_injective
  have hgodd : Odd (Nat.card g.ker) := by
    obtain ⟨n, hn⟩ := hgker.exists_card_eq
    rw [hn]
    exact hp.pow
  have hgi : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).mp
    (normal_odd_eq_bot_of_twoPerfect_cubic hB hBthree hBcore g.ker hgodd)
  have hchar : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have he : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (Fact.out : p.Prime).ne_one
    subst p
    obtain ⟨k, hk⟩ := hp
    omega
  exact Matrix.GeneralLinearGroup.binaryTetrahedral_of_faithful_cubic_action
    hchar hB hBthree hBcore g hgi

theorem actual_sylow_actor_model
    (hp : Odd p) (hP : IsPGroup p P) (hr : primeRank p P ≤ 2)
    (hA : IsPPerfect 2 A) (hthree : Nat.card (A ⧸ pCore 2 A) = 3)
    (a : A →* MulAut P) (hm : (pCore 2 A).map a ≠ ⊥) (S : Sylow 2 A) :
    Nonempty (((S : Subgroup A).map a) ≃* QuaternionGroup 2) := by
  obtain ⟨e⟩ := (actual_actor_models hp hP hr hA hthree a hm).2
  let j := (pCore 2 a.range).equivMapOfInjective a.range.subtype a.range.subtype_injective
  exact ⟨((MulEquiv.subgroupCongr
    (S.image_eq_embedded_twoCore_of_cubic_quotient a hA hthree hm)).trans j.symm).trans e⟩

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
