module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.SupercriticalNineSource.ShapeActions
public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical
public import Theory.GroupTheory.PGroup.SupercriticalExistence

/-!
# Selecting the actual normal source subgroup

A nontrivial two-core action on O_p(Q), p=3 or 5, survives restriction to
its characteristic supercritical subgroup. The cyclic alternative has a
two-group of automorphisms, so two-perfectness excludes it. The remaining
subgroup is normal in Q and has precisely one of the two source shapes.
The original conjugation homomorphism is preserved by the embedding.

Source: Aschbacher--Smith 15.4.10, printed p.1159, applying A.1.21 and A.1.25.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
open FamilySource Matrix.GeneralLinearGroup.PrimeThreeFiveResidual

/-- Supercritical selection with the literal original two-core action. -/
theorem exists_normal_source_shape {Q X : Type*} [Group Q] [Finite Q] [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 5)
    (hr : primeRank p Q ≤ 2) (hX : IsPPerfect 2 X) (f : X →* Q)
    (hne : (pCore 2 X).map ((MulAut.conjNormal : Q →* MulAut (pCore p Q)).comp f) ≠ ⊥) :
    ∃ P : Subgroup Q, ∃ hP : P.Normal,
      Chapter1.XiOddQuotient p P ∧ P ≤ pCore p Q ∧
        (pCore 2 X).map ((@MulAut.conjNormal Q _ P hP).comp f) ≠ ⊥ := by
  let B := pCore p Q
  have hB : IsPGroup p B := pCore_isPGroup
  have hp2 : p ≠ 2 := by rcases hp with rfl | rfl <;> decide
  have hodd : Odd p := by rcases hp with rfl | rfl <;> decide
  cases subsingleton_or_nontrivial B with
  | inl hs =>
    let : Subsingleton B := hs
    exfalso
    apply hne
    apply eq_bot_iff.mpr
    rintro y ⟨x, _, rfl⟩
    apply MulEquiv.ext
    intro b
    exact Subsingleton.elim _ _
  | inr hs =>
    let : Nontrivial B := hs
    obtain ⟨C, hC⟩ := hB.exists_supercriticalPSubgroup hp2
    let : C.Characteristic := hC.characteristic
    let : Nontrivial C := hC.nontrivial_of_nontrivial hB
    let aB := (MulAut.conjNormal : Q →* MulAut B).comp f
    let aC := (MulAut.characteristic C).comp aB
    have hnC : (pCore 2 X).map aC ≠ ⊥ := by
      intro hb
      apply hne
      apply eq_bot_iff.mpr
      rintro y ⟨x, hx, rfl⟩
      have hh : aB x ∈ (MulAut.characteristic C).ker :=
        mem_bot.mp (hb ▸ mem_map_of_mem aC hx)
      exact Subgroup.disjoint_def.mp
        (IsPGroup.disjoint_of_coprime (pCore_isPGroup.map aB)
          (hC.isPGroup_restriction_kernel hB hodd)
          ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr hp2.symm))
        (mem_map_of_mem aB hx) hh
    have hmodel := (ChapterA.lemma_A_1_25_1 hodd hB
      ((primeRank_subgroup_le p B).trans hr) C hC).2
    have hshape : Chapter1.XiOddQuotient p C := by
      rcases hmodel with ⟨hc, _⟩ | ⟨hc, ⟨e⟩⟩ | ⟨hc, he, _⟩
      · let : IsCyclic C := isCyclic_of_prime_card hc
        have hAut : IsPGroup 2 (MulAut C) := by
          have hcard : Nat.card (MulAut C) = p - 1 := by
            rw [IsCyclic.card_mulAut, hc, Nat.totient_prime (Fact.out : p.Prime)]
          rcases hp with rfl | rfl
          · exact IsPGroup.of_card (n := 1) (by simpa using hcard)
          · exact IsPGroup.of_card (n := 2) (by simpa using hcard)
        have ha := hX.hom_eq_one_of_isPGroup hAut aC
        exact (hnC ((Subgroup.map_eq_bot_iff _).mpr (by
          intro x _
          exact DFunLike.congr_fun ha x))).elim
      · let : CommGroup C := e.toMonoidHom.commGroupOfInjective e.injective
        refine Or.inl ⟨?_, hc⟩
        exact { toIsMulCommutative := inferInstance
                exponent_dvd_p := hC.exponent_dvd_p }
      · exact Or.inr ⟨he, hc,
          ((Fact.out : p.Prime).eq_one_or_self_of_dvd _ hC.exponent_dvd_p).resolve_left
            (Nat.ne_of_gt Monoid.one_lt_exponent)⟩
    let P := C.map B.subtype
    let : P.Normal := inferInstance
    let e : C ≃* P := C.equivMapOfInjective B.subtype B.subtype_injective
    let aP := (MulAut.conjNormal : Q →* MulAut P).comp f
    have he : (MulAut.congr e).toMonoidHom.comp aC = aP := by
      apply MonoidHom.ext
      intro x
      apply MulEquiv.ext
      intro c
      obtain ⟨c, rfl⟩ := e.surjective c
      change e (aC x (e.symm (e c))) = aP x (e c)
      rw [e.symm_apply_apply]
      apply Subtype.ext
      rfl
    refine ⟨P, inferInstance, hshape.of_mulEquiv e, map_subtype_le _, ?_⟩
    intro hb
    apply hnC
    apply eq_bot_iff.mpr
    rintro y ⟨x, hx, rfl⟩
    apply (MulAut.congr e).injective
    have hh := mem_bot.mp (hb ▸ mem_map_of_mem aP hx)
    simpa only [← he, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      map_one] using hh

variable {G : Type*} [Group G] [Finite G]

/-- The prime-five source exclusion forces the original two-core to
centralize O₅(M/O₂(M)), with supercritical selection discharged. -/
theorem twoCore_image_centralizes_fiveCore
    (T : Sylow 2 G) (M X Z : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hXM : X ≤ M) (hM : HasCharacteristicTwo M)
    (hX : X ∈ NormalCentralizerXi (T : Subgroup G) Z)
    (hX3 : Nat.card (X ⧸ pCore 2 X) = 3) (hr5 : primeRank 5 M ≤ 2)
    (hex : ∀ Y ∈ Chapter1.Xi G (T : Subgroup G), Y ∉ Chapter3.XiPlus G (T : Subgroup G)) :
    image M (X.pCoreIn 2) ≤ centralizer (pCore 5 (CoreQuotient M) : Set (CoreQuotient M)) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let f := (quotientMap M).comp (inclusion hXM)
  let a := (MulAut.conjNormal : CoreQuotient M →* MulAut (pCore 5 (CoreQuotient M))).comp f
  have hb : (pCore 2 X).map a = ⊥ := by
    by_contra hne
    have hr : primeRank 5 (CoreQuotient M) ≤ 2 :=
      (primeRank_quotient_le_of_isTwoGroup 5 (by decide) (pCore 2 M) pCore_isPGroup).trans hr5
    obtain ⟨P, hP, hs, _, hmove⟩ := exists_normal_source_shape (Or.inr rfl) hr hX.1.2.1 f hne
    let : P.Normal := hP
    exact hmove (five_core_action_trivial_of_source_exclusion T M X Z hTM hXM hM hX hX3 hex P hs)
  rintro q ⟨m, hm, rfl⟩ b hbP
  obtain ⟨x, hx, hxv⟩ := hm
  have hmval : (x : G) = (m : G) := hxv
  have ha : a x = 1 := mem_bot.mp (hb ▸ mem_map_of_mem a hx)
  have hh := congrArg (fun c : MulAut (pCore 5 (CoreQuotient M)) =>
    (c ⟨b, hbP⟩ : CoreQuotient M)) ha
  change f x * b * (f x)⁻¹ = b at hh
  have he : f x = quotientMap M m := congrArg (quotientMap M) (Subtype.ext hmval)
  rw [he] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SupercriticalNineSource
