module

public import CFSG.Quasithin.ChapterA.Section02.MinimalReduction.Nonsemisimple.RankTwoSieve.ProperSL2
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure
public import CFSG.Quasithin.ChapterA.Section02.OddLie.ClassicalStructure.Unitary

/-!
# Signed degree-three quotients with a large defining field

The actual block SL₂ in PSL₃ and the fixed-field SL₂ in PSU₃ are proper
and injective. Transport them through the source model isomorphism, then
lift their literal ranges along the original quotient map. The proper-section
induction contradiction in `ProperSL2` excludes every odd defining exponent
greater than two. All model embeddings and properness conditions are proved
by their matrix constructions, not supplied as additional source premises.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.2.12,
printed p.36.
-/

public section
open Subgroup Theory.GroupTheory Matrix
namespace CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
universe u
variable {K : GroupClass.{u}} {G Q : Type u}
  [Group G] [Group Q] [Finite G] [Finite Q]

private theorem proper_comp_equiv {A B C : Type*} [Group A] [Group B] [Group C]
    (j : A →* B) (hj : j.range ≠ ⊤) (a : B ≃* C) :
    (a.toMonoidHom.comp j).range ≠ ⊤ := by
  intro ht
  apply hj
  apply MonoidHom.range_eq_top.mpr
  intro b
  obtain ⟨g,hg⟩ := (MonoidHom.range_eq_top.mp ht) (a b)
  exact ⟨g,a.injective hg⟩

/-- The block SL₂ in PSL₃(pᵉ) gives the original source contradiction. -/
theorem no_psl_three_large_quotient
    (ih : TheoremsOnProperSections K G) (hqt : IsQuasithin G) (hk : IsKGroup K G)
    (f : G →* Q) (hf : Function.Surjective f)
    (p e : ℕ) (hp : p.Prime) (ho : Odd p) (he : 2 < e)
    (hmodel : ClassicalGroup.IsPSL Q 3 (p^e)) : False := by
  obtain ⟨F,hF,hfin,hcard,⟨a⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow
    (by simpa only [← Nat.card_eq_fintype_card] using hcard)
  let b := (OddLie.ClassicalStructure.linearModelEquiv F 0).toMonoidHom.comp
    (OddLie.ClassicalStructure.linearFundamental F 0)
  have hb : Function.Injective b :=
    (OddLie.ClassicalStructure.linearModelEquiv F 0).injective.comp
      (OddLie.ClassicalStructure.linearFundamental_injective F 0)
  have hproper : b.range ≠ ⊤ := proper_comp_equiv _
    (OddLie.ClassicalStructure.linearFundamental_proper F 0)
    (OddLie.ClassicalStructure.linearModelEquiv F 0)
  exact no_large_proper_sl2_quotient ih hqt hk f hf ho hcard he
    (a.symm.toMonoidHom.comp b) (a.symm.injective.comp hb)
    (proper_comp_equiv b hproper a.symm)

/-- The fixed-field SL₂ in PSU₃(pᵉ) gives the same source contradiction. -/
theorem no_psu_three_large_quotient
    (ih : TheoremsOnProperSections K G) (hqt : IsQuasithin G) (hk : IsKGroup K G)
    (f : G →* Q) (hf : Function.Surjective f)
    (p e : ℕ) (hp : p.Prime) (ho : Odd p) (he : 2 < e)
    (hmodel : ClassicalGroup.IsPSU Q 3 (p^e)) : False := by
  obtain ⟨F,hF,hfin,J,hcard,hconj,⟨a⟩⟩ := hmodel
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by intro heq; subst p; exact (by decide : ¬ Odd 2) ho
  have hq : IsPrimePow (p^e) := (isPrimePow_nat_iff _).mpr ⟨p,e,hp,by omega,rfl⟩
  have hfixed : Nat.card (FixedBy.subfield F J.conj) = p^e :=
    J.fixed_card_prime_power hq hcard hconj
  let : Fintype (FixedBy.subfield F J.conj) := Fintype.ofFinite _
  let : CharP (FixedBy.subfield F J.conj) p := charP_of_card_eq_prime_pow
    (by simpa only [← Nat.card_eq_fintype_card] using hfixed)
  obtain ⟨b,c,hb,hproper,_⟩ :=
    OddLie.ClassicalStructure.unitary_fundamental (n := 1) J hp2 (by omega) hcard hconj
  exact no_large_proper_sl2_quotient ih hqt hk f hf ho hfixed he
    (a.symm.toMonoidHom.comp b) (a.symm.injective.comp hb)
    (proper_comp_equiv b hproper a.symm)

end CFSG.Quasithin.ChapterA.Section02.Nonsemisimple.RankTwoSieve
end
