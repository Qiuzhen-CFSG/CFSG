module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.Models
public import GorensteinWalter.PSL2SchurMultiplier
public import Theory.GroupTheory.CoveringKernelCard
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv

/-!
# Complete rank-one subcases of classical FF recognition

Every quasisimple cover of PSL₂(q), q even and at least eight, is the
simple group itself: the existing identity covering is universal. For
odd q > 3, q ≠ 9, the universal covering kernel has order two. If the
original group has trivial two-core, its covering kernel is therefore
trivial as well. These arguments identify the whole original group.

The concrete exceptional isomorphisms then close q = 4, 5, 9 through
alternating groups and q = 7 through PSL₃(2). Thus all even parameters
and the small odd parameters 5, 7, 9 are settled without any module
hypothesis. Exclusion of the other odd parameters is not asserted here.

Source: Aschbacher–Smith, B.1.13, B.4.4, I.1.3(1),(3) and K.3.1,
printed pp.73, 87, 407 and 453. The actual universal-cover calculations
are proved in `GorensteinWalter.PSL2SchurMultiplier`; the exceptional
comparisons reuse the attributed ATLAS ports and existing CFSG proofs.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical

universe u
variable {L : Type u} [Group L] [Finite L] [IsQuasisimple L]

private def projectiveCover (F : Type) [Field F] [Finite F]
    [Fact (3 < Nat.card F)] (e : L ⧸ center L ≃* PSL(2, F)) :
    Covering L PSL(2, F) where
  toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
  surjective := e.surjective.comp (QuotientGroup.mk'_surjective _)

/-- The universal identity cover identifies every even PSL₂(q) cover for q ≥ 8. -/
theorem isPSL_of_even_rank_one {q : ℕ} (hq : 8 ≤ q) (he : Even q)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 q) : ClassicalGroup.IsPSL L 2 q := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  let f := projectiveCover F e
  have hu := GorensteinWalter.PSL2Cover.identity_isUniversal_of_even F
    (hcard.symm ▸ he) (by omega)
  let a := hu.lift f
  have ha := hu.lift_fac f
  have hf : Function.Injective f.toMonoidHom := by
    intro x y hxy
    obtain ⟨b, rfl⟩ := a.surjective x
    obtain ⟨c, rfl⟩ := a.surjective y
    have hb := congrArg (fun k : Covering PSL(2, F) PSL(2, F) => k b) ha
    have hc := congrArg (fun k : Covering PSL(2, F) PSL(2, F) => k c) ha
    apply congrArg a
    exact hb.symm.trans (hxy.trans hc)
  exact ⟨F, hF, hfin, hcard, ⟨MulEquiv.ofBijective f.toMonoidHom ⟨hf, f.surjective⟩⟩⟩

/-- The universal double-cover bound and trivial two-core identify an odd PSL₂(q) cover, with the exceptional q = 9 excluded. -/
theorem isPSL_of_odd_rank_one {q : ℕ} (hcore : pCore 2 L = ⊥)
    (hq : 3 < q) (ho : Odd q) (h9 : q ≠ 9)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 q) : ClassicalGroup.IsPSL L 2 q := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := h
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  let f := projectiveCover F e
  have hu := GorensteinWalter.PSL2Cover.isUniversal_of_odd F (hcard.symm ▸ ho) (by omega)
  let a := hu.lift f
  have ha : f.toMonoidHom.comp a.toMonoidHom =
      (GorensteinWalter.PSL2Cover.cover F).toMonoidHom :=
    congrArg Covering.toMonoidHom (hu.lift_fac f)
  have hd := kernel_card_dvd_of_surjective_factor _ _ _ a.surjective ha
  have hc : Nat.card (GorensteinWalter.PSL2Cover.cover F).toMonoidHom.ker = 2 := by
    rw [Nat.card_congr
      (GorensteinWalter.PSL2Cover.kernelEquivTwo F (hcard.symm ▸ ho)).toEquiv]
    exact Nat.card_zmod 2
  have hp : IsPGroup 2 f.toMonoidHom.ker :=
    IsPGroup.of_card_dvd_pow (n := 1) (by simpa only [pow_one, hc] using hd)
  have hk : f.toMonoidHom.ker = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← hcore]
    exact le_sSup ⟨inferInstance, hp⟩
  exact ⟨F, hF, hfin, hcard,
    ⟨MulEquiv.ofBijective f.toMonoidHom
      ⟨f.toMonoidHom.ker_eq_bot_iff.mp hk, f.surjective⟩⟩⟩

omit [Finite L] [IsQuasisimple L] in
/-- At q = 4 the original simple central quotient is the actual alternating group A₅. -/
theorem conclusion_of_psl2_four
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 4) : Conclusion L := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
  exact Or.inr ⟨5, by decide,
    ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card4EquivAlt5 hc)⟩⟩

omit [Finite L] [IsQuasisimple L] in
/-- At q = 5 field transport and the icosahedral comparison identify the actual alternating quotient A₅. -/
theorem conclusion_of_psl2_five
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 5) : Conclusion L := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let f : F ≃+* ZMod 5 := (ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hc)).symm
  exact Or.inr ⟨5, by decide,
    ⟨(e.trans (Atlas.fieldEquivPSL 2 f)).trans
      Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some⟩⟩

omit [Finite L] [IsQuasisimple L] in
/-- The exceptional q = 9 quotient is A₆; no claim of trivial covering center is made. -/
theorem conclusion_of_psl2_nine
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 9) : Conclusion L := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
  exact Or.inr ⟨6, by decide,
    ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hc)⟩⟩

/-- At q = 7 the whole group is PSL₃(2), since the possible double covering kernel lies in its trivial two-core. -/
theorem conclusion_of_psl2_seven (hcore : pCore 2 L = ⊥)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 7) : Conclusion L := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := isPSL_of_odd_rank_one hcore
    (by decide : 3 < 7) (by decide : Odd 7) (by decide : 7 ≠ 9) h
  have hp : KnownSimple.LinearParameters 3 2 := by
    exact ⟨(isPrimePow_nat_iff 2).mpr ⟨2, 1, by decide, by decide, by decide⟩,
      by decide, by omega⟩
  apply Or.inl
  apply IsEvenLieGroup.classical
  apply IsClassicalAt.isEvenClassicalGroup (q := 2) _ (by decide)
  exact .linear 3 hp ⟨ZMod 2, inferInstance, inferInstance, Nat.card_zmod 2,
    ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card7EquivPsl3Two hc)⟩⟩

/-- All permitted even-field linear rank-one catalogue entries satisfy the B.1.13 conclusion. -/
theorem conclusion_of_even_psl2 {q : ℕ} (hp : KnownSimple.LinearParameters 2 q)
    (he : Even q) (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 q) : Conclusion L := by
  by_cases h4 : q = 4
  · exact conclusion_of_psl2_four (h4 ▸ h)
  have hq : 8 ≤ q := by
    obtain ⟨p, a, hprime, ha, hpa⟩ := (isPrimePow_nat_iff q).mp hp.1
    have hd : 2 ∣ p := (by decide : Nat.Prime 2).dvd_of_dvd_pow
      (hpa.symm ▸ even_iff_two_dvd.mp he)
    have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq (by decide) hprime).mp hd |>.symm
    subst p
    have ha3 : 3 ≤ a := by
      by_contra hh
      have ha2 : a ≤ 2 := by omega
      interval_cases a <;> norm_num at hpa <;> have := hp.2.2 rfl <;> omega
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) ha3
      _ = q := hpa
  exact Or.inl (.classical
    ((IsClassicalAt.linear 2 hp (isPSL_of_even_rank_one hq he h)).isEvenClassicalGroup he))

/-- Apply the closed rank-one subcases at the exact classical catalogue
parameter. Only the remaining odd-field exclusion is outside this result. -/
theorem conclusion_of_psl2_even_or_small {q : ℕ} (hcore : pCore 2 L = ⊥)
    (hp : KnownSimple.LinearParameters 2 q)
    (h : ClassicalGroup.IsPSL (L ⧸ center L) 2 q)
    (hq : Even q ∨ q = 5 ∨ q = 7 ∨ q = 9) : Conclusion L := by
  rcases hq with he | rfl | rfl | rfl
  · exact conclusion_of_even_psl2 hp he h
  · exact conclusion_of_psl2_five h
  · exact conclusion_of_psl2_seven hcore h
  · exact conclusion_of_psl2_nine h

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical
