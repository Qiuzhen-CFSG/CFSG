module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.PrimePSL2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuadraticPSL2
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# The alternating-five section in the odd rank-one embedding rows

A prime-field PSL₂ group with two-core quotient A₅ is itself A₅, since
simplicity kills its two-core. Its order forces the prime to be five.
Applying this to the proved proper quadratic-field embedding leaves exactly
PSL₂(25). The prime-field embedding retains both exceptional congruences.

Source: Aschbacher–Smith A.3.14(3), extracted from A.3.12(8), pp.47–49.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings

/-- The A₅ section forces the defining prime to be five and kills the two-core. -/
theorem prime_field_parameter_of_five_section {B : Type*} [Group B] [Finite B] {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hgt : 3 < p) (hm : ClassicalGroup.IsPSL B 2 p)
    (he : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))) :
    p = 5 ∧ Nonempty (B ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : IsSimpleGroup B := e.isSimpleGroup_congr.mpr
    (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega))
  have hc : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr he.some.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hcore : pCore 2 B = ⊥ := by
    rcases (inferInstance : (pCore 2 B).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · have hi := hc
      rw [ht] at hi
      simp at hi
  let q := QuotientGroup.mk' (pCore 2 B)
  have hqi : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp
    ((QuotientGroup.ker_mk' _).trans hcore)
  let b := (MulEquiv.ofBijective q ⟨hqi,QuotientGroup.mk'_surjective _⟩).trans he.some
  have hcard : Nat.card B = 60 := by
    rw [Nat.card_congr b.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have horder := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (hF.symm ▸ ho)
  rw [hF,←Nat.card_congr e.toEquiv,hcard] at horder
  have hp5 : p ≤ 5 := by
    by_contra hh
    have hh : 6 ≤ p := by omega
    have hs : 35 ≤ p ^ 2 - 1 := by
      have : 36 ≤ p ^ 2 := by nlinarith
      omega
    nlinarith
  have hpne4 : p ≠ 4 := by intro he; norm_num [he] at hp
  exact ⟨by omega,⟨b⟩⟩

/-- The quadratic row of A.3.14 has precisely the field of order twenty-five. -/
theorem proper_quadraticPSL2_five_models
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hL : L.IsCComponent) (hBL : B ≤ L)
    (hne : B ≠ L) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSL L 2 (p ^ 2))
    (hsection : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))) :
    p = 5 ∧ Nonempty (B ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨hgt, hsmall⟩ := proper_quadraticPSL2_models T hB hL hBL hne hp ho hmodel
  exact prime_field_parameter_of_five_section hp ho hgt hsmall hsection

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
