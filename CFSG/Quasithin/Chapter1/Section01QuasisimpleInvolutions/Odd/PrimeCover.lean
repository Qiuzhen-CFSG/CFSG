module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Odd.LinearActions
public import CFSG.Quasithin.ChapterI.Section01.LieMultipliers.PSL2
public import Theory.SpecificGroups.SL2.SylowInnerFixer

/-!
# Excluding the prime-field SL₂ cover in 1.1.5

The proved universal SL₂ projection maps onto the original quasisimple group.
If this map were injective, its original marked inner automorphism would
transport to a nonidentity inner Sylow fixer of SL₂, which the scalar
centralizer calculation excludes. Its kernel is consequently nontrivial.
The center of SL₂ has order two, so that kernel is the whole center and the
original group is the actual simple projective quotient.

This proves the cover exclusion for every prime in the source, without
waiting for the broader I.2.2 cover tables. Together with the prime-field
action calculation it supplies canonical row (e) whenever the independent
Fermat--Mersenne restriction holds.
Source: Aschbacher--Smith, proof of 1.1.5(3), printed p.503; I.1.3(1).
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions

universe u
variable {L : Type u} [Group L] [Finite L] [IsQuasisimple L]
variable {α : MulAut L} {P : Sylow 2 L}

/-- The universal SL₂ cover and its scalar Sylow centralizer rule out the
double cover. No multiplier or covering hypothesis remains. -/
theorem MarkedInvolution.linear_two_prime_center_eq_bot
    (d : MarkedInvolution α P) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 p) : center L = ⊥ := by
  have hlarge := linear_two_field_large ho hm
  have hi := (d.linear_two_prime_inner_and_center hp ho hm).1
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let : Fact (3 < Nat.card F) := ⟨by omega⟩
  let c : Covering L PSL(2,F) := {
    toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
    surjective := e.surjective.comp (QuotientGroup.mk'_surjective _) }
  have hu : Covering.IsUniversal.{0,0,u} (GorensteinWalter.PSL2Cover.cover F) :=
    GorensteinWalter.PSL2Cover.isUniversal_of_card_prime F (hcard ▸ hp)
  let a := hu.lift c
  have hzcard : Nat.card (center SL(2,F)) = 2 := by
    rw [← GorensteinWalter.sl2ProjectiveProjection_ker F]
    exact GorensteinWalter.sl2ProjectiveProjection_ker_card F (hcard ▸ ho)
  have hk : a.toMonoidHom.ker ≠ ⊥ := by
    intro hk
    let f : L ≃* SL(2,F) := (MulEquiv.ofBijective a.toMonoidHom
      ⟨(MonoidHom.ker_eq_bot_iff _).mp hk, a.surjective⟩).symm
    let Q := P.mapSurjective (f := f.toMonoidHom) f.surjective
    let b := MulAut.congr f α
    have hbi : b ∈ (MulAut.conj (G := SL(2,F))).range := by
      obtain ⟨g, hg⟩ := hi
      refine ⟨f g, ?_⟩
      rw [← MulAut.congr_conj, hg]
    have hbfix : ∀ x ∈ Q, b x = x := by
      rintro x ⟨y, hy, rfl⟩
      change f (α (f.symm (f y))) = f y
      rw [f.symm_apply_apply, d.fixes y hy]
    have hb := Matrix.SpecialLinearGroup.inner_sylow_fixer_eq_one (hcard ▸ ho) Q b hbi hbfix
    have hα1 : α = 1 := (MulAut.congr f).injective (hb.trans (map_one _).symm)
    have hh := d.order_two
    simp [hα1] at hh
  let : Nontrivial a.toMonoidHom.ker :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hk
  have hker : a.toMonoidHom.ker = center SL(2,F) :=
    Subgroup.eq_of_le_of_card_ge a.ker_le_center (by rw [hzcard]; exact Finite.one_lt_card)
  let f : L ≃* PSL(2,F) :=
    (QuotientGroup.quotientKerEquivOfSurjective a.toMonoidHom a.surjective).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : IsSimpleGroup PSL(2,F) := e.symm.isSimpleGroup
  let : IsSimpleGroup L := f.isSimpleGroup
  exact Subgroup.center_eq_bot_of_simple_perfect

open Chapter15.Section03.Candidates.ComponentStructure

/-- The prime-field row (e), with the double-cover exclusion discharged.
Only the source's Fermat--Mersenne parameter remains explicit. -/
theorem MarkedInvolution.linear_two_prime
    (d : MarkedInvolution α P) {p : ℕ} (hp : IsFermatOrMersennePrime p) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (L ⧸ center L) 2 p) : ModelAction115 L α :=
  d.linear_two_prime_of_center_eq_bot hp ho hm (d.linear_two_prime_center_eq_bot hp.1 ho hm)

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
