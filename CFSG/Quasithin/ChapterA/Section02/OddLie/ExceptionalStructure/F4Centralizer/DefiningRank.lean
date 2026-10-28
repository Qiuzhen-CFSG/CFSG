module

public import Theory.SpecificGroups.LieType.F4RootCentralizer.DefiningPair
public import CFSG.Quasithin.ChapterA.Section02.OddLie.RootCoverTransfer
public import CFSG.Quasithin.Defs

/-!
# The F₄ source exclusion from defining rank

Transport the actual two-root plane through the prescribed identification
G/Z(G) ≃ F₄(F). The proved root-cover transfer gives defining rank at most
one in its complementary residual, whereas the plane gives rank at least two.
The final application derives every local rank bound from quasithinness of G.

Oddness of the original center and its defining-prime-free order remain
explicit preceding-source inputs: A.2.13 is owned by qt-a02-minimal-reduction,
and the initial O_p(G)=1 step of A.2.17 by qt-a02-defining-kernel-source.
The final owners qt-a02-odd-exceptional-structure and qt-a02-odd-lie discharge
these inputs. This does not assert their unfinished ambient reductions.

Source: Aschbacher–Smith A.2.17, printed p.39, especially (*) and the F₄ case.
The original quotient map, field, and marked fundamental SL₂ are preserved.
-/

public noncomputable section

namespace CFSG.Quasithin.ChapterA.Section02.F4DefiningRank
open Subgroup Theory.GroupTheory
open ExceptionalSplit ExceptionalSplit.F4RootCentralizer
open scoped MatrixGroups
open RootCoverTransfer

variable {F Q G : Type*} [Field F] [Finite F] [Group Q] [Finite Q] [Group G] [Finite G]

/-- The two-root plane contradicts the source defining-rank bound, using
exactly the prescribed quotient identification and long-root map. -/
theorem source_bound_contradiction {p : ℕ} [Fact p.Prime] [CharP F p]
    (e : Q ≃* F4 F)
    (hbound : primeRank p (complementaryResidual p
      ((e.symm.toMonoidHom).comp (F4RootSL2.hom (F := F))).range) ≤ 1) : False := by
  let j : SL(2,F) →* Q := e.symm.toMonoidHom.comp F4RootSL2.hom
  let C : Subgroup Q := centralizer (j.range : Set Q)
  let f : Centralizer F →* C := (e.symm.toMonoidHom.comp (Centralizer F).subtype).codRestrict _ (by
    intro x
    apply mem_centralizer_iff.mpr
    rintro _ ⟨A, rfl⟩
    have hx := mem_centralizer_iff.mp
      (show (x : F4 F) ∈ centralizer ((F4RootSL2.hom (F := F)).range : Set (F4 F)) from
        (centralizer_eq_range_centralizer (F := F)) ▸ x.property)
      (F4RootSL2.hom A) ⟨A, rfl⟩
    simpa only [j, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Subgroup.coe_subtype, map_mul] using congrArg e.symm hx)
  let J := complementaryResidual p j.range
  let g : Residual p F →* J :=
    (C.subtype.comp (f.comp (Residual p F).subtype)).codRestrict _ (by
      intro x
      exact ⟨f x.val, Subgroup.map_primeToResidual_le_of_hom p f
        ⟨x.val, x.property, rfl⟩, rfl⟩)
  have hgi : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact e.symm.injective (congrArg (fun z : J => (z : Q)) h)
  have hl := (DefiningPair.two_le_primeRank_residual (F := F) p).trans
    (Theory.GroupTheory.primeRank_le_of_injective p g hgi)
  have hb : primeRank p J ≤ 1 := hbound
  omega

/-- A.2.17's actual central-cover contradiction. The original center
hypotheses and local rank bounds produce the complementary bound internally. -/
theorem central_quotient_contradiction {p d : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ d)
    (e : G ⧸ center G ≃* F4 F)
    (ho : Odd (Nat.card (center G))) (hcop : Nat.Coprime p (Nat.card (center G)))
    (hlocal : ∀ s : ℕ, s = 3 ∨ s = p → ∀ z : G, z ≠ 1 → z ^ 2 = 1 →
      primeRank s (centralizer ({z} : Set G)) ≤ 2) : False := by
  have hF : (2 : F) ≠ 0 := by
    intro h
    have hlt : 2 < p := lt_of_le_of_ne (Fact.out : p.Prime).two_le (Ne.symm hp)
    exact Nat.not_dvd_of_pos_of_lt (by decide : 0 < 2) hlt
      ((CharP.cast_eq_zero_iff F p 2).mp (by simpa using h))
  let j : SL(2,F) →* G ⧸ center G := e.symm.toMonoidHom.comp F4RootSL2.hom
  have hj : Function.Injective j := e.symm.injective.comp (F4RootSL2.hom_injective hF)
  exact source_bound_contradiction e
    (quotient_complementary_rank_bounds hp hcard ho hcop j hj hlocal).2

/-- The original F₄ source branch is excluded on G, not on an assumed
quasithin quotient. The center conditions are supplied by the earlier A.2
ambient analysis; no centralizer model or rank witness remains a premise. -/
theorem not_quasithin_of_centralQuotientEquiv {p d : ℕ} [Fact p.Prime] [CharP F p]
    (hp : p ≠ 2) (hcard : Nat.card F = p ^ d)
    (e : G ⧸ center G ≃* F4 F)
    (ho : Odd (Nat.card (center G))) (hcop : Nat.Coprime p (Nat.card (center G))) :
    ¬ IsQuasithin G := by
  intro hqt
  apply central_quotient_contradiction hp hcard e ho hcop
  intro s hs z hz hz2
  have hloc := Theory.GroupTheory.isTwoLocal_involution_centralizer (orderOf_eq_prime hz2 hz)
  rcases hs with hs | hs
  · subst s
    exact (isQuasithin_iff_twoLocal.mp hqt) _ hloc 3 (by decide) (by decide)
  · subst s
    exact (isQuasithin_iff_twoLocal.mp hqt) _ hloc p Fact.out
      ((Fact.out : p.Prime).odd_of_ne_two hp)

end CFSG.Quasithin.ChapterA.Section02.F4DefiningRank
