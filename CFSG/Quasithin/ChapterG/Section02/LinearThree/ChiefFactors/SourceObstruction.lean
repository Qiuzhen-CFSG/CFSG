module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.PointChief
public import Theory.GroupTheory.NoncentralChiefRefinement.Transport

/-!
# The larger-field obstruction in every chief series of L₁

The scalar point V₁ is an actual noncentral two-chief subgroup of the
literal two-residual L₁, of order 2^n when n>1. Insert this interval into a
complete chief series and apply equivariant Jordan–Hölder. Every complete
chief series therefore contains a noncentral two-factor of that order,
which cannot even be isomorphic as a group to a natural plane of order
2^(2n). In particular, the all-natural assertion in G.2.5(8) would force
n=1 under the full setup and the earlier U≤T and I=LU conclusions.

This is an obstruction to the requested general source assembly, not a
proof that larger-field setups exist or that the source hypotheses imply
n=1. No residual convention or theorem hypothesis is changed. The source
statement still requires resolution; the binary branch is unaffected.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.2.1 and
G.2.5(8), printed pp.332,335–336. The scan specifies O²(N_L(V₁)).
-/

public section

namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors
open NoncentralChiefRefinement ResidualRestriction
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}

/-- Every complete chief series of the actual residual contains the scalar
chief factor, up to an isomorphism preserving its ambient conjugation action.
This prevents choosing a different series to discard the scalar factor. -/
theorem complete_chief_series_scalar_factor (d : Hypothesis D F n g h)
    (hn : 1 < n) (hUT : D.U ≤ D.T) (hILU : I D g h = D.L ⊔ D.U)
    (t : ChiefSeries D.L₁) (ht0 : t.head = ⊥) (htl : t.last = ⊤) :
    ∃ i : Fin t.length,
      IsNoncentralTwo (t i.castSucc) (t i.succ) ∧
      Nat.card (Section (t i.castSucc) (t i.succ)) = 2 ^ n ∧
      ¬ Nonempty (Section (t i.castSucc) (t i.succ) ≃*
        Multiplicative (Fin 2 → F)) := by
  obtain ⟨a⟩ := exists_pointAlignment d
  obtain ⟨s, hs0, hsl, j, hj0, hj1⟩ := exists_complete_chiefSeries_containing
    (⊥ : NormalNode D.L₁) (PointChief.pointNode (D := D))
    ((covBy_iff_isChief _ _).mpr (PointChief.point_chief a hn hUT hILU))
  obtain ⟨e, he⟩ := s.exists_sectionEquiv_matching t
    (hs0.trans ht0.symm) (hsl.trans htl.symm)
  obtain ⟨f⟩ := he j
  rw [hj0, hj1] at f
  refine ⟨e j, f.isNoncentralTwo_iff.mp (PointChief.point_noncentral_two a hn hUT hILU),
    (Nat.card_congr f.equiv.symm.toEquiv).trans
      (PointChief.point_section_card a hn hUT hILU), ?_⟩
  rintro ⟨q⟩
  exact PointChief.point_section_not_natural_plane a hn hUT hILU ⟨f.equiv.trans q⟩

/-- The all-natural part of G.2.5(8), even without equivariance or the count,
would force the binary field. This does not assert that its premise follows
from the source hypotheses. -/
theorem natural_chief_series_requires_binary (d : Hypothesis D F n g h)
    (hUT : D.U ≤ D.T) (hILU : I D g h = D.L ⊔ D.U)
    (t : ChiefSeries D.L₁) (ht0 : t.head = ⊥) (htl : t.last = ⊤)
    (hnatural : ∀ i : Fin t.length, IsNoncentralTwo (t i.castSucc) (t i.succ) →
      Nonempty (Section (t i.castSucc) (t i.succ) ≃* Multiplicative (Fin 2 → F))) :
    n = 1 := by
  by_contra hn
  have hpos := d.exponent_pos
  obtain ⟨i, hi, _, hnot⟩ := complete_chief_series_scalar_factor d
    (by omega) hUT hILU t ht0 htl
  exact hnot (hnatural i hi)

/-- In every larger-field source setup, the full clause (8) chief-series
conclusion is impossible for any proposed multiplicities. The obstruction
already occurs in its all-natural assertion, independently of the count. -/
theorem larger_field_chief_description_obstruction (d : Hypothesis D F n g h)
    (hn : 1 < n) (hUT : D.U ≤ D.T) (hILU : I D g h = D.L ⊔ D.U)
    (r s : ℕ) :
    ¬ ∃ t : ChiefSeries D.L₁, t.head = ⊥ ∧ t.last = ⊤ ∧
      t.noncentralTwoCount = r + s + 2 ∧
      ∀ i : Fin t.length, IsNoncentralTwo (t i.castSucc) (t i.succ) →
        Nonempty (Section (t i.castSucc) (t i.succ) ≃* Multiplicative (Fin 2 → F)) := by
  rintro ⟨t, ht0, htl, _, ht⟩
  have he := natural_chief_series_requires_binary d hUT hILU t ht0 htl ht
  omega

end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors
