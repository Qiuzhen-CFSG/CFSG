module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.Reductions
public import CFSG.Quasithin.ChapterE.Section03.Parameters

/-!
# Actual offender input and parabolic replacements in 11.2.4

E.3.10 puts every noncentral conjugate contained in T in the genuine A_n
fixed-space family. Conjugation by L₂ preserves R₂, hence keeps these
conjugates in T, and preserves noncentrality. The uniform small-action
exclusion therefore applies after this replacement, although V₁ may move.

These are the group-theoretic inputs to the remaining model calculation,
not a proof of that calculation or of the complete source theorem.

Source: Aschbacher--Smith, 11.2.4, printed p.769, using E.3.10, p.232.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The original induced automizer belongs to E.3.8's actual fixed-space family. -/
theorem conjugate_mem_fixedSpaceFamily [IsElementaryAbelian 2 V]
    (hs : globalS V = S.field.degree) (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hne : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    inducedAutomizer V (V.map (MulAut.conj g).toMonoidHom) ∈
      fixedSpaceFamily (automizerRepresentation V) S.field.degree := by
  have hc : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom) = 0 := by
    simp [subgroupCorank]
  have hn := hg.trans S.sylow_normalizes
  have hb : (subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom) : ℕ∞) < globalS V := by
    rw [hc, hs]
    exact_mod_cast S.field.degree_pos
  have h := (inducedAutomizer_mem_fixedSpaceFamily_of_corank_lt_globalS g
    (le_inf le_rfl hn) hb hne).2
  simpa only [hs, ENat.toNat_natCast, hc, Nat.sub_zero] using h

/-- The local residual normalizes its literal radical O₂(LᵢT). -/
theorem residual_normalizes_radical {c : Coordinates D S.field}
    (f : InvariantFlag c) (i : Fin 2) :
    f.Li i ≤ normalizer (f.Ri i : Set G) := by
  exact (le_sup_left : f.Li i ≤ f.Li i ⊔ (T : Subgroup G)).trans
    ((f.Li i ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))

/-- A replacement inside the plane residual is still an original conjugate in T. -/
theorem replacement_le_sylow {c : Coordinates D S.field} (f : InvariantFlag c)
    {A : Subgroup G} (hA : A ≤ f.Ri 1) {l : G} (hl : l ∈ f.Li 1) :
    A.map (MulAut.conj l).toMonoidHom ≤ T := by
  have hn := residual_normalizes_radical D S f 1 hl
  have hm : A.map (MulAut.conj l).toMonoidHom ≤ f.Ri 1 := by
    rw [← mem_normalizer_iff_map_conj_eq.mp hn]
    exact map_mono hA
  exact hm.trans (localRadical_le_sylow _)

omit [Finite G] in
/-- Conjugating the actor by an element normalizing V preserves noncentrality. -/
theorem replacement_noncentral {A : Subgroup G}
    (hne : ⁅V, A⁆ ≠ ⊥) {l : G} (hl : l ∈ normalizer (V : Set G)) :
    ⁅V, A.map (MulAut.conj l).toMonoidHom⁆ ≠ ⊥ := by
  intro hz
  apply hne
  apply (map_eq_bot_iff_of_injective _ (f := (MulAut.conj l).toMonoidHom)
    (MulAut.conj l).injective).mp
  have hlV : V.map (MulAut.conj l).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp hl
  rwa [map_commutator, hlV]

/-- Uniform exclusion applies to every L₂-replacement in R₂. No invariance
of the distinguished first line under the replacement is asserted or used. -/
theorem no_smallAction_after_replacement {c : Coordinates D S.field}
    (f : InvariantFlag c) (hsmall : NoSmallActions f) (g : G)
    (hA : V.map (MulAut.conj g).toMonoidHom ≤ f.Ri 1)
    (hne : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    {l : G} (hl : l ∈ f.Li 1) (W : Subgroup G) :
    ¬ SmallSymmetricAction f
      ((V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj l).toMonoidHom) W := by
  have ht := replacement_le_sylow D S f hA hl
  have hn := replacement_noncentral hne
    (D.normalizes ((localResidual_le _).trans inf_le_left hl))
  rw [offender_map_conj_map] at ht hn ⊢
  exact hsmall (l * g) ht hn W

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.RootParabolic
