module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Centralizers

/-!
# From root geometry to the global parameters and weak closure

If r=m, an attained minimizing subspace has a nontrivial residual action
by the centralizer theorem. The root calculation places a conjugate of V₃
in it, or identifies it with a conjugate of V₂ in the actual SL₃ row.
The preceding V₃ centralizer control excludes the first alternative.
The E.3 definition of s then gives s=m, including when r is infinite.

For every corank-j generator of Wj, E.3.10 puts its actual automizer image
in A₂ when j<m-1. The model's inner-actor calculation places it in TL.
Centralizing generators are handled directly by the already proved Sylow
centralizer identity. The flag fixed-line identity finishes clause (4).

The model and lower-bound inputs remain unproved here and have independent
owners. These conditional deductions do not assert the complete source lemma.
Source: Aschbacher--Smith, 11.2.2(3--4), printed p.768.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

omit [Finite G] in
private theorem centralizer_conjugate_le {P M : Subgroup G} (g : G)
    (hg : g ∈ M) (hP : centralizer (P : Set G) ≤ M) :
    centralizer (P.map (MulAut.conj g).toMonoidHom : Set G) ≤ M := by
  have h := map_mono (f := (MulAut.conj g).toMonoidHom) hP
  have he : M.map (MulAut.conj g).toMonoidHom = M :=
    mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer hg)
  rw [map_centralizer_equiv, he] at h
  exact h

/-- The source alternative is deduced from an attained escaping centralizer,
not assumed as a numerical label. The SL₃ branch keeps its actual marking. -/
theorem global_parameters {c : Coordinates D S.field} (f : InvariantFlag c)
    (hmodel : FixedCodimensions D S c) (hroot : RootGeometry D S f)
    (hE : HypothesisE61 KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hr : (naturalParameter D S c : ℕ∞) ≤ globalR V)
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    ((naturalParameter D S c : ℕ∞) < globalR V ∨
      (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
        globalR V = naturalParameter D S c ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G))) ∧
      @globalS G _ V D.elementary = naturalParameter D S c := by
  let := D.elementary
  refine ⟨?_, ?_⟩
  · by_cases hstrict : (naturalParameter D S c : ℕ∞) < globalR V
    · exact Or.inl hstrict
    have heq : globalR V = naturalParameter D S c := le_antisymm (le_of_not_gt hstrict) hr
    obtain ⟨U, hUV, hout, hcor⟩ := globalR_attained (V := V) (by rw [heq]; simp)
    have hUm : subgroupCorank V U = naturalParameter D S c :=
      ENat.natCast_inj.mp (hcor.trans heq)
    have hU : U ≠ ⊥ := by
      intro hz
      have hd := hmodel.dimension
      rw [← hz, hUm] at hd
      omega
    have hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G) :=
      fun h => hout ((hE.centralizer_le_iff hU hUV).mp h)
    have hres : ¬ oddCentralizerCondition (normalizer (L : Set G)) V U := by
      intro h
      apply hescape
      apply (centralizer_control D S hmodel hE hr hUV _ h).1
      rw [hUm]
      have hm := naturalParameter_gt_one D S c
      omega
    rcases hroot.minimal_fixed U hUV hUm hres with ⟨l, hl⟩ | ⟨hsl, l, hl⟩
    · exact (hescape ((Subgroup.centralizer_le hl).trans
        (centralizer_conjugate_le (l : G) (L.le_normalizer l.property) hthree))).elim
    · refine Or.inr ⟨hsl, heq, ?_⟩
      intro hplane
      apply hescape
      rw [← hl]
      exact centralizer_conjugate_le (l : G) (L.le_normalizer l.property) hplane
  · rw [globalS, localM_of_fixedCodimensions D S hmodel, min_eq_right hr]

/-- E.3.10 and the natural A₂ calculation apply to every actual generator
of Wj; centralizing generators use the literal two-core of LT. -/
theorem weakClosure_bound_of_two_family {c : Coordinates D S.field} (f : InvariantFlag c)
    (htwo : letI := D.elementary; ∀ A : Subgroup G, A ≤ (T : Subgroup G) →
      inducedAutomizer V A ∈ fixedSpaceFamily (automizerRepresentation V) 2 →
      A ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hs : @globalS G _ V D.elementary = naturalParameter D S c)
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    {j : ℕ} (hj : j < naturalParameter D S c - 1) :
    indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
      f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G) := by
  let := D.elementary
  have hW : indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L := by
    rw [weakClosure_eq_sSup_gamma]
    apply sSup_le
    rintro A ⟨⟨g, hAV, hi⟩, hAT⟩
    have hcor : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A = j := by
      simp only [subgroupCorank, hi, Nat.log_pow (by decide : 1 < 2)]
    by_cases hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥
    · have hAC : A ≤ centralizer (V : Set G) := hAV.trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm))
      have hcore : A ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
        rw [← seed_sylow_centralizer D S]
        exact le_inf hAT hAC
      exact le_inf hAT (hcore.trans le_sup_right)
    · have hsmall : (subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A : ℕ∞) <
          globalS V := by
        rw [hcor, hs]
        exact_mod_cast (show j < naturalParameter D S c by omega)
      have hfamily := (inducedAutomizer_mem_fixedSpaceFamily_of_corank_lt_globalS g
        (le_inf hAV (hAT.trans S.sylow_normalizes)) hsmall hcomm).2
      rw [hs, ENat.toNat_natCast, hcor] at hfamily
      have hfamilyTwo := fixedSpaceFamily_mono (automizerRepresentation V)
        (by decide : 0 < (2 : ℕ)) (show 2 ≤ naturalParameter D S c - j by omega) hfamily
      exact le_inf hAT (htwo A hAT hfamilyTwo)
  exact ⟨hW, le_inf (hline.trans inf_le_left)
    ((hline.trans inf_le_right).trans (Subgroup.centralizer_le hW))⟩

/-- E.3.10 and the natural A₂ calculation apply to every actual generator
of Wj; centralizing generators use the literal two-core of LT. -/
theorem weakClosure_bound {c : Coordinates D S.field} (f : InvariantFlag c)
    (hroot : RootGeometry D S f)
    (hs : @globalS G _ V D.elementary = naturalParameter D S c)
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))
    {j : ℕ} (hj : j < naturalParameter D S c - 1) :
    indexedWeakClosure V (T : Subgroup G) j ≤ sourceTL T L ∧
      f.Vi 0 ≤ V ⊓ centralizer (indexedWeakClosure V (T : Subgroup G) j : Set G) :=
  weakClosure_bound_of_two_family D S f hroot.two_family hs hline hj

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters
