module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Flag
public import CFSG.Quasithin.ChapterE.Section03.Parameters

/-!
# A moving conjugate in the field-four triangle

The literal W₀(T,V) cannot lie in O₂(IT) when I escapes M and its
normalizer lies in M: otherwise weak closure identifies it with W₀(O₂(IT),V),
which I normalizes. The equality C_{IT}(U)=O₂(IT) therefore supplies an
actual conjugate A of V in T moving U. Centralizer rigidity below s(G,V)
then bounds the rank of Aut_A(U) from below.

The flag application retains the original second radical R₂. The swapped
module U and its kernel identity are explicit earlier construction inputs;
this does not assert that such a module exists or eliminate the triangle.
Source: Aschbacher--Smith, 11.4.1(2), printed p.776, using E.3.6 and
11.2.2(3,5).
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin Chapter11.ChosenNaturalSource
open ChapterE
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle
variable {G : Type*} [Group G] [Finite G]

/-- An escaping subgroup cannot contain the original weak closure in its two-core. -/
theorem weakClosure_not_le_core (T : Sylow 2 G) (V I M : Subgroup G)
    (hout : ¬ I ≤ M)
    (hN : normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ M) :
    ¬ indexedWeakClosure V (T : Subgroup G) 0 ≤ (I ⊔ (T : Subgroup G)).pCoreIn 2 := by
  intro hW
  have he : indexedWeakClosure V (T : Subgroup G) 0 =
      indexedWeakClosure V ((I ⊔ (T : Subgroup G)).pCoreIn 2) 0 := by
    apply le_antisymm (SubgroupFamily.span_le_span_of_span_le hW)
    apply weakClosure_mono V 0
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (I ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  apply hout
  have hI : I ≤ normalizer ((I ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
    (le_sup_left : I ≤ I ⊔ (T : Subgroup G)).trans
      ((I ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  exact hI.trans ((normalizer_le_weakClosure_normalizer V _ 0).trans (he ▸ hN))

/-- A whole conjugate, rather than a chosen abstract actor, moves the swapped module. -/
theorem exists_noncentral_conjugate (T : Sylow 2 G) (V I U M : Subgroup G)
    (hout : ¬ I ≤ M)
    (hN : normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ M)
    (hC : (I ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) =
      (I ⊔ (T : Subgroup G)).pCoreIn 2) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T ∧
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G) := by
  by_contra! hn
  apply weakClosure_not_le_core T V I M hout hN
  rw [← hC]
  refine le_inf ((indexedWeakClosure_le V _ 0).trans le_sup_right) ?_
  apply sSup_le
  intro A hA
  obtain ⟨g, rfl, hg⟩ := (mem_gamma_zero_iff V (T : Subgroup G) A).mp hA
  exact hn g hg

/-- E.3.6 bounds the literal action image of a moving conjugate by s(G,V). -/
theorem conjugate_action_rank_lower (V U : Subgroup G) [IsElementaryAbelian 2 V]
    (hU : IsPGroup 2 U) (g : G)
    (hn : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (U : Set G))
    (hc : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (U : Set G)) :
    globalS V ≤
      (Representation.BinaryOffender.rank
        (inducedAutomizer U (V.map (MulAut.conj g).toMonoidHom)) : ℕ∞) := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  rw [rank_inducedAutomizer U A hn]
  by_contra! h
  have h' : (subgroupCorank A (A ⊓ centralizer (U : Set G)) : ℕ∞) < globalS A := by
    simpa only [A, globalS_map_equiv] using h
  have he := centralizer_inf_eq_of_corank_lt_globalS inf_le_left h' hU
  apply hc
  apply le_centralizer_iff.mp
  intro u hu
  have hm : u ∈ U ⊓ centralizer ((A ⊓ centralizer (U : Set G)) : Set G) :=
    ⟨hu, (le_centralizer_iff.mpr (inf_le_right :
      A ⊓ centralizer (U : Set G) ≤ centralizer (U : Set G))) hu⟩
  exact (he.le hm).2

variable {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)

/-- The original chosen flag supplies a conjugate inside R₂ with action rank at least four. -/
theorem flag_exists_large_conjugate_action (I U : Subgroup G)
    (hout : ¬ I ≤ normalizer (L : Set G))
    (hN : normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
      normalizer (L : Set G))
    (hC : (I ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) =
      (I ⊔ (T : Subgroup G)).pCoreIn 2)
    (hU : IsPGroup 2 U) (hTU : (T : Subgroup G) ≤ normalizer (U : Set G))
    (hW : indexedWeakClosure V (T : Subgroup G) 0 ≤ f.Ri 1)
    (hs : (4 : ℕ∞) ≤ @globalS G _ V D.elementary) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ f.Ri 1 ∧
      V.map (MulAut.conj g).toMonoidHom ≤ T ∧
      inducedAutomizer U (V.map (MulAut.conj g).toMonoidHom) ≠ ⊥ ∧
      4 ≤ Representation.BinaryOffender.rank
        (inducedAutomizer U (V.map (MulAut.conj g).toMonoidHom)) := by
  let _ := D.elementary
  obtain ⟨g, hg, hc⟩ := exists_noncentral_conjugate T V I U _ hout hN hC
  have hn := hg.trans hTU
  refine ⟨g, ?_, hg, mt (inducedAutomizer_eq_bot_iff hn).mp hc, ?_⟩
  · exact (gamma_le_weakClosure ((mem_gamma_zero_iff V (T : Subgroup G) _).mpr
      ⟨g, rfl, hg⟩)).trans hW
  · exact_mod_cast hs.trans (conjugate_action_rank_lower V U hU g hn hc)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle
