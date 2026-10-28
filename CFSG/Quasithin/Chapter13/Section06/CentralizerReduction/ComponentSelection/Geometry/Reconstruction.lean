module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Reconstruction.Transport

/-!
# Nonsingular reconstruction in the A₅ centralizer reduction

The actual residual span V_v is v's polar hyperplane, and the hyperplanes
indexed by its nonsingular vectors generate the marked module V. If V_v
were normal in G_v = C_G(v), conjugation in G_v would permute this family:
the moving-seed construction in `Reconstruction.Transport` proves this
without assuming that G_v already normalizes V. Generation then forces
G_v ≤ N_G(V), so a counterexample gives the relative nonnormality of 13.6.8.
The identified hyperplane also supplies the earlier M_v-action premise.

The quadratic fusion assertion `FusionPreservesForm`, from 13.2.6(2), is
retained as an explicit earlier-source input. The parent geometry reduction
owns its discharge and the assembly with the Thompson/FF branch.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.879 and 928, 13.2.6(2) and the reduction immediately before 13.6.8.
-/

public section

open Subgroup BinaryPermutation.FiveCentralizerGeometry
open BinaryPermutation.FiveGeometry
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

private theorem normalizer_perp_of_normal (s : A5Module.Marking L V)
    (hn : ((Vv L (A5Module.markedZ s) (A5Module.markedV s)).subgroupOf
      (Gv (A5Module.markedV s))).Normal) :
    Gv (A5Module.markedV s) ≤ normalizer (vectorPerp s v : Set G) := by
  rw [← Vv_eq_vectorPerp s]
  exact (normal_subgroupOf_iff_le_normalizer
    (Vv_le_Gv L _ _ (A5Module.markedZ_mem_Gv s))).mp hn

/-- Hypothetical relative normality makes every G_v-conjugate of a member
of the nonsingular family another member of that family. -/
theorem nonsingularFamily_conjugate_mem (s : A5Module.Marking L V)
    (hf : FusionPreservesForm s)
    (hn : ((Vv L (A5Module.markedZ s) (A5Module.markedV s)).subgroupOf
      (Gv (A5Module.markedV s))).Normal)
    (g : G) (hg : g ∈ Gv (A5Module.markedV s))
    (W : Subgroup G) (hW : W ∈ nonsingularFamily s) :
    W.map (MulAut.conj g).toMonoidHom ∈ nonsingularFamily s := by
  obtain ⟨u, huVv, hu, rfl⟩ := hW
  have hN := normalizer_perp_of_normal s hn
  have humem : s.map (Multiplicative.ofAdd u) ∈ vectorPerp s v :=
    Vv_eq_vectorPerp s ▸ huVv
  have huwmem : MulAut.conj g (s.map (Multiplicative.ofAdd u)) ∈ vectorPerp s v :=
    (mem_normalizer_iff.mp (hN hg) _).mp humem
  obtain ⟨w, hw⟩ := s.range_eq.ge (vectorPerp_le s v huwmem)
  have hwmem : s.map w ∈ Vv L (A5Module.markedZ s) (A5Module.markedV s) := by
    rw [Vv_eq_vectorPerp s, hw]
    exact huwmem
  have hvu : form.polarBilin v u = 0 := by
    obtain ⟨t, ht, he⟩ := humem
    have ht_eq := s.injective he
    rw [ht_eq] at ht
    exact ht
  refine ⟨w.toAdd, hwmem, ?_, ?_⟩
  · exact fun he => hu ((hf g u w.toAdd hw.symm).trans he)
  · exact Reconstruction.perp_conjugate_of_normal s hf hN g hg u w.toAdd hu hvu hw.symm

/-- G_v genuinely permutes the actual nonsingular-vector family under
hypothetical relative normality of V_v. No action on V is assumed. -/
theorem nonsingularFamily_conjugate (s : A5Module.Marking L V)
    (hf : FusionPreservesForm s)
    (hn : ((Vv L (A5Module.markedZ s) (A5Module.markedV s)).subgroupOf
      (Gv (A5Module.markedV s))).Normal)
    (g : G) (hg : g ∈ Gv (A5Module.markedV s)) :
    (fun W : Subgroup G => W.map (MulAut.conj g).toMonoidHom) '' nonsingularFamily s =
      nonsingularFamily s := by
  apply Set.Subset.antisymm
  · rintro _ ⟨W, hW, rfl⟩
    exact nonsingularFamily_conjugate_mem s hf hn g hg W hW
  · intro W hW
    refine ⟨W.map (MulAut.conj g⁻¹).toMonoidHom,
      nonsingularFamily_conjugate_mem s hf hn g⁻¹ (inv_mem hg) W hW, ?_⟩
    change (W.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = W
    rw [map_map]
    have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
        MonoidHom.id G := by
      ext x
      change g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x
      group
    rw [he, Subgroup.map_id]

/-- The reconstruction argument preceding 13.6.8: relative normality of
V_v in C_G(v) forces C_G(v) to normalize the whole marked module. -/
theorem Gv_le_normalizer_of_Vv_normal (s : A5Module.Marking L V)
    (hf : FusionPreservesForm s)
    (hn : ((Vv L (A5Module.markedZ s) (A5Module.markedV s)).subgroupOf
      (Gv (A5Module.markedV s))).Normal) :
    Gv (A5Module.markedV s) ≤ normalizer (V : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  have hm : (sSup (nonsingularFamily s)).map (MulAut.conj g).toMonoidHom ≤ V := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro W hW
    apply map_le_iff_le_comap.mp
    exact (le_sSup (nonsingularFamily_conjugate_mem s hf hn g hg W hW)).trans
      (nonsingularFamily_le s)
  rw [nonsingularFamily_sSup_eq s] at hm
  exact hm (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)

/-- The source counterexample supplies the nonnormality premise of 13.6.8,
and hence the input to the Thompson/FF reduction. -/
theorem Vv_not_normal_of_failure (s : A5Module.Marking L V)
    (hf : FusionPreservesForm s)
    (hfailure : ¬ Gv (A5Module.markedV s) ≤ normalizer (V : Set G)) :
    ¬ ((Vv L (A5Module.markedZ s) (A5Module.markedV s)).subgroupOf
      (Gv (A5Module.markedV s))).Normal := by
  exact fun hn => hfailure (Gv_le_normalizer_of_Vv_normal s hf hn)

/-- The identified hyperplane supplies the M_v-action premise used by the
same source reduction, from the earlier M_v ≤ N_G(V). -/
theorem Mv_normalizes_marked_Vv (s : A5Module.Marking L V)
    (hf : FusionPreservesForm s) (M : Subgroup G)
    (hM : Mv M (A5Module.markedV s) ≤ normalizer (V : Set G)) :
    Mv M (A5Module.markedV s) ≤
      normalizer (Vv L (A5Module.markedZ s) (A5Module.markedV s) : Set G) :=
  Mv_normalizes_Vv_of_perp s hf M hM (Vv_eq_vectorPerp s)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
