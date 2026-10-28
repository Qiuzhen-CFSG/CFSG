module

public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.SylowFlags
public import Theory.SpecificGroups.BinaryLinear.OrderedFlagGeneration
/-!
# Two invariant parabolics in the actual binary SL4 and SL5 groups

A Sylow two-subgroup is the stabilizer of a full binary flag. Every
Sylow-normalizing automorphism is inner or graph-times-inner and hence
preserves the end cuts as a set and the middle cuts as a set. The two
corresponding partial-flag stabilizers are proper and generate the whole
group, because every minimal parabolic omits a cut in one of these sets.
This gives an intrinsic pair for any actual Sylow, without module or
normalizer-image hypotheses.

Source: Aschbacher–Smith, proof of B.6.9, printed p.116; the rank-three and
rank-four binary linear cases of the invariant-parabolic argument.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic

private theorem graph_fixes_symmetric_cuts {m : ℕ} (b : Basis m)
    (g : LinearGroup (m+1))
    (hB : (cutStabilizer b Set.univ).map
      (graphLinear (m+1) * MulAut.conj g).toMonoidHom = cutStabilizer b Set.univ)
    (cuts : Set (Fin m)) (hc : ∀ i : Fin m, i.rev ∈ cuts ↔ i ∈ cuts) :
    (cutStabilizer b cuts).map (graphLinear (m+1) * MulAut.conj g).toMonoidHom =
      cutStabilizer b cuts := by
  let a := graphLinear (m+1) * MulAut.conj g
  have hp (j : Fin m) : (parabolic (cutSpace b j)).map a.toMonoidHom =
      parabolic (cutSpace b j.rev) := by
    rw [graph_inner_map_parabolic, graph_inner_cutSpace_of_fullFlag b g hB]
  ext x
  change x ∈ (cutStabilizer b cuts).map a.toMonoidHom ↔ x ∈ cutStabilizer b cuts
  rw [Subgroup.mem_map_equiv, mem_cutStabilizer, mem_cutStabilizer]
  have hm (j : Fin m) : a.symm x ∈ parabolic (cutSpace b j) ↔
      x ∈ parabolic (cutSpace b j.rev) := by
    rw [← hp j, Subgroup.mem_map_equiv]
  constructor
  · intro hx j hj
    have he := (hm j.rev).mp (hx j.rev ((hc j).mpr hj))
    change x ∈ parabolic (cutSpace b j)
    simpa only [Fin.rev_rev] using he
  · intro hx j hj
    exact (hm j).mpr (hx j.rev ((hc j).mpr hj))

private theorem automorphism_fixes_symmetric_cuts {m : ℕ}
    (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4) (b : Basis m)
    (cuts : Set (Fin m)) (hc : ∀ i : Fin m, i.rev ∈ cuts ↔ i ∈ cuts)
    (a : MulAut (LinearGroup (m+1)))
    (hB : (cutStabilizer b Set.univ).map a.toMonoidHom = cutStabilizer b Set.univ) :
    (cutStabilizer b cuts).map a.toMonoidHom = cutStabilizer b cuts := by
  obtain ⟨g, rfl | rfl⟩ := smallDimension_inner_graph (by omega) (by omega) a
  · exact inner_fixes_cutStabilizer b g hB cuts
  · exact graph_fixes_symmetric_cuts b g hB cuts hc

private theorem cuts_ne_top {m : ℕ} (b : Basis m) (cuts : Set (Fin m))
    (hc : cuts.Nonempty) : cutStabilizer b cuts ≠ ⊤ := by
  intro he
  obtain ⟨i,hi⟩ := hc
  have ht : cutStabilizer b ∅ ≤ cutStabilizer b cuts := by rw [he]; exact le_top
  exact ((cutStabilizer_le_iff b ∅ cuts).mp ht hi)

private theorem complementary_cuts_generate {m : ℕ} (hm : 1 ≤ m)
    (b : Basis m) (cuts : Set (Fin m)) :
    cutStabilizer b cuts ⊔ cutStabilizer b cutsᶜ = ⊤ := by
  apply top_unique
  rw [← iSup_minimalParabolic_eq_top hm b]
  apply iSup_le
  intro i
  by_cases hi : i ∈ cuts
  · apply le_trans _ le_sup_right
    apply (cutStabilizer_le_iff b {i}ᶜ cutsᶜ).mpr
    intro j hj he
    exact hj (he ▸ hi)
  · apply le_trans _ le_sup_left
    apply (cutStabilizer_le_iff b {i}ᶜ cuts).mpr
    intro j hj he
    exact hi (he ▸ hj)

/-- Two proper flag stabilizers containing the same Sylow subgroup generate
SL4(2) or SL5(2), and every automorphism preserving that Sylow fixes both. -/
private theorem exists_automorphism_invariant_parabolic_pair_aux {m : ℕ}
    (hm₀ : 3 ≤ m) (hm₁ : m ≤ 4) (S : Sylow 2 (LinearGroup (m+1))) :
    ∃ P Q : Subgroup (LinearGroup (m+1)), P ⊔ Q = ⊤ ∧ P ≠ ⊤ ∧ Q ≠ ⊤ ∧
      (S : Subgroup (LinearGroup (m+1))) ≤ P ∧
      (S : Subgroup (LinearGroup (m+1))) ≤ Q ∧
      ∀ a : MulAut (LinearGroup (m+1)),
        (S : Subgroup (LinearGroup (m+1))).map a.toMonoidHom = S →
        P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q := by
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S
  let cuts : Set (Fin m) := {i | i.val=0 ∨ i.val=m-1}
  have hrev (i : Fin m) : i.rev ∈ cuts ↔ i ∈ cuts := by
    simp only [cuts, Set.mem_ofPred_eq, Fin.val_rev]
    have hi := i.isLt
    omega
  have hrev' (i : Fin m) : i.rev ∈ cutsᶜ ↔ i ∈ cutsᶜ := not_congr (hrev i)
  have hc : cuts.Nonempty := ⟨⟨0,by omega⟩,Or.inl rfl⟩
  have hcc : cutsᶜ.Nonempty := by
    refine ⟨⟨1,by omega⟩,?_⟩
    change ¬(1=0 ∨ 1=m-1)
    omega
  refine ⟨cutStabilizer b cuts,cutStabilizer b cutsᶜ,
    complementary_cuts_generate (by omega) b cuts,cuts_ne_top b cuts hc,
    cuts_ne_top b cutsᶜ hcc,?_,?_,?_⟩
  · rw [hb]; exact (cutStabilizer_le_iff b Set.univ cuts).mpr (Set.subset_univ _)
  · rw [hb]; exact (cutStabilizer_le_iff b Set.univ cutsᶜ).mpr (Set.subset_univ _)
  · intro a ha
    rw [hb] at ha
    exact ⟨automorphism_fixes_symmetric_cuts (by omega) hm₁ b cuts hrev a ha,
      automorphism_fixes_symmetric_cuts (by omega) hm₁ b cutsᶜ hrev' a ha⟩

theorem exists_automorphism_invariant_parabolic_pair {n : ℕ} (hn : n=4 ∨ n=5)
    (S : Sylow 2 (LinearGroup n)) :
    ∃ P Q : Subgroup (LinearGroup n), P ⊔ Q = ⊤ ∧ P ≠ ⊤ ∧ Q ≠ ⊤ ∧
      (S : Subgroup (LinearGroup n)) ≤ P ∧ (S : Subgroup (LinearGroup n)) ≤ Q ∧
      ∀ a : MulAut (LinearGroup n), (S : Subgroup (LinearGroup n)).map a.toMonoidHom = S →
        P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q := by
  rcases hn with rfl | rfl
  · exact exists_automorphism_invariant_parabolic_pair_aux (by decide) (by decide) S
  · exact exists_automorphism_invariant_parabolic_pair_aux (by decide) (by decide) S
end BinaryLinear.InvariantNodeActions
