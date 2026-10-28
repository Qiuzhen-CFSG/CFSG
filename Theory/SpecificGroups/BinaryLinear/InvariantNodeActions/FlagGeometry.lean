module

public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.SylowFlags
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.GraphDuality

/-!
# Graph reversal on actual binary flag stabilizers

Inverse transpose composed with an inner automorphism sends the stabilizer
of W to that of (gW)ᗮ. If it preserves the full flag stabilizer, reconstruction
of invariant subspaces identifies these complements with the reversed cuts.
It therefore reverses the marked minimal parabolics. Inner automorphisms
preserving the full flag fix each partial flag individually.

For a preserved minimal parabolic, the same reconstruction applies directly
to its retained cuts: their dimensions are stable under d ↦ m+1-d, forcing
the missing cut to have middle dimension. No Sylow adjustment is assumed.
A common Sylow subgroup supplies a common full flag for two arbitrary bases;
their cuts align by dimension, so two distinct minimal parabolics cannot
both be preserved individually by a graph-times-inner automorphism.

These are the intrinsic geometric steps used in Aschbacher–Smith 13.8.25,
printed pp.959–960 (PDF pp.976–977) of `refs/quasithin.pdf`. They apply to
all positive binary dimensions, hence in particular the source dimensions
3, 4 and 5. Automorphism coverage and ambient-group assembly are separate.
-/

public section

namespace BinaryLinear.InvariantNodeActions
open OuterCyclic

theorem graph_inner_cut_finrank {m : ℕ} (b : Basis m) (g : LinearGroup (m + 1))
    (i : Fin m) :
    Module.finrank (ZMod 2) (flagOrthogonal ((cutSpace b i).map g.toLinearMap)) =
      m - i.val := by
  rw [flagOrthogonal_finrank, LinearEquiv.finrank_map_eq, cutSpace_finrank]
  omega

private theorem graph_inner_cut_proper {m : ℕ} (b : Basis m) (g : LinearGroup (m + 1))
    (i : Fin m) :
    flagOrthogonal ((cutSpace b i).map g.toLinearMap) ≠ ⊥ ∧
      flagOrthogonal ((cutSpace b i).map g.toLinearMap) ≠ ⊤ := by
  have hd := graph_inner_cut_finrank b g i
  have hi := i.isLt
  constructor <;> intro h
  · rw [h, finrank_bot] at hd
    omega
  · rw [h, finrank_top, Module.finrank_fin_fun] at hd
    omega

/-- The full-flag hypothesis identifies the reversed cut after the actual
inner-conjugation adjustment and inverse transpose. -/
theorem graph_inner_cutSpace_of_fullFlag {m : ℕ} (b : Basis m)
    (g : LinearGroup (m + 1))
    (h : (cutStabilizer b Set.univ).map
      (graphLinear (m + 1) * MulAut.conj g).toMonoidHom = cutStabilizer b Set.univ)
    (i : Fin m) :
    flagOrthogonal ((cutSpace b i).map g.toLinearMap) = cutSpace b i.rev := by
  have hle : cutStabilizer b Set.univ ≤ parabolic (cutSpace b i) := by
    intro s hs
    exact (mem_cutStabilizer b Set.univ s).mp hs i (Set.mem_univ i)
  have hm := Subgroup.map_mono (f := (graphLinear (m + 1) * MulAut.conj g).toMonoidHom) hle
  rw [h, graph_inner_map_parabolic] at hm
  obtain ⟨h0, h1⟩ := graph_inner_cut_proper b g i
  obtain ⟨j, hj⟩ := fullFlag_invariant_subspace b _ h0 h1 hm
  have hd := congrArg (fun W : Submodule (ZMod 2) (Space (m + 1)) =>
    Module.finrank (ZMod 2) W) hj
  rw [graph_inner_cut_finrank, cutSpace_finrank] at hd
  have he : j = i.rev := by
    apply Fin.ext
    simp only [Fin.val_rev]
    have := i.isLt
    omega
  simpa only [he] using hj

/-- A graph-times-inner automorphism preserving the full flag reverses its
minimal parabolics, with the basis and product order both fixed. -/
theorem graph_inner_reverses_minimalParabolic {m : ℕ} (b : Basis m)
    (g : LinearGroup (m + 1))
    (h : (cutStabilizer b Set.univ).map
      (graphLinear (m + 1) * MulAut.conj g).toMonoidHom = cutStabilizer b Set.univ)
    (i : Fin m) :
    (minimalParabolic b i).map (graphLinear (m + 1) * MulAut.conj g).toMonoidHom =
      minimalParabolic b i.rev := by
  let a := graphLinear (m + 1) * MulAut.conj g
  have hp (j : Fin m) : (parabolic (cutSpace b j)).map a.toMonoidHom =
      parabolic (cutSpace b j.rev) := by
    rw [graph_inner_map_parabolic, graph_inner_cutSpace_of_fullFlag b g h]
  ext s
  change s ∈ (cutStabilizer b {i}ᶜ).map a.toMonoidHom ↔ s ∈ cutStabilizer b {i.rev}ᶜ
  rw [Subgroup.mem_map_equiv, mem_cutStabilizer, mem_cutStabilizer]
  have hm (j : Fin m) : a.symm s ∈ parabolic (cutSpace b j) ↔
      s ∈ parabolic (cutSpace b j.rev) := by
    rw [← hp j, Subgroup.mem_map_equiv]
  constructor
  · intro hs j hj
    have hji : j.rev ∈ ({i}ᶜ : Set (Fin m)) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Fin.rev_ne_iff] using hj
    have ht := (hm j.rev).mp (hs j.rev hji)
    change s ∈ parabolic (cutSpace b j)
    simpa only [Fin.rev_rev] using ht
  · intro hs j hj
    apply (hm j).mpr
    apply hs j.rev
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, Fin.rev_injective.ne_iff] using hj

/-- Individual preservation of any marked minimal parabolic forces the
middle-node equation. Reconstruction of its invariant subspaces avoids any
assumption that its full flag is preserved. -/
theorem graph_inner_preserves_minimalParabolic_middle {m : ℕ} (b : Basis m)
    (i : Fin m) (g : LinearGroup (m + 1))
    (h : (minimalParabolic b i).map (graphLinear (m + 1) * MulAut.conj g).toMonoidHom =
      minimalParabolic b i) :
    2 * (i.val + 1) = m + 1 := by
  have he : i.rev = i := by
    by_contra hne
    have hle : minimalParabolic b i ≤ parabolic (cutSpace b i.rev) := by
      intro s hs
      exact (mem_cutStabilizer b {i}ᶜ s).mp hs i.rev hne
    have hm := Subgroup.map_mono (f := (graphLinear (m + 1) * MulAut.conj g).toMonoidHom) hle
    rw [h, graph_inner_map_parabolic] at hm
    obtain ⟨h0, h1⟩ := graph_inner_cut_proper b g i.rev
    obtain ⟨j, hj, heq⟩ := (cutStabilizer_le_parabolic_iff b {i}ᶜ _ h0 h1).mp hm
    have hd := congrArg (fun W : Submodule (ZMod 2) (Space (m + 1)) =>
      Module.finrank (ZMod 2) W) heq
    rw [graph_inner_cut_finrank, cutSpace_finrank] at hd
    have hji : j = i := by
      apply Fin.ext
      simp only [Fin.val_rev] at hd
      have := i.isLt
      omega
    exact hj hji
  have hd := congrArg Fin.val he
  simp only [Fin.val_rev] at hd
  have := i.isLt
  omega

/-- No graph-times-inner automorphism preserves two distinct minimal
parabolics individually when they contain a common Sylow two-subgroup.
The original bases and node markings are arbitrary. -/
theorem graph_inner_not_preserves_two_minimalParabolics {m : ℕ}
    (b c : Basis m) (i j : Fin m) (T : Sylow 2 (LinearGroup (m + 1)))
    (g : LinearGroup (m + 1))
    (hTP : (T : Subgroup (LinearGroup (m + 1))) ≤ minimalParabolic b i)
    (hTQ : (T : Subgroup (LinearGroup (m + 1))) ≤ minimalParabolic c j)
    (hne : minimalParabolic b i ≠ minimalParabolic c j) :
    ¬ ((minimalParabolic b i).map (graphLinear (m + 1) * MulAut.conj g).toMonoidHom =
        minimalParabolic b i ∧
      (minimalParabolic c j).map (graphLinear (m + 1) * MulAut.conj g).toMonoidHom =
        minimalParabolic c j) := by
  rintro ⟨hP, hQ⟩
  have hi := graph_inner_preserves_minimalParabolic_middle b i g hP
  have hj := graph_inner_preserves_minimalParabolic_middle c j g hQ
  have hij : i = j := Fin.ext (by omega)
  obtain ⟨d, _, hbd, hcd⟩ := commonSylow_minimalParabolic_alignment b c i j T hTP hTQ
  apply hne
  rw [hbd, hcd, hij]

end BinaryLinear.InvariantNodeActions
