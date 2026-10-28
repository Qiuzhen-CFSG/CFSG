module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Binary.CentralizerGeometry

/-!
# Sylow-containing flags and the central transvection

Every proper subspace stabilized by the component Sylow lies between the
image line and fixed hyperplane of its central transvection. Indeed its
binary parabolic radical is normalized by that Sylow and hence lies in it.
The transvection centralizes the radical, whose centralizer is contained in
the radical itself. The rank-one action now gives the two inclusions.

Dimensions therefore identify all the end-node flags, and identify a flag
of types `{1,n-1}` with the transvection's centralizer flag. Its overgroup
with all of S lies in M. Only S intersected with L is used in the radical
argument; no ambient normality of L or invariance under all of S is asserted.

Source: Aschbacher–Smith 2.3.9(7), combined manuscript of 1 March 2004,
printed pp.525–526. This proves the geometric identification needed for
the degree-five `{1,4}` relative-block obstruction.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open Subgroup

variable {n : ℕ} {G : Type*} [Group G] {L : Subgroup G} [NeZero n]
  {e : L ≃* PSL n} {t : L}

private theorem radical_le_sylow {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (T : Sylow 2 (BinaryLinear.GL V)) (W : Submodule (ZMod 2) V)
    (hTW : (T : Subgroup _) ≤ BinaryLinear.parabolic W) :
    BinaryLinear.radical W ≤ T := by
  exact sup_eq_right.mp (T.is_maximal'
    ((BinaryLinear.radical_two W).to_sup_of_normal_left' T.isPGroup'
      (hTW.trans (BinaryLinear.parabolic_le_normalizer W))) le_sup_right)

variable {H M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Every proper subspace stabilized by the component Sylow lies between the
image line and fixed hyperplane of its central transvection. -/
theorem TransvectionCoordinates.subspace_bounds
    (c : TransvectionCoordinates e t) (h : LocalSetup H L M S z)
    (ht : IsConjugationProjection L z t) (W : Space n) (hW : W ≠ ⊥) (hWt : W ≠ ⊤)
    (hSW : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ subspaceStabilizer e W) :
    c.line ≤ W ∧ W ≤ c.hyperplane := by
  let := h.finite
  obtain ⟨T, hT⟩ := exists_component_sylow h
  let T' := T.mapSurjective (f := (linearModel e).toMonoidHom) (linearModel e).surjective
  have hT'W : (T' : Subgroup _) ≤ BinaryLinear.parabolic W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hSW (hT ▸ hx)
  have hrad := radical_le_sylow T' W hT'W
  have hcentral : linearModel e t ∈ centralizer (BinaryLinear.radical W : Set _) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hrad hx
    have hyS : y ∈ ((S : Subgroup H).map H.subtype).subgroupOf L := hT ▸ hy
    have hc := projection_centralizes_normalizer h e ht hyS (le_normalizer y.property)
    have hcy : y * t = t * y := Subtype.ext hc
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg (linearModel e) hcy
  have htr := BinaryLinear.centralizer_radical_le hW hWt hcentral
  constructor
  · apply Submodule.span_le.mpr
    rintro v rfl
    obtain ⟨v₀, hv₀⟩ := LinearMap.surjective c.functional_ne_zero (1 : ZMod 2)
    have hd := htr.2 v₀
    rw [c.action, hv₀, one_smul, add_sub_cancel_left] at hd
    exact hd
  · intro v hv
    have hf := htr.1 v hv
    rw [c.action] at hf
    have hz : c.functional v • c.vector = 0 := add_eq_left.mp hf
    exact (smul_eq_zero.mp hz).resolve_right c.vector_ne_zero


/-- Apply the radical argument to each constituent of an actual flag. -/
theorem TransvectionCoordinates.flag_subspace_bounds
    (c : TransvectionCoordinates e t) (h : LocalSetup H L M S z)
    (ht : IsConjugationProjection L z t) (F : Flag n)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F)
    (W : Space n) (hW : W ∈ F.spaces) : c.line ≤ W ∧ W ≤ c.hyperplane := by
  apply c.subspace_bounds h ht W (F.proper W hW).1 (F.proper W hW).2
  intro x hx
  exact (mem_flagStabilizer e F x).mp (hSF hx) W hW

/-- A Sylow-containing line parabolic is marked by the projection's image line. -/
theorem TransvectionCoordinates.flag_spaces_eq_line
    (c : TransvectionCoordinates e t) (h : LocalSetup H L M S z)
    (ht : IsConjugationProjection L z t) (F : Flag n)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F)
    (hF : F.types = {1}) : F.spaces = {c.line} := by
  classical
  apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
  refine ⟨F.nonempty, ?_⟩
  intro W hW
  have hd : Module.finrank (ZMod 2) W ∈ F.types := Finset.mem_image.mpr ⟨W, hW, rfl⟩
  rw [hF, Finset.mem_singleton] at hd
  exact (Submodule.eq_of_le_of_finrank_eq (c.flag_subspace_bounds h ht F hSF W hW).1
    (c.line_finrank.trans hd.symm)).symm

/-- The dual end-node parabolic is marked by the projection's fixed hyperplane. -/
theorem TransvectionCoordinates.flag_spaces_eq_hyperplane
    (c : TransvectionCoordinates e t) (h : LocalSetup H L M S z)
    (ht : IsConjugationProjection L z t) (F : Flag n)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F)
    (hF : F.types = {n - 1}) : F.spaces = {c.hyperplane} := by
  classical
  apply Finset.eq_singleton_iff_nonempty_unique_mem.mpr
  refine ⟨F.nonempty, ?_⟩
  intro W hW
  have hd : Module.finrank (ZMod 2) W ∈ F.types := Finset.mem_image.mpr ⟨W, hW, rfl⟩
  rw [hF, Finset.mem_singleton] at hd
  apply Submodule.eq_of_le_of_finrank_eq (c.flag_subspace_bounds h ht F hSF W hW).2
  have := c.hyperplane_finrank
  omega

/-- Dimensions identify both constituents of the Sylow-containing end flag. -/
theorem TransvectionCoordinates.flag_spaces_eq_of_types
    (c : TransvectionCoordinates e t) (h : LocalSetup H L M S z)
    (ht : IsConjugationProjection L z t) (F : Flag n)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F)
    (hF : F.types = {1, n - 1}) : F.spaces = {c.line, c.hyperplane} := by
  classical
  have line_eq (W : Space n) (hW : W ∈ F.spaces)
      (hd : Module.finrank (ZMod 2) W = 1) : W = c.line :=
    (Submodule.eq_of_le_of_finrank_eq (c.flag_subspace_bounds h ht F hSF W hW).1
      (c.line_finrank.trans hd.symm)).symm
  have hyperplane_eq (W : Space n) (hW : W ∈ F.spaces)
      (hd : Module.finrank (ZMod 2) W = n - 1) : W = c.hyperplane := by
    apply Submodule.eq_of_le_of_finrank_eq (c.flag_subspace_bounds h ht F hSF W hW).2
    have := c.hyperplane_finrank
    omega
  apply Finset.Subset.antisymm
  · intro W hW
    have hd : Module.finrank (ZMod 2) W ∈ F.types := Finset.mem_image.mpr ⟨W, hW, rfl⟩
    rw [hF] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd ⊢
    exact hd.elim (fun hd => Or.inl (line_eq W hW hd))
      (fun hd => Or.inr (hyperplane_eq W hW hd))
  · intro W hW
    simp only [Finset.mem_insert, Finset.mem_singleton] at hW
    rcases hW with rfl | rfl
    · have hd : 1 ∈ F.types := by rw [hF]; simp
      obtain ⟨W, hW, hd⟩ := Finset.mem_image.mp hd
      rwa [← line_eq W hW hd]
    · have hd : n - 1 ∈ F.types := by rw [hF]; simp
      obtain ⟨W, hW, hd⟩ := Finset.mem_image.mp hd
      rwa [← hyperplane_eq W hW hd]

/-- A flag of types `{1,n-1}` containing the component Sylow has exactly the
projected transvection as its centralizer marking. -/
theorem TransvectionCoordinates.centralizer_eq_flag_of_types
    (c : TransvectionCoordinates e t) (h : LocalSetup H L M S z)
    (ht : IsConjugationProjection L z t) (F : Flag n)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F)
    (hF : F.types = {1, n - 1}) : centralizer ({t} : Set L) = flagStabilizer e F := by
  rw [c.centralizer_eq]
  ext x
  rw [mem_flagStabilizer]
  simp only [c.flag_spaces_eq_of_types h ht F hSF hF, Finset.mem_insert,
    Finset.mem_singleton, forall_eq_or_imp, forall_eq, mem_inf, mem_subspaceStabilizer]

/-- The geometric identification lets the centralizer bound apply to the
given flag, without assuming it was the flag constructed from the coordinates. -/
theorem TransvectionCoordinates.flagOvergroup_le_of_types
    (c : TransvectionCoordinates e t) (h : LocalSetup H L M S z)
    (ht : IsConjugationProjection L z t) (F : Flag n) (hn : 2 ≤ n)
    (hSF : ((S : Subgroup H).map H.subtype).subgroupOf L ≤ flagStabilizer e F)
    (hF : F.types = {1, n - 1}) :
    flagOvergroup e F ((S : Subgroup H).map H.subtype) ≤ M := by
  have he : flagStabilizer e F = flagStabilizer e (c.flag hn) :=
    (c.centralizer_eq_flag_of_types h ht F hSF hF).symm.trans (c.centralizer_eq_flag hn)
  change ambientFlagStabilizer e F ⊔ _ ≤ M
  change (flagStabilizer e F).map L.subtype ⊔ _ ≤ M
  rw [he]
  exact c.flagOvergroup_le hn h ht

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary

end
