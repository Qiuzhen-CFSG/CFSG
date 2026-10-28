module

public import Theory.AlgebraicGroup.Parabolic.RelativeRoot.source_chevalley_torus_fiber_bridge

/-!
This module extracts a root vector from every nonzero invariant submodule of a
relative-root fiber.  The canonical coordinate equivalence transports a
nonzero vector to finitely many fiber coordinates.  Distinct fiber roots are
separated by a coroot pairing, and the corresponding Chevalley torus action
is used successively to cancel one coordinate at a time.  The resulting
single-coordinate vector is a nonzero root vector in the original submodule.
No irreducibility or orbit-spanning theorem is used; the only input is the
source Chevalley torus action formula and root-system perfectness.
-/

namespace Theory.AlgebraicGroup

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]

set_option warningAsError false

public abbrev FiberIndex (S : RelativeRootRepresentationSource K) :=
  { γ : S.D.Root // γ ∈ relativeRootFiberAtHeight
      S.D S.coeff S.J S.height S.root }

private lemma root_pairing_functional_injective
    (S : RelativeRootRepresentationSource K) :
    Function.Injective (fun γ : S.D.Root =>
      (fun β : S.D.Root => S.D.pairing γ β)) := by
  intro α β hab
  apply S.pairing.root.injective
  apply S.pairing.toPerfPair.injective
  change S.pairing.toLinearMap (S.pairing.root α) =
    S.pairing.toLinearMap (S.pairing.root β)
  apply LinearMap.ext_on
    (RootPairing.IsRootSystem.span_coroot_eq_top (P := S.pairing))
  rintro _ ⟨δ, rfl⟩
  rw [S.pairing.root_coroot_eq_pairing]
  calc
    S.pairing.pairing α δ = (S.D.pairing α δ : ℚ) := by
      symm
      simpa only [Equiv.refl_apply] using S.rootSystemRealization.1 α δ
    _ = (S.D.pairing β δ : ℚ) := by
      exact_mod_cast congrFun hab δ
    _ = S.pairing.pairing β δ := by
      simpa only [Equiv.refl_apply] using S.rootSystemRealization.1 β δ

private lemma exists_pairing_ne
    (S : RelativeRootRepresentationSource K) {α β : S.D.Root}
    (hne : α ≠ β) :
    ∃ δ : S.D.Root, S.D.pairing α δ ≠ S.D.pairing β δ := by
  by_contra h
  apply hne
  apply root_pairing_functional_injective S
  funext δ
  exact not_ne_iff.mp ((not_exists.mp h) δ)

private lemma torus_action_coordinate
    (S : RelativeRootRepresentationSource K) (M : RelativeRootFiberModule S)
    (β : S.D.Root) (u : kˣ) (a : RelativeRootFiberCoordinate S) :
    (M.representation.action (S.chevalleyTorusLeviPoint β u⁻¹)).1
        (M.coordinateLinearEquiv a) =
      M.coordinateLinearEquiv (fun γ =>
        ((u : k) ^ S.D.pairing γ.1 β) * a γ) := by
  classical
  letI : Finite (FiberIndex S) := by infer_instance
  letI := Fintype.ofFinite (FiberIndex S)
  have ha : a = ∑ γ : FiberIndex S,
      @Pi.single _ (fun _ => k) (inferInstance) (Classical.decEq _) γ (a γ) := by
    funext γ
    simp
  have hsum : M.coordinateLinearEquiv a =
      ∑ γ : FiberIndex S, M.rootVector (γ, a γ) := by
    calc
      M.coordinateLinearEquiv a = M.coordinateLinearEquiv
          (∑ γ : FiberIndex S,
            @Pi.single _ (fun _ => k) (inferInstance) (Classical.decEq _) γ (a γ)) := by
            exact congrArg M.coordinateLinearEquiv ha
      _ = ∑ γ : FiberIndex S, M.coordinateLinearEquiv
          (@Pi.single _ (fun _ => k) (inferInstance) (Classical.decEq _) γ (a γ)) := by
            rw [map_sum]
      _ = ∑ γ : FiberIndex S, M.rootVector (γ, a γ) := by
            apply Finset.sum_congr rfl
            intro γ hγ
            rw [M.rootVector_coordinate]
  have hcoord : (fun γ => ((u : k) ^ S.D.pairing γ.1 β) * a γ) =
      ∑ γ : FiberIndex S,
        @Pi.single _ (fun _ => k) (inferInstance) (Classical.decEq _) γ
          (((u : k) ^ S.D.pairing γ.1 β) * a γ) := by
    funext γ
    simp
  rw [hsum, map_sum]
  calc
    (∑ γ : FiberIndex S,
        (M.representation.action (S.chevalleyTorusLeviPoint β u⁻¹)).1
          (M.rootVector (γ, a γ))) =
        ∑ γ : FiberIndex S, M.coordinateLinearEquiv
          (@Pi.single _ (fun _ => k) (inferInstance) (Classical.decEq _) γ
            (((u : k) ^ S.D.pairing γ.1 β) * a γ)) := by
      apply Finset.sum_congr rfl
      intro γ hγ
      rw [M.chevalleyTorus_inv_action_rootVector, M.rootVector_coordinate]
      rw [← M.coordinateLinearEquiv.map_smul]
      apply congrArg M.coordinateLinearEquiv
      funext η
      by_cases hη : η = γ
      · subst η
        simp [smul_eq_mul]
      · simp [Pi.single, hη]
    _ = M.coordinateLinearEquiv
          (∑ γ : FiberIndex S,
            @Pi.single _ (fun _ => k) (inferInstance) (Classical.decEq _) γ
              (((u : k) ^ S.D.pairing γ.1 β) * a γ)) := by
      rw [map_sum]
    _ = M.coordinateLinearEquiv (fun γ =>
          ((u : k) ^ S.D.pairing γ.1 β) * a γ) := by
      rw [hcoord]

public theorem RelativeRootFiberModule.exists_rootVector_mem_of_invariant_submodule
    (S : RelativeRootRepresentationSource K) (M : RelativeRootFiberModule S)
    (W : Submodule k M.V) (hW : IsInvariantSubmodule M.representation W)
    (hW0 : W ≠ ⊥) :
    ∃ γ : FiberIndex S, ∃ t : k, t ≠ 0 ∧ M.rootVector (γ, t) ∈ W := by
  classical
  letI : Finite (FiberIndex S) := by infer_instance
  letI := Fintype.ofFinite (FiberIndex S)
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  let a : RelativeRootFiberCoordinate S := M.coordinateLinearEquiv.symm v
  have ha0 : a ≠ 0 := by
    intro ha
    apply hv0
    have hcoord : M.coordinateLinearEquiv a = v :=
      M.coordinateLinearEquiv.apply_symm_apply v
    rw [← hcoord, ha]
    simp
  obtain ⟨α, hα⟩ : ∃ α : FiberIndex S, a α ≠ 0 := by
    by_contra h
    apply ha0
    funext γ
    exact not_ne_iff.mp ((not_exists.mp h) γ)
  let coord : RelativeRootFiberCoordinate S → M.V := M.coordinateLinearEquiv
  have hcoordW : coord a ∈ W := by
    change M.coordinateLinearEquiv a ∈ W
    rw [M.coordinateLinearEquiv.apply_symm_apply]
    exact hvW
  have process : ∀ (s : Finset (FiberIndex S)) (b : RelativeRootFiberCoordinate S),
      (∀ γ, γ ≠ α → γ ∈ s ∨ b γ = 0) → b α ≠ 0 → coord b ∈ W →
      ∃ b', (∀ γ, γ ≠ α → b' γ = 0) ∧
        b' α ≠ 0 ∧ coord b' ∈ W := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro b hbSupport hbα hbW
        refine ⟨b, ?_, hbα, hbW⟩
        intro γ hγ
        exact (hbSupport γ hγ).resolve_left (by simp)
    | @insert β s hβ ih =>
        intro b hbSupport hbα hbW
        by_cases hβα : β = α
        · subst β
          exact ih b
            (by
              intro γ hγα
              exact (hbSupport γ hγα).elim
                (fun hmem => by
                  rcases Finset.mem_insert.mp hmem with hmem | hmem
                  · exact (hγα hmem).elim
                  · exact Or.inl hmem)
                Or.inr) hbα hbW
        · obtain ⟨δ, hδ⟩ := exists_pairing_ne S (α := α.1) (β := β.1)
            (fun h => hβα (Subtype.ext h.symm))
          obtain ⟨u, hu⟩ := exists_unit_zpow_ne_one (k := k)
            (show S.D.pairing α δ - S.D.pairing β δ ≠ 0 by omega)
          let la : k := (u : k) ^ S.D.pairing α δ
          let lb : k := (u : k) ^ S.D.pairing β δ
          have hsep : la ≠ lb := by
            dsimp [la, lb]
            intro heq
            have heqU : u ^ S.D.pairing α δ = u ^ S.D.pairing β δ := by
              apply Units.ext
              simpa only [Units.val_zpow_eq_zpow_val] using heq
            apply hu
            rw [zpow_sub, heqU]
            simp
          let b' : RelativeRootFiberCoordinate S := fun γ =>
            (((u : k) ^ S.D.pairing γ.1 δ) - lb) * b γ
          have hb'α : b' α ≠ 0 := by
            dsimp [b', la, lb]
            exact mul_ne_zero (sub_ne_zero.mpr hsep) hbα
          have hb'W : coord b' ∈ W := by
            have hact := torus_action_coordinate S M δ u b
            have hactW := hW (S.chevalleyTorusLeviPoint δ u⁻¹)
              (coord b) hbW
            have heq : coord b' =
                (M.representation.action
                  (S.chevalleyTorusLeviPoint δ u⁻¹)).1 (coord b) - lb • coord b := by
              rw [hact]
              let c : RelativeRootFiberCoordinate S :=
                fun γ => ((u : k) ^ S.D.pairing γ.1 δ) * b γ
              change M.coordinateLinearEquiv b' =
                M.coordinateLinearEquiv c - lb • M.coordinateLinearEquiv b
              have hmap : M.coordinateLinearEquiv (c - lb • b) =
                  M.coordinateLinearEquiv c - lb • M.coordinateLinearEquiv b := by
                rw [map_sub, map_smul]
              rw [← hmap]
              apply congrArg M.coordinateLinearEquiv
              funext γ
              simp [b', c, lb, sub_mul]
            rw [heq]
            exact W.sub_mem hactW (W.smul_mem lb hbW)
          have hb'β : b' β = 0 := by
            change ((u : k) ^ S.D.pairing β δ - lb) * b β = 0
            rw [show (u : k) ^ S.D.pairing β δ = lb by rfl, sub_self, zero_mul]
          have hb'Support : ∀ γ, γ ≠ α → γ ∈ s ∨ b' γ = 0 := by
            intro γ hγα
            by_cases hγs : γ ∈ s
            · exact Or.inl hγs
            · by_cases hγβ : γ = β
              · exact Or.inr (hγβ ▸ hb'β)
              · exact (hbSupport γ hγα).elim
                  (fun hγin => by
                    rcases Finset.mem_insert.mp hγin with hEq | hIn
                    · exact (hγβ hEq).elim
                    · exact (hγs hIn).elim)
                  (fun hbγ => Or.inr (by dsimp [b']; rw [hbγ, mul_zero]))
          exact ih b' hb'Support hb'α hb'W
  obtain ⟨b, hbzero, hbα, hbW⟩ := process
    (Finset.univ.erase α) a (by
      intro γ hγα
      by_cases hγα' : γ = α
      · exact (hγα hγα').elim
      · exact Or.inl (Finset.mem_erase.mpr ⟨hγα', Finset.mem_univ _⟩))
    hα hcoordW
  have hbform : b =
      @Pi.single _ (fun _ => k) (inferInstance) (Classical.decEq _) α (b α) := by
    funext γ
    by_cases hγα : γ = α
    · subst γ
      simp
    · have hzero := hbzero γ hγα
      rw [@Pi.single_apply _ (Classical.decEq _) k inferInstance α (b α) γ]
      simp [hγα, hzero]
  refine ⟨α, b α, hbα, ?_⟩
  have hroot : M.rootVector (α, b α) = coord b := by
    rw [M.rootVector_coordinate α (b α), ← hbform]
  have _hroot_ne_zero : M.rootVector (α, b α) ≠ 0 :=
    M.rootVector_ne_zero α hbα
  exact hroot ▸ hbW

end Theory.AlgebraicGroup
