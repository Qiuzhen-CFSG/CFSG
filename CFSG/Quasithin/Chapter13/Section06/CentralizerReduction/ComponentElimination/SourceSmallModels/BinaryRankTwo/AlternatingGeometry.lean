module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.MovingPlane
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo.CubicActions
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Recognizing the A₆ parabolic from its moving binary plane

On the literal even-weight permutation quotient, a Sylow-invariant plane is
conjugate to the canonical syntheme plane. Its stabilizer is therefore a
conjugate of the syntheme parabolic. The join of the marked subgroup D with
an ambient Sylow two-subgroup has order divisible by 8 and 3, so containment
in this parabolic of order 24 is equality.

Two-perfectness of D and normalization by the Sylow subgroup identify D with
the embedded two-residual of the join. Transporting the checked cubic through
the same conjugation puts it in D; the existing cubic calculation then shows
that D fixes only zero on the actual augmentation quotient.

This supplies the A₆ parabolic placement and cubic marking used in the
Sp₄(2)′ block branch of Aschbacher–Smith, Lemma 13.6.22, printed p.932.
The source's prime-support hypothesis is unnecessary here: divisibility of
|D| by 3 suffices. Plane invariance and dimension already give the placement,
so the displacement identity in `MovingPlane` need not be used again.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo

private def coordinateSwap : Equiv.Perm (Fin 6) := Equiv.swap 0 4 * Equiv.swap 1 5

private theorem map_flag_borel :
    (H1 ⊓ H2).map (MulAut.conj coordinateSwap).toMonoidHom = borel := by
  have hp : coordinateSwap • pair 4 5 = pair 0 1 := by decide
  have hs : coordinateSwap • baseSyntheme = baseSyntheme := by decide
  rw [Subgroup.map_inf _ _ _ (MulAut.conj coordinateSwap).injective]
  change (MulAction.stabilizer S (pair 4 5)).map _ ⊓
    (MulAction.stabilizer S baseSyntheme).map _ = borel
  rw [← MulAction.stabilizer_smul_eq_stabilizer_map_conj,
    ← MulAction.stabilizer_smul_eq_stabilizer_map_conj, hp, hs]
  rfl

private theorem T0_isPGroup : IsPGroup 2 T0 := by
  have hb : IsPGroup 2 borel := borelSylow.isPGroup'
  have hm : (H1 ⊓ H2) ≤ borel.comap (MulAut.conj coordinateSwap).toMonoidHom :=
    Subgroup.map_le_iff_le_comap.mp map_flag_borel.le
  exact (hb.comap_of_injective _ (MulAut.conj coordinateSwap).injective).to_le
    (inf_le_left.trans hm)

private theorem exists_conjugate_T0_le (S : Sylow 2 (alternatingGroup (Fin 6))) :
    ∃ g : alternatingGroup (Fin 6),
      (T0.subgroupOf (alternatingGroup (Fin 6))).map (MulAut.conj g).toMonoidHom ≤ S := by
  obtain ⟨R, hR⟩ := (T0_isPGroup.comap_subtype (K := alternatingGroup (Fin 6))).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) R S
  have hc : (R : Subgroup (alternatingGroup (Fin 6))).map
      (MulAut.conj g).toMonoidHom = S :=
    congrArg (fun U : Sylow 2 (alternatingGroup (Fin 6)) =>
      (U : Subgroup (alternatingGroup (Fin 6)))) hg
  exact ⟨g, (Subgroup.map_mono hR).trans_eq hc⟩

private theorem pullback_invariant {A W : Type*} [Group A]
    [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) A W) (J : Subgroup A)
    (E : Submodule (ZMod 2) W) (hE : J ≤ subspaceStabilizer ρ E)
    (g t : A) (ht : g * t * g⁻¹ ∈ J) :
    (E.map (ρ g⁻¹)).map (ρ t) = E.map (ρ g⁻¹) := by
  have hc : E.map (ρ (g * t * g⁻¹)) = E := by
    apply le_antisymm
    · rintro _ ⟨v, hv, rfl⟩
      exact (hE ht v).mpr hv
    · intro v hv
      refine ⟨ρ (g * t * g⁻¹)⁻¹ v, (hE (J.inv_mem ht) v).mpr hv, ?_⟩
      exact ρ.self_inv_apply _ v
  have he : t * g⁻¹ = g⁻¹ * (g * t * g⁻¹) := by group
  rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul, he,
    map_mul, Module.End.mul_eq_comp, Submodule.map_comp, hc]

/-- The stabilizer of an ambient Sylow-invariant plane lies in a conjugate
of the actual syntheme parabolic. -/
theorem alternating_plane_placement
    (S : Sylow 2 (alternatingGroup (Fin 6)))
    (J : Subgroup (alternatingGroup (Fin 6))) (hSJ : (S : Subgroup _) ≤ J)
    (E : Submodule (ZMod 2) (natural (Fin 6)))
    (hdim : Module.finrank (ZMod 2) E = 2)
    (hE : J ≤ subspaceStabilizer (alternatingNaturalRepresentation (Ω := Fin 6)) E) :
    ∃ g : alternatingGroup (Fin 6), J ≤ AlternatingAction.parabolic.map
      (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := exists_conjugate_T0_le S
  let ρ := alternatingNaturalRepresentation (Ω := Fin 6)
  have hinv := pullback_invariant ρ J E hE g
  let f := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom g⁻¹)
  have hdim' : Module.finrank (ZMod 2) (E.map (ρ g⁻¹)) = 2 :=
    (f.finrank_map_eq E).trans hdim
  have he : E.map (ρ g⁻¹) = canonicalPlane := by
    apply canonicalPlane_unique (E.map (ρ g⁻¹)) hdim'
    intro t ht
    have htA : t ∈ alternatingGroup (Fin 6) := ht.2
    exact hinv ⟨t, htA⟩ (hSJ (hg (Subgroup.mem_map_of_mem _ ht)))
  refine ⟨g, ?_⟩
  intro x hx
  have hc := hinv (g⁻¹ * x * g) (by simpa only [mul_assoc,
    mul_inv_cancel_left, mul_inv_cancel, mul_one] using hx)
  rw [he] at hc
  have hp : g⁻¹ * x * g ∈ AlternatingAction.parabolic :=
    ((canonicalPlane_stabilizer_alternating (g⁻¹ * x * g)).mp hc).1
  exact ⟨g⁻¹ * x * g, hp, by simp [MulAut.conj_apply, mul_assoc]⟩

/-- The Sylow two-subgroup and the factor three force the join to be the
whole conjugate parabolic. -/
theorem alternating_parabolic_eq_of_three_dvd
    (S : Sylow 2 (alternatingGroup (Fin 6)))
    (D : Subgroup (alternatingGroup (Fin 6))) (h3 : 3 ∣ Nat.card D)
    (e : MovingPlane (alternatingNaturalRepresentation (Ω := Fin 6)) S D) :
    ∃ g : alternatingGroup (Fin 6), D ⊔ (S : Subgroup _) =
      AlternatingAction.parabolic.map (MulAut.conj g).toMonoidHom := by
  have hplace : ∃ g : alternatingGroup (Fin 6),
      D ⊔ (S : Subgroup (alternatingGroup (Fin 6))) ≤
        AlternatingAction.parabolic.map (MulAut.conj g).toMonoidHom := by
    apply alternating_plane_placement (S := S) (E := e.plane)
    · exact le_sup_right
    · exact e.dimension
    · exact e.invariant
  obtain ⟨g, hg⟩ := hplace
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩
  have hP : Nat.card (AlternatingAction.parabolic.map (MulAut.conj g).toMonoidHom) = 24 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    change Nat.card a6SynthemeStabilizer = 24
    exact a6SynthemeStabilizer_order
  have hS : Nat.card S = 8 :=
    (Nat.card_congr (S.equiv a6BorelSylow).toEquiv).trans a6Borel_order
  let J : Subgroup (alternatingGroup (Fin 6)) := D ⊔ (S : Subgroup _)
  have h8 : 8 ∣ Nat.card J := by
    rw [← hS]
    exact Subgroup.card_dvd_of_le le_sup_right
  have h3' := h3.trans (Subgroup.card_dvd_of_le (show D ≤ D ⊔ (S : Subgroup _) from le_sup_left))
  have h24 : 24 ∣ Nat.card J :=
    (show Nat.Coprime 3 8 by decide).mul_dvd_of_dvd_of_dvd h3' h8
  rw [hP]
  exact Nat.le_of_dvd Nat.card_pos h24

/-- Parabolic recognition with a cubic marking inside the two-perfect D.
Only divisibility of |D| by three is required of its odd part. -/
theorem alternating_movingPlane_recognition_of_three_dvd
    (S : Sylow 2 (alternatingGroup (Fin 6)))
    (D : Subgroup (alternatingGroup (Fin 6)))
    (hD : IsPPerfect 2 D) (hn : (S : Subgroup _) ≤ normalizer (D : Set (alternatingGroup (Fin 6))))
    (h3 : 3 ∣ Nat.card D)
    (e : MovingPlane (alternatingNaturalRepresentation (Ω := Fin 6)) S D) :
    ∃ g : alternatingGroup (Fin 6),
      D ⊔ (S : Subgroup _) = AlternatingAction.parabolic.map (MulAut.conj g).toMonoidHom ∧
      g * AlternatingAction.actor * g⁻¹ ∈ D := by
  obtain ⟨g, hg⟩ := alternating_parabolic_eq_of_three_dvd S D h3 e
  refine ⟨g, hg, ?_⟩
  have hr := embedded_pResidual_join_pGroup D (S : Subgroup _) hD S.isPGroup' hn
  rw [hg, ← map_embedded_pResidual] at hr
  rw [← hr]
  exact Subgroup.mem_map_of_mem _ AlternatingAction.actor_mem_residual

/-- The source-consumable A₆ recognition from the moving plane and the
Sylow three-subgroup of order three. -/
theorem alternating_movingPlane_recognition
    (S : Sylow 2 (alternatingGroup (Fin 6)))
    (D : Subgroup (alternatingGroup (Fin 6)))
    (hD : IsPPerfect 2 D) (hn : (S : Subgroup _) ≤ normalizer (D : Set (alternatingGroup (Fin 6))))
    (hQ : ∃ Q : Sylow 3 D, Nat.card Q = 3)
    (e : MovingPlane (alternatingNaturalRepresentation (Ω := Fin 6)) S D) :
    ∃ g : alternatingGroup (Fin 6),
      D ⊔ (S : Subgroup _) = AlternatingAction.parabolic.map (MulAut.conj g).toMonoidHom ∧
      g * AlternatingAction.actor * g⁻¹ ∈ D := by
  obtain ⟨Q, hQ⟩ := hQ
  apply alternating_movingPlane_recognition_of_three_dvd S D hD hn _ e
  rw [← hQ]
  exact (Q : Subgroup D).card_subgroup_dvd_card

/-- Application of the constructed marking: D fixes only zero on the
literal binary natural quotient. -/
theorem alternating_movingPlane_fixed_eq_zero
    (S : Sylow 2 (alternatingGroup (Fin 6)))
    (D : Subgroup (alternatingGroup (Fin 6)))
    (hD : IsPPerfect 2 D) (hn : (S : Subgroup _) ≤ normalizer (D : Set (alternatingGroup (Fin 6))))
    (hQ : ∃ Q : Sylow 3 D, Nat.card Q = 3)
    (e : MovingPlane (alternatingNaturalRepresentation (Ω := Fin 6)) S D)
    (w : natural (Fin 6))
    (hw : ∀ d ∈ D, alternatingNaturalRepresentation (Ω := Fin 6) d w = w) : w = 0 := by
  obtain ⟨g, _, hg⟩ := alternating_movingPlane_recognition S D hD hn hQ e
  exact G2Action.conjugate_fixed_eq_zero
    (alternatingNaturalRepresentation (Ω := Fin 6)) AlternatingAction.actor
    AlternatingAction.cubic_fixed_eq_zero g w (hw _ hg)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.BinaryRankTwo
