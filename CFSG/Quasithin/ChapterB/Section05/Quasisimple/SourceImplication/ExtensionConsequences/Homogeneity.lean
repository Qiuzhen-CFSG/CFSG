module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCohomology

/-!
# Homogeneity of the actual B.5.1 moved quotient

Transvections prove irreducibility of the natural SL module even after
restriction to the binary prime field. A chosen coordinate summand then
witnesses homogeneity of repeated natural modules. Their fixed space is zero,
so quotienting the literal moved module by its fixed vectors preserves these
coordinates. This proves B.5.1(3) from the four action alternatives, with no
additional source parameter and no restriction on the binary field degree.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1(3),
printed pp.99 and 102.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace ExtensionConsequences
universe u v w z
variable {G : Type u} {H : Type v} [Group G] [Group H]
  {V : Type w} {W : Type z} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) H W}

def actionSymm (e : ActionEquiv ρ σ) : ActionEquiv σ ρ where
  groupEquiv := e.groupEquiv.symm
  linearEquiv := e.linearEquiv.symm
  intertwines g v := by
    apply e.linearEquiv.injective
    simp only [e.linearEquiv.apply_symm_apply, e.intertwines, e.groupEquiv.apply_symm_apply]

theorem irreducible_of_equiv (e : ActionEquiv ρ σ) (hi : IsIrreducible σ) :
    IsIrreducible ρ := by
  let := hi
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial σ
  let : Nontrivial V := e.linearEquiv.symm.injective.nontrivial
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation σ := ⟨S.toSubmodule.comap e.linearEquiv.symm.toLinearMap, by
    intro g w hw
    change e.linearEquiv.symm (σ g w) ∈ S
    have he := (actionSymm e).intertwines g w
    change e.linearEquiv.symm (σ g w) = _ at he
    rw [he]
    exact S.apply_mem_toSubmodule _ hw⟩
  rcases eq_bot_or_eq_top T with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.comap_injective_of_surjective e.linearEquiv.symm.surjective
    change T.toSubmodule = Submodule.comap e.linearEquiv.symm.toLinearMap ⊥
    rw [hb]
    ext w
    change w = 0 ↔ e.linearEquiv.symm w = 0
    exact e.linearEquiv.symm.map_eq_zero_iff.symm
  · right
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.comap_injective_of_surjective e.linearEquiv.symm.surjective
    change T.toSubmodule = Submodule.comap e.linearEquiv.symm.toLinearMap ⊤
    rw [ht]
    rfl

theorem homogeneous_of_irreducible (hi : IsIrreducible ρ) : IsHomogeneousAction ρ := by
  let S : Subrepresentation ρ := ⊤
  let e : ActionEquiv S.toRepresentation ρ :=
    ⟨MulEquiv.refl G, Submodule.topEquiv, fun _ _ => rfl⟩
  refine ⟨1, by decide, S, irreducible_of_equiv e hi,
    e.linearEquiv.symm.trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) S.toSubmodule).symm, ?_⟩
  intro g v
  rfl

theorem homogeneous_of_repeated {r : ℕ} (hr : 0 < r)
    (e : ActionEquiv ρ (repeated σ r)) (hi : IsIrreducible σ) :
    IsHomogeneousAction ρ := by
  classical
  let i : Fin r := ⟨0, hr⟩
  let j : W →ₗ[ZMod 2] V := e.linearEquiv.symm.toLinearMap.comp (LinearMap.single (ZMod 2) (fun _ : Fin r => W) i)
  have hj : Function.Injective j := by
    intro a b hab
    have h := congrArg (fun v => e.linearEquiv v i) hab
    simpa [j] using h
  have heq (g : G) (w : W) : ρ g (j w) = j (σ (e.groupEquiv g) w) := by
    apply e.linearEquiv.injective
    rw [e.intertwines]
    change repeated σ r _ (e.linearEquiv (e.linearEquiv.symm _)) =
      e.linearEquiv (e.linearEquiv.symm _)
    simp only [LinearEquiv.apply_symm_apply]
    ext k
    by_cases hk : k = i
    · subst k; simp [repeated]
    · simp [repeated, Pi.single_eq_of_ne hk]
  let S : Subrepresentation ρ := ⟨j.range, by
    rintro g v ⟨w, rfl⟩
    exact ⟨σ (e.groupEquiv g) w, (heq g w).symm⟩⟩
  let q : W ≃ₗ[ZMod 2] S.toSubmodule := LinearEquiv.ofInjective j hj
  have hq (g : G) (w : W) : q (σ (e.groupEquiv g) w) = S.toRepresentation g (q w) := by
    apply Subtype.ext
    exact (heq g w).symm
  let t : ActionEquiv S.toRepresentation σ :=
    ⟨e.groupEquiv, q.symm, by
      intro g v
      apply q.injective
      rw [LinearEquiv.apply_symm_apply, hq, LinearEquiv.apply_symm_apply]⟩
  refine ⟨r, hr, S, irreducible_of_equiv t hi,
    e.linearEquiv.trans (LinearEquiv.piCongrRight fun _ => q), ?_⟩
  intro g v
  funext k
  change q (e.linearEquiv (ρ g v) k) = S.toRepresentation g (q (e.linearEquiv v k))
  rw [e.intertwines]
  exact hq g _

open Matrix.SpecialLinearGroup Representation.OneCohomology.SLHigherNatural

theorem linearNatural_irreducible (F : BinaryField) {d : ℕ} (hd : 2 ≤ d) :
    IsIrreducible (linearNatural F d) := by
  classical
  let : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  have hs : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.toSubmodule_injective h)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra! h
    exact hv0 (funext h)
  have hm (i : Fin d) (hik : i ≠ k) (a : F.Carrier) : Pi.single i a ∈ S := by
    have h := S.toSubmodule.sub_mem (S.apply_mem_toSubmodule (transvection hik (a / v k)) hv) hv
    change specialLinearNatural d _ v - v ∈ S at h
    rw [action_transvection, add_sub_cancel_left, div_mul_cancel₀ _ hk] at h
    exact h
  have hall (i : Fin d) (a : F.Carrier) : Pi.single i a ∈ S := by
    by_cases hik : i = k
    · subst i
      obtain ⟨j, hj⟩ := exists_ne k
      have h := S.toSubmodule.sub_mem
        (S.apply_mem_toSubmodule (transvection hj.symm a) (hm j hj 1)) (hm j hj 1)
      change specialLinearNatural d _ (Pi.single j 1) - Pi.single j 1 ∈ S at h
      simpa only [action_transvection, Pi.single_eq_same, mul_one, add_sub_cancel_left] using h
    · exact hm i hik a
  apply top_unique
  intro v _
  have h := S.toSubmodule.sum_mem (fun i (_ : i ∈ Finset.univ) => hall i (v i))
  change v ∈ S.toSubmodule
  simpa only [Finset.univ_sum_single] using h

theorem linearNatural_invariants (F : BinaryField) {d : ℕ} (hd : 2 ≤ d) :
    (linearNatural F d).invariants = ⊥ := by
  classical
  let : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  apply bot_unique
  intro v hv
  change v = 0
  ext j
  obtain ⟨i, hij⟩ := exists_ne j
  have h := hv (transvection hij (1 : F.Carrier))
  change specialLinearNatural d _ v = v at h
  rw [action_transvection] at h
  have hz : (Pi.single i (v j) : Fin d → F.Carrier) = 0 := by
    simpa only [one_mul] using (add_eq_left.mp h)
  simpa only [Pi.single_eq_same, Pi.zero_apply] using congrFun hz i

theorem invariants_of_equiv (e : ActionEquiv ρ σ) (hσ : σ.invariants = ⊥) :
    ρ.invariants = ⊥ := by
  apply bot_unique
  intro v hv
  apply e.linearEquiv.injective
  rw [map_zero]
  apply (Submodule.mem_bot (ZMod 2)).mp
  rw [← hσ]
  intro h
  obtain ⟨g, rfl⟩ := e.groupEquiv.surjective h
  rw [← e.intertwines, hv g]

theorem repeated_invariants (r : ℕ) (hσ : σ.invariants = ⊥) :
    (repeated σ r).invariants = ⊥ := by
  apply bot_unique
  intro v hv
  change v = 0
  ext i
  apply (Submodule.mem_bot (ZMod 2)).mp
  rw [← hσ]
  intro g
  exact congrFun (hv g) i

noncomputable def movedQuotientEquiv {L : Subgroup G} (s : MovedSection ρ L)
    (h : Representation.invariants (s.space.toRepresentation.comp L.subtype) = ⊥) :
    ActionEquiv (s.action.comp L.subtype) (s.space.toRepresentation.comp L.subtype) where
  groupEquiv := MulEquiv.refl L
  linearEquiv := s.central.toSubmodule.quotEquivOfEqBot (s.central_eq.trans h)
  intertwines g v := by
    induction v using Submodule.Quotient.induction_on with | _ v =>
    rfl

theorem homogeneous_moved_quotient {L : Subgroup G} (s : MovedSection ρ L)
    (F : BinaryField) {d r : ℕ} (hd : 2 ≤ d) (hr : 0 < r)
    (e : ActionEquiv (s.space.toRepresentation.comp L.subtype)
      (repeated (linearNatural F d) r)) :
    IsHomogeneousAction (s.action.comp L.subtype) := by
  have hz := invariants_of_equiv e (repeated_invariants r (linearNatural_invariants F hd))
  let q := movedQuotientEquiv s hz
  let e' : ActionEquiv (s.action.comp L.subtype) (repeated (linearNatural F d) r) :=
    ⟨q.groupEquiv.trans e.groupEquiv, q.linearEquiv.trans e.linearEquiv,
      fun g v => (congrArg e.linearEquiv (q.intertwines g v)).trans
        (e.intertwines (q.groupEquiv g) (q.linearEquiv v))⟩
  exact homogeneous_of_repeated hr e' (linearNatural_irreducible F hd)

theorem clause_three {L : Subgroup G} (s : MovedSection ρ L)
    (h : QuasisimpleActionCase ρ L s) :
    IsHomogeneousAction (s.action.comp L.subtype) ∨
      ∃ d, (d = 4 ∨ d = 5) ∧
        IsNaturalPlusDual (s.space.toRepresentation.comp L.subtype) d := by
  cases h with
  | irreducible _ _ hi _ _ => exact Or.inl (homogeneous_of_irreducible hi)
  | doubleThree F _ e _ _ => exact Or.inl (homogeneous_moved_quotient s F (by decide) (by decide) e)
  | naturalDual d hd _ hn => exact Or.inr ⟨d, hd, hn⟩
  | repeatedNatural d r hd hr _ _ hn =>
    obtain ⟨e⟩ := hn
    exact Or.inl (homogeneous_moved_quotient s BinaryField.two (by rcases hd with rfl | rfl <;> decide) hr e)
end ExtensionConsequences
end CFSG.Quasithin.ChapterB.QuasisimpleSource
