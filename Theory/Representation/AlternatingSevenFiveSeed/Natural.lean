module
public import Theory.Representation.AlternatingSevenFiveRestriction
public import Theory.Representation.AlternatingSevenFiveRestriction.PermutationObstruction
public import Theory.Representation.SL2FourProjectiveRecognition.Copies
public import Theory.Representation.SL2FourNaturalOrbits.ElementaryActors

/-!
# The natural four-space on a Sylow-normalized A₅ in A₇

The Sylow four-group of the actual A₅ acts quadratically. Its fixed plane
and its Weyl conjugate are complementary: a vector in their intersection
is fixed by a three-cycle, hence is zero. The upper-root coordinates then
identify the whole four-space with the natural SL₂(4) module.

Source: Aschbacher–Smith C.1.24 and C.5.13; the root-pair coordinate
recognition is the field-four case of G.1.3 and G.1.7.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.AlternatingSevenFiveSeed
open SL2FourNatural SL2FourNatural.ProjectiveRecognition
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
  [FiniteDimensional (ZMod 2) M]

private theorem root_pair
    (σ : Representation (ZMod 2) SL M)
    (hd : Module.finrank (ZMod 2) M = 4)
    (hq : IsQuadratic σ BorelFactors.U0)
    (hr : fixedCodim σ (zpowers (upper 1)) = 2)
    (hc : ∀ (c : SL), orderOf c = 3 → ∀ x, σ c x = x → x = 0) :
    RootPair σ weyl (fixedSpace σ BorelFactors.U0) := by
  let A := fixedSpace σ BorelFactors.U0
  have hu (t : F) : upper t ∈ BorelFactors.U0 :=
    (BorelFactors.mem_U0 _).mpr ⟨t, rfl⟩
  have hm (t : F) (x : M) : σ (upper t) x - x ∈ A := by
    intro a
    exact hq a a.property (upper t) (hu t) x
  have hA : Module.finrank (ZMod 2) A = 2 := by
    have hlo : LinearMap.range (σ (upper 1) - LinearMap.id) ≤ A := by
      rintro _ ⟨x, rfl⟩
      exact hm 1 x
    have hup : A ≤ fixedSpace σ (zpowers (upper 1)) :=
      fixedSpace_antitone σ (zpowers_le.mpr (hu 1))
    have hl := Submodule.finrank_mono hlo
    have hh := Submodule.finrank_mono hup
    have he := fixedCodim_add_finrank σ (zpowers (upper 1))
    rw [← fixedCodim_zpowers_eq_displacement_rank, hr] at hl
    rw [hr, hd] at he
    omega
  have hw : Function.Injective (σ weyl) := by
    intro x y he
    simpa only [σ.inv_self_apply] using congrArg (σ weyl⁻¹) he
  have hD : Module.finrank (ZMod 2) (A.map (σ weyl)) = 2 :=
    (A.equivMapOfInjective (σ weyl) hw).finrank_eq.symm.trans hA
  have hdis : Disjoint A (A.map (σ weyl)) := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx.2
    have hx1 : σ (upper 1) (σ weyl y) = σ weyl y := hx.1 ⟨upper 1, hu 1⟩
    have hy1 : σ (upper 1) y = y := hy ⟨upper 1, hu 1⟩
    have hw2 (v : M) : σ weyl (σ weyl v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, weyl_mul_self, map_one]
      rfl
    have ho : orderOf (upper 1 * weyl * upper 1 * weyl) = 3 :=
      orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    exact hc _ ho _ (by
      simp only [map_mul, Module.End.mul_apply, hw2, hy1, hx1])
  have hsup : A ⊔ A.map (σ weyl) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have he := Submodule.finrank_sup_add_finrank_inf_eq A (A.map (σ weyl))
    rw [hdis.eq_bot, finrank_bot, add_zero, hA, hD] at he
    omega
  exact ⟨⟨hdis, codisjoint_iff.mpr hsup⟩,
    fun t x hx => hx ⟨upper t, hu t⟩, hm⟩

private theorem natural_of_quadratic
    (σ : Representation (ZMod 2) SL M)
    (hd : Module.finrank (ZMod 2) M = 4)
    (hq : IsQuadratic σ BorelFactors.U0)
    (hr : fixedCodim σ (zpowers (upper 1)) = 2)
    (hc : ∀ (c : SL), orderOf c = 3 → ∀ x, σ c x = x → x = 0) :
    ∃ l : M ≃ₗ[ZMod 2] SL2FourNatural.V,
      ∀ g x, l (σ g x) = specialLinearNatural 2 g (l x) := by
  let A := fixedSpace σ BorelFactors.U0
  have hpair := root_pair σ hd hq hr hc
  have hdiag : ∀ x ∈ A, σ diagonalWord x ∈ A := by
    intro x hx a
    obtain ⟨t, ht⟩ := (BorelFactors.mem_U0 a.val).mp a.property
    have he : ∀ t : F, upper t * diagonalWord = diagonalWord * upper (ProjectiveRecognition.omega * t) := by
      decide +kernel
    have hh : σ (upper (ProjectiveRecognition.omega * t)) x = x :=
      hx ⟨_, (BorelFactors.mem_U0 _).mpr ⟨_, rfl⟩⟩
    change σ a.val (σ diagonalWord x) = σ diagonalWord x
    rw [← ht]
    rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply, hh]
  let : Finite M := Module.finite_of_finite (ZMod 2)
  obtain ⟨s, l, hl⟩ := natural_coordinates hpair hdiag
  have hs : s = 1 := by
    have he := l.finrank_eq
    rw [hd, Module.finrank_pi_fintype, finrank_vector] at he
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at he
    omega
  subst s
  refine ⟨l.trans (LinearEquiv.funUnique (Fin 1) (ZMod 2) SL2FourNatural.V), ?_⟩
  intro g x
  exact hl g x 0

/-- Restriction to the actual Sylow-normalized A₅ is the natural SL₂(4)
module, with the original group and vector actions retained. -/
theorem natural_restriction
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 7)) M)
    (hρ : Function.Injective ρ) (hd : Module.finrank (ZMod 2) M = 4)
    (B : Subgroup (alternatingGroup (Fin 7)))
    (e : B ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 (alternatingGroup (Fin 7)))
    (hSN : (S : Subgroup _) ≤ normalizer (B : Set (alternatingGroup (Fin 7)))) :
    ∃ eB : B ≃* SL, ∃ l : M ≃ₗ[ZMod 2] SL2FourNatural.V,
      ∀ (b : B) x, l (ρ b.val x) = specialLinearNatural 2 (eB b) (l x) := by
  let eB : B ≃* SL := e.trans alternatingFiveEquiv.symm
  let f : SL →* alternatingGroup (Fin 7) := B.subtype.comp eB.symm.toMonoidHom
  let σ := ρ.comp f
  have hf : Function.Injective f := Subtype.val_injective.comp eB.symm.injective
  let P : Sylow 2 B := (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2).mapSurjective
    (f := eB.symm.toMonoidHom) eB.symm.surjective
  have hP := AlternatingSevenFiveRestriction.sylow_quadratic ρ hρ hd B e S hSN P
  have hupper (t : F) : f (upper t) ∈ (P : Subgroup B).map B.subtype := by
    refine ⟨eB.symm (upper t), ?_, rfl⟩
    change eB.symm (upper t) ∈
      (Matrix.SpecialLinearGroup.upperUnipotent F).map eB.symm.toMonoidHom
    exact mem_map_of_mem _ ((BorelFactors.mem_U0 _).mpr ⟨t, rfl⟩)
  have hq : IsQuadratic σ BorelFactors.U0 := by
    intro a ha b hb x
    obtain ⟨t, rfl⟩ := (BorelFactors.mem_U0 a).mp ha
    obtain ⟨u, rfl⟩ := (BorelFactors.mem_U0 b).mp hb
    exact hP _ (hupper t) _ (hupper u) x
  have hr : fixedCodim σ (zpowers (upper 1)) = 2 := by
    have ho : orderOf (upper 1) = 2 :=
      orderOf_eq_prime (by decide +kernel) (by decide +kernel)
    have hc := AlternatingSevenConjugatePair.Model.involution_fixedCodim ρ hρ hd
      (f (upper 1)) ((orderOf_injective f hf _).trans ho)
    have he : fixedSpace σ (zpowers (upper 1)) = fixedSpace ρ (zpowers (f (upper 1))) := by
      ext x
      rw [mem_fixedSpace_zpowers_iff, mem_fixedSpace_zpowers_iff]
      rfl
    change Module.finrank (ZMod 2) (M ⧸ fixedSpace σ (zpowers (upper 1))) = 2
    rw [he]
    exact hc
  have hthree : ∀ (c : SL), orderOf c = 3 → ∀ x, σ c x = x → x = 0 := by
    intro c hc x hx
    have hb : orderOf (eB.symm c) = 3 :=
      (orderOf_injective eB.symm.toMonoidHom eB.symm.injective c).trans hc
    have hcycle := Theory.SpecificGroups.Alternating.SevenFivePlacement.isThreeCycle_of_order_three
      B e S hSN (eB.symm c) hb
    exact binaryAlternatingSeven_threeCycle_fixedPointFree ρ hρ hd (f c) hcycle x hx
  obtain ⟨l, hl⟩ := natural_of_quadratic σ hd hq hr hthree
  refine ⟨eB, l, ?_⟩
  intro b x
  have hh := hl (eB b) x
  simpa only [σ, f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    eB.symm_apply_apply, Subgroup.coe_subtype] using hh

end Representation.AlternatingSevenFiveSeed
