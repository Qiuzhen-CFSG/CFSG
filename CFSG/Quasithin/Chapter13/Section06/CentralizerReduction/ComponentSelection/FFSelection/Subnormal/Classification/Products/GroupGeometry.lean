module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products.Contracts
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products.GroupGeometry.ModelCores
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products.GroupGeometry.SmallProducts
/-!
# Group geometry of the two B.5.6 product alternatives

The three-cores of the listed factors and the Sylow-normalized cubic-axis
argument give normality and placement in an actual S₃ factor. Transport
through the supplied internal product retains both original inclusions.
The same two axes catalogue every normal cubic. In the hyperplane case,
the first SL₃(2) factor has trivial three-core, so only the second factor
can contain the selected cubic.

No module dimension or cubic normality is assumed here. The independent
section comparisons are used only in GroupGeometry.Application.

Source: Aschbacher–Smith, B.5.6(3),(5), printed p.105, and 13.6.10, p.928.
-/

@[expose] public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification.Products
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open GroupGeometry
variable {E : Type*} [Group E] [Finite E]

private theorem internal_position {F₁ F₂ : Subgroup E} (hp : InternalProduct F₁ F₂)
    (h₁ : Nonempty (F₁ ≃* Equiv.Perm (Fin 3)) ∨ pCore 3 F₁ = ⊥)
    (h₂ : Nonempty (F₂ ≃* Equiv.Perm (Fin 3)) ∨ pCore 3 F₂ = ⊥) :
    CubicFactorPosition F₁ F₂ := by
  intro B R hs hc hR
  let f := hp.equiv.symm
  let B' := B.map f.toMonoidHom
  let R' := R.mapSurjective (f := f.toMonoidHom) f.surjective
  have hc' : Nat.card B' = 3 := (card_map_of_injective f.injective).trans hc
  have hR' : (R' : Subgroup (F₁ × F₂)) ≤ normalizer (B' : Set (F₁ × F₂)) := by
    change (R.map f.toMonoidHom : Subgroup _) ≤ _
    rw [← B.map_equiv_normalizer_eq f]
    exact map_mono hR
  obtain ⟨hn, ha⟩ := product_cubic_position h₁ h₂ B' R' (hs.map f.surjective) hc' hR'
  have hnB : B.Normal := by
    simpa only [B', comap_map_eq_self_of_injective (f := f.toMonoidHom) f.injective]
      using hn.comap f.toMonoidHom
  refine ⟨hnB, ?_⟩
  rcases ha with ⟨he, hm⟩ | ⟨he, hm⟩
  · refine Or.inl ⟨?_, hm⟩
    intro b hb
    have hx : f b ∈ (pCore 3 F₁).prod (⊥ : Subgroup F₂) :=
      he ▸ mem_map_of_mem f.toMonoidHom hb
    have heq : b = ((f b).1 : E) := by
      calc
        b = hp.equiv (f b) := (hp.equiv.apply_symm_apply b).symm
        _ = ((f b).1 : E) * ((f b).2 : E) := hp.apply_eq _ _
        _ = ((f b).1 : E) := by rw [show (f b).2 = 1 from hx.2]; simp
    rw [heq]
    exact (f b).1.property
  · refine Or.inr ⟨?_, hm⟩
    intro b hb
    have hx : f b ∈ (⊥ : Subgroup F₁).prod (pCore 3 F₂) :=
      he ▸ mem_map_of_mem f.toMonoidHom hb
    have heq : b = ((f b).2 : E) := by
      calc
        b = hp.equiv (f b) := (hp.equiv.apply_symm_apply b).symm
        _ = ((f b).1 : E) * ((f b).2 : E) := hp.apply_eq _ _
        _ = ((f b).2 : E) := by rw [show (f b).1 = 1 from hx.1]; simp
    rw [heq]
    exact (f b).2.property

private theorem internal_catalogue {F₁ F₂ : Subgroup E} (hp : InternalProduct F₁ F₂)
    (h₁ : Nonempty (F₁ ≃* Equiv.Perm (Fin 3)) ∨ pCore 3 F₁ = ⊥)
    (h₂ : Nonempty (F₂ ≃* Equiv.Perm (Fin 3)) ∨ pCore 3 F₂ = ⊥) :
    NormalCubicCatalogue E := by
  refine ⟨((pCore 3 F₁).prod ⊥).comap hp.equiv.symm.toMonoidHom,
    ((⊥ : Subgroup F₁).prod (pCore 3 F₂)).comap hp.equiv.symm.toMonoidHom, ?_⟩
  intro B hn hc
  let f := hp.equiv.symm
  have hc' : Nat.card (B.map f.toMonoidHom) = 3 :=
    (card_map_of_injective f.injective).trans hc
  have ha := product_normal_catalogue h₁ h₂ (B.map f.toMonoidHom)
    (hn.map f.toMonoidHom f.surjective) hc'
  have hi := comap_map_eq_self_of_injective (f := f.toMonoidHom) f.injective B
  rcases ha with he | he
  · exact Or.inl (hi.symm.trans (congrArg (comap f.toMonoidHom) he))
  · exact Or.inr (hi.symm.trans (congrArg (comap f.toMonoidHom) he))

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) E W)

/-- B.5.6(3) gives normality and placement in an actual S₃ factor. -/
theorem twoFactors_cubic_position (hc : SourceTwoFactorCase σ) :
    CubicFactorPosition hc.first hc.second :=
  internal_position hc.product (factor_threeCore (hc.firstCase.factorModel σ))
    (factor_threeCore (hc.secondCase.factorModel σ))

/-- B.5.6(3) supplies a two-entry catalogue of all normal cubics. -/
theorem twoFactors_normal_catalogue (hc : SourceTwoFactorCase σ) : NormalCubicCatalogue E :=
  internal_catalogue hc.product (factor_threeCore (hc.firstCase.factorModel σ))
    (factor_threeCore (hc.secondCase.factorModel σ))

omit [Finite E] in
private theorem hyperplane_first_core (hc : HyperplaneCase σ) : pCore 3 hc.first = ⊥ := by
  apply (map_eq_bot_iff_of_injective (f := hc.firstEquiv.toMonoidHom) _ hc.firstEquiv.injective).mp
  rw [pCore_map_iso, binary_sl3_threeCore]

/-- B.5.6(5) excludes the SL₃(2) factor and selects the actual second factor. -/
theorem hyperplane_cubic_position (hc : HyperplaneCase σ)
    (B : Subgroup E) (R : Sylow 2 E) (hs : B.IsSubnormal) (hb : Nat.card B = 3)
    (hR : (R : Subgroup E) ≤ normalizer (B : Set E)) :
    B.Normal ∧ B ≤ hc.second ∧ Nonempty (hc.second ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨hn, hp⟩ := internal_position hc.product (Or.inr (hyperplane_first_core σ hc))
    (factor_threeCore (hc.secondCase.factorModel σ)) B R hs hb hR
  refine ⟨hn, ?_⟩
  rcases hp with ⟨_, ⟨e⟩⟩ | hp
  · have hh := symmetricThree_threeCore_card e
    rw [hyperplane_first_core σ hc, card_bot] at hh
    omega
  · exact hp

/-- B.5.6(5) supplies the normal cubic catalogue without any module bound. -/
theorem hyperplane_normal_catalogue (hc : HyperplaneCase σ) : NormalCubicCatalogue E :=
  internal_catalogue hc.product (Or.inr (hyperplane_first_core σ hc))
    (factor_threeCore (hc.secondCase.factorModel σ))
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification.Products
