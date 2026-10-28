module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.InitialSieve.ModelInterface
public import Theory.SpecificGroups.AlternatingSix.OuterSolvable
public import Theory.SpecificGroups.Alternating.SevenComponent
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The alternating exclusions in the initial component sieve

The residual O²(C_L(v)) has no nontrivial two-group quotient. For the
actual A₆ and A₇ models the outer automorphism group is a two-group,
so the residual acts through the inner subgroup, without assuming that
Tᵥ normalizes K. The central supplement then makes z inner, contradicting
the odd permutation prescribed in 1.1.5(3)(c,d). The triple covers are
excluded separately: their order-three centers cannot be two-cores when
the ambient odd core is trivial.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.1.5(3)(c,d), printed pp.501–503; proof of 13.6.6, printed pp.926–927.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
open A5Module

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- The source residual remains two-perfect in its actual local embedding. -/
theorem residual_two_perfect (s : Marking L V) : IsPPerfect 2 (residual s) := by
  let e : residual s ≃* Lv L (markedV s) := subgroupOfEquivOfLe (Lv_le_Gv L (markedV s))
  exact (isPPerfect_embedded_pResidual 2 (L ⊓ Gv (markedV s))).of_surjective
    e.symm.toMonoidHom e.symm.surjective

/-- A two-group outer quotient forces the literal residual image into K*. -/
theorem residual_inner (s : Marking L V) (K : Subgroup (Gv (markedV s)))
    (hn : residual s ≤ X K) (ho : IsPGroup 2 (MulAut.Outer K)) :
    ((residual s).subgroupOf (X K)).map (NormalizerAction.quotient K) ≤
      NormalizerAction.componentImage K := by
  let f : residual s →* MulAut.Outer K :=
    (QuotientGroup.mk' (MulAut.innerSubgroup K)).comp
      (K.normalizerMonoidHom.comp (inclusion hn))
  have hp : IsPGroup 2 ((residual s) ⧸ f.ker) :=
    (ho.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hf := residual_two_perfect s f.ker inferInstance hp
  rintro _ ⟨x, hx, rfl⟩
  apply (NormalizerAction.action_mem_inner_iff K _).mp
  rw [NormalizerAction.action_quotient]
  apply (QuotientGroup.eq_one_iff _).mp
  exact MonoidHom.mem_ker.mp (show (⟨x, hx⟩ : residual s) ∈ f.ker by rw [hf]; trivial)

private theorem not_three_center {D : Type*} [Group D]
    (hcenter : center D = pCore 2 D)
    (he : Nonempty (center D ≃* Multiplicative (ZMod 3))) : False := by
  obtain ⟨e⟩ := he
  have hc : Nat.card (pCore 2 D) = 3 := by
    rw [← hcenter, Nat.card_congr e.toEquiv]
    simp
  rcases (pCore_isPGroup (p := 2) (G := D)).card_eq_or_dvd with h | h <;>
    rw [hc] at h <;> norm_num at h

private theorem odd_action_not_inner {D : Type*} [Group D] {n : ℕ}
    (hn : 4 ≤ n) {α : MulAut D} (σ : Equiv.Perm (Fin n))
    (hs : Equiv.Perm.sign σ = -1)
    (e : D ≃* alternatingGroup (Fin n))
    (ha : ∀ x : D, (e (α x) : Equiv.Perm (Fin n)) = σ * e x * σ⁻¹) :
    α ∉ MulAut.innerSubgroup D := by
  rintro ⟨g, hg⟩
  have he : MulAut.conjNormal (H := alternatingGroup (Fin n)) σ =
      MulAut.conjNormal (H := alternatingGroup (Fin n)) (e g) := by
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    apply Subtype.ext
    change σ * (e y : Equiv.Perm (Fin n)) * σ⁻¹ =
      (e g : Equiv.Perm (Fin n)) * e y * (e g : Equiv.Perm (Fin n))⁻¹
    simpa only [← hg, MulAut.conj_apply, map_mul, map_inv, coe_mul, coe_inv] using (ha y).symm
  have heq := GroupTheory.AutAlternating.conjNormal_injective_alternatingGroup n hn he
  have hsg : Equiv.Perm.sign (e g : Equiv.Perm (Fin n)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp (e g).property
  rw [← heq, hs] at hsg
  norm_num at hsg

/-- Exclude an odd alternating action, including the genuine triple cover. -/
theorem no_alternating {κ : CFSG.Quasithin.GroupClass} {T : Sylow 2 G} {s : Marking L V}
    (d : Setup κ T s) (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K) {n : ℕ} (hn : n = 6 ∨ n = 7)
    (σ : Equiv.Perm (Fin n)) (hs : Equiv.Perm.sign σ = -1) :
    ¬ AlternatingAction (K.normalizerMonoidHom ⟨zLocal s, a.z_normalizes⟩) n σ := by
  let : IsQuasisimple K := hK.2
  have hc := IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot hodd K)
  rintro (⟨e, he⟩ | ⟨_, he, _⟩)
  · have ho : IsPGroup 2 (MulAut.Outer K) := by
      apply IsPGroup.of_equiv (G := MulAut.Outer (alternatingGroup (Fin n))) _
        (MulAut.outerCongr e).symm
      rcases hn with rfl | rfl
      · exact IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card
      · exact alternatingGroup.SevenComponent.outer_two
    have hi := z_inner_of_residual_inner s K a.z_normalizes a.residual_normalizes
      (z_mem_central_supplement s d.V_le_L) (residual_inner s K a.residual_normalizes ho)
    exact odd_action_not_inner (by rcases hn with rfl | rfl <;> decide) σ hs e he hi
  · exact not_three_center hc he


variable {κ : CFSG.Quasithin.GroupClass} {T : Sylow 2 G} {s : Marking L V}

/-- Source alternative (c) is impossible, including the triple cover of A₆. -/
theorem not_six (d : Setup κ T s) (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K) (σ : Equiv.Perm (Fin 6)) (hs : σ.IsSwap) :
    ¬ AlternatingAction (K.normalizerMonoidHom ⟨zLocal s, a.z_normalizes⟩) 6 σ :=
  no_alternating d K hK hodd a (Or.inl rfl) σ hs.sign_eq

/-- Source alternative (d) is impossible, including the triple cover of A₇. -/
theorem not_seven (d : Setup κ T s) (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K) (σ : Equiv.Perm (Fin 7))
    (hs : σ.cycleType = {2, 2, 2}) :
    ¬ AlternatingAction (K.normalizerMonoidHom ⟨zLocal s, a.z_normalizes⟩) 7 σ := by
  apply no_alternating d K hK hodd a (Or.inr rfl) σ
  rw [Equiv.Perm.sign_of_cycleType, hs]
  norm_num

/-- In every surviving clause of the full source alternative, z is inner. -/
theorem z_inner_of_model_action (d : Setup κ T s) (K : Subgroup (Gv (markedV s)))
    (hK : IsComponent (Gv (markedV s)) K) (hodd : pPrimeCore 2 (Gv (markedV s)) = ⊥)
    (a : ActionData s (T : Subgroup G) K)
    (hm : ModelAction115 K (K.normalizerMonoidHom ⟨zLocal s, a.z_normalizes⟩)) :
    K.normalizerMonoidHom ⟨zLocal s, a.z_normalizes⟩ ∈ MulAut.innerSubgroup K := by
  cases hm with
  | lie _ _ hi => exact hi
  | two_cover _ _ _ hi => exact hi
  | six σ hs ha => exact (not_six d K hK hodd a σ hs ha).elim
  | seven σ hs ha => exact (not_seven d K hK hodd a σ hs ha).elim
  | odd _ hi => exact hi
  | sporadic _ _ _ ha => exact ha.1

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.InitialSieve.ModelExclusions
