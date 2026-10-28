module

public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Preparation
public import CFSG.Quasithin.ChapterG.Section08.DihedralProducts.G09Extraction
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DecompositionConsequences
public import Theory.Representation.NonsplitFour
import Mathlib.Tactic

/-!+# The noncubic Fitting reduction in G.9.4

Centralizing the three-residual of the Fitting subgroup would put its
commutator with the actor in the three-core. Thus the noncubic branch makes
G.9.2's conditional sharper bound vacuous. Trivial two-core gives odd order,
so the precise earlier nilpotent-rigidity witness applies. Its residual
conclusions also force the actual ambient five-core to be nontrivial.

If this five-core fixes the ordinary factor spaces, normality and
irreducibility make those spaces zero. The internal decomposition then has
only its distinguished four-dimensional factor. The order of GL₄(2)
subsequently forces the five-core to be cyclic of order five.

Source: Aschbacher--Smith, G.9.4, printed pp.354--355, PDF pp.365--366.
The ordinary-factor action and the five-normalizer calculation are separate
obligations; neither is assumed in the Fitting hypothesis.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition.FiveCore

open Subgroup NilpotentRigidity

universe u v

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {m : ℕ}

/-- The noncubic premise concerns the literal embedded three-residual. -/
theorem residual_noncentral
    (hn : ¬ IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G)) :
    ⁅threeResidual (fittingSubgroup G), A⁆ ≠ ⊥ := by
  intro hc
  let F := fittingSubgroup G
  let S : Sylow 3 F := default
  let P := S.map F.subtype
  let q := QuotientGroup.mk' (pCore 3 G)
  have hP : P ≤ pCore 3 G := S.map_le_pCore inferInstance inferInstance 3
  have hgen : threeResidual F ⊔ P = F := by
    have hs := congrArg (fun J : Subgroup F => J.map F.subtype)
      (pResidual_sup_sylow_eq_top S)
    simpa only [threeResidual, P, Subgroup.map_sup, ← MonoidHom.range_eq_map,
      range_subtype] using hs
  have hPq : P.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff P).mpr
    simpa only [q, QuotientGroup.ker_mk'] using hP
  have hFq : F.map q = (threeResidual F).map q := by
    calc
      F.map q = (threeResidual F ⊔ P).map q := congrArg (Subgroup.map q) hgen.symm
      _ = (threeResidual F).map q := by rw [Subgroup.map_sup, hPq, sup_bot_eq]
  have hcomm : ⁅F, A⁆.map q = ⊥ := by
    rw [map_commutator, hFq, ← map_commutator, hc, Subgroup.map_bot]
  have hle : ⁅F, A⁆ ≤ pCore 3 G := by
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff ⁅F, A⁆).mp hcomm
  exact hn (pCore_isPGroup.to_le hle)

/-- The faithful irreducible binary action gives the odd-order input to G.9.2. -/
theorem fitting_odd (h : FittingHypothesis K ρ A m) :
    Odd (Nat.card (fittingSubgroup G)) := by
  let : Representation.IsIrreducible ρ := h.irreducible
  have hcore := h.toSetup.twoCore_eq_bot
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro hd
  let S : Sylow 2 (fittingSubgroup G) := default
  have hb : S.map (fittingSubgroup G).subtype = ⊥ :=
    bot_unique ((S.map_le_pCore inferInstance inferInstance 2).trans hcore.le)
  have hb' : (S : Subgroup (fittingSubgroup G)) = ⊥ :=
    (map_eq_bot_iff_of_injective _ (fittingSubgroup G).subtype_injective).mp hb
  exact S.ne_bot_of_dvd_card hd hb'

/-- All G.9.2 premises are supplied by the original Fitting hypothesis and
the noncubic branch assumption. -/
theorem nilpotentHypothesis (h : FittingHypothesis K ρ A m)
    (hn : ¬ IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G)) :
    Hypothesis ρ A (fittingSubgroup G) m where
  toSetup := h.toSetup
  nilpotent := inferInstance
  odd_order := fitting_odd h
  normalizes := by rw [Subgroup.normalizer_eq_top]; exact le_top
  faithful_on_X := h.faithful_fitting
  degree_le_of_centralizes hc := (residual_noncentral hn hc).elim

/-- The exact G.9.2 witness, applied to the actual Fitting subgroup. -/
theorem nilpotentConclusion (h : FittingHypothesis K ρ A m)
    (rigidity : NilpotentRigidityInput ρ)
    (hn : ¬ IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G)) :
    NilpotentRigidity.Conclusion ρ A (fittingSubgroup G) m :=
  rigidity A (fittingSubgroup G) m (nilpotentHypothesis h hn)

/-- The distinguished dihedral factor is present, and the internal natural
ordinary factors retain their actual actions. -/
theorem decomposition (h : FittingHypothesis K ρ A m)
    (rigidity : NilpotentRigidityInput ρ)
    (hn : ¬ IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G)) :
    ∃ H : Subgroup G, A ≤ H ∧ H ≤ fittingSubgroup G ⊔ A ∧
      Nonempty (ClassifiedDecomposition ρ H True) := by
  obtain ⟨H, hAH, hHF, ⟨d⟩⟩ := (nilpotentConclusion h rigidity hn).decomposition
  refine ⟨H, hAH, hHF, ⟨{
    count := d.count
    internal := d.internal
    exceptional_factor := fun _ => d.exceptional_factor (residual_noncentral hn)
    ordinary_factor := ?_ }⟩⟩
  intro i hi
  exact d.ordinary_factor i (Or.inr (hi.resolve_left (not_not_intro trivial)))

/-- Nontriviality is established for O₅(G), not merely for a dihedral factor. -/
theorem fiveCore_ne_bot (h : FittingHypothesis K ρ A m)
    (rigidity : NilpotentRigidityInput ρ)
    (hn : ¬ IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G)) :
    pCore 5 G ≠ ⊥ := by
  have hc := ChapterG.Section08.five_core_noncentral_of_residuals A (fittingSubgroup G)
    inferInstance (fitting_odd h) (nilpotentConclusion h rigidity hn).residual_centralizes
    (residual_noncentral hn)
  have hle : (pCore 5 (fittingSubgroup G)).map (fittingSubgroup G).subtype ≤ pCore 5 G :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map _⟩
  intro he
  have hb := bot_unique (hle.trans he.le)
  apply hc
  rw [hb]
  intro a _ x hx
  have hxone : x = 1 := Subgroup.mem_bot.mp hx
  simp [hxone]

/-- A nontrivial normal subgroup has zero fixed space in the faithful
irreducible module. Here it applies to the actual ambient five-core. -/
theorem fiveCore_invariants_eq_bot (h : FittingHypothesis K ρ A m)
    (hne : pCore 5 G ≠ ⊥) :
    Representation.invariants (ρ.comp (pCore 5 G).subtype) = ⊥ := by
  let : Representation.IsIrreducible ρ := h.irreducible
  by_contra hfix
  have hle := Representation.le_ker_of_normal_invariants_ne_bot ρ (pCore 5 G) hfix
  rw [ρ.ker_eq_bot h.faithful] at hle
  exact hne (bot_unique hle)

/-- Once O₅(G) fixes the ordinary summands, the distinguished factor is
the whole module. This is the irreducibility step on printed p.354. -/
theorem degree_four_of_ordinary_fixed (h : FittingHypothesis K ρ A m)
    (hne : pCore 5 G ≠ ⊥) {H : Subgroup G}
    (d : ClassifiedDecomposition ρ H True)
    (hfix : ∀ i : Fin d.count, 0 < i.val →
      movedSpace ρ (d.internal.factor i) ≤
        Representation.invariants (ρ.comp (pCore 5 G).subtype)) :
    Module.finrank (ZMod 2) V = 4 := by
  obtain ⟨hpos, _, hd⟩ := d.exceptional_factor trivial
  rw [d.internal.finrank_eq_sum]
  rw [Finset.sum_eq_single (⟨0, hpos⟩ : Fin d.count)]
  · exact hd
  · intro i _ hi
    have hipos : 0 < i.val := Nat.pos_of_ne_zero (fun he => hi (Fin.ext he))
    have hb : movedSpace ρ (d.internal.factor i) = ⊥ :=
      bot_unique ((hfix i hipos).trans (fiveCore_invariants_eq_bot h hne).le)
    rw [hb]
    exact finrank_bot (ZMod 2) V
  · simp

private theorem matrix_four_card :
    Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ]

/-- The order restriction is proved using the actual faithful representation. -/
theorem fiveCore_card (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 4) (hne : pCore 5 G ≠ ⊥) :
    Nat.card (pCore 5 G) = 5 := by
  have hG := Representation.card_dvd_card_GL_of_injective ρ hf
  rw [hd, matrix_four_card] at hG
  have hc := (pCore 5 G).card_subgroup_dvd_card.trans hG
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 5) (G := G)).exists_card_eq
  have hkpos : 0 < k := by
    by_contra h
    have hz : k = 0 := by omega
    exact hne (Subgroup.card_eq_one.mp (by simpa [hz] using hk))
  have hkle : k ≤ 1 := by
    by_contra h
    have htwo : 2 ≤ k := by omega
    have hbad : 25 ∣ 20160 := (pow_dvd_pow 5 htwo).trans (hk ▸ hc)
    norm_num at hbad
  have he : k = 1 := by omega
  simpa [he] using hk

/-- The cyclic order-five core required by the linear normalizer calculation. -/
theorem fiveCore_cyclic (hf : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 4) (hne : pCore 5 G ≠ ⊥) :
    IsCyclic (pCore 5 G) :=
  isCyclic_of_prime_card (fiveCore_card hf hd hne)

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition.FiveCore
