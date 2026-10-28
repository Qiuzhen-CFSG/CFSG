module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Highest
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility
public import Theory.Representation.BinaryOffender.InnerNormalizerActors
public import Theory.GroupTheory.AutomorphismOvergroupCore

/-!
# Conditional Levi displacement from the four-dimensional estimate

A nonempty restricted support makes the marked SL₄ action nontrivial, hence
faithful by simplicity. An elementary cubic actor in the literal parabolic
quotient embeds in the full linear normalizer with the same action, rank and
fixed codimension. The four-dimensional displacement premise therefore gives
the required strict inequality on the radical fixed space.

The binary Smith–Timmesfeld theorem supplies fixed-space irreducibility directly
over F₂. Thus `quotient_estimate_of_four` retains only the original faithful
irreducibility hypotheses and `FourDisplacementInput`; the latter remains the
independent SL₄ displacement input to be discharged by the end-node assembly.

Source: Guralnick–Malle, Classification of 2F-modules II, Theorem 3.1 and
Proposition 4.7(2); Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

namespace Levi

/-- An active root on a nonzero vector makes the marked SL₄ action faithful. -/
theorem action_injective_of_support (e : Fin 2) {J : Finset (Fin 4)} {v : V}
    (hv : v ≠ 0) (h : SL5TenDimensional.Classification.LocalHighestVector σ J v)
    (hJ : (restrictedSupport e J).Nonempty) : Function.Injective (action σ e) := by
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup FourSmallModules.Group := (Atlas.Order20160A8.sl4TwoEquivPSL.trans
    Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).isSimpleGroup
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (inferInstance : (action σ e).ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact hk
  · obtain ⟨i, hi⟩ := hJ
    have hmove := (localHighestVector_restrict σ e h).swap_ne_self
      (by intro hz; exact hv (congrArg Subtype.val hz)) hi
    have hone : action σ e (FourSmallModules.simpleSwap i) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [hk]
      trivial
    exact False.elim (hmove (by rw [hone]; rfl))

/-- The intrinsic SL₄ two-rank bound used for quotient actors. -/
theorem four_primeRank_le : primeRank 2 FourSmallModules.Group ≤ 4 := by
  have h := Theory.GroupTheory.primeRank_le_of_injective 2
    (MulAut.conj : FourSmallModules.Group →* MulAut FourSmallModules.Group)
    (Theory.GroupTheory.conj_injective_of_center_eq_bot Atlas.Order20160A8.binary_sl_center)
  have hb : primeRank 2 (MulAut FourSmallModules.Group) ≤ 4 := by
    rw [Theory.GroupTheory.primeRank_equiv 2 (MulAut.congr Atlas.Order20160A8.sl4TwoEquivPSL)]
    exact BinaryLinear.AutomorphismTwoRank.psl4_two_rank_le
  exact h.trans hb

/-- Apply the four-dimensional displacement contract to an actor in the literal quotient. -/
theorem quotient_actor_estimate [FiniteDimensional (ZMod 2) V]
    (hfour : FourDisplacementInput σ) (e : Fin 2)
    (hi : IsIrreducible (action σ e)) {J : Finset (Fin 4)} {v : V}
    (hv : v ≠ 0) (h : SL5TenDimensional.Classification.LocalHighestVector σ J v)
    (hJ : 2 ≤ (restrictedSupport e J).card)
    (A : Subgroup (parabolic e ⧸ radical e))
    (hA : IsElementaryTwo A) (hc : IsCubic (quotientRepresentation σ e) A) :
    2 * rank A < fixedCodim (quotientRepresentation σ e) A := by
  have hf := action_injective_of_support σ e hv h
    (Finset.card_pos.mp (by omega))
  let τ := action σ e
  let f := (normalizerEmbedding τ).comp (quotientEquiv e).toMonoidHom
  have hfi : Function.Injective f :=
    (normalizerEmbedding_injective τ hf).comp (quotientEquiv e).injective
  have he (g : parabolic e ⧸ radical e) (w : FixedSpace σ e) :
      (LinearEquiv.refl (ZMod 2) (FixedSpace σ e)) (quotientRepresentation σ e g w) =
      normalizerRepresentation τ (f g) ((LinearEquiv.refl (ZMod 2) (FixedSpace σ e)) w) := by
    change quotientRepresentation σ e g w = action σ e (quotientEquiv e g) w
    rw [action_quotientEquiv]
  let : IsElementaryAbelian 2 A := hA.2
  have hAf : IsElementaryTwo (A.map f) := by
    refine ⟨?_, IsElementaryAbelian.map f⟩
    intro hbot
    exact hA.1 (Subgroup.map_injective hfi (by simpa only [Subgroup.map_bot] using hbot))
  have hcf := Exceptional.cubic_map_equivariant (quotientRepresentation σ e)
    (normalizerRepresentation τ) f (LinearEquiv.refl (ZMod 2) (FixedSpace σ e)) he hc
  have hr : rank A ≤ 4 := by
    have hp : primeRank 2 (parabolic e ⧸ radical e) ≤ 4 := by
      rw [Theory.GroupTheory.primeRank_equiv 2 (quotientEquiv e)]
      exact four_primeRank_le
    have hn := (primeRank_le_iff_elementary_card_le _).mp hp A hA.2
    have hl := Nat.log_mono_right (b := 2) hn
    simpa only [rank, Nat.log_pow (by decide : 1 < 2)] using hl
  have hd := hfour e τ hf hi (restrictedSupport e J)
    ⟨v, mem_fixedSpace_of_upperFixed σ e h.upper_fixed⟩
    (by intro hz; exact hv (congrArg Subtype.val hz))
    (localHighestVector_restrict σ e h) hJ (A.map f) hAf hcf
    (by rwa [rank_map_injective f hfi])
  rwa [rank_map_injective f hfi,
    ← fixedCodim_map_equivariant (quotientRepresentation σ e)
      (normalizerRepresentation τ) f (LinearEquiv.refl (ZMod 2) (FixedSpace σ e)) he] at hd

end Levi

/-- Assembly from fixed-space irreducibility, also available independently of
irreducibility of the ambient representation. -/
theorem quotient_estimate_of_four_of_fixedSpace_irreducible [FiniteDimensional (ZMod 2) V]
    (hfour : FourDisplacementInput σ) (hi : ∀ e : Fin 2, IsIrreducible (Levi.action σ e)) :
    QuotientEstimate σ := by
  intro e J v hv h hJ A hA hc
  exact Levi.quotient_actor_estimate σ hfour e (hi e) hv h hJ A hA hc

/-- The end-parabolic quotient estimate for a faithful irreducible binary SL₅
module, conditional only on SL₄ displacement on its two radical fixed spaces.
The binary Smith–Timmesfeld theorem discharges the fixed-space irreducibility
premise, while an active restricted root supplies the faithful SL₄ action. -/
theorem quotient_estimate_of_four [FiniteDimensional (ZMod 2) V]
    (_hf : Function.Injective σ) (hi : IsIrreducible σ)
    (hfour : FourDisplacementInput σ) : QuotientEstimate σ := by
  let : IsIrreducible σ := hi
  exact quotient_estimate_of_four_of_fixedSpace_irreducible σ hfour
    (Levi.action_irreducible σ)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
