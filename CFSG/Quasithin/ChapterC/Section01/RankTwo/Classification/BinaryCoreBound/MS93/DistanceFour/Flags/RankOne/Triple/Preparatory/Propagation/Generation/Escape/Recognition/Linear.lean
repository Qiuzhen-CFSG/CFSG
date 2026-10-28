module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.Models.Dimensions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.CentralAttachments.Basic
public import Theory.Representation.PSL3Two.ElementaryEightAction

/-!
# A transvection forces a split natural moving module

For a faithful binary SL3(2) representation, three conjugate involutions
bound the moving dimension and the fixed-space codimension by three times
the displacement rank. A transvection therefore bounds both by three.
Faithfulness on the moving space excludes dimensions at most two by counting
endomorphisms. The resulting elementary eight-group has actual marked natural
coordinates, whose fixed space vanishes. Rank-nullity supplies the complement.

This proves the representation step of the natural-section inference in
Meierfrankenfeld--Stellmacher (1993), (4.6.8)(2), p.906, with the meaning of
c(U)=1 from p.881. No complete reducibility is assumed.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation.Recognition
open ModuleAlternatives.CentralAttachments
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A faithful binary SL3(2) action containing a transvection has an actual
natural moving submodule complementary to its fixed space. -/
theorem linear_split (ρ : Representation (ZMod 2) SL V) (hf : Function.Injective ρ)
    (t : SL) (ht : t ^ 2 = 1) (hne : t ≠ 1)
    (hsmall : fixedCodim ρ (zpowers t) ≤ 1) :
    ∃ (e : Multiplicative (moving ρ).toSubmodule ≃* Multiplicative (Fin 3 → ZMod 2))
      (marking : SL ≃* SL),
      (∀ g v, (e (Multiplicative.ofAdd ((moving ρ).toRepresentation g v))).toAdd =
        (marking g).val.mulVec (e (Multiplicative.ofAdd v)).toAdd) ∧
      IsCompl (moving ρ).toSubmodule (fixedSpace ρ ⊤) := by
  let D := (moving ρ).toSubmodule
  let σ := (moving ρ).toRepresentation
  have hfD : Function.Injective σ := moving_faithful ρ hf
  have hdim_le : Module.finrank (ZMod 2) D ≤ 3 := by
    have h := ModuleAlternatives.Models.commutator_finrank_le_three_mul ρ t ht hne
    change Module.finrank (ZMod 2) D ≤ _ at h
    omega
  have hdim : Module.finrank (ZMod 2) D = 3 := by
    by_contra hn
    have hd : Module.finrank (ZMod 2) D ≤ 2 := by omega
    let : Finite (Module.End (ZMod 2) D) := Module.finite_of_finite (ZMod 2)
    have hc := Nat.card_le_card_of_injective σ hfD
    rw [Matrix.PSL3Two.card_SL, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, Module.finrank_linearMap] at hc
    have hp : 2 ^ (Module.finrank (ZMod 2) D * Module.finrank (ZMod 2) D) ≤ 2 ^ 4 :=
      Nat.pow_le_pow_right (by decide) (by nlinarith)
    change 168 ≤ 2 ^ (Module.finrank (ZMod 2) D * Module.finrank (ZMod 2) D) at hc
    norm_num at hp
    omega
  let : Finite D := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative D) := ⟨by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro v
    change (2 : ℕ) • v.toAdd = 0
    have hz : (2 : ZMod 2) = 0 := by decide
    calc
      (2 : ℕ) • v.toAdd = (2 : ZMod 2) • v.toAdd :=
        (Nat.cast_smul_eq_nsmul (ZMod 2) 2 v.toAdd).symm
      _ = 0 := by rw [hz, zero_smul]⟩
  let l : SL →* (D ≃ₗ[ZMod 2] D) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) D).toMonoidHom.comp σ.asGroupHom
  let a : SL →* MulAut (Multiplicative D) := {
    toFun g := (l g).toAddEquiv.toMultiplicative
    map_one' := by
      apply MulEquiv.ext
      intro v
      change σ 1 v.toAdd = v.toAdd
      simp
    map_mul' g h := by
      apply MulEquiv.ext
      intro v
      change σ (g*h) v.toAdd = σ g (σ h v.toAdd)
      rw [map_mul]
      rfl }
  have ha : Function.Injective a := by
    intro g h he
    apply hfD
    apply LinearMap.ext
    intro v
    exact congrArg (fun f : MulAut (Multiplicative D) => (f (Multiplicative.ofAdd v)).toAdd) he
  have hc : Nat.card (Multiplicative D) = 8 := by
    change Nat.card D = 8
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]
    decide
  obtain ⟨e, marking, he⟩ := Matrix.PSL3Two.exists_natural_marking (Multiplicative D) hc a ha
  refine ⟨e, marking, he, ?_⟩
  have hfixed : fixedSpace σ ⊤ = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    have hnatural : e (Multiplicative.ofAdd v) = 1 := by
      have hfix : (e (Multiplicative.ofAdd v)).toAdd ∈
          Representation.OneCohomology.fixed (specialLinearNatural (k := ZMod 2) 3) := by
        intro g
        have h := he (marking.symm g) (Multiplicative.ofAdd v)
        have hh : σ (marking.symm g) v = v := hv ⟨marking.symm g, mem_top _⟩
        change (e (Multiplicative.ofAdd (σ (marking.symm g) v))).toAdd = _ at h
        rw [hh, marking.apply_symm_apply] at h
        exact h.symm
      rw [Representation.OneCohomology.SLHigherNatural.fixed_eq_bot (by decide : 2 ≤ 3)] at hfix
      exact hfix
    exact congrArg Multiplicative.toAdd (e.injective (hnatural.trans e.map_one.symm))
  have hdis : Disjoint (fixedSpace ρ ⊤) D :=
    (disjoint_iff_fixedMoving_eq_bot ρ).mpr hfixed
  have hbound : fixedCodim ρ ⊤ ≤ 3 := by
    have h := ModuleAlternatives.Models.fixedCodim_top_le_three_mul ρ t ht hne
    omega
  have hs := Submodule.finrank_sup_add_finrank_inf_eq D (fixedSpace ρ ⊤)
  have hnull := fixedCodim_add_finrank ρ ⊤
  rw [hdis.symm.eq_bot, finrank_bot, add_zero, hdim] at hs
  have htop : D ⊔ fixedSpace ρ ⊤ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hupper := Submodule.finrank_le (D ⊔ fixedSpace ρ ⊤)
    omega
  exact ⟨hdis.symm, codisjoint_iff.mpr htop⟩
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Propagation.Generation.Recognition
