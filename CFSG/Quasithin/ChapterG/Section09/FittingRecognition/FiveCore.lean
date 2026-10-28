module

public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Models
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.FiveCore.Contracts
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.FiveCore.Reduction

/-!
# Assembly of the noncubic Fitting branch

The original Fitting hypothesis supplies every premise of G.9.2 and makes
the ambient five-core nontrivial. Its fixed space vanishes by irreducibility.
Fixing the ordinary factor spaces therefore forces degree four, while the
G.9.2 equality forces actor rank one. The GL₄(2) order calculation gives a
normal core of order five.

The faithful representation identifies G with its actual linear image.
Transporting the core, the actor, and its normal closure through this
isomorphism applies the independent linear normalizer calculation to the
literal normal closure required by G.9.4(2).

The theorem below remains conditional on the two published linear
calculations. It is not the completed source branch until these are proved.
Source: Aschbacher--Smith, G.9.4, printed pp.354--355, PDF pp.365--366.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition

open Subgroup NilpotentRigidity

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {m : ℕ}

/-- Apply the concrete linear normalizer theorem through the faithful
representation, preserving the normal closure of the given actor. -/
theorem FiveCore.normalClosure_dihedral_of_linearNormalizer
    (h : Setup ρ A m) (hm : 0 < m)
    (hcard : Nat.card (pCore 5 G) = 5)
    (normalizer : FiveCore.LinearNormalizerRecognition V) :
    Nonempty (Subgroup.normalClosure (A : Set G) ≃* DihedralGroup 5) := by
  let L := ρ.toHomUnits.range
  have hi : Function.Injective ρ.toHomUnits := by
    intro g k he
    exact h.faithful (congrArg Units.val he)
  let e : G ≃* L := MonoidHom.ofInjective hi
  let X := (pCore 5 G).map e.toMonoidHom
  let E := A.map e.toMonoidHom
  have hXn : X.Normal := (pCore_normal (p := 5) (G := G)).map e.toMonoidHom e.surjective
  have hXc : Nat.card X = 5 := by
    exact (Subgroup.card_map_of_injective (K := pCore 5 G)
      (f := e.toMonoidHom) e.injective).trans hcard
  let : IsElementaryAbelian 2 A := h.elementary
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.map e.toMonoidHom
  have hEne : E ≠ ⊥ := by
    intro he
    have hAb := (A.map_eq_bot_iff_of_injective e.injective).mp he
    exact (Nat.ne_of_gt hm) (h.actor_eq_bot_iff.mp hAb)
  obtain ⟨f⟩ := normalizer L X E hXn hXc hE hEne
  have hclosure : (Subgroup.normalClosure (A : Set G)).map e.toMonoidHom =
      Subgroup.normalClosure (E : Set L) := by
    exact Subgroup.map_normalClosure (A : Set G) e.toMonoidHom e.surjective
  exact ⟨((MulEquiv.subgroupMap e (Subgroup.normalClosure (A : Set G))).trans
    (MulEquiv.subgroupCongr hclosure)).trans f⟩

/-- Conditional assembly of G.9.4(2). The two outstanding premises are
independent module/normalizer lemmas, not recognition fields of the input. -/
theorem caseTwo_of_fiveCore_inputs (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (rigidity : NilpotentRigidityInput ρ)
    (hn : ¬ IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G))
    (ordinary : FiveCore.OrdinaryFactorsFixed ρ A)
    (normalizer : Module.finrank (ZMod 2) V = 4 →
      FiveCore.LinearNormalizerRecognition V) : CaseTwo ρ A m := by
  have hne := FiveCore.fiveCore_ne_bot h rigidity hn
  obtain ⟨H, _, hHF, ⟨d⟩⟩ := FiveCore.decomposition h rigidity hn
  have hd := FiveCore.degree_four_of_ordinary_fixed h hne d (ordinary H hHF d)
  have he := (FiveCore.nilpotentConclusion h rigidity hn).degree_noncentral
    (FiveCore.residual_noncentral hn)
  have hmone : m = 1 := by omega
  exact ⟨hmone, hd, FiveCore.normalClosure_dihedral_of_linearNormalizer h.toSetup hm
    (FiveCore.fiveCore_card h.faithful hd hne) (normalizer hd)⟩

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
