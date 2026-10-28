module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Basic
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import GorensteinWalter.PSL2Center

/-!
# The center-parity reduction in the fixed-component recognition sieve

For the quasisimple branch of 14.7.68, the nonidentity central involution
makes the component center even. Among the six genuine model/action
alternatives of 1.1.5, this excludes the simple Lie-type case, both
alternating/triple-cover cases, and the odd linear case. The exceptional
two-covers and the sporadic models remain, with their original actions
and their literal two-core quotients retained.

The actual component application uses relative normality to apply 1.1.5.
Its center parity is transported through the subgroup-of equivalence.
The earlier identity U = [U,K] is still explicit; its source producer is
qt-14-07-components (14.7.48(2)). The universal earlier 1.1.5 implication
retains its source owners qt-1-01/qt-1-01-quasisimple-involutions.

Independently, the ambient image of O²(C_{L_u}(z)) is exactly K: monotonicity
places it in O²(H), while two-perfectness gives the reverse containment.
This identifies the actor for the remaining model comparisons.

Neither the exceptional two-cover exclusion nor selection of Ru among
the sporadic alternatives is asserted here. In particular this is not
an even-center recognition theorem, and it does not construct the required
FixedRudvalisCover. Those branches and the final assembly remain open.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
1.1.5(3), printed pp.501--503; 14.7.68(2), printed p.1071 (PDF p.1088).
-/

@[expose] public section
noncomputable section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter15.Section03.Candidates.ComponentStructure

private theorem not_even_center_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : ¬ 2 ∣ Nat.card (center A) := by
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hz]
  simp

private theorem not_alternatingAction_of_even_center {A : Type*} [Group A]
    {α : MulAut A} {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hn : 4 ≤ n) (heven : 2 ∣ Nat.card (center A)) : ¬ AlternatingAction α n σ := by
  rintro (⟨e, _⟩ | ⟨_, ⟨e⟩, _⟩)
  · exact not_even_center_of_equiv e
      (alternatingGroup.center_eq_bot (by simpa using hn)) heven
  · have hc : Nat.card (center A) = 3 := by
      rw [Nat.card_congr e.toEquiv]
      simp
    omega

private theorem not_odd_model_of_even_center {A : Type*} [Group A]
    (heven : 2 ∣ Nat.card (center A)) :
    ¬ (ClassicalGroup.IsPSL A 3 3 ∨
      ∃ p : ℕ, IsFermatOrMersennePrime p ∧ ClassicalGroup.IsPSL A 2 p) := by
  rintro (h | ⟨p, _, h⟩)
  · obtain ⟨k, hk, hf, _, ⟨e⟩⟩ := h
    let : Field k := hk
    let : Finite k := hf
    let : Group.IsPerfect (SL(3,k)) := Atlas.sl_perfect 3 (by decide)
    exact not_even_center_of_equiv e
      (Group.IsPerfect.center_quotient_center_eq_bot (SL(3,k))) heven
  · obtain ⟨k, hk, hf, _, ⟨e⟩⟩ := h
    let : Field k := hk
    let : Finite k := hf
    exact not_even_center_of_equiv e (GorensteinWalter.psl2_center_eq_bot k) heven

/-- The exact two surviving branches after the center-parity argument. -/
theorem modelAction115_of_even_center {A : Type*} [Group A] [Group.IsPerfect A]
    {α : MulAut A} (heven : 2 ∣ Nat.card (center A)) (h : ModelAction115 A α) :
    (center A ≠ ⊥ ∧ center A = pCore 2 A ∧
      (ClassicalGroup.IsPSL (A ⧸ pCore 2 A) 3 4 ∨
        ClassificationModels.IsG2At (A ⧸ pCore 2 A) 4) ∧
      α ∈ (MulAut.conj (G := A)).range) ∨
    (∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* name.Carrier) ∧ TwoCentralInner α) := by
  cases h with
  | lie hs _ _ =>
    let := hs
    have hz := Subgroup.center_eq_bot_of_simple_perfect (G := A)
    exact (not_even_center_of_equiv (MulEquiv.refl A) hz heven).elim
  | two_cover hn hz hm hi => exact Or.inl ⟨hn, hz, hm, hi⟩
  | six σ _ ha => exact (not_alternatingAction_of_even_center (n := 6) (by decide) heven ha).elim
  | seven σ _ ha => exact (not_alternatingAction_of_even_center (n := 7) (by decide) heven ha).elim
  | odd hm _ => exact (not_odd_model_of_even_center heven hm).elim
  | sporadic name hn hm ha => exact Or.inr ⟨name, hn, hm, ha⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Theory.GroupTheory Chapter12.Section08
open Chapter15.Section03.Candidates.ComponentStructure
open ClassificationModels
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
namespace Data
variable (d : Data T L V F W)

/-- The ordinary-component application retains the literal conjugation by z.
The 14.7.48(2) generation premise still has its earlier source owner. -/
theorem fixedComponent_evenModelActions
    (h115 : ∀ (H : Subgroup G) (S : Sylow 2 H) (M : Subgroup G) (z : G),
      Chapter1.Lemma115Hypotheses H S M z →
        ∀ A : Subgroup H, Theory.GroupTheory.IsComponent H A →
          HasModelAction115 A z)
    (hgen : F.U = ⁅F.U, K F⁆)
    (u : F.U) (hne : (u : G) ≠ 1) (hmax : IsMaximalTwoLocal F.H)
    (hsyl : Chapter1.IsSylowIn 2 (d.fixedSylow u) (d.fixedCentralizer u))
    {Lu : Subgroup G} (hLu : Lu ≤ d.fixedCentralizer u)
    (hn : (Lu.subgroupOf (d.fixedCentralizer u)).Normal) (hq : IsQuasisimple Lu)
    (hKLu : K F ≤ Lu) :
    ∃ α : MulAut (Lu.subgroupOf (d.fixedCentralizer u)),
      (∀ x : Lu.subgroupOf (d.fixedCentralizer u),
        ((α x : d.fixedCentralizer u) : G) = d.z * (x : G) * d.z⁻¹) ∧
      ((center (Lu.subgroupOf (d.fixedCentralizer u)) ≠ ⊥ ∧
        center (Lu.subgroupOf (d.fixedCentralizer u)) =
          pCore 2 (Lu.subgroupOf (d.fixedCentralizer u)) ∧
        (ClassicalGroup.IsPSL ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
          pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) 3 4 ∨
        IsG2At ((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
          pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) 4) ∧
        α ∈ (MulAut.conj (G := Lu.subgroupOf (d.fixedCentralizer u))).range) ∨
      (∃ name : SporadicName, name ≠ .j3 ∧
        Nonempty (((Lu.subgroupOf (d.fixedCentralizer u)) ⧸
          pCore 2 (Lu.subgroupOf (d.fixedCentralizer u))) ≃* name.Carrier) ∧
        TwoCentralInner α)) := by
  let := hq
  let e := subgroupOfEquivOfLe hLu
  let : IsQuasisimple (Lu.subgroupOf (d.fixedCentralizer u)) :=
    IsQuasisimple.of_mulEquiv e.symm
  have heven : 2 ∣ Nat.card (center (Lu.subgroupOf (d.fixedCentralizer u))) := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    exact d.fixed_component_center_even u hne hLu
      (d.fixed_mem_component_of_commutator hgen u hKLu)
  obtain ⟨α, ha, hm⟩ := d.fixedComponent_modelAction115 h115 u hne hmax hsyl hLu hn hq
  exact ⟨α, ha, modelAction115_of_even_center heven hm⟩

/-- The original K is exactly the two-residual of the component's z-centralizer.
This identifies the actor used in the model comparison, in ambient coordinates. -/
theorem fixedComponent_centralizerResidual {Lu : Subgroup G} (hKLu : K F ≤ Lu) :
    (pResidual 2 (Lu ⊓ centralizer ({d.z} : Set G) : Subgroup G)).map
      (Lu ⊓ centralizer ({d.z} : Set G)).subtype = K F := by
  rw [← d.centralizer_eq]
  apply le_antisymm
  · exact embedded_pResidual_mono 2 (inf_le_right : Lu ⊓ F.H ≤ F.H)
  · have hm := embedded_pResidual_mono 2 (le_inf hKLu (K_le_H F))
    rw [(pResidual_eq_top_iff 2 _).mpr (K_twoPerfect F),
      ← MonoidHom.range_eq_map, range_subtype] at hm
    exact hm

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
