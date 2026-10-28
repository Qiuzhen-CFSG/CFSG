module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Action
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Cases
public import Theory.Representation.SL3DoubledNaturalOffenders.Centralizer
public import Theory.Representation.BinaryOffender.IrreducibleDiagonal

/-!
# Exclusion of the natural central quotient under central action

An invertible additive map commuting with the natural SL₃(2) action is the
identity: the additive commutant consists of F₂-scalars. Apply this on the
literal central quotient. The resulting fixed displacements, together with
commutator generation, force the commuting actor to fix the whole moved
space, even when that space has nonzero component-fixed vectors.

For the actual plus action this proves [U_K,L_v]=1. The genuine marked
13.6.11 theorem contradicts this under the specified Sylow and 13.6.14
invariance. The natural-module premise must still come from the classifier;
this module supplies its exclusion, not the classification application.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 13.6.20,
printed p.931, using 13.6.11 and B.5.1/B.5.6.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
open ComponentSelection ChapterB.QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

private theorem natural_commuting_actor_fixes (ρ : Representation (ZMod 2) D V)
    (C : Subgroup D) (e : ActionEquiv (ρ.comp C.subtype) BinaryLinearThree.W)
    (b : D) (hc : ∀ c ∈ C, Commute b c) (w : V) : ρ b w = w := by
  let f : BinaryLinearThree.Vector →+ BinaryLinearThree.Vector :=
    e.linearEquiv.toAddEquiv.toAddMonoidHom.comp
      ((ρ b).toAddMonoidHom.comp e.linearEquiv.symm.toAddEquiv.toAddMonoidHom)
  have hf : Function.Injective f :=
    e.linearEquiv.injective.comp ((ρ.apply_bijective b).1.comp e.linearEquiv.symm.injective)
  have he (c : C) (x : BinaryLinearThree.Vector) :
      e.linearEquiv.symm (BinaryLinearThree.W (e.groupEquiv c) x) =
        ρ c (e.linearEquiv.symm x) := by
    apply e.linearEquiv.injective
    rw [e.linearEquiv.apply_symm_apply]
    simpa only [MonoidHom.comp_apply, Subgroup.coe_subtype,
      e.linearEquiv.apply_symm_apply] using
      (e.intertwines c (e.linearEquiv.symm x)).symm
  obtain ⟨a, ha⟩ := SL3DoubledNaturalOffenders.natural_centralizer_scalar f (by
    intro c x
    obtain ⟨c, rfl⟩ := e.groupEquiv.surjective c
    change e.linearEquiv (ρ b (e.linearEquiv.symm (BinaryLinearThree.W (e.groupEquiv c) x))) =
      BinaryLinearThree.W (e.groupEquiv c) (e.linearEquiv (ρ b (e.linearEquiv.symm x)))
    rw [he, ← e.intertwines]
    apply congrArg e.linearEquiv
    change (ρ b * ρ c) _ = (ρ c * ρ b) _
    rw [← map_mul, ← map_mul, (hc c c.property).eq])
  have ha0 : a ≠ 0 := by
    intro h
    have hz : ∀ x, f x = 0 := by intro x; rw [ha, h, zero_smul]
    have h01 : (0 : BinaryLinearThree.Vector) = 1 := hf ((hz 0).trans (hz 1).symm)
    exact zero_ne_one (congrFun h01 0)
  have ha1 : a = 1 := by
    fin_cases a
    · exact (ha0 rfl).elim
    · rfl
  have hw := ha (e.linearEquiv w)
  simp only [ha1, one_smul] at hw
  apply e.linearEquiv.injective
  change e.linearEquiv (ρ b (e.linearEquiv.symm (e.linearEquiv w))) = _ at hw
  rwa [e.linearEquiv.symm_apply_apply] at hw

private theorem fixes_moved_of_natural_central_quotient (ρ : Representation (ZMod 2) D V)
    (C : Subgroup D) (s : MovedSection ρ C)
    (hfull : subspaceCommutator ρ s.space.toSubmodule C = s.space.toSubmodule)
    (e : ActionEquiv (s.action.comp C.subtype) BinaryLinearThree.W)
    (b : D) (hc : ∀ c ∈ C, Commute b c)
    (w : s.space.toSubmodule) : s.space.toRepresentation b w = w := by
  have hd (w : s.space.toSubmodule) :
      s.space.toRepresentation b w - w ∈ fixedSpace s.space.toRepresentation C := by
    rw [← s.central_eq]
    apply (Submodule.Quotient.mk_eq_zero s.central.toSubmodule).mp
    change s.central.toSubmodule.mkQ (s.space.toRepresentation b w - w) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (natural_commuting_actor_fixes s.action C e b hc
      (s.central.toSubmodule.mkQ w))
  have htop : subspaceCommutator s.space.toRepresentation ⊤ C = ⊤ := by
    apply top_unique
    intro w _
    have hw : (w : V) ∈ subspaceCommutator ρ s.space.toSubmodule C := by
      rw [hfull]; exact w.property
    have hl : subspaceCommutator ρ s.space.toSubmodule C ≤
        (subspaceCommutator s.space.toRepresentation ⊤ C).map s.space.toSubmodule.subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨c, hc, x, hx, rfl⟩
      exact ⟨s.space.toRepresentation c ⟨x, hx⟩ - ⟨x, hx⟩,
        Submodule.subset_span ⟨c, hc, ⟨x, hx⟩, Submodule.mem_top, rfl⟩, rfl⟩
    obtain ⟨w', hw', he⟩ := hl hw
    exact (Subtype.ext he : w' = w) ▸ hw'
  apply fixes_commutatorSubspace_of_commutes_of_displacement_fixed
    s.space.toRepresentation hc hd
  rw [htop]
  trivial

section Actual
variable {G : Type*} [Group G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]

/-- Centrality on W_K and a natural central quotient force L_v to fix U_K. -/
theorem single_natural_centralizes_UK
    (s : MovedSection (wkRepresentation K L T z v hL hz)
      (plusImage K L T z v hL hz K))
    (hfull : subspaceCommutator (wkRepresentation K L T z v hL hz)
      s.space.toSubmodule (plusImage K L T z v hL hz K) = s.space.toSubmodule)
    (e : ActionEquiv (s.action.comp (plusImage K L T z v hL hz K).subtype)
      BinaryLinearThree.W)
    (hc : ⁅plusImage K L T z v hL hz K, plusImage K L T z v hL hz (Lv L v)⁆ = ⊥) :
    ⁅UK K L T z v, Lv L v⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro u hu
  apply mem_centralizer_iff.mpr
  intro l hl
  let b := plusMk K L T z v hL hz
    ⟨l, (show Lv L v ≤ plusActor K L T v from le_sup_right.trans le_sup_left) hl⟩
  have hb : b ∈ plusImage K L T z v hL hz (Lv L v) := mem_map_of_mem _ hl
  have hbc : ∀ c ∈ plusImage K L T z v hL hz K, Commute b c := by
    intro c hc'
    exact mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hc) hc') b hb
  let w := (movedEquivUK K L T z v hL hz s).symm ⟨u, hu⟩
  have hw := fixes_moved_of_natural_central_quotient
    (wkRepresentation K L T z v hL hz) (plusImage K L T z v hL hz K) s hfull e b hbc w.toAdd
  have he := congrArg (fun x : s.space.toSubmodule => (x.val.toMul : G)) hw
  change ((wkRepresentation K L T z v hL hz b w.toAdd.val).toMul : G) = _ at he
  rw [wkRepresentation_apply] at he
  exact mul_inv_eq_iff_eq_mul.mp he


end Actual

variable {G : Type*} [Group G] (K L T : Subgroup G)

/-- Apply the actual 13.6.11 contradiction, retaining the marked source data. -/
theorem not_single_natural_of_marking [Finite G] {V : Subgroup G}
    (s₀ : A5Module.Marking L V)
    [IsElementaryAbelian 2 (Uv (A5Module.markedZ s₀) (A5Module.markedV s₀))]
    [IsElementaryAbelian 2 (WK K L T (A5Module.markedZ s₀) (A5Module.markedV s₀))]
    (S : Sylow 2 (Gv (A5Module.markedV s₀)))
    (hS : (S : Subgroup (Gv (A5Module.markedV s₀))).map
      (Gv (A5Module.markedV s₀)).subtype = Tv T (A5Module.markedV s₀))
    (hL : Tv T (A5Module.markedV s₀) ≤ normalizer (Lv L (A5Module.markedV s₀) : Set G))
    (hz : Tv T (A5Module.markedV s₀) ≤ centralizer ({A5Module.markedZ s₀} : Set G))
    (hK : K ∈ Yz L T (A5Module.markedZ s₀) (A5Module.markedV s₀))
    (hn : Tv T (A5Module.markedV s₀) ≤ normalizer (K : Set G))
    (s : MovedSection (wkRepresentation K L T (A5Module.markedZ s₀) (A5Module.markedV s₀) hL hz) (plusImage K L T (A5Module.markedZ s₀) (A5Module.markedV s₀) hL hz K))
    (hfull : subspaceCommutator (wkRepresentation K L T (A5Module.markedZ s₀) (A5Module.markedV s₀) hL hz)
      s.space.toSubmodule (plusImage K L T (A5Module.markedZ s₀) (A5Module.markedV s₀) hL hz K) = s.space.toSubmodule)
    (e : ActionEquiv (s.action.comp (plusImage K L T (A5Module.markedZ s₀) (A5Module.markedV s₀) hL hz K).subtype) BinaryLinearThree.W)
    (hc : ⁅plusImage K L T (A5Module.markedZ s₀) (A5Module.markedV s₀) hL hz K, plusImage K L T (A5Module.markedZ s₀) (A5Module.markedV s₀) hL hz (Lv L (A5Module.markedV s₀))⁆ = ⊥) :
    False :=
  UK_commutator_ne_bot s₀ K T S hS hz hK hn
    (single_natural_centralizes_UK K L T (A5Module.markedZ s₀) (A5Module.markedV s₀) hL hz s hfull e hc)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives
