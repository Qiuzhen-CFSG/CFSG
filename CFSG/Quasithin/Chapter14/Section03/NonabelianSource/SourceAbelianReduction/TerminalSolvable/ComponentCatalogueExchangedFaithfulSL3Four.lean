module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueExchangedFaithfulSource
public import Theory.SpecificGroups.PSL3Four.OuterSylowCommutator

/-!
# Excluding SL₃(4) in the faithful exchanged branch

The original exchanging element x is outer on the component orbit H:
inner conjugation would identify its constituent with its dual, contrary
to the retained non-self-duality. The model calculation applies to x and
the original dotted Sylow intersection S ∩ H, through the actual equivalence
with SL₃(GF(4)) and its central quotient.

Thus `[⟨x⟩, S ∩ H]` has nontrivial Frattini subgroup. On the source side,
G.10.9(2) puts precisely this commutator in the original elementary actor X,
so its inherited elementary structure gives trivial Frattini subgroup.
No monotonicity assertion for Frattini subgroups is used.

Source: Aschbacher--Smith, G.11.6, printed p.366, and G.10.9(2), p.360.
This discharges the SL₃(4) exclusion for the faithful exchanged recognition;
the G.9 model sieve and its final A₇ assembly remain with that consumer.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

private def dual_equiv {K D U V : Type*} [Field K] [Group D]
    [AddCommGroup U] [AddCommGroup V] [Module K U] [Module K V]
    {ρ : Representation K D U} {σ : Representation K D V}
    (e : Representation.Equiv ρ σ) : Representation.Equiv σ.dual ρ.dual := by
  refine Representation.Equiv.mk e.toLinearEquiv.dualMap ?_
  intro g
  ext f u
  change f (σ g⁻¹ (e u)) = f (e (ρ g⁻¹ u))
  exact congrArg f (congrArg (fun l => l u) (e.isIntertwining' g⁻¹)).symm

private theorem not_inner_of_conjugate_dual
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (H : Subgroup D) [H.Normal]
    (R : Subrepresentation (ρ.comp H.subtype)) (x : D)
    (hn : ¬ Nonempty (Representation.Equiv R.toRepresentation R.toRepresentation.dual))
    (hd : Nonempty (Representation.Equiv R.toRepresentation
      (conjugateSubrepresentation ρ H R x).toRepresentation.dual)) :
    MulAut.conjNormal (H := H) x ∉ MulAut.innerSubgroup H := by
  rintro ⟨h,hh⟩
  have hc (a : H) : (⟨x * a.val * x⁻¹, (inferInstance : H.Normal).conj_mem a a.property x⟩ : H) =
      h * a * h⁻¹ := by
    exact (DFunLike.congr_fun hh a).symm
  let σ := R.toRepresentation
  let e : Representation.Equiv σ (conjugateRep (G := D) σ x) :=
    Representation.Equiv.mk (LinearMap.GeneralLinearGroup.toLinearEquiv (σ.asGroupHom h)) (by
      intro a
      change σ h ∘ₗ σ a = (conjugateRep (G := D) σ x) a ∘ₗ σ h
      rw [conjugateRep_apply, hc]
      change σ h * σ a = σ (h * a * h⁻¹) * σ h
      rw [← map_mul, ← map_mul]
      simp only [inv_mul_cancel_right])
  let f := (conjugateSubrepresentationEquiv ρ H R x).toRepresentationEquiv
  obtain ⟨d⟩ := hd
  exact hn ⟨d.trans (dual_equiv (e.trans f.symm))⟩

namespace ExchangedFaithfulSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : ExchangedFaithfulSource T M Mc F g B v L I)

include s

/-- The original exchanging element induces an outer automorphism of H. -/
theorem exists_exchanging_outer :
    let := componentOrbit_top_normal L
    ∃ x : F.terminalDot (F.X g), I.map (F.terminalRepresentation x) ≠ I ∧
      MulAut.conjNormal (H := componentOrbit L ⊤) (x : F.TerminalHdot) ∉
        MulAut.innerSubgroup (componentOrbit L ⊤) := by
  let := componentOrbit_top_normal L
  obtain ⟨x,hx,_⟩ := s.completion.1
  exact ⟨x,hx,not_inner_of_conjugate_dual F.terminalRepresentation (componentOrbit L ⊤)
    (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant)
    x s.faithful_data.2.1 (s.faithful_data.2.2.2 x hx)⟩

/-- Each cyclic commutator lies in the original elementary actor, by monotonicity
of commutators, without any assertion of Frattini monotonicity. -/
theorem cyclic_sylow_commutator_le (x : F.terminalDot (F.X g)) :
    ⁅zpowers (x : F.TerminalHdot),
      (sylow (F := F) : Subgroup F.TerminalHdot) ⊓ componentOrbit L ⊤⁆ ≤
      F.terminalDot (F.X g) ⊓ componentOrbit L ⊤ :=
  (commutator_mono (zpowers_le.mpr x.property) le_rfl).trans s.sylow_commutator_le

/-- Trivial Frattini subgroup for the individual exchanging element follows
from the inherited elementary structure on its actual cyclic commutator. -/
theorem cyclic_sylow_commutator_frattini (x : F.terminalDot (F.X g)) :
    frattini (⁅zpowers (x : F.TerminalHdot),
      (sylow (F := F) : Subgroup F.TerminalHdot) ⊓ componentOrbit L ⊤⁆ :
        Subgroup F.TerminalHdot) = ⊥ := by
  have hle := (s.cyclic_sylow_commutator_le x).trans inf_le_left
  let C := (⁅zpowers (x : F.TerminalHdot),
      (sylow (F := F) : Subgroup F.TerminalHdot) ⊓ componentOrbit L ⊤⁆ :
        Subgroup F.TerminalHdot)
  let : IsElementaryAbelian 2 C :=
    IsElementaryAbelian.of_injective (inclusion hle) (inclusion_injective hle)
  let : Fact (IsPGroup 2 C) := ⟨IsElementaryAbelian.isPGroup 2 C⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := 2)

/-- The source SL₃(4) row is impossible: the same exchanging element has a
cyclic Sylow commutator with both trivial and nontrivial Frattini subgroup. -/
theorem not_sl3Four_equiv
    (e : componentOrbit L ⊤ ≃*
      Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) : False := by
  let := componentOrbit_top_normal L
  let : Group.IsPerfect (componentOrbit L ⊤) := s.component.orbit_isPerfect ⊤
  obtain ⟨x,_,hxouter⟩ := s.exists_exchanging_outer
  obtain ⟨_,hXS,_⟩ := Recognition.source_terminal_actor_normal_in_point_sylow
    s.simple T s.empty s.maximal s.unique_overgroup s.many_overgroups s.seed_card
    (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
    s.normalizer_not_mem s.hypothesis
  let eZ : (componentOrbit L ⊤) ⧸ center (componentOrbit L ⊤) ≃*
      Matrix.PSL3Four.PSL := QuotientGroup.congr _ _ e (by
    ext z
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hz
      refine ⟨((centerCongr e).symm ⟨z,hz⟩ : componentOrbit L ⊤),
        ((centerCongr e).symm ⟨z,hz⟩).property, ?_⟩
      exact congrArg Subtype.val ((centerCongr e).apply_symm_apply ⟨z,hz⟩))
  exact Matrix.PSL3Four.OuterSylowCommutator.cyclic_commutator_frattini_ne_bot
    (GaloisField 2 2) (n := 2) (by decide) (by simpa using Matrix.PSL3Four.card_F)
    (componentOrbit L ⊤) eZ (sylow (F := F)) x (hXS x.property)
    (elemPow_eq_one_of_isElementaryAbelian (x : F.TerminalHdot) x.property)
    hxouter (s.cyclic_sylow_commutator_frattini x)

/-- There is no group equivalence from the faithful exchanged orbit to SL₃(4). -/
theorem not_nonempty_sl3Four_equiv :
    ¬ Nonempty (componentOrbit L ⊤ ≃*
      Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) := by
  rintro ⟨e⟩
  exact s.not_sl3Four_equiv e

end ExchangedFaithfulSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
