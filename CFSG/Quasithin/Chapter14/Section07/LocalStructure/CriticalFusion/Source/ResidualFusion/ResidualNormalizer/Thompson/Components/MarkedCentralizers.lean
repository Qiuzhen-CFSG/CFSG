module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Components.MarkedActions
public import Theory.Representation.PSL3Two.NaturalSylowFixed
public import Theory.Representation.PSL3Two.NaturalOrbits
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Marked small-action centralizers in 14.7.67(4)

A vector in the binary deleted permutation module for A₅ is fixed by a
nonidentity element of order three: lift it to the augmentation core and
cycle three equal coordinates. On the natural SL₃(2) module, transitivity
transports an explicit cubic element fixing the first basis vector.
A Sylow two-subgroup fixes at most two natural vectors, so every nonzero
coordinate of a Sylow-fixed vector in repeated natural modules is the same.
The same cubic element therefore fixes all coordinates simultaneously.

The marked quotient maps the original vector stabilizer onto the model
stabilizer. If its two-residual were trivial, the original finite stabilizer
and its image would be two-groups, contradicting the cubic element. An
invariant direct complement leaves the stabilizer unchanged.

The final theorem applies this calculation to the original component action
and original generator of V₁. It retains the marked decomposition as an
explicit premise: constructing that decomposition and excluding components
unconditionally remain with the source assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.67(4), printed p.1070, PDF p.1087.
-/

public section
noncomputable section
open scoped IsMulCommutative
open Subgroup Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Theory.GroupTheory
namespace ResidualNormalizer.Components
open ChapterB.QuasisimpleSource
universe u v w x
variable {A : Type u} [Group A] {E : Type v} [AddCommGroup E] [Module (ZMod 2) E]
variable {M : Type w} [Group M] {N : Type x} [AddCommGroup N] [Module (ZMod 2) N]

private def triple (a b c : Fin 5) : Equiv.Perm (Fin 5) :=
  Equiv.swap a b * Equiv.swap b c

private theorem triple_certificate : ∀ v : Fin 5 → ZMod 2,
    ∃ a b c : Fin 5, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ v a = v b ∧ v b = v c := by decide

private theorem triple_properties : ∀ a b c : Fin 5,
    a ≠ b → a ≠ c → b ≠ c →
    triple a b c ≠ 1 ∧ (triple a b c) ^ 3 = 1 ∧ (triple a b c).sign = 1 := by decide

private theorem triple_fixes (v : Fin 5 → ZMod 2) (a b c : Fin 5)
    (hab : v a = v b) (hbc : v b = v c) :
    BinaryPermutation.representation (Fin 5) (triple a b c) v = v := by
  funext i
  change v ((Equiv.swap b c) ((Equiv.swap a b) i)) = v i
  rw [Equiv.apply_swap_eq_self hbc, Equiv.apply_swap_eq_self hab]

private theorem a5_cubic (v : BinaryPermutation.natural (Fin 5)) :
    ∃ g : alternatingGroup (Fin 5), g ≠ 1 ∧ g ^ 3 = 1 ∧ alternatingNatural 5 g v = v := by
  let e := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  let w := e.symm v
  obtain ⟨a, b, c, hab, hac, hbc, hvab, hvbc⟩ := triple_certificate w.val
  obtain ⟨hn, hpow, hsign⟩ := triple_properties a b c hab hac hbc
  let g : alternatingGroup (Fin 5) := ⟨triple a b c, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩
  refine ⟨g, fun he => hn (congrArg Subtype.val he), Subtype.ext hpow, ?_⟩
  have hf : BinaryPermutation.coreRepresentation (Fin 5) g.val w = w :=
    Subtype.ext (triple_fixes w.val a b c hvab hvbc)
  have he := BinaryPermutation.coreEquivNatural_equivariant (Fin 5) (by decide) g.val w
  change e (BinaryPermutation.coreRepresentation (Fin 5) g.val w) = alternatingNatural 5 g (e w) at he
  rw [hf] at he
  simpa [w] using he.symm

private def cubicMatrix : BinaryLinearThree.Group :=
  ⟨![![1, 0, 0], ![0, 0, 1], ![0, 1, 1]], by decide⟩
private theorem cubicMatrix_ne : cubicMatrix ≠ 1 := by decide
private theorem cubicMatrix_pow : cubicMatrix ^ 3 = 1 := by decide
private theorem cubicMatrix_fixed : BinaryLinearThree.W cubicMatrix ![1, 0, 0] = ![1, 0, 0] := by decide

private theorem natural_cubic (v : BinaryLinearThree.Vector) :
    ∃ g : BinaryLinearThree.Group, g ≠ 1 ∧ g ^ 3 = 1 ∧ BinaryLinearThree.W g v = v := by
  by_cases hv : v = 0
  · exact ⟨cubicMatrix, cubicMatrix_ne, cubicMatrix_pow, by simp [hv]⟩
  obtain ⟨a, ha⟩ := BinaryLinearThree.natural_transitive_nonzero ![1, 0, 0] v (by decide) hv
  refine ⟨MulAut.conj a cubicMatrix, ?_, ?_, ?_⟩
  · exact fun h => cubicMatrix_ne ((MulAut.conj a).injective (h.trans (map_one _).symm))
  · rw [← map_pow, cubicMatrix_pow, map_one]
  · rw [← ha]
    change BinaryLinearThree.W (a * cubicMatrix * a⁻¹)
      (BinaryLinearThree.W a ![1, 0, 0]) = BinaryLinearThree.W a ![1, 0, 0]
    rw [← Module.End.mul_apply, ← map_mul]
    simp only [mul_assoc, inv_mul_cancel, mul_one, map_mul, Module.End.mul_apply,
      cubicMatrix_fixed]

private theorem fixed_eq_zero_or (P : Sylow 2 BinaryLinearThree.Group)
    (u v : Representation.BinaryOffender.fixedSpace BinaryLinearThree.W (P : Subgroup BinaryLinearThree.Group))
    (hu : u ≠ 0) : v = 0 ∨ v = u := by
  classical
  by_contra hn
  push Not at hn
  have hc := BinaryLinearThree.card_sylow_natural_fixed_le_two P
  let := Fintype.ofFinite (Representation.BinaryOffender.fixedSpace BinaryLinearThree.W (P : Subgroup BinaryLinearThree.Group))
  have hthree : ({0, u, v} : Finset (Representation.BinaryOffender.fixedSpace BinaryLinearThree.W (P : Subgroup BinaryLinearThree.Group))).card = 3 := by
    simp [Ne.symm hu, Ne.symm hn.1, Ne.symm hn.2]
  have hle := Finset.card_le_univ ({0, u, v} : Finset (Representation.BinaryOffender.fixedSpace BinaryLinearThree.W (P : Subgroup BinaryLinearThree.Group)))
  rw [hthree, ← Nat.card_eq_fintype_card] at hle
  omega

private theorem repeated_cubic (r : ℕ) (v : Fin r → BinaryLinearThree.Vector)
    (P : Sylow 2 BinaryLinearThree.Group)
    (hP : (P : Subgroup BinaryLinearThree.Group) ≤ pointStabilizer (repeated (linearNatural BinaryField.two 3) r) v) :
    ∃ g : BinaryLinearThree.Group, g ≠ 1 ∧ g ^ 3 = 1 ∧
      repeated (linearNatural BinaryField.two 3) r g v = v := by
  classical
  have hv (i : Fin r) : v i ∈ Representation.BinaryOffender.fixedSpace BinaryLinearThree.W (P : Subgroup BinaryLinearThree.Group) := by
    intro a
    exact congrFun (hP a.property) i
  by_cases hn : ∃ i, v i ≠ 0
  · obtain ⟨i, hi⟩ := hn
    obtain ⟨g, hg, hpow, hfix⟩ := natural_cubic (v i)
    refine ⟨g, hg, hpow, ?_⟩
    funext j
    change BinaryLinearThree.W g (v j) = v j
    rcases fixed_eq_zero_or P ⟨v i, hv i⟩ ⟨v j, hv j⟩
      (fun h => hi (congrArg Subtype.val h)) with he | he
    · have hj : v j = 0 := congrArg Subtype.val he
      simp [hj]
    · have hj : v j = v i := congrArg Subtype.val he
      rw [hj, hfix]
  · push Not at hn
    refine ⟨cubicMatrix, cubicMatrix_ne, cubicMatrix_pow, ?_⟩
    funext i
    change BinaryLinearThree.W cubicMatrix (v i) = v i
    simp [hn i]

private theorem not_two_of_cubic {G : Type*} [Group G] (g : G)
    (hne : g ≠ 1) (hpow : g ^ 3 = 1) : ¬ IsPGroup 2 G := by
  intro hp
  exact hne ((hp.powEquiv (by decide : Nat.Coprime 2 3)).injective
    (by simpa using hpow))

private theorem marking_stabilizer_map {ρ : Representation (ZMod 2) A E}
    {σ : Representation (ZMod 2) M N} (m : QuotientActionMarking ρ σ) (v : E) :
    (pointStabilizer ρ v).map m.quotient = pointStabilizer σ (m.coordinates v) := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    change σ (m.quotient a) (m.coordinates v) = m.coordinates v
    rw [← m.intertwines, show ρ a v = v from ha]
  · intro hb
    obtain ⟨a, rfl⟩ := m.onto b
    refine ⟨a, ?_, rfl⟩
    apply m.coordinates.injective
    exact (m.intertwines a v).trans hb

private theorem marking_sylow [Finite A] {ρ : Representation (ZMod 2) A E}
    {σ : Representation (ZMod 2) M N} (m : QuotientActionMarking ρ σ) (v : E)
    (P : Sylow 2 A) (hP : (P : Subgroup A) ≤ pointStabilizer ρ v) :
    ((P.mapSurjective m.onto : Sylow 2 M) : Subgroup M) ≤
      pointStabilizer σ (m.coordinates v) := by
  rw [Sylow.coe_mapSurjective, ← marking_stabilizer_map m v]
  exact Subgroup.map_mono hP

private theorem residual_ne_bot_of_marked_not_two [Finite A]
    {ρ : Representation (ZMod 2) A E} {σ : Representation (ZMod 2) M N}
    (m : QuotientActionMarking ρ σ) (v : E)
    (hn : ¬ IsPGroup 2 (pointStabilizer σ (m.coordinates v))) :
    pResidual 2 (pointStabilizer ρ v) ≠ ⊥ := by
  intro h
  have hp : IsPGroup 2 (pointStabilizer ρ v) :=
    (isPGroup_quotient_pResidual (G := pointStabilizer ρ v) 2).of_equiv
      ((QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot)
  have hi := hp.of_surjective (m.quotient.subgroupMap (pointStabilizer ρ v))
    (m.quotient.subgroupMap_surjective (pointStabilizer ρ v))
  rw [marking_stabilizer_map m v] at hi
  exact hn hi

private theorem decomposition_stabilizer {ρ : Representation (ZMod 2) A E}
    (m : SmallModuleDecomposition ρ) (v : E) :
    ∃ w : m.movedSpace, pointStabilizer ρ v = pointStabilizer m.movedSpace.toRepresentation w := by
  obtain ⟨w, z, hw, hz, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp m.splitting.codisjoint v
  refine ⟨⟨w, hw⟩, ?_⟩
  ext a
  change ρ a (w + z) = w + z ↔ m.movedSpace.toRepresentation a ⟨w, hw⟩ = ⟨w, hw⟩
  rw [map_add, (ρ.mem_invariants z).mp hz a, add_left_inj]
  constructor
  · intro h; exact Subtype.ext h
  · intro h; exact congrArg Subtype.val h

/-- Each marked small action has a stabilizer with nontrivial two-residual at
any vector fixed by a Sylow two-subgroup. The repeated action uses the same
marking in every coordinate; its Sylow fixed space has at most two elements. -/
theorem SmallMovedAction.pointStabilizer_residual_ne_bot [Finite A]
    {ρ : Representation (ZMod 2) A E} (h : SmallMovedAction ρ)
    (v : E) (P : Sylow 2 A) (hP : (P : Subgroup A) ≤ pointStabilizer ρ v) :
    pResidual 2 (pointStabilizer ρ v) ≠ ⊥ := by
  cases h with
  | alternatingFive m =>
    apply residual_ne_bot_of_marked_not_two m v
    obtain ⟨g, hg, hpow, hfix⟩ := a5_cubic (m.coordinates v)
    exact not_two_of_cubic (⟨g, hfix⟩ : pointStabilizer (alternatingNatural 5) (m.coordinates v))
      (fun h => hg (congrArg Subtype.val h)) (Subtype.ext hpow)
  | linearThree r _ _ m =>
    apply residual_ne_bot_of_marked_not_two m v
    obtain ⟨g, hg, hpow, hfix⟩ :=
      repeated_cubic r (m.coordinates v) (P.mapSurjective m.onto) (marking_sylow m v P hP)
    exact not_two_of_cubic
      (⟨g, hfix⟩ : pointStabilizer (repeated (linearNatural BinaryField.two 3) r) (m.coordinates v))
      (fun h => hg (congrArg Subtype.val h)) (Subtype.ext hpow)

/-- The marked decomposition gives precisely the O² calculation used in
14.7.67(4). The invariant complement contributes no stabilizer condition. -/
theorem SmallModuleDecomposition.pointStabilizer_residual_ne_bot [Finite A]
    {ρ : Representation (ZMod 2) A E} (m : SmallModuleDecomposition ρ)
    (v : E) (_hv : v ≠ 0) (P : Sylow 2 A)
    (hP : (P : Subgroup A) ≤ pointStabilizer ρ v) :
    pResidual 2 (pointStabilizer ρ v) ≠ ⊥ := by
  obtain ⟨w, hw⟩ := decomposition_stabilizer m v
  rw [hw] at hP ⊢
  exact m.action.pointStabilizer_residual_ne_bot w P hP

end ResidualNormalizer.Components

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Data
open ResidualNormalizer ResidualNormalizer.Components
variable (d : Data T L V F W)

/-- Conditional source application of the small-action centralizer calculation.
The original vector stabilizer maps to the literal C_B(V₁), as proved by
`residualComponentPointStabilizer_map`. The source local geometry makes that
stabilizer a two-group, contradicting this calculation. Constructing the
marked decomposition remains the independent source B.5.1 application. -/
theorem false_of_residual_component_smallModuleDecomposition
    (hSylow : Chapter1.IsSylowIn 2 (F.Ri L 1) (Y L F))
    {B : Subgroup G} (hB : B ∈ Chapter1.cComponentsIn (J L F))
    (m : letI := (d.residualSpan_reduced hSylow).elementary
      SmallModuleDecomposition (d.residualComponentRepresentation hSylow (hB.1.trans J_le_Y))) :
    False := by
  let := (d.residualSpan_reduced hSylow).elementary
  obtain ⟨P, hP⟩ := d.residual_component_point_fixed_by_sylow hSylow hB
  exact m.pointStabilizer_residual_ne_bot d.residualPointVector d.residualPointVector_ne_zero
    P hP (d.residual_component_point_stabilizer_residual_eq_bot hSylow hB)

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
