module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.SL2.BorelSmallInvariant.Basic
public import Stellmacher.OmegaOneCenterMap

/-!
# Concrete Borel and torus interfaces for the E.6 blocks

A Borel is specified as the full preimage of an actual model subgroup under
an isomorphism of L/O₂(L): a point stabilizer in A₃ or A₅, or the upper
triangular subgroup of SL₂ in even characteristic. In particular, for A₃
the Borel quotient is trivial; it is not the normalizer of its trivial
Sylow two-subgroup.

`RankOneBlockTorus` describes the intrinsic calculation on Ω₁(Z(S)) needed
in E.6.7 and E.6.11. Its regular action is literal conjugation on the
nonidentity displacement elements. It is an output specification, not an
assumption asserting either source theorem. Constructing it from the block
definition and the exact covering theorem I.2.3 remains required.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.12,
C.1.29, I.2.3, and E.6.7, E.6.11; printed pp.124, 134, 413, 246, 249.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE.Section06
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
variable {G : Type*} [Group G]

/-- Regularity of the actual conjugation action on D minus its identity. -/
def RegularConjugationOnNonidentity (X D : Subgroup G) : Prop :=
  X ≤ normalizer (D : Set G) ∧
    ∀ a : D, a ≠ 1 → ∀ b : D, b ≠ 1 →
      ∃! x : X, (x : G) * (a : G) * (x : G)⁻¹ = (b : G)

/-- Nonempty regular orbits make the conjugation action faithful. -/
theorem RegularConjugationOnNonidentity.faithful
    {X D : Subgroup G} (h : RegularConjugationOnNonidentity X D) (hD : D ≠ ⊥) :
    Function.Injective (D.normalizerMonoidHom.comp (inclusion h.1)) := by
  obtain ⟨aD, haD⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD
  intro x y hxy
  let bD := D.normalizerMonoidHom (inclusion h.1 x) aD
  have hbD : bD ≠ 1 := by
    intro he
    exact haD ((D.normalizerMonoidHom (inclusion h.1 x)).injective
      (he.trans (map_one _).symm))
  obtain ⟨z, _, hz⟩ := h.2 aD haD bD hbD
  have hx : (x : G) * (aD : G) * (x : G)⁻¹ = (bD : G) := rfl
  have hy : (y : G) * (aD : G) * (y : G)⁻¹ = (bD : G) := by
    have he := congrArg (fun f : MulAut D => (f aD : G)) hxy
    exact he.symm
  exact (hz x hx).trans (hz y hy).symm

/-- The full preimage of a point stabilizer in the alternating quotient. -/
def AlternatingBlockBorel (L : Type*) [Group L] (B : Subgroup L) (n : ℕ) : Prop :=
  ∃ (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin n)) (i : Fin n),
    B = (MulAction.stabilizer (alternatingGroup (Fin n)) i).comap
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))

/-- The full preimage of an actual upper triangular rank-one Borel. -/
def L2BlockBorel (L : Type*) [Group L] (B : Subgroup L) (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F,
      B = (Matrix.SpecialLinearGroup.rankOneBorel F).comap
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))

/-- Matched block and Borel types, including the distinct A₅ and L₂(4) modules. -/
def ChiZeroBlockBorel (L : Type*) [Group L] (B : Subgroup L) : Prop :=
  (∃ n, ChapterC.IsL2EvenBlock L n ∧ L2BlockBorel L B n) ∨
    (ChapterC.IsAlternatingBlock L 3 ∧ AlternatingBlockBorel L B 3) ∨
    (ChapterC.IsAlternatingBlock L 5 ∧ AlternatingBlockBorel L B 5)

/-- The intrinsic even-field torus calculation. Both products, the displacement
order, its regular action, and the index of the full Borel preimage are retained. -/
structure RankOneBlockTorus (L : Type*) [Group L] (S : Sylow 2 L)
    (B : Subgroup L) (n : ℕ) where
  torus : Subgroup L
  le_borel : torus ≤ B
  cyclic : IsCyclic torus
  order : Nat.card torus = 2 ^ n - 1
  normalizes_sylow : torus ≤ normalizer (S : Set L)
  borel_product : (B : Set L) = (S : Set L) * (torus : Set L)
  disjoint_sylow : Disjoint (S : Subgroup L) torus
  center_decomposition : Stellmacher.omegaOneCenterAmbient (S : Subgroup L) =
    (Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ⊓ center L) ⊔
      ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), torus⁆
  center_disjoint : Disjoint
    (Stellmacher.omegaOneCenterAmbient (S : Subgroup L) ⊓ center L)
    ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), torus⁆
  displacement_order :
    Nat.card ↥⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), torus⁆ = 2 ^ n
  regular : RegularConjugationOnNonidentity torus
    ⁅Stellmacher.omegaOneCenterAmbient (S : Subgroup L), torus⁆
  borel_index : B.index = 2 ^ n + 1

/-- An alternating block has order divisible by three, via the actual quotient.
This is the numerical block input to the faithful E₉ exclusion. -/
theorem three_dvd_card_alternating_block (L : Type*) [Group L] [Finite L]
    {n : ℕ} (h : ChapterC.IsAlternatingBlock L n) (hn : n = 3 ∨ n = 5) :
    3 ∣ Nat.card L := by
  obtain ⟨e⟩ := h.2.2.quotient_iso
  have he : Nat.card (L ⧸ pCore 2 L) = Nat.card (alternatingGroup (Fin n)) :=
    Nat.card_congr e.toEquiv
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [he]
    rcases hn with rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num
  exact hd.trans (Subgroup.card_quotient_dvd_card (pCore 2 L))

end CFSG.Quasithin.ChapterE.Section06
