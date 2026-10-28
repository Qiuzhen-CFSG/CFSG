module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.Projection
public import Theory.SpecificGroups.PSL3Two.Parabolics.ResidualRecognition
public import Theory.GroupTheory.MinimalParabolicResidual

/-!
# Lifting the noncentral linear-three projection

The projection constructed in `Projection.lean` lands in the literal
`K⁺`-image.  Its action identity alone only identifies the image modulo the
centralizer of `K⁺`; it does not give containment in the original subgroup.
This file records the source lift with those two pieces of data kept explicit:
the ambient component centralizer is absorbed by `K⁺`, and the kernel of the
literal plus map on the actor is contained in the original `K`.

These are sufficient conditions for lifting an element of `Lᵥ` from the plus
quotient; they have not been established from the earlier source conclusions.
The separate `NoncentralLift` route uses only the projection kernel on `Lᵥ`
and retains ambient normalization of `K` as its remaining source obligation.
The `PSL₃(2)` residual recognition used by the source branch is re-exported
below as a separate theorem so its Sylow marking remains visible to the
assembly owner.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), Lemma 13.6.20,
printed p.931; the residual recognition is the concrete `SL₃(2)` parabolic
calculation in `Theory.SpecificGroups.PSL3Two.Parabolics.ResidualRecognition`.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree
open ComponentSelection

variable {G : Type*} [Group G]

private theorem residualPlusMap_mem_of_center_absorbed [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (f : Lv L v →* plusImage K L T z v hL hz K)
    (hf : ∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
      (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
        residualPlusMap K L T z v hL hz l * k *
          (residualPlusMap K L T z v hL hz l)⁻¹)
    (hcenter : centralizer
      (plusImage K L T z v hL hz K : Set (Gplus K L T z v hL hz)) ≤
        plusImage K L T z v hL hz K)
    (l : Lv L v) :
    residualPlusMap K L T z v hL hz l ∈ plusImage K L T z v hL hz K := by
  let C := plusImage K L T z v hL hz K
  let q := residualPlusMap K L T z v hL hz l
  let a := f l
  have hd : q⁻¹ * a ∈ centralizer (C : Set (Gplus K L T z v hL hz)) := by
    rw [mem_centralizer_iff]
    intro k hk
    have hh := hf l ⟨k, hk⟩
    change (k : Gplus K L T z v hL hz) *
        (q⁻¹ * (a : Gplus K L T z v hL hz)) =
      (q⁻¹ * (a : Gplus K L T z v hL hz)) * k
    calc
      (k : Gplus K L T z v hL hz) * (q⁻¹ * (a : Gplus K L T z v hL hz)) =
          q⁻¹ * (q * k * q⁻¹) * (a : Gplus K L T z v hL hz) := by group
      _ = q⁻¹ * ((a : Gplus K L T z v hL hz) * k * (a : Gplus K L T z v hL hz)⁻¹) *
          (a : Gplus K L T z v hL hz) := by rw [hh]
      _ = (q⁻¹ * (a : Gplus K L T z v hL hz)) * k := by group
  have hdC : q⁻¹ * a ∈ C := hcenter hd
  change q ∈ C
  have hq : q = (a : Gplus K L T z v hL hz) * (q⁻¹ * a)⁻¹ := by
    group
  rw [hq]
  exact C.mul_mem a.property (C.inv_mem hdC)

/-- The literal plus-kernel lifts a projected element back to the original
subgroup.  This is the exact kernel/normalization obligation needed after the
parabolic residual has been recognized; it is intentionally not inferred
from equality of quotient images. -/
theorem lv_le_of_plus_projection
    [Finite G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (f : Lv L v →* plusImage K L T z v hL hz K)
    (hf : ∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
      (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
        residualPlusMap K L T z v hL hz l * k *
          (residualPlusMap K L T z v hL hz l)⁻¹)
    (hcenter : centralizer
      (plusImage K L T z v hL hz K : Set (Gplus K L T z v hL hz)) ≤
        plusImage K L T z v hL hz K)
    (hker : (plusConjugation K L T z v hL hz).ker ≤
      (K.subgroupOf (plusActor K L T v))) :
    Lv L v ≤ K := by
  intro l hl
  have hq := residualPlusMap_mem_of_center_absorbed K L T z v hL hz f hf hcenter ⟨l, hl⟩
  obtain ⟨x, hx, hxeq⟩ := hq
  let a : plusActor K L T v := inclusion (le_sup_right.trans le_sup_left) ⟨l, hl⟩
  let b : plusActor K L T v := x
  have hab : plusMk K L T z v hL hz a = plusMk K L T z v hL hz b := by
    change residualPlusMap K L T z v hL hz ⟨l, hl⟩ = _
    exact hxeq.symm
  have hquot : plusMk K L T z v hL hz (a⁻¹ * b) = 1 := by
    rw [map_mul, map_inv, hab]
    simp
  have hmk : a⁻¹ * b ∈ (plusMk K L T z v hL hz).ker :=
    MonoidHom.mem_ker.mpr hquot
  have hconj : a⁻¹ * b ∈ (plusConjugation K L T z v hL hz).ker := by
    rw [plusConjugation_ker K L T z v hL hz]
    rw [plusMk_ker K L T z v hL hz] at hmk
    exact hmk
  have hKsub : a⁻¹ * b ∈ K.subgroupOf (plusActor K L T v) := hker hconj
  have hK : ((a⁻¹ * b : plusActor K L T v) : G) ∈ K := hKsub
  have hbK : (b : G) ∈ K := hx
  have haK : (a : G) ∈ K := by
    have hmc : (b : G) * (((a⁻¹ * b : plusActor K L T v) : G)⁻¹) = (a : G) := by
      change (b : G) * (((a : G)⁻¹ * (b : G))⁻¹) = (a : G)
      group
    have hm := K.mul_mem hbK (K.inv_mem hK)
    simpa [hmc] using hm
  exact haK

/-! The subgroup called `L_K` in the source can be kept literal in the
ambient group.  It is the intersection with `K`; the preceding lift is the
mathematical content needed to identify it with `Lᵥ`. -/

def LK (K L : Subgroup G) (v : G) : Subgroup G := K ⊓ Lv L v

theorem lv_eq_LK_of_plus_projection
    [Finite G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (f : Lv L v →* plusImage K L T z v hL hz K)
    (hf : ∀ (l : Lv L v) (k : plusImage K L T z v hL hz K),
      (f l : Gplus K L T z v hL hz) * k * (f l : Gplus K L T z v hL hz)⁻¹ =
        residualPlusMap K L T z v hL hz l * k *
          (residualPlusMap K L T z v hL hz l)⁻¹)
    (hcenter : centralizer
      (plusImage K L T z v hL hz K : Set (Gplus K L T z v hL hz)) ≤
        plusImage K L T z v hL hz K)
    (hker : (plusConjugation K L T z v hL hz).ker ≤
      (K.subgroupOf (plusActor K L T v))) :
    Lv L v = LK K L v ∧ LK K L v ≤ K := by
  have hLv := lv_le_of_plus_projection K L T z v hL hz f hf hcenter hker
  refine ⟨?_, inf_le_left⟩
  change Lv L v = K ⊓ Lv L v
  exact le_antisymm (le_inf hLv le_rfl) inf_le_right

/-! The concrete residual-recognition output needed by the source assembly.
The caller supplies the actual Sylow marking of the projected range; the
recognizer then returns both the full maximal parabolic and its two-residual,
with the conjugation and Borel equations retained. -/

theorem recognize_projected_residual
    {A : Subgroup Matrix.PSL3Two.SL} (S : Sylow 2 Matrix.PSL3Two.SL)
    (hA : IsPPerfect 2 A) (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hS : (S : Subgroup Matrix.PSL3Two.SL) ≤
      normalizer (A : Set Matrix.PSL3Two.SL)) :
    IsCoatom (normalizer (A : Set Matrix.PSL3Two.SL)) ∧
      Nat.card (normalizer (A : Set Matrix.PSL3Two.SL)) = 24 ∧
      (S : Subgroup Matrix.PSL3Two.SL) ≤
        normalizer (A : Set Matrix.PSL3Two.SL) ∧
      A = (pResidual 2 (normalizer (A : Set Matrix.PSL3Two.SL))).map
        (normalizer (A : Set Matrix.PSL3Two.SL)).subtype ∧
      ∃ (g : Matrix.PSL3Two.SL) (P : Subgroup Matrix.PSL3Two.SL),
        (P = Matrix.PSL3Two.pointParabolicSL ∨
          P = Matrix.PSL3Two.lineParabolicSL) ∧
        (normalizer (A : Set Matrix.PSL3Two.SL)).map
            (MulAut.conj g).toMonoidHom = P ∧
        A.map (MulAut.conj g).toMonoidHom =
          (pResidual 2 P).map P.subtype ∧
        (S : Subgroup Matrix.PSL3Two.SL).map (MulAut.conj g).toMonoidHom =
          Matrix.PSL3Two.borelSL ∧
        Matrix.PSL3Two.borelSL ≤ P := by
  exact Matrix.PSL3Two.ResidualRecognition.recognize A S hA hc hS

/-! The two-residual is generated by its commutators with the marked Sylow
two-subgroup. The full parabolic has order 24 and its two-residual has order
12, so the residual is distinct from the parabolic. `ParabolicProjection`
constructs the actual Sylow marking and proves this commutator equality for
the source projection without retaining either hypothesis below.
-/

theorem residual_eq_commutator_of_unique_sylow
    {P : Subgroup Matrix.PSL3Two.SL} (S : Sylow 2 P)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup P) ⊤)
    (hcore : ¬ (S : Subgroup P) ≤ pCore 2 P) :
    ⁅pResidual 2 P, (S : Subgroup P)⁆ = pResidual 2 P := by
  exact Subgroup.commutator_twoResidual_eq_of_normal_sylow_subgroup S hu
    (S : Subgroup P) le_rfl S.le_normalizer hcore

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree
