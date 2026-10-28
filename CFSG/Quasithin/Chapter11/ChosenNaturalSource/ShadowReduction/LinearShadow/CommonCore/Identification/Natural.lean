module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Conjugates
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Kernel
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Natural coordinates on the literal common pair

`PairNaturalMarking` records an actual group equivalence on K/O₂(K), an
isomorphism on P, and their conjugation intertwining equation. Its field
is independent of the field marking on V: compatibility is a later theorem,
11.3.8. Constructing the marking remains a representation-theoretic obligation.

Upper and lower transvections express every vector as a sum of two
displacements. Transport by the marking proves [P,K] = P and computes
|P| = q^(2j). These facts feed the actual core-identification assembly;
no semisimplicity or commutator equality is inserted into the marking.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
second paragraph of printed p.774, applying G.1.7.
-/

@[expose] public noncomputable section
open Subgroup Matrix
open scoped commutatorElement
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
variable {G : Type*} [Group G] (V H : Subgroup G) (h : G)

/-- The original residual acts on the actual ambient pair core by conjugation. -/
def pairResidualAction (hn : outsideResidual H ≤ normalizer (pairCore V H h : Set G)) :
    outsideResidual H →* MulAut (pairCore V H h) :=
  (pairCore V H h).normalizerMonoidHom.comp (inclusion hn)

/-- Output specification for actual natural summands, over an independent marked field. -/
structure PairNaturalMarking (F : BinaryField) where
  multiplicity : ℕ
  positive : 0 < multiplicity
  normalizes : outsideResidual H ≤ normalizer (pairCore V H h : Set G)
  quotientEquiv : (outsideResidual H ⧸ pCore 2 (outsideResidual H)) ≃*
    SpecialLinearGroup (Fin 2) F.Carrier
  coordinates : pairCore V H h ≃* Multiplicative (Fin multiplicity → Fin 2 → F.Carrier)
  intertwines : ∀ (k : outsideResidual H) (v : pairCore V H h) (i : Fin multiplicity),
    (coordinates (pairResidualAction V H h normalizes k v)).toAdd i =
      mulVec (quotientEquiv (QuotientGroup.mk' _ k)).val ((coordinates v).toAdd i)

variable {V H h} {F : BinaryField}

/-- Two opposite transvections generate every natural summand by displacements. -/
theorem PairNaturalMarking.commutator_eq (c : PairNaturalMarking V H h F) :
    ⁅pairCore V H h, outsideResidual H⁆ = pairCore V H h := by
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp c.normalizes)
  have hdisplacement (g : SpecialLinearGroup (Fin 2) F.Carrier)
      (w : Fin c.multiplicity → Fin 2 → F.Carrier) :
      ∃ x : pairCore V H h, (x : G) ∈ ⁅pairCore V H h, outsideResidual H⁆ ∧
        ∀ i, (c.coordinates x).toAdd i = mulVec g.val (w i) - w i := by
    obtain ⟨k,hk⟩ := c.quotientEquiv.surjective g
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (outsideResidual H)) k
    let v := c.coordinates.symm (Multiplicative.ofAdd w)
    let x := pairResidualAction V H h c.normalizes k v * v⁻¹
    refine ⟨x,?_,?_⟩
    · change ⁅(k : G), (v : G)⁆ ∈ ⁅pairCore V H h, outsideResidual H⁆
      rw [commutator_comm]
      exact commutator_mem_commutator k.property v.property
    · intro i
      have hev : c.coordinates v = Multiplicative.ofAdd w := c.coordinates.apply_symm_apply _
      have hem : c.coordinates x = c.coordinates (pairResidualAction V H h c.normalizes k v) *
          (c.coordinates v)⁻¹ := by
        dsimp only [x]
        rw [map_mul, map_inv]
      rw [hem]
      change (c.coordinates (pairResidualAction V H h c.normalizes k v)).toAdd i +
        -(c.coordinates v).toAdd i = _
      rw [c.intertwines, hk, hev]
      simp only [toAdd_ofAdd, sub_eq_add_neg]
  intro a ha
  let aP : pairCore V H h := ⟨a,ha⟩
  let w := (c.coordinates aP).toAdd
  let u : SpecialLinearGroup (Fin 2) F.Carrier :=
    SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1
  let l : SpecialLinearGroup (Fin 2) F.Carrier :=
    SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) 1
  obtain ⟨x,hx,hxc⟩ := hdisplacement u (fun i => ![0,w i 0])
  obtain ⟨y,hy,hyc⟩ := hdisplacement l (fun i => ![w i 1,0])
  have hxy : x * y = aP := by
    apply c.coordinates.injective
    apply Multiplicative.toAdd.injective
    funext i j
    rw [map_mul]
    change (c.coordinates x).toAdd i j + (c.coordinates y).toAdd i j = w i j
    rw [hxc,hyc]
    fin_cases j <;>
      simp [u,l, SpecialLinearGroup.transvection_coe,
        mulVec, dotProduct, Fin.sum_univ_two]
  have he : (x : G) * (y : G) = a := congrArg Subtype.val hxy
  exact he ▸ (⁅pairCore V H h, outsideResidual H⁆).mul_mem hx hy

/-- Cardinality follows from the actual coordinate isomorphism. -/
theorem PairNaturalMarking.card (c : PairNaturalMarking V H h F) :
    Nat.card (pairCore V H h) = (2 ^ F.degree) ^ (2 * c.multiplicity) := by
  rw [Nat.card_congr c.coordinates.toEquiv]
  have he : Nat.card (Multiplicative (Fin c.multiplicity → Fin 2 → F.Carrier)) =
      Nat.card (Fin c.multiplicity → Fin 2 → F.Carrier) :=
    Nat.card_congr Multiplicative.toAdd
  rw [he, Nat.card_fun, Nat.card_fun, Nat.card_fin, Nat.card_fin, F.card_eq, ← pow_mul]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
