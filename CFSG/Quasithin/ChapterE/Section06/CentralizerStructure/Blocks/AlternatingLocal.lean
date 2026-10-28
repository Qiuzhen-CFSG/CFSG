module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Models
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.AlternatingLocal.A3Action
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.AlternatingLocal.A5Natural
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.AlternatingLocal.A5Quotient
public import CFSG.Quasithin.ChapterC.Section01.BlockDefs
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Alternating-block indices, fixed points, and Sylow-center calculations

A point-stabilizer Borel has index n by transitivity of A_n on its n letters.
The full natural-module identification of U(L) in C.1.13(c) implies
U(L) ∩ Z(L) = 1: a fixed core vector has constant coordinates, and an
odd-degree constant vector of even weight is zero. This identification is
an explicit earlier-source input; it is stronger than the defining model
of U(L)/C_U(L) and must be constructed by the C.1.13 owner.

For A₅, the natural action is faithful and its Sylow-fixed vectors have
order two. Combining these concrete calculations with the natural lift and
O₂(L) = U(L) Z(L) proves that the intrinsic omega-center quotient has order
two. The theorem below discharges the model and disjointness premises of
`A5Quotient`; only the stated C.1.13 inputs remain for the source owner.
In particular, the possible central extension is retained.

There is an obstruction to the requested uniform intrinsic Sylow-center
calculation. C.1.13(c) identifies an A₃-block with A₄. Its Sylow two-subgroup
is the abelian four-group, while Z(A₄) = 1. Consequently
|Ω₁(Z(S))/(Ω₁(Z(S)) ∩ Z(L))| = 4, not 2. Both the concrete calculation and
its transport along L ≃ A₄ are proved below. Thus the printed intermediate
claim m_i = 1 in E.6.7 cannot be used for A₃ with that intrinsic definition
of Z_i. This does not refute E.6.7 under its additional ambient hypotheses;
the publicly imported `A3Action` module proves the ambient action bound
using the additional commutator and central-Sylow hypotheses.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), C.1.13(c), printed pp.124–125; E.6.7 and E.6.10,
printed pp.246 and 248–249. In the last paragraph of E.6.10's proof the
fixed-point-free layer is U(L_i) = [O₂(L_i),L_i], rather than the printed
O₂(L_i); the central extension permitted in C.1.13(c) must be retained.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.AlternatingLocal

open Subgroup Theory.GroupTheory ChapterC

/-- The preimage of a point stabilizer has index the permutation degree.
The Sylow-containment condition in the application is unnecessary for this index. -/
theorem borel_index {L : Type*} [Group L] {B : Subgroup L} {n : ℕ}
    (hn : 3 ≤ n) (hB : AlternatingBlockBorel L B n) : B.index = n := by
  obtain ⟨e, i, rfl⟩ := hB
  rw [Subgroup.index_comap_of_surjective _
    (e.surjective.comp (QuotientGroup.mk'_surjective _))]
  let := alternatingGroup.isPretransitive_of_three_le_card (Fin n) (by simpa using hn)
  exact (MulAction.index_stabilizer_of_transitive (alternatingGroup (Fin n)) i).trans
    (Nat.card_fin n)

private theorem a4_omega_center_eq_sylow (S : Sylow 2 (alternatingGroup (Fin 4))) :
    Stellmacher.omegaOneCenterAmbient (S : Subgroup (alternatingGroup (Fin 4))) = S := by
  rw [alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (Nat.card_fin 4) S]
  let K := alternatingGroup.kleinFour (Fin 4)
  let : IsKleinFour K := alternatingGroup.kleinFour_isKleinFour (Nat.card_fin 4)
  let : IsMulCommutative K := IsKleinFour.isMulCommutative
  ext x
  rw [Stellmacher.mem_omegaOneCenterAmbient_iff]
  constructor
  · exact fun h => h.1
  · intro hx
    refine ⟨hx, ?_, ?_⟩
    · have hp := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : K)
      rw [IsKleinFour.exponent_two] at hp
      exact congrArg Subtype.val hp
    · intro y hy
      exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : K) ⟨x, hx⟩)

/-- In the actual A₄ model from C.1.13(c), the intrinsic omega-center
quotient has order four. This diagnoses the A₃ step in the printed E.6.7 proof. -/
theorem a4_omega_center_quotient_card (S : Sylow 2 (alternatingGroup (Fin 4))) :
    let Z := Stellmacher.omegaOneCenterAmbient (S : Subgroup (alternatingGroup (Fin 4)))
    Nat.card (Z ⧸ (center (alternatingGroup (Fin 4))).subgroupOf Z) = 4 := by
  dsimp only
  rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 4)),
    bot_subgroupOf]
  exact (Nat.card_congr QuotientGroup.quotientBot.toEquiv).trans
    (by
      rw [a4_omega_center_eq_sylow]
      exact alternatingGroup.card_two_sylow_of_card_eq_four (Nat.card_fin 4) S)

private theorem natural_fixed_eq_zero {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (v : BinaryPermutation.natural (Fin n))
    (hv : ∀ a : alternatingGroup (Fin n),
      BinaryPermutation.naturalRepresentation (Fin n) a.val v = v) : v = 0 := by
  let := alternatingGroup.isPretransitive_of_three_le_card (Fin n) (by simpa using hn)
  have ho : Odd (Fintype.card (Fin n)) := by simpa using hodd
  let e := BinaryPermutation.coreEquivNatural (Fin n) ho
  obtain ⟨w, rfl⟩ := e.surjective v
  have hw (a : alternatingGroup (Fin n)) :
      BinaryPermutation.coreRepresentation (Fin n) a.val w = w := by
    apply e.injective
    exact (BinaryPermutation.coreEquivNatural_equivariant (Fin n) ho a.val w).trans (hv a)
  let i : Fin n := ⟨0, by omega⟩
  have hconst : ∀ j, w.val j = w.val i := by
    intro j
    obtain ⟨a, ha⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin n)) i j
    have he := congrArg (fun u : BinaryPermutation.core (Fin n) => u.val j) (hw a)
    change w.val (a.val.symm j) = w.val j at he
    have hij : a.val i = j := ha
    rw [← hij, Equiv.symm_apply_apply] at he
    simpa only [hij] using he.symm
  have hc : w.val ∈ BinaryPermutation.constants (Fin n) := by
    apply Submodule.mem_span_singleton.mpr
    refine ⟨w.val i, ?_⟩
    ext j
    simpa [BinaryPermutation.allOne] using (hconst j).symm
  have hz : w.val = 0 :=
    Submodule.disjoint_def.mp (BinaryPermutation.core_isCompl_constants (Fin n) ho).disjoint
      w.val w.property hc
  have hw0 : w = 0 := Subtype.ext hz
  rw [hw0, map_zero]


/-- The full natural-module identification of C.1.13(c) makes U(L) disjoint
from Z(L). The input concerns U itself, with its literal conjugation action;
the defining identification of U/C_U(L) alone does not supply this input.
No assertion that O₂(L) is centerless is made, so the A₅ central extension
allowed in C.1.13(c) is retained. -/
theorem blockU_inf_center_eq_bot_of_natural_lift {L : Type*} [Group L] {n : ℕ}
    (h : IsAlternatingBlock L n) (hn : n = 3 ∨ n = 5)
    (eQ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin n))
    (eU : blockU L ≃* Multiplicative (BinaryPermutation.natural (Fin n)))
    (he : ∀ (l : L) (u : blockU L),
      Multiplicative.toAdd (eU (blockConjugate L l u)) =
        BinaryPermutation.naturalRepresentation (Fin n)
          (eQ (QuotientGroup.mk' (pCore 2 L) l)).val
          (Multiplicative.toAdd (eU u))) :
    blockU L ⊓ center L = ⊥ := by
  apply le_bot_iff.mp
  rintro x ⟨hxU, hxC⟩
  let u : blockU L := ⟨x, hxU⟩
  have hconj (l : L) : blockConjugate L l u = u := by
    apply Subtype.ext
    change l * x * l⁻¹ = x
    rw [mem_center_iff.mp hxC l, mul_inv_cancel_right]
  have ho : Odd n := by rcases hn with rfl | rfl <;> decide
  have hz := natural_fixed_eq_zero h.1 ho (Multiplicative.toAdd (eU u)) (by
    intro a
    obtain ⟨l, rfl⟩ := eQ.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) a
    dsimp only [Function.comp_apply]
    rw [← he, hconj])
  have hu : u = 1 := eU.injective (by
    rw [map_one]
    exact hz)
  exact congrArg Subtype.val hu


/-- The intrinsic A₅-block omega-center quotient has order two, retaining
the central extension allowed by C.1.13(c). The only additional inputs are
the full equivariant natural lift and core decomposition supplied by that
earlier source result. Faithfulness, the Sylow fixed-vector count, and
disjointness from the center are proved here, rather than assumed. -/
theorem a5_omega_center_quotient_card {L : Type*} [Group L] [Finite L]
    (h : IsAlternatingBlock L 5)
    (eQ : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (eU : blockU L ≃* Multiplicative (BinaryPermutation.natural (Fin 5)))
    (he : ∀ (l : L) (u : blockU L),
      Multiplicative.toAdd (eU (blockConjugate L l u)) =
        BinaryPermutation.naturalRepresentation (Fin 5)
          (eQ (QuotientGroup.mk' (pCore 2 L) l)).val
          (Multiplicative.toAdd (eU u)))
    (hcore : pCore 2 L = blockU L ⊔ center L)
    (S : Sylow 2 L) :
    let Z := Stellmacher.omegaOneCenterAmbient (S : Subgroup L)
    Nat.card (Z ⧸ (center L).subgroupOf Z) = 2 := by
  exact a5_omega_center_quotient_card_of_natural_lift h eQ eU he hcore
    (blockU_inf_center_eq_bot_of_natural_lift h (Or.inr rfl) eQ eU he)
    a5_natural_faithful a5_natural_sylow_fixed_card S


/-- Transport the order-four calculation through the exact A₃-block
isomorphism in C.1.13(c), kept as an explicit upstream input. -/
theorem omega_center_quotient_card_of_equiv_a4 {L : Type*} [Group L] [Finite L]
    (e : L ≃* alternatingGroup (Fin 4)) (S : Sylow 2 L) :
    let Z := Stellmacher.omegaOneCenterAmbient (S : Subgroup L)
    Nat.card (Z ⧸ (center L).subgroupOf Z) = 4 := by
  have hc : center L = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have he : e x ∈ center (alternatingGroup (Fin 4)) := by
      rw [mem_center_iff]
      intro a
      obtain ⟨l, rfl⟩ := e.surjective a
      simpa only [map_mul] using congrArg e (mem_center_iff.mp hx l)
    rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at he
    exact e.injective (he.trans (map_one e).symm)
  dsimp only
  rw [hc, bot_subgroupOf]
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hp : (P : Subgroup (alternatingGroup (Fin 4))) =
      (S : Subgroup L).map e.toMonoidHom := Sylow.coe_mapSurjective _ _
  calc
    _ = Nat.card (Stellmacher.omegaOneCenterAmbient (S : Subgroup L)) :=
      Nat.card_congr QuotientGroup.quotientBot.toEquiv
    _ = Nat.card ((Stellmacher.omegaOneCenterAmbient (S : Subgroup L)).map e.toMonoidHom) :=
      Nat.card_congr ((Stellmacher.omegaOneCenterAmbient (S : Subgroup L)).equivMapOfInjective
        e.toMonoidHom e.injective).toEquiv
    _ = Nat.card (Stellmacher.omegaOneCenterAmbient (P : Subgroup (alternatingGroup (Fin 4)))) := by
      rw [hp, Stellmacher.omegaOneCenterAmbient_map_injective e.toMonoidHom e.injective]
    _ = 4 := by
      rw [a4_omega_center_eq_sylow]
      exact alternatingGroup.card_two_sylow_of_card_eq_four (Nat.card_fin 4) P

/-- The order-two intrinsic claim cannot be assembled from the A₃
isomorphism asserted by C.1.13(c). -/
theorem omega_center_quotient_ne_two_of_equiv_a4 {L : Type*} [Group L] [Finite L]
    (e : L ≃* alternatingGroup (Fin 4)) (S : Sylow 2 L) :
    let Z := Stellmacher.omegaOneCenterAmbient (S : Subgroup L)
    Nat.card (Z ⧸ (center L).subgroupOf Z) ≠ 2 := by
  dsimp only
  rw [omega_center_quotient_card_of_equiv_a4 e S]
  decide

end CFSG.Quasithin.ChapterE.Section06.AlternatingLocal
