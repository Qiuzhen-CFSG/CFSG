module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.OuterReselection.Fusion
import all CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit.MonomialWitness.SylowPlacement
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.NormalizerCertificate

/-!
# The first conjugacy family's weak closure in the fixed five-prime Sylow

The checked coordinate census and ambient fusion witnesses reduce the original
family to candidates 0, 1 and 5. To exclude the second fusion representative,
first absorb the graph factor of an ambient conjugator into the original actor.
For the resulting special-linear conjugator, its first row is a simultaneous
eigenvector for the two diagonal signs. It has at most one nonzero coordinate,
so its squared norm is a square. The second representative instead requires the
first diagonal entry of the conjugated graph matrix to be 2 or 3, both nonsquares
in ZMod 5. Small finite field certificates check these scalar implications.

The three remaining coordinate lists have even first torus exponent. Their
words therefore lie in the join of the original and moved actors. The existing
simultaneous-placement proof supplies the reverse weak-closure inclusion and
places this exact Sylow in the monomial overgroup. These are precisely the
inputs to the parent's `monomialJoin_of_weakClosure` theorem.

The intentional `import all` adapts the original private Sylow placement and
graph-extension decomposition, as in `OuterReselection.Coordinates`; no existing
public boundary is changed.

Source: Aschbacher--Smith E.1.5 and E.1.14(7), printed pp.210 and 214, and the
literal matrix actor in `FiveSourceAudit.Model`. The coordinate census and
conjugators are proved in `OuterReselection.Fusion`. Matrix carriers retain
their imported ATLAS attribution and `LICENSES/ATLAS.txt`.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups Matrix Pointwise
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.NormalizerCertificate.WeakClosure
open FiveSourceAudit OuterReselection OuterReselection.Fusion
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem inner_mem (m : SL(3, ZMod 5)) : innerSL m ∈ FiveSourceAudit.inner := by
  rw [← innerSL_range]
  exact ⟨m, rfl⟩

private theorem word_decode (a : C) (m : SL(3, ZMod 5)) (b : Bool)
    (h : word a = innerSL m * (if b then graphElement else 1)) :
    a.2 = b ∧ mat a.1 = m := by
  obtain ⟨l,c⟩ := a
  cases c <;> cases b
  · simp only [word, Bool.false_eq_true, ↓reduceIte, mul_one] at h
    exact ⟨rfl, innerSL_injective h⟩
  · simp only [word, Bool.false_eq_true, ↓reduceIte, mul_one] at h
    have ht := FiveSourceAudit.inner.mul_mem (FiveSourceAudit.inner.inv_mem (inner_mem m))
      (h ▸ inner_mem (mat l))
    simp only [inv_mul_cancel_left] at ht
    exact (graphElement_not_mem_inner ht).elim
  · simp only [word, Bool.false_eq_true, ↓reduceIte, mul_one] at h
    have ht := FiveSourceAudit.inner.mul_mem (FiveSourceAudit.inner.inv_mem (inner_mem (mat l)))
      (h.symm ▸ inner_mem m)
    simp only [inv_mul_cancel_left] at ht
    exact (graphElement_not_mem_inner ht).elim
  · simp only [word, ↓reduceIte] at h
    exact ⟨rfl, innerSL_injective (mul_right_cancel h)⟩

private theorem representative_decode (m : SL(3, ZMod 5)) (b : Bool)
    (h : innerSL m * (if b then graphElement else 1) ∈ representative) :
    ∃ a ∈ codes 4, a.2 = b ∧ mat a.1 = m := by
  rw [← candidate_four] at h
  obtain ⟨a, ha, he⟩ := h
  exact ⟨a, ha, word_decode a m b he⟩

private theorem representative_row : ∀ a ∈ codes 4,
    (mat a.1).val 0 1 = 0 ∧ (mat a.1).val 0 2 = 0 := by decide +kernel

private theorem representative_outer_row : ∀ a ∈ codes 4, a.2 = true →
    (mat a.1).val 0 0 = 2 ∨ (mat a.1).val 0 0 = 3 := by decide +kernel

private def RowSquare (x y z : ZMod 5) : Prop := ∀ α β : ZMod 5,
    -x = α * x → -y = α * y → z = α * z →
    x = β * x → -y = β * y → -z = β * z →
    x * x + y * y + z * z ≠ 2 ∧ x * x + y * y + z * z ≠ 3

private instance (x y z : ZMod 5) : Decidable (RowSquare x y z) := by
  unfold RowSquare
  infer_instance

private theorem row_square : ∀ x y z : ZMod 5, RowSquare x y z := by decide +kernel

private theorem conjugate_inner (g m : SL(3, ZMod 5)) :
    MulAut.conj (innerSL g) (innerSL m) = innerSL (g * m * g⁻¹) := by
  simp only [MulAut.conj_apply, map_mul, map_inv]

private theorem conjugate_graph (g : SL(3, ZMod 5)) :
    MulAut.conj (innerSL g) graphElement = innerSL (g * SpecialLinearGroup.transpose g) * graphElement := by
  have ht := (Matrix.PSL3.OuterSolvable.graphSL (ZMod 5)).map_inv g
  change (SpecialLinearGroup.transpose g⁻¹)⁻¹ = ((SpecialLinearGroup.transpose g)⁻¹)⁻¹ at ht
  simp only [inv_inv] at ht
  change innerSL g * graphElement * (innerSL g)⁻¹ = _
  rw [← map_inv, mul_assoc, graph_innerSL, ht, ← mul_assoc, ← map_mul]

private theorem inner_conjugate_ne_representative (g : SL(3, ZMod 5))
    (he : actor.map (MulAut.conj (innerSL g)).toMonoidHom = representative) : False := by
  have hm {x : Model} (hx : x ∈ actor) : MulAut.conj (innerSL g) x ∈ representative :=
    he ▸ mem_map.mpr ⟨x, hx, rfl⟩
  have hr := hm (show innerSL (SL3.standardInvolution (ZMod 5)) ∈ actor from subset_closure (by simp))
  have hs := hm (show innerSL secondDiagonal ∈ actor from subset_closure (by simp))
  have ht := hm (show graphElement ∈ actor from subset_closure (by simp))
  rw [conjugate_inner] at hr hs
  rw [conjugate_graph] at ht
  obtain ⟨a, ha, _, hea⟩ :=
    representative_decode (g * SL3.standardInvolution (ZMod 5) * g⁻¹) false
      (by simpa only [Bool.false_eq_true, if_false, mul_one] using hr)
  obtain ⟨b, hb, _, heb⟩ :=
    representative_decode (g * secondDiagonal * g⁻¹) false
      (by simpa only [Bool.false_eq_true, if_false, mul_one] using hs)
  obtain ⟨c, hc, hct, hec⟩ :=
    representative_decode (g * SpecialLinearGroup.transpose g) true ht
  have hra : g * SL3.standardInvolution (ZMod 5) = mat a.1 * g := by
    rw [hea, mul_assoc, inv_mul_cancel, mul_one]
  have hrb : g * secondDiagonal = mat b.1 * g := by
    rw [heb, mul_assoc, inv_mul_cancel, mul_one]
  have hara := representative_row a ha
  have harb := representative_row b hb
  have h₁ (j : Fin 3) := congrArg (fun m : SL(3, ZMod 5) => m.val 0 j) hra
  have h₂ (j : Fin 3) := congrArg (fun m : SL(3, ZMod 5) => m.val 0 j) hrb
  change ∀ j : Fin 3, (g.val * (SL3.standardInvolution (ZMod 5)).val) 0 j =
    ((mat a.1).val * g.val) 0 j at h₁
  change ∀ j : Fin 3, (g.val * secondDiagonal.val) 0 j =
    ((mat b.1).val * g.val) 0 j at h₂
  simp only [Matrix.mul_apply, Fin.sum_univ_three,
    hara.1, hara.2, zero_mul, add_zero] at h₁
  simp only [Matrix.mul_apply, Fin.sum_univ_three,
    harb.1, harb.2, zero_mul, add_zero] at h₂
  have hh := row_square (g.val 0 0) (g.val 0 1) (g.val 0 2)
    ((mat a.1).val 0 0) ((mat b.1).val 0 0)
    (by simpa [SL3.standardInvolution] using h₁ 0)
    (by simpa [SL3.standardInvolution] using h₁ 1)
    (by simpa [SL3.standardInvolution] using h₁ 2)
    (by simpa [secondDiagonal] using h₂ 0)
    (by simpa [secondDiagonal] using h₂ 1)
    (by simpa [secondDiagonal] using h₂ 2)
  have hnorm := congrArg (fun m : SL(3, ZMod 5) => m.val 0 0) hec
  change (mat c.1).val 0 0 = (g.val * g.val.transpose) 0 0 at hnorm
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] at hnorm
  obtain hh' | hh' := representative_outer_row c hc hct
  · exact hh.1 (hnorm.symm.trans hh')
  · exact hh.2 (hnorm.symm.trans hh')

private theorem family_inner_conjugate {A : Subgroup Model} (hA : A ∈ family) :
    ∃ g : SL(3, ZMod 5), A = actor.map (MulAut.conj (innerSL g)).toMonoidHom := by
  obtain ⟨g, rfl⟩ := hA
  let : FiveSourceAudit.inner.Normal := inferInstanceAs
    (Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure.innerPart (ZMod 5)).Normal
  have hg : g ∈ FiveSourceAudit.inner ⊔ zpowers graphElement :=
    FiveSourceAudit.inner_sup_graph ▸ mem_top g
  obtain ⟨i, hi, z, hz, rfl⟩ := mem_sup_of_normal_left.mp hg
  rw [← innerSL_range] at hi
  obtain ⟨m, rfl⟩ := hi
  have hza : z ∈ actor := (zpowers_le.mpr (subset_closure (by simp))) hz
  have hzmap : actor.map (MulAut.conj z).toMonoidHom = actor :=
    conj_smul_eq_self_of_mem hza
  refine ⟨m, ?_⟩
  have he : (MulAut.conj (innerSL m * z)).toMonoidHom =
      (MulAut.conj (innerSL m)).toMonoidHom.comp (MulAut.conj z).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, ← Subgroup.map_map, hzmap]

/-- The second fusion target is outside the literal original conjugacy family. -/
theorem representative_not_mem_family : representative ∉ family := by
  intro h
  obtain ⟨g, hg⟩ := family_inner_conjugate h
  exact inner_conjugate_ne_representative g hg.symm

private theorem first_mem_join : innerSL (SL3.standardInvolution (ZMod 5)) ∈ actorJoin :=
  mem_sup_left (subset_closure (by simp))
private theorem graph_mem_join : graphElement ∈ actorJoin :=
  mem_sup_left (subset_closure (by simp))
private theorem diagonal_mem_join : innerSL witnessDiagonal ∈ actorJoin := by
  have ht : innerSL witnessDiagonal * graphElement ∈ actorJoin :=
    mem_sup_right ⟨graphElement, subset_closure (by simp), moved_graph⟩
  exact (actorJoin.mul_mem_cancel_right graph_mem_join).mp ht
private theorem signedSwap_mem_join : innerSL signedSwap ∈ actorJoin := by
  have he : signedSwap = witnessDiagonal⁻¹ * witnessSwap := by decide +kernel
  rw [he, map_mul, map_inv]
  exact actorJoin.mul_mem (actorJoin.inv_mem diagonal_mem_join) (mem_sup_right swap_mem_movedActor)

private theorem even_matrix : ∀ a : C, a.1.1.1 = 0 ∨ a.1.1.1 = 2 →
    mat a.1 = SL3.standardInvolution (ZMod 5) ^ (a.1.1.1.val / 2) *
      witnessDiagonal ^ a.1.1.2.val * (if a.1.2 then signedSwap else 1) := by decide +kernel

private theorem even_word_mem_join (a : C) (ha : a.1.1.1 = 0 ∨ a.1.1.1 = 2) :
    word a ∈ actorJoin := by
  rw [word, even_matrix a ha, map_mul, map_mul, map_pow, map_pow]
  apply actorJoin.mul_mem
  · apply actorJoin.mul_mem
    · exact actorJoin.mul_mem (actorJoin.pow_mem first_mem_join _)
        (actorJoin.pow_mem diagonal_mem_join _)
    · split
      · exact signedSwap_mem_join
      · simp
  · split
    · exact graph_mem_join
    · exact actorJoin.one_mem

private theorem first_codes_even : ∀ i : Fin 8, i = 0 ∨ i = 1 ∨ i = 5 →
    ∀ a ∈ codes i, a.1.1.1 = 0 ∨ a.1.1.1 = 2 := by decide +kernel

/-- Every member of the original family lying in the fixed Sylow lies in
its two-actor join. The five other candidates are excluded by actual fusion
and the square-row obstruction. -/
theorem family_le_actorJoin {A : Subgroup Model} (hA : A ∈ family)
    (hAS : A ≤ (standardSylow : Subgroup Model)) : A ≤ actorJoin := by
  have hc : Nat.card A = 8 := by
    obtain ⟨g, rfl⟩ := hA
    rw [card_map_of_injective (MulAut.conj g).injective, card_actor]
  obtain ⟨i, rfl⟩ := candidate_of_census census A (family_elementary.1 A hA) hAS hc
  have hi : i = 0 ∨ i = 1 ∨ i = 5 := by
    by_contra hnot
    have hf := family_elementary.2 (innerSL (witness i)) _ hA
    rw [candidate_conjugate, target, if_neg hnot, candidate_four] at hf
    exact representative_not_mem_family hf
  rintro _ ⟨a, ha, rfl⟩
  exact even_word_mem_join a (first_codes_even i hi a ha)

/-- The fixed coordinate Sylow is contained in the literal monomial overgroup. -/
theorem standardSylow_le_monomialOvergroup :
    (standardSylow : Subgroup Model) ≤ monomialOvergroup := by
  rw [standardSylow_coe]
  exact FiveSourceAudit.commonTwo_le_monomial

/-- Exact weak closure of the original conjugacy family at the fixed Sylow. -/
theorem weakClosure_standardSylow :
    weakClosure (standardSylow : Subgroup Model) family = actorJoin := by
  apply le_antisymm
  · apply sSup_le
    rintro A ⟨hA, hAS⟩
    exact family_le_actorJoin hA hAS
  · exact actorJoin_le_weakClosure standardSylow
      (by rw [standardSylow_coe]; exact FiveSourceAudit.actor_le_commonTwo)
      (by rw [standardSylow_coe]; exact FiveSourceAudit.movedActor_le_commonTwo)

/-- The exact input needed by the parent's monomial/normalizer assembly. -/
theorem exists_sylow_weakClosure : ∃ S : Sylow 2 Model,
    (S : Subgroup Model) ≤ monomialOvergroup ∧
      weakClosure (S : Subgroup Model) family = actorJoin :=
  ⟨standardSylow, standardSylow_le_monomialOvergroup, weakClosure_standardSylow⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.NormalizerCertificate.WeakClosure
