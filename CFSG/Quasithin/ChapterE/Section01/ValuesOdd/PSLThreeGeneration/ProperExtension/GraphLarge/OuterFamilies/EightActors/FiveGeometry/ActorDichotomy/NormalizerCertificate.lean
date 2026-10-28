module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveGeometry.ActorDichotomy.Families
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.RootGeneration

/-!
# Explicit generators for the five-prime weak-closure normalizer

The two block matrices below normalize the join of the original actor and its
specified conjugate. Their actions are checked on five generators, using the
literal faithful matrix embedding and inverse-transpose action. Together with
the monomial coordinate cycle they produce an elementary matrix. Conjugating
by that cycle and inverse transpose, and taking powers, supplies all elementary
matrices; elementary generation then gives the whole graph extension.

The remaining finite census is isolated explicitly: the actor join must equal
the full conjugacy-family weak closure at a Sylow in the monomial overgroup.
The conditional consumer uses precisely that equality and does not assert the
unproved census or an exact order for the normalizer.

Source: the matrix diagnostic in `FiveSourceAudit/source/README.md` and
Aschbacher--Smith E.1.5 and E.1.14(7), printed pp.210 and 214. The elementary
generation theorem retains its ATLAS attribution and `LICENSES/ATLAS.txt`.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.NormalizerCertificate
open FiveSourceAudit
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The first off-monomial block matrix from the diagnostic. -/
@[expose] def firstMatrix : SL(3, ZMod 5) :=
  ⟨!![3,0,0;0,4,2;0,2,4], by decide +kernel⟩

/-- The second off-monomial block matrix from the diagnostic. -/
@[expose] def secondMatrix : SL(3, ZMod 5) :=
  ⟨!![4,0,0;0,1,1;0,3,2], by decide +kernel⟩

/-- The candidate weak closure, retaining the full two known actors. -/
@[expose] noncomputable def actorJoin : Subgroup Model := actor ⊔ movedActor

private theorem firstSign_mem : innerSL (SL3.standardInvolution (ZMod 5)) ∈ actorJoin :=
  mem_sup_left (subset_closure (by simp))
private theorem secondSign_mem : innerSL secondDiagonal ∈ actorJoin :=
  mem_sup_left (subset_closure (by simp))
private theorem graph_mem : graphElement ∈ actorJoin :=
  mem_sup_left (subset_closure (by simp))
private theorem swap_mem : innerSL witnessSwap ∈ actorJoin :=
  mem_sup_right swap_mem_movedActor
private theorem diagonal_mem : innerSL witnessDiagonal ∈ actorJoin := by
  have h : innerSL witnessDiagonal * graphElement ∈ actorJoin := by
    apply mem_sup_right
    exact ⟨graphElement, subset_closure (by simp), moved_graph⟩
  exact (actorJoin.mul_mem_cancel_right graph_mem).mp h

private theorem actorJoin_le_of_generators {P : Subgroup Model}
    (hr : innerSL (SL3.standardInvolution (ZMod 5)) ∈ P)
    (hs : innerSL secondDiagonal ∈ P) (hu : innerSL witnessSwap ∈ P)
    (hd : innerSL witnessDiagonal ∈ P) (hg : graphElement ∈ P) : actorJoin ≤ P := by
  apply sup_le
  · rw [actor, closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hr
    · exact hs
    · exact hg
  · exact movedActor_le_of_generators hu hs (P.mul_mem hd hg)

private theorem conj_inner (n x : SL(3, ZMod 5)) :
    MulAut.conj (innerSL n) (innerSL x) = innerSL (n * x * n⁻¹) := by
  simp only [MulAut.conj_apply, map_mul, map_inv]

private theorem conj_graph (n : SL(3, ZMod 5)) :
    MulAut.conj (innerSL n) graphElement =
      innerSL (n * (SpecialLinearGroup.transpose n⁻¹)⁻¹) * graphElement := by
  change innerSL n * graphElement * (innerSL n)⁻¹ = _
  rw [← map_inv, mul_assoc, graph_innerSL, ← mul_assoc, ← map_mul]

private theorem normalizes_of_generator_images (n : SL(3, ZMod 5))
    (hr : innerSL (n * SL3.standardInvolution (ZMod 5) * n⁻¹) ∈ actorJoin)
    (hs : innerSL (n * secondDiagonal * n⁻¹) ∈ actorJoin)
    (hu : innerSL (n * witnessSwap * n⁻¹) ∈ actorJoin)
    (hd : innerSL (n * witnessDiagonal * n⁻¹) ∈ actorJoin)
    (hg : innerSL (n * (SpecialLinearGroup.transpose n⁻¹)⁻¹) ∈ actorJoin) :
    innerSL n ∈ normalizer (actorJoin : Set Model) := by
  have h : actorJoin ≤ actorJoin.comap (MulAut.conj (innerSL n)).toMonoidHom := by
    apply actorJoin_le_of_generators
    · simpa only [mem_comap, MulEquiv.coe_toMonoidHom, conj_inner] using hr
    · simpa only [mem_comap, MulEquiv.coe_toMonoidHom, conj_inner] using hs
    · simpa only [mem_comap, MulEquiv.coe_toMonoidHom, conj_inner] using hu
    · simpa only [mem_comap, MulEquiv.coe_toMonoidHom, conj_inner] using hd
    · simpa only [mem_comap, MulEquiv.coe_toMonoidHom, conj_graph] using actorJoin.mul_mem hg graph_mem
  exact mem_normalizer_fintype (fun x hx => h hx)

/-- The first block matrix normalizes the actual join of the two actors. -/
theorem first_normalizes_actorJoin :
    innerSL firstMatrix ∈ normalizer (actorJoin : Set Model) := by
  apply normalizes_of_generator_images
  · have he : firstMatrix * SL3.standardInvolution (ZMod 5) * firstMatrix⁻¹ =
        secondDiagonal * witnessSwap := by decide +kernel
    rw [he, map_mul]
    exact actorJoin.mul_mem secondSign_mem swap_mem
  · have he : firstMatrix * secondDiagonal * firstMatrix⁻¹ = secondDiagonal := by decide +kernel
    rw [he]
    exact secondSign_mem
  · have he : firstMatrix * witnessSwap * firstMatrix⁻¹ = SL3.standardInvolution (ZMod 5) := by decide +kernel
    rw [he]
    exact firstSign_mem
  · have he : firstMatrix * witnessDiagonal * firstMatrix⁻¹ =
        SL3.standardInvolution (ZMod 5) * witnessSwap * witnessDiagonal := by decide +kernel
    rw [he, map_mul, map_mul]
    exact actorJoin.mul_mem (actorJoin.mul_mem firstSign_mem swap_mem) diagonal_mem
  · have he : firstMatrix * (SpecialLinearGroup.transpose firstMatrix⁻¹)⁻¹ =
        witnessDiagonal * witnessSwap := by decide +kernel
    rw [he, map_mul]
    exact actorJoin.mul_mem diagonal_mem swap_mem

/-- The second block matrix normalizes the same actual actor join. -/
theorem second_normalizes_actorJoin :
    innerSL secondMatrix ∈ normalizer (actorJoin : Set Model) := by
  apply normalizes_of_generator_images
  · have he : secondMatrix * SL3.standardInvolution (ZMod 5) * secondMatrix⁻¹ =
        secondDiagonal * witnessSwap := by decide +kernel
    rw [he, map_mul]
    exact actorJoin.mul_mem secondSign_mem swap_mem
  · have he : secondMatrix * secondDiagonal * secondMatrix⁻¹ = secondDiagonal := by decide +kernel
    rw [he]
    exact secondSign_mem
  · have he : secondMatrix * witnessSwap * secondMatrix⁻¹ = witnessDiagonal * witnessSwap := by decide +kernel
    rw [he, map_mul]
    exact actorJoin.mul_mem diagonal_mem swap_mem
  · have he : secondMatrix * witnessDiagonal * secondMatrix⁻¹ =
        SL3.standardInvolution (ZMod 5) * witnessSwap * witnessDiagonal := by decide +kernel
    rw [he, map_mul, map_mul]
    exact actorJoin.mul_mem (actorJoin.mul_mem firstSign_mem swap_mem) diagonal_mem
  · have he : secondMatrix * (SpecialLinearGroup.transpose secondMatrix⁻¹)⁻¹ =
        secondDiagonal * witnessDiagonal := by decide +kernel
    rw [he, map_mul]
    exact actorJoin.mul_mem secondSign_mem diagonal_mem


/-- A short matrix certificate produces one elementary matrix. Intermediate
matrices keep each kernel computation to at most four matrix factors. The
word is `acbcacacacacbcaca`, with a = firstMatrix, b = secondMatrix, and
c = witnessCycle. -/
private theorem root_mem (P : Subgroup SL(3, ZMod 5))
    (ha : firstMatrix ∈ P) (hb : secondMatrix ∈ P) (hc : witnessCycle ∈ P) :
    SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : ZMod 5) ∈ P := by
  let q1 : SL(3, ZMod 5) := ⟨!![0,3,3;3,2,3;1,1,4], by decide +kernel⟩
  let q2 : SL(3, ZMod 5) := ⟨!![2,4,1;4,4,1;1,2,1], by decide +kernel⟩
  let q3 : SL(3, ZMod 5) := ⟨!![1,0,4;1,4,1;4,2,1], by decide +kernel⟩
  let q4 : SL(3, ZMod 5) := ⟨!![2,2,4;3,3,2;1,3,0], by decide +kernel⟩
  let q5 : SL(3, ZMod 5) := ⟨!![0,0,2;1,1,0;4,2,0], by decide +kernel⟩
  have h1 : firstMatrix * witnessCycle * secondMatrix = q1 := by
    apply Subtype.ext
    decide +kernel
  have h2 : q1 * witnessCycle * firstMatrix * witnessCycle = q2 := by
    apply Subtype.ext
    decide +kernel
  have h3 : q2 * firstMatrix * witnessCycle * firstMatrix = q3 := by
    apply Subtype.ext
    decide +kernel
  have h4 : q3 * witnessCycle * firstMatrix * witnessCycle = q4 := by
    apply Subtype.ext
    decide +kernel
  have h5 : q4 * secondMatrix * witnessCycle * firstMatrix = q5 := by
    apply Subtype.ext
    decide +kernel
  have h6 : q5 * witnessCycle * firstMatrix =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : ZMod 5) := by
    apply Subtype.ext
    decide +kernel
  have hm1 : q1 ∈ P := h1 ▸ P.mul_mem (P.mul_mem ha hc) hb
  have hm2 : q2 ∈ P := h2 ▸ P.mul_mem (P.mul_mem (P.mul_mem hm1 hc) ha) hc
  have hm3 : q3 ∈ P := h3 ▸ P.mul_mem (P.mul_mem (P.mul_mem hm2 ha) hc) ha
  have hm4 : q4 ∈ P := h4 ▸ P.mul_mem (P.mul_mem (P.mul_mem hm3 hc) ha) hc
  have hm5 : q5 ∈ P := h5 ▸ P.mul_mem (P.mul_mem (P.mul_mem hm4 hb) hc) ha
  exact h6 ▸ P.mul_mem (P.mul_mem hm5 hc) ha

private theorem graph_root {i j : Fin 3} (hij : i ≠ j) (a : ZMod 5) :
    (SpecialLinearGroup.transpose (SpecialLinearGroup.transvection hij a))⁻¹ =
      SpecialLinearGroup.transvection hij.symm (-a) := by
  have h : SpecialLinearGroup.transpose (SpecialLinearGroup.transvection hij a) =
      SpecialLinearGroup.transvection hij.symm a := by
    apply Subtype.ext
    simp [SpecialLinearGroup.transpose, SpecialLinearGroup.transvection_coe,
      Matrix.transpose_add, Matrix.transpose_single]
  rw [h, SpecialLinearGroup.transvection_inv]

private theorem linear_eq_top (P : Subgroup SL(3, ZMod 5))
    (ha : firstMatrix ∈ P) (hb : secondMatrix ∈ P) (hc : witnessCycle ∈ P)
    (hg : ∀ x ∈ P, (SpecialLinearGroup.transpose x)⁻¹ ∈ P) : P = ⊤ := by
  have h12 (a : ZMod 5) : SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) a ∈ P := by
    have hp : ∀ a : ZMod 5,
        (SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : ZMod 5)) ^ a.val =
          SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) a := by decide +kernel
    exact hp a ▸ P.pow_mem (root_mem P ha hb hc) a.val
  have h01 (a : ZMod 5) : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) a ∈ P := by
    have he : ∀ a : ZMod 5, witnessCycle *
        SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) a * witnessCycle⁻¹ =
          SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) a := by decide +kernel
    exact he a ▸ P.mul_mem (P.mul_mem hc (h12 a)) (P.inv_mem hc)
  have h20 (a : ZMod 5) : SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) a ∈ P := by
    have he : ∀ a : ZMod 5, witnessCycle *
        SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) a * witnessCycle⁻¹ =
          SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) a := by decide +kernel
    exact he a ▸ P.mul_mem (P.mul_mem hc (h01 a)) (P.inv_mem hc)
  have h21 (a : ZMod 5) : SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) a ∈ P := by
    simpa only [graph_root, neg_neg] using hg _ (h12 (-a))
  have h10 (a : ZMod 5) : SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) a ∈ P := by
    simpa only [graph_root, neg_neg] using hg _ (h01 (-a))
  have h02 (a : ZMod 5) : SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) a ∈ P := by
    simpa only [graph_root, neg_neg] using hg _ (h20 (-a))
  apply top_unique
  intro g _
  apply Atlas.sl_elementary_induction (fun x => x ∈ P) _ (fun _ _ => P.mul_mem) g
  intro i j hij a
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h01 a
  · exact h02 a
  · exact h10 a
  · exact (hij rfl).elim
  · exact h12 a
  · exact h20 a
  · exact h21 a
  · exact (hij rfl).elim

private theorem inner_sup_graph : FiveSourceAudit.inner ⊔ zpowers graphElement = ⊤ := by
  apply Subgroup.map_injective (Matrix.PSL3.OddPrimeGraphExtension.graphExtension (ZMod 5)).subtype_injective
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  change (Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure.innerPart (ZMod 5)).map _ ⊔
    zpowers (Matrix.PSL3.OuterSolvable.graph (ZMod 5)) = _
  rw [Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure.innerPart,
    map_subgroupOf_eq_of_le (show MulAut.innerSubgroup PSL(3, ZMod 5) ≤
      Matrix.PSL3.OddPrimeGraphExtension.graphExtension (ZMod 5) from le_sup_left)]
  rw [← MonoidHom.range_eq_map, range_subtype]
  rfl

/-- The monomial group and the two displayed matrices generate the entire
literal automorphism carrier, by elementary-matrix generation. -/
theorem eq_top_of_monomial_and_matrices (H : Subgroup Model)
    (hK : monomialOvergroup ≤ H) (ha : innerSL firstMatrix ∈ H)
    (hb : innerSL secondMatrix ∈ H) : H = ⊤ := by
  have hc : innerSL witnessCycle ∈ H := hK (mem_sup_left ⟨_, witnessCycle_mem_linear, rfl⟩)
  have hg : graphElement ∈ H := hK (mem_sup_right (mem_zpowers _))
  have hpre : H.comap innerSL = ⊤ := by
    apply linear_eq_top _ ha hb hc
    intro x hx
    change innerSL (SpecialLinearGroup.transpose x)⁻¹ ∈ H
    have hh := H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)
    rw [graph_innerSL, mul_inv_cancel_right] at hh
    exact hh
  have hI : FiveSourceAudit.inner ≤ H := by
    rw [← innerSL_range]
    rintro x ⟨y, rfl⟩
    exact show y ∈ H.comap innerSL from hpre ▸ mem_top y
  apply top_unique
  rw [← inner_sup_graph]
  exact sup_le hI (zpowers_le.mpr hg)

/-- Unconditional generation for the normalizer of the explicit actor join. -/
theorem monomial_sup_actorJoin_normalizer :
    monomialOvergroup ⊔ normalizer (actorJoin : Set Model) = ⊤ :=
  eq_top_of_monomial_and_matrices _ le_sup_left
    (mem_sup_right first_normalizes_actorJoin) (mem_sup_right second_normalizes_actorJoin)

/-- The two known actors already lie in the actual weak closure whenever
they lie in the chosen Sylow. The reverse inclusion is the remaining census. -/
theorem actorJoin_le_weakClosure (S : Sylow 2 Model)
    (ha : actor ≤ (S : Subgroup Model)) (hb : movedActor ≤ (S : Subgroup Model)) :
    actorJoin ≤ weakClosure (S : Subgroup Model) family := by
  apply sup_le
  · apply le_sSup
    refine ⟨?_, ha⟩
    refine ⟨1, ?_⟩
    change actor = actor.map (MonoidHom.id Model)
    exact (map_id actor).symm
  · exact le_sSup ⟨movedActor_mem_family, hb⟩

/-- The existing simultaneous-placement proof supplies a literal Sylow
inside the monomial group and the lower inclusion needed by the census. -/
theorem exists_sylow_actorJoin_le : ∃ S : Sylow 2 Model,
    (S : Subgroup Model) ≤ monomialOvergroup ∧
      actorJoin ≤ weakClosure (S : Subgroup Model) family := by
  obtain ⟨S, ha, hK, hb⟩ := simultaneous_sylow_placement
  exact ⟨S, hK, actorJoin_le_weakClosure S ha hb⟩

/-- Exact consumer: the finite weak-closure census discharges `MonomialJoin`.
No normalizer order or maximal-subgroup classification is needed. -/
theorem monomialJoin_of_weakClosure (S : Sylow 2 Model)
    (hK : (S : Subgroup Model) ≤ monomialOvergroup)
    (hW : weakClosure (S : Subgroup Model) family = actorJoin) : MonomialJoin := by
  refine ⟨S, hK, ?_⟩
  rw [hW]
  exact monomial_sup_actorJoin_normalizer

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.ActorDichotomy.NormalizerCertificate
