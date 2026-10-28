module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.InnerDegree.Reduction
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual.Weyl
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph.Construction


/-!
# Five root conjugates and two radical conjugates generate Sp₄

Four coordinate long-root groups and the conjugate of root 0 by `rootElement 7 1`
generate the actual matrix group. The identity
`x₇(1) x₀(t) x₇(1) = x₀(t) x₂(t) x₄(t)` supplies the first short-root group;
hyperbolic-pair swaps then give all eight standard root groups.

The upper-plane radical and its opposite contain the first five root groups.
The actual exceptional graph automorphism transports the two constructions to
short roots and point radicals. On a plane shear with symmetric block
`[[a,b],[b,c]]`, its image has point-radical coordinates `(a,c,a*c+b²)`.
In particular the conjugating elements always belong to the original Sp₄(F).
These generation results hold over every finite field of characteristic two.

The final application discharges both generation premises of the original
ambient-actor degree estimate, retaining elementary placement and the
normalizer-invariant subgroup classification as independent premises.

Source: Guralnick--Malle, *Classification of 2F-modules II*, Proposition 6.2,
part 1A, author manuscript pp.38--39
(https://agag-malle.math.rptu.de/~malle/download/failfactlie.dvi);
Aschbacher--Smith K.3.4, printed pp.456--457.
-/

public section

open Matrix Subgroup
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open scoped CharTwo
namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.InnerDegree
variable {F : Type*} [Field F] [CharP F 2]

private def swapFirst : Sp F := rootElement 0 1 * rootElement 1 1 * rootElement 0 1
private def swapSecond : Sp F := rootElement 2 1 * rootElement 3 1 * rootElement 2 1

private lemma swapFirst_val : (swapFirst (F := F)).val =
    fromBlocks !![0,0;0,1] !![1,0;0,0] !![1,0;0,0] !![0,0;0,1] := by
  change rootMatrix 0 1 * rootMatrix 1 1 * rootMatrix 0 1 = _
  simp [rootMatrix, fromBlocks_multiply]
  all_goals
    (repeat' apply And.intro) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.single, CharTwo.add_self_eq_zero]

private lemma swapSecond_val : (swapSecond (F := F)).val =
    fromBlocks !![1,0;0,0] !![0,0;0,1] !![0,0;0,1] !![1,0;0,0] := by
  change rootMatrix 2 1 * rootMatrix 3 1 * rootMatrix 2 1 = _
  simp [rootMatrix, fromBlocks_multiply]
  all_goals
    (repeat' apply And.intro) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.single, CharTwo.add_self_eq_zero]

private lemma root_seven (t : F) : rootElement 7 t =
    swapFirst * rootElement 4 t * swapFirst := by
  apply Subtype.ext
  change rootMatrix 7 t = (swapFirst (F := F)).val * rootMatrix 4 t * (swapFirst (F := F)).val
  rw [swapFirst_val]
  simp [rootMatrix, fromBlocks_multiply]
  all_goals
    (repeat' apply And.intro) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.vecMul, dotProduct, Matrix.single, vecHead, vecTail]

private lemma root_six (t : F) : rootElement 6 t =
    swapSecond * rootElement 4 t * swapSecond := by
  apply Subtype.ext
  change rootMatrix 6 t = (swapSecond (F := F)).val * rootMatrix 4 t * (swapSecond (F := F)).val
  rw [swapSecond_val]
  simp [rootMatrix, fromBlocks_multiply]
  all_goals
    (repeat' apply And.intro) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.vecMul, dotProduct, Matrix.single, vecHead, vecTail]

private lemma root_five (t : F) : rootElement 5 t =
    swapFirst * rootElement 6 t * swapFirst := by
  apply Subtype.ext
  change rootMatrix 5 t = (swapFirst (F := F)).val * rootMatrix 6 t * (swapFirst (F := F)).val
  rw [swapFirst_val]
  simp [rootMatrix, fromBlocks_multiply]
  all_goals
    (repeat' apply And.intro) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.single]

private theorem eq_top_of_first_five (H : Subgroup (Sp F))
    (h : ∀ (j : Fin 5) (t : F), rootElement (j.castLE (by decide)) t ∈ H) : H = ⊤ := by
  have hw₀ : swapFirst (F := F) ∈ H := H.mul_mem (H.mul_mem (h 0 1) (h 1 1)) (h 0 1)
  have hw₁ : swapSecond (F := F) ∈ H := H.mul_mem (H.mul_mem (h 2 1) (h 3 1)) (h 2 1)
  have h₆ (t : F) : rootElement 6 t ∈ H := by
    rw [root_six]
    exact H.mul_mem (H.mul_mem hw₁ (h 4 t)) hw₁
  apply eq_top_of_rootElement_mem
  intro r t
  fin_cases r
  · exact h 0 t
  · exact h 1 t
  · exact h 2 t
  · exact h 3 t
  · exact h 4 t
  · change rootElement 5 t ∈ H
    rw [root_five]; exact H.mul_mem (H.mul_mem hw₀ (h₆ t)) hw₀
  · exact h₆ t
  · change rootElement 7 t ∈ H
    rw [root_seven]; exact H.mul_mem (H.mul_mem hw₀ (h 4 t)) hw₀

private theorem fifth_long_root (t : F) :
    rootElement 7 1 * rootElement 0 t * rootElement 7 1 =
      rootElement 0 t * rootElement 2 t * rootElement 4 t := by
  apply Subtype.ext
  change rootMatrix 7 1 * rootMatrix 0 t * rootMatrix 7 1 =
    rootMatrix 0 t * rootMatrix 2 t * rootMatrix 4 t
  simp [rootMatrix, fromBlocks_multiply]
  all_goals
    (repeat' apply And.intro) <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single]

private theorem root_inv (r : Fin 8) (t : F) : (rootElement r t)⁻¹ = rootElement r t := by
  apply inv_eq_of_mul_eq_one_left
  rw [RootSubgroup.element_add, CharTwo.add_self_eq_zero, RootSubgroup.element_zero]

omit [CharP F 2] in
private theorem root_mem (r : Fin 8) (t : F) : rootElement r t ∈ RootSubgroup.group r :=
  (RootSubgroup.mem_group_iff r _).mpr ⟨t, rfl⟩

private theorem five_long_conjugates : ∃ c : Fin 5 → Sp F,
    (⨆ j, (RootSubgroup.group 0).map (MulAut.conj (c j)).toMonoidHom) = ⊤ := by
  classical
  have he (j : Fin 4) : ∃ w : Sp F,
      (RootSubgroup.group 0).map (MulAut.conj w).toMonoidHom =
        RootSubgroup.group (j.castLE (by decide)) := by
    fin_cases j
    · exact RootNormalizerResidual.exists_root_conjugation (F := F) 0
    · exact RootNormalizerResidual.exists_root_conjugation (F := F) 1
    · exact RootNormalizerResidual.exists_root_conjugation (F := F) 2
    · exact RootNormalizerResidual.exists_root_conjugation (F := F) 3
  choose w hw using he
  let c : Fin 5 → Sp F := Fin.snoc w (rootElement 7 1)
  let H : Subgroup (Sp F) := ⨆ j, (RootSubgroup.group 0).map (MulAut.conj (c j)).toMonoidHom
  have hlong (j : Fin 4) (t : F) : rootElement (j.castLE (by decide)) t ∈ H := by
    apply (le_iSup (fun k => (RootSubgroup.group 0).map (MulAut.conj (c k)).toMonoidHom)
      j.castSucc)
    dsimp only [c]
    rw [Fin.snoc_castSucc, hw]
    exact root_mem _ _
  have hx (t : F) : rootElement 7 1 * rootElement 0 t * rootElement 7 1 ∈ H := by
    apply (le_iSup (fun k => (RootSubgroup.group 0).map (MulAut.conj (c k)).toMonoidHom) 4)
    refine ⟨rootElement 0 t, root_mem _ _, ?_⟩
    change rootElement 7 1 * rootElement 0 t * (rootElement 7 (1 : F))⁻¹ = _
    rw [root_inv]
  have hfour (t : F) : rootElement 4 t ∈ H := by
    have hx' := hx t
    rw [fifth_long_root] at hx'
    exact (H.mul_mem_cancel_left (H.mul_mem (hlong 0 t) (hlong 2 t))).mp hx'
  refine ⟨c, eq_top_of_first_five H ?_⟩
  intro j t
  fin_cases j
  · exact hlong 0 t
  · exact hlong 1 t
  · exact hlong 2 t
  · exact hlong 3 t
  · exact hfour t

private theorem conjugate_generation_transport {G : Type*} [Group G]
    (a : MulAut G) {U W : Subgroup G} (hUW : U.map a.toMonoidHom ≤ W)
    {n : ℕ} (hgen : ∃ c : Fin n → G,
      (⨆ j, U.map (MulAut.conj (c j)).toMonoidHom) = ⊤) :
    ∃ c : Fin n → G, (⨆ j, W.map (MulAut.conj (c j)).toMonoidHom) = ⊤ := by
  obtain ⟨c, hc⟩ := hgen
  refine ⟨a ∘ c, top_unique ?_⟩
  have ht : (⨆ j, U.map (MulAut.conj (c j)).toMonoidHom).map a.toMonoidHom = ⊤ := by
    rw [hc, map_top_of_surjective _ a.surjective]
  rw [← ht, Subgroup.map_iSup]
  apply iSup_le
  intro j
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
  apply (le_iSup (fun k => W.map (MulAut.conj ((a ∘ c) k)).toMonoidHom) j)
  refine ⟨a u, hUW (mem_map_of_mem _ hu), ?_⟩
  simp [MulAut.conj_apply]

open DiagramAutomorphisms.ExceptionalGraph

private theorem graph_long_le_short [Finite F] :
    (RootSubgroup.group 0).map (graphAut (F := F)).toMonoidHom ≤ RootSubgroup.group 4 := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨t, rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hx
  rw [MulEquiv.coe_toMonoidHom, graphAut_apply, graphEnd_root]
  exact root_mem 4 t

private def opposite : Sp F := swapFirst * swapSecond

private theorem opposite_val : (opposite (F := F)).val = fromBlocks 0 1 1 0 := by
  change (swapFirst (F := F)).val * (swapSecond (F := F)).val = _
  rw [swapFirst_val, swapSecond_val]
  simp [fromBlocks_multiply]
  (repeat' apply And.intro) <;> ext i j <;> fin_cases i <;> fin_cases j <;> rfl

private theorem opposite_inv : (opposite (F := F))⁻¹ = opposite := by
  apply inv_eq_of_mul_eq_one_left
  apply Subtype.ext
  change (opposite (F := F)).val * (opposite (F := F)).val = 1
  rw [opposite_val]
  simp [fromBlocks_multiply]

private theorem opposite_long (j : Fin 2) (t : F) :
    opposite * rootElement (![0,2] j) t * opposite = rootElement (![1,3] j) t := by
  fin_cases j
  · change opposite * rootElement 0 t * opposite = rootElement 1 t
    apply Subtype.ext
    change (opposite (F := F)).val * rootMatrix 0 t * (opposite (F := F)).val = _
    rw [opposite_val]
    simp [rootMatrix, rootElement, fromBlocks_multiply]
  · change opposite * rootElement 2 t * opposite = rootElement 3 t
    apply Subtype.ext
    change (opposite (F := F)).val * rootMatrix 2 t * (opposite (F := F)).val = _
    rw [opposite_val]
    simp [rootMatrix, rootElement, fromBlocks_multiply]

omit [CharP F 2] in
private theorem upper_root_mem_plane (j : Fin 3) (t : F) :
    rootElement (![0,2,4] j) t ∈ planeRadicalAmbient := by
  let B : Plane.symmetricMatrices F :=
    ⟨![single 0 0 t, single 1 1 t, single 0 1 t + single 1 0 t] j, by
      change _ᵀ = _
      fin_cases j <;> simp [transpose_add, transpose_single, add_comm]⟩
  have hm : (Plane.shear B).val ∈ planeRadicalAmbient :=
    mem_map_of_mem planeLocal.subtype
      (show Plane.shear B ∈ Plane.radical from Plane.quotientMap_shear B)
  have he : (Plane.shear B).val = rootElement (![0,2,4] j) t := by
    apply Subtype.ext
    fin_cases j <;> rfl
  rwa [he] at hm

private theorem two_plane_conjugates : ∃ c : Fin 2 → Sp F,
    (⨆ j, planeRadicalAmbient.map (MulAut.conj (c j)).toMonoidHom) = ⊤ := by
  let c : Fin 2 → Sp F := ![1, opposite]
  let H : Subgroup (Sp F) :=
    ⨆ j, planeRadicalAmbient.map (MulAut.conj (c j)).toMonoidHom
  have hu (j : Fin 3) (t : F) : rootElement (![0,2,4] j) t ∈ H := by
    apply (le_iSup (fun k => planeRadicalAmbient.map (MulAut.conj (c k)).toMonoidHom) 0)
    refine ⟨_, upper_root_mem_plane j t, ?_⟩
    simp [c]
  have hl (j : Fin 2) (t : F) : rootElement (![1,3] j) t ∈ H := by
    apply (le_iSup (fun k => planeRadicalAmbient.map (MulAut.conj (c k)).toMonoidHom) 1)
    refine ⟨rootElement (![0,2] j) t, ?_, ?_⟩
    · fin_cases j
      · exact upper_root_mem_plane 0 t
      · exact upper_root_mem_plane 1 t
    · change opposite * rootElement (![0,2] j) t * (opposite (F := F))⁻¹ = _
      rw [opposite_inv, opposite_long]
  refine ⟨c, eq_top_of_first_five H ?_⟩
  intro j t
  fin_cases j
  · exact hu 0 t
  · exact hl 0 t
  · exact hu 1 t
  · exact hl 1 t
  · exact hu 2 t

private theorem graph_plane_le_point [Finite F] :
    planeRadicalAmbient.map (graphAut (F := F)).toMonoidHom ≤ pointRadicalAmbient := by
  rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
  have hm := Plane.radical_matrix ⟨g, hg⟩
  have hb := (Plane.radical_blocks ⟨g, hg⟩).2.2.2
  have hs : g.val.val (.inl 1) (.inr 0) = g.val.val (.inl 0) (.inr 1) :=
    congrArg (fun B : Matrix (Fin 2) (Fin 2) F => B 0 1) hb
  refine ⟨pointRadicalElement (g.val.val (.inl 0) (.inr 0))
    (g.val.val (.inl 1) (.inr 1))
    (g.val.val (.inl 0) (.inr 0) * g.val.val (.inl 1) (.inr 1) +
      g.val.val (.inl 0) (.inr 1) ^ 2),
    pointRadicalElement_mem _ _ _, ?_⟩
  apply Subtype.ext
  change pointRadicalMatrix _ _ _ = graphMatrix g.val.val
  conv_rhs => rw [hm]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [graphMatrix, minor, first, second, pointRadicalMatrix, Matrix.fromBlocks,
      Matrix.toBlocks₁₂, hs, pow_two]

/-- Five actual inner conjugates of either distinguished root generate Sp₄(F). -/
theorem exists_five_centralRoot_conjugates [Finite F] (i : Bool) :
    ∃ c : Fin 5 → Sp F,
      (⨆ j, (centralRoot i).map (MulAut.conj (c j)).toMonoidHom) = ⊤ := by
  cases i
  · exact five_long_conjugates
  · exact conjugate_generation_transport graphAut graph_long_le_short five_long_conjugates

/-- Two actual inner conjugates of either embedded radical generate Sp₄(F). -/
theorem exists_two_radical_conjugates [Finite F] (i : Bool) :
    ∃ c : Fin 2 → Sp F,
      (⨆ j, (radical i).map (MulAut.conj (c j)).toMonoidHom) = ⊤ := by
  cases i
  · exact conjugate_generation_transport graphAut graph_plane_le_point two_plane_conjugates
  · exact two_plane_conjugates

open Representation Representation.BinaryOffender

variable {V G : Type*} [Finite F]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  [Group G] [Finite G] {ρG : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The source degree estimate with both generation premises discharged on the
actual symplectic group. Elementary placement and normalizer-invariant subgroup
classification remain the independent geometric inputs. -/
theorem source_ambient_inner_degree_of_parabolic_geometry {K : GroupClass}
    (h : SourceHypothesis K ρG L) {r : ℕ} (hF : Nat.card F = 2 ^ r)
    (e : L ⧸ center L ≃* Sp F)
    (hplace : ∀ A : Subgroup (Sp F), IsElementaryTwo A →
      ∃ (g : Sp F) (i : Bool), A.map (MulAut.conj g).toMonoidHom ≤ radical i)
    (hnormal : ∀ (i : Bool) (B : Subgroup (Sp F)), B ≤ radical i → B ≠ ⊥ →
      normalizer (radical (F := F) i : Set (Sp F)) ≤ normalizer (B : Set (Sp F)) →
      B = centralRoot i ∨ B = radical i)
    (A : Subgroup G) (hAL : A ≤ L) (hA : IsElementaryTwo A)
    (hcodim : fixedCodim ρG A ≤ 2 * rank A) :
    Module.finrank (ZMod 2) V ≤ 12 * r :=
  source_ambient_inner_degree_of_geometry h hF e hplace hnormal
    exists_five_centralRoot_conjugates exists_two_radical_conjugates A hAL hA hcodim

end CFSG.Quasithin.ChapterK.Symplectic.Recognition.InnerDegree
