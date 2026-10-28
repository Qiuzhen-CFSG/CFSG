module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.OctonionLocals

/-!
# The natural and dual halves of the long octonion local group

The literal graph involution swaps the Peirce triples with the permutation
(1 2) on each triple. Thus its conjugation on SL₃ is inverse transpose
conjugated by that permutation matrix. Packing the octonion coordinates proves
this group identity without a representation or a faithfulness assumption.

For any linear action of this group in characteristic two, an injective
additive natural submodule and its graph translate give injective six-coordinate
maps with exactly the published octonion actions. Products of three elementary
root displacements isolate each natural coordinate and annihilate the dual
half; this proves injectivity without assuming a direct-sum decomposition.
Coordinatewise field automorphisms remove field twists, and the corrected graph
translate converts a dual submodule to a natural one. `Long.Module` applies all
three constructions to the literal Leech fixed space.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284.
The octonion formulas come from the existing attributed ATLAS port; this module
adds proofs against those formulas and copies no additional upstream code.
-/

open Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.ModuleModel
open OctonionLocals
open PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight
@[expose] public noncomputable section
variable {F : Type*} [Field F] [CharP F 2]

def blockIn : SL(3,F) →* longLocal (F := F) :=
  BlockRealization.blockHom.codRestrict _ (fun A =>
    (show BlockRealization.blockHom.range ≤ longLocal (F := F) from le_sup_left)
      ⟨A, rfl⟩)

def graphIn : longLocal (F := F) :=
  ⟨graph, (show Subgroup.zpowers (graph : Model F) ≤ longLocal from le_sup_right)
    (Subgroup.mem_zpowers _)⟩

theorem graphIn_sq : (graphIn (F := F)) ^ 2 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (graph : Model F).val (graph.val x) = x
  rw [graph_apply, graph_apply]
  ext i
  fin_cases i <;> rfl

def flip : SL(3,F) :=
  ⟨!![1,0,0;0,0,1;0,1,0], by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩

def graphTwist (A : SL(3,F)) : SL(3,F) :=
  flip * A⁻¹.transpose * flip

theorem graphTwist_val (A : SL(3,F)) :
    (graphTwist A).val = flip.val * BlockRealization.cofactor A.val * flip.val := rfl

theorem graphTwist_cofactor (A : SL(3,F)) :
    BlockRealization.cofactor (graphTwist A).val = flip.val * A.val * flip.val := by
  rw [graphTwist_val]
  simp only [BlockRealization.cofactor, Matrix.adjugate_mul_distrib, Matrix.transpose_mul]
  have hf : (flip (F := F)).val.adjugate.transpose = flip.val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [flip, Matrix.adjugate_fin_three, CharTwo.neg_eq]
  rw [hf]
  have ha := BlockRealization.cofactor_cofactor A
  exact congrArg (fun M => flip.val * M * flip.val) ha

def reverseThree (u : Fin 3 → F) : Fin 3 → F := ![u 0,u 2,u 1]

omit [Field F] [CharP F 2] in
theorem reverseThree_twice (u : Fin 3 → F) : reverseThree (reverseThree u) = u := by
  ext i
  fin_cases i <;> rfl

theorem flip_mulVec (u : Fin 3 → F) : flip.val *ᵥ u = reverseThree u := by
  ext i
  fin_cases i <;> simp [flip, reverseThree, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem graphTwist_mulVec (A : SL(3,F)) (u : Fin 3 → F) :
    (graphTwist A).val *ᵥ u =
      reverseThree (BlockRealization.cofactor A.val *ᵥ reverseThree u) := by
  rw [graphTwist_val, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    flip_mulVec, flip_mulVec]

theorem graphTwist_cofactor_mulVec (A : SL(3,F)) (u : Fin 3 → F) :
    BlockRealization.cofactor (graphTwist A).val *ᵥ u =
      reverseThree (A.val *ᵥ reverseThree u) := by
  rw [graphTwist_cofactor, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    flip_mulVec, flip_mulVec]

theorem graph_pack (a b : F) (u w : Fin 3 → F) :
    (graph : Model F).val (BlockRealization.pack a b u w) =
      BlockRealization.pack b a (reverseThree w) (reverseThree u) := by
  rw [graph_apply]
  ext i
  fin_cases i <;> rfl

theorem blockIn_graphIn (A : SL(3,F)) :
    blockIn A * graphIn = graphIn * blockIn (graphTwist A) := by
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (BlockRealization.blockHom A).val (graph.val x) =
    graph.val ((BlockRealization.blockHom (graphTwist A)).val x)
  rw [← BlockRealization.pack_eta x]
  change BlockRealization.blockLinear A.val (graph.val _) =
    graph.val (BlockRealization.blockLinear (graphTwist A).val _)
  rw [graph_pack, BlockRealization.blockLinear_pack, BlockRealization.blockLinear_pack,
    graph_pack, graphTwist_mulVec, graphTwist_cofactor_mulVec,
    reverseThree_twice, reverseThree_twice]

abbrev Three (F : Type*) := Fin 3 → F

def naturalPart : Six F →+ Three F where
  toFun v := ![v 0,v 3,v 4]
  map_zero' := by ext i; fin_cases i <;> rfl
  map_add' _ _ := by ext i; fin_cases i <;> rfl

def reverseDualPart : Six F →+ Three F where
  toFun v := ![v 5,v 1,v 2]
  map_zero' := by ext i; fin_cases i <;> rfl
  map_add' _ _ := by ext i; fin_cases i <;> rfl

def naturalSix : Three F →+ Six F where
  toFun u := ![u 0,0,0,u 1,u 2,0]
  map_zero' := by ext i; fin_cases i <;> rfl
  map_add' u v := by ext j; fin_cases j <;> simp

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The image of an additive natural module and its actual graph translate. -/
def graphCoordinates (ρ : longLocal (F := F) →* (V ≃ₗ[F] V)) (n : Three F →+ V) :
    Six F →+ V :=
  n.comp naturalPart +
    (ρ graphIn).toAddEquiv.toAddMonoidHom.comp (n.comp reverseDualPart)

omit [CharP F 2] in
theorem graphCoordinates_apply (ρ : longLocal (F := F) →* (V ≃ₗ[F] V)) (n : Three F →+ V)
    (v : Six F) :
    graphCoordinates ρ n v = n ![v 0,v 3,v 4] + ρ graphIn (n ![v 5,v 1,v 2]) := rfl

omit [CharP F 2] in
theorem graphCoordinates_naturalSix (ρ : longLocal (F := F) →* (V ≃ₗ[F] V)) (n : Three F →+ V)
    (u : Three F) : graphCoordinates ρ n (naturalSix u) = n u := by
  rw [graphCoordinates_apply]
  change n ![u 0,u 1,u 2] + ρ graphIn (n ![0,0,0]) = n u
  have hz : (![0,0,0] : Three F) = 0 := by ext i; fin_cases i <;> rfl
  have he : ![u 0,u 1,u 2] = u := by ext j; fin_cases j <;> rfl
  rw [he, hz, map_zero, map_zero, add_zero]

theorem graphCoordinates_graph (ρ : longLocal (F := F) →* (V ≃ₗ[F] V)) (n : Three F →+ V)
    (v : Six F) :
    ρ graphIn (graphCoordinates ρ n v) = graphCoordinates ρ n (action graph v) := by
  have hh (w : V) : ρ graphIn (ρ graphIn w) = w := by
    have hp : ρ graphIn * ρ graphIn = 1 := by
      rw [← map_mul, ← pow_two, graphIn_sq, map_one]
    change (ρ graphIn * ρ graphIn) w = w
    rw [hp]
    rfl
  rw [graphCoordinates_apply, map_add, hh, action_graph, graphCoordinates_apply]
  change ρ graphIn (n ![v 0,v 3,v 4]) + n ![v 5,v 1,v 2] = _
  exact add_comm _ _

theorem graphCoordinates_block (ρ : longLocal (F := F) →* (V ≃ₗ[F] V)) (n : Three F →+ V)
    (hn : ∀ A u, ρ (blockIn A) (n u) = n (A.val *ᵥ u))
    (A : SL(3,F)) (v : Six F) :
    ρ (blockIn A) (graphCoordinates ρ n v) =
      graphCoordinates ρ n (action (BlockRealization.blockHom A) v) := by
  have hg (u : Three F) : ρ (blockIn A) (ρ graphIn (n u)) =
      ρ graphIn (n ((graphTwist A).val *ᵥ u)) := by
    calc
      ρ (blockIn A) (ρ graphIn (n u)) =
          ρ (blockIn A * graphIn) (n u) := by rw [map_mul]; rfl
      _ = ρ graphIn (ρ (blockIn (graphTwist A)) (n u)) := by
        rw [blockIn_graphIn, map_mul]; rfl
      _ = _ := by rw [hn]
  rw [graphCoordinates_apply, map_add, hn, hg, action_block, graphCoordinates_apply]
  congr 1
  · congr 1
    ext i
    fin_cases i <;> rfl
  · congr 2
    rw [graphTwist_mulVec]
    rfl

private def root01 : SL(3,F) :=
  ⟨!![1,1,0;0,1,0;0,0,1], by simp [Matrix.det_fin_three]⟩
private def root12 : SL(3,F) :=
  ⟨!![1,0,0;0,1,1;0,0,1], by simp [Matrix.det_fin_three]⟩
private def root20 : SL(3,F) :=
  ⟨!![1,0,0;0,1,0;1,0,1], by simp [Matrix.det_fin_three]⟩

private def displacement (A : SL(3,F)) (v : Six F) : Six F :=
  action (BlockRealization.blockHom A) v - v

private theorem displacement01 (v : Six F) :
    displacement root01 v = ![v 3,0,v 5,0,0,0] := by
  rw [displacement, action_block]
  ext i
  fin_cases i <;> simp [root01, BlockRealization.cofactor, Matrix.adjugate_fin_three,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, CharTwo.neg_eq]

private theorem displacement12 (v : Six F) :
    displacement root12 v = ![0,v 2,0,v 4,0,0] := by
  rw [displacement, action_block]
  ext i
  fin_cases i <;> simp [root12, BlockRealization.cofactor, Matrix.adjugate_fin_three,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, CharTwo.neg_eq]

private theorem displacement20 (v : Six F) :
    displacement root20 v = ![0,0,0,0,v 0,v 1] := by
  rw [displacement, action_block]
  ext i
  fin_cases i <;> simp [root20, BlockRealization.cofactor, Matrix.adjugate_fin_three,
    Matrix.mulVec, dotProduct, Fin.sum_univ_three, CharTwo.neg_eq]

/-- Root displacements separate the natural half from its graph translate.
The input is additive, so this also accommodates all field twists. -/
theorem graphCoordinates_injective (ρ : longLocal (F := F) →* (V ≃ₗ[F] V)) (n : Three F →+ V)
    (hninj : Function.Injective n)
    (hn : ∀ A u, ρ (blockIn A) (n u) = n (A.val *ᵥ u)) :
    Function.Injective (graphCoordinates ρ n) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hd (A : SL(3,F)) (w : Six F) (hw : graphCoordinates ρ n w = 0) :
      graphCoordinates ρ n (displacement A w) = 0 := by
    rw [displacement, map_sub, ← graphCoordinates_block ρ n hn, hw, map_zero, sub_self]
  have h0 := hd root01 _ (hd root12 _ (hd root20 v hv))
  have h1 := hd root12 _ (hd root20 _ (hd root01 v hv))
  have h2 := hd root20 _ (hd root01 _ (hd root12 v hv))
  rw [displacement20, displacement12, displacement01] at h0
  rw [displacement01, displacement20, displacement12] at h1
  rw [displacement12, displacement01, displacement20] at h2
  have hn0 : n ![v 0,0,0] = 0 := by
    change graphCoordinates ρ n (naturalSix ![v 0,0,0]) = 0 at h0
    rwa [graphCoordinates_naturalSix] at h0
  have hn1 : n ![0,v 3,0] = 0 := by
    change graphCoordinates ρ n (naturalSix ![0,v 3,0]) = 0 at h1
    rwa [graphCoordinates_naturalSix] at h1
  have hn2 : n ![0,0,v 4] = 0 := by
    change graphCoordinates ρ n (naturalSix ![0,0,v 4]) = 0 at h2
    rwa [graphCoordinates_naturalSix] at h2
  have hz (w : Three F) (hw : n w = 0) : w = 0 := hninj (hw.trans (map_zero n).symm)
  have hv0 : v 0 = 0 := congrFun (hz _ hn0) 0
  have hv3 : v 3 = 0 := congrFun (hz _ hn1) 1
  have hv4 : v 4 = 0 := congrFun (hz _ hn2) 2
  rw [graphCoordinates_apply, hv0, hv3, hv4] at hv
  have hz0 : (![0,0,0] : Three F) = 0 := by ext i; fin_cases i <;> rfl
  rw [hz0, map_zero, zero_add] at hv
  have hd0 : n ![v 5,v 1,v 2] = 0 :=
    (ρ graphIn).injective (hv.trans (map_zero _).symm)
  have hvd := hz _ hd0
  ext i
  fin_cases i
  · exact hv0
  · exact congrFun hvd 1
  · exact congrFun hvd 2
  · exact hv3
  · exact hv4
  · exact congrFun hvd 0


/-- Apply a field automorphism in each of the three coordinates. -/
def fieldCoordinates (σ : F ≃+* F) : Three F ≃+ Three F where
  toFun u i := σ (u i)
  invFun u i := σ.symm (u i)
  left_inv u := by ext i; exact σ.symm_apply_apply (u i)
  right_inv u := by ext i; exact σ.apply_symm_apply (u i)
  map_add' u v := by ext i; exact map_add σ (u i) (v i)

omit [CharP F 2] in
theorem fieldCoordinates_mulVec (σ : F ≃+* F) (A : Matrix (Fin 3) (Fin 3) F)
    (u : Three F) : fieldCoordinates σ (A *ᵥ u) = A.map σ *ᵥ fieldCoordinates σ u := by
  ext i
  simp [fieldCoordinates, Matrix.mulVec, dotProduct, map_sum, map_mul]

/-- An actual additive change of coordinates removes a coefficient-field twist. -/
def untwistNatural (σ : F ≃+* F) (n : Three F →+ V) : Three F →+ V :=
  n.comp (fieldCoordinates σ).toAddMonoidHom

omit [CharP F 2] [Module F V] in
theorem untwistNatural_injective (σ : F ≃+* F) (n : Three F →+ V)
    (hn : Function.Injective n) : Function.Injective (untwistNatural σ n) :=
  hn.comp (fieldCoordinates σ).injective

omit [CharP F 2] in
theorem untwistNatural_equivariant (ρ : longLocal (F := F) →* (V ≃ₗ[F] V))
    (σ : F ≃+* F) (n : Three F →+ V)
    (hn : ∀ A u, ρ (blockIn A) (n u) = n (A.val.map σ *ᵥ u)) (A : SL(3,F))
    (u : Three F) : ρ (blockIn A) (untwistNatural σ n u) =
      untwistNatural σ n (A.val *ᵥ u) := by
  change ρ (blockIn A) (n (fieldCoordinates σ u)) = n (fieldCoordinates σ (A.val *ᵥ u))
  rw [hn, fieldCoordinates_mulVec]

/-- Correct the literal graph permutation before translating a dual submodule. -/
def reverseCoordinates : Three F ≃+ Three F where
  toFun := reverseThree
  invFun := reverseThree
  left_inv := reverseThree_twice
  right_inv := reverseThree_twice
  map_add' u v := by ext i; fin_cases i <;> rfl

def graphNatural (ρ : longLocal (F := F) →* (V ≃ₗ[F] V)) (n : Three F →+ V) :
    Three F →+ V :=
  (ρ graphIn).toAddEquiv.toAddMonoidHom.comp (n.comp reverseCoordinates.toAddMonoidHom)

omit [CharP F 2] in
theorem graphNatural_injective (ρ : longLocal (F := F) →* (V ≃ₗ[F] V))
    (n : Three F →+ V) (hn : Function.Injective n) : Function.Injective (graphNatural ρ n) :=
  (ρ graphIn).injective.comp (hn.comp reverseCoordinates.injective)

theorem graphNatural_equivariant (ρ : longLocal (F := F) →* (V ≃ₗ[F] V))
    (n : Three F →+ V)
    (hn : ∀ A u, ρ (blockIn A) (n u) = n (BlockRealization.cofactor A.val *ᵥ u))
    (A : SL(3,F)) (u : Three F) :
    ρ (blockIn A) (graphNatural ρ n u) = graphNatural ρ n (A.val *ᵥ u) := by
  change ρ (blockIn A) (ρ graphIn (n (reverseThree u))) =
    ρ graphIn (n (reverseThree (A.val *ᵥ u)))
  change (ρ (blockIn A) * ρ graphIn) (n (reverseThree u)) = _
  rw [← map_mul, blockIn_graphIn, map_mul]
  change ρ graphIn (ρ (blockIn (graphTwist A)) (n (reverseThree u))) = _
  rw [hn, graphTwist_cofactor_mulVec, reverseThree_twice]

end
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.ModuleModel
