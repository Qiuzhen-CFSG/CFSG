module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The root-coordinate calculations use the licensed split-octonion model from
Atlas/LinearGroups/G2, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917;
see LICENSES/ATLAS-CITATION.cff.
Changes: the long-local plane action, its exact five-root kernel, and the
identification of the actual two-core and rank-one quotient in characteristic two.
-/

public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Geometry
public import Theory.SpecificGroups.SL2.TwoCore
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The two-core and rank-one quotient of the long G₂ local group

In characteristic two, the long local group acts on the plane spanned by the
first three coordinate vectors, modulo the first-vector line. Its four matrix
entries define a surjective homomorphism to SL₂, split by the opposite-vector
stabilizer. The five-root/block factorization identifies the kernel with exactly
the five-root subgroup. In particular this proves normality inside the local
group, without asserting normality in the ambient G₂ group.

For a finite field, the kernel is a two-group and SL₂ has trivial two-core,
including over F₂. Thus the kernel is the entire local two-core. The scalar
center of SL₂ is trivial in characteristic two, giving the actual quotient
isomorphism to PSL₂. Over F₂ the core has order 32 in the full G₂(2) model.
The explicit quotient map commutes with coefficientwise field transport.

Source: Aschbacher--Smith, F.1.12(I)(3), printed pp. 262--264 of
`refs/quasithin.pdf`. This supplies the long-local quotient and core clauses;
the amalgam and its other local group are assembled by the source consumer.
-/

@[expose] public section

open Atlas.SplitOctonion Atlas.G2 Atlas.G2.Explicit Atlas.G2.PairStabilizer
open scoped MatrixGroups Pointwise
namespace Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2]

private theorem factor (g : local₂ (F := F)) :
    ∃ (t : Fin 6 → F) (M : SL(2,F)), t 4 = 0 ∧ g.val = unipotentProduct t * blockHom M := by
  have hg := g.property
  rw [← SetLike.mem_coe, local₂_eq_radical₂_mul_fixingPair] at hg
  obtain ⟨u, ⟨t, ht, rfl⟩, m, hm, he⟩ := hg
  refine ⟨t, imageSL ⟨m,hm⟩, ht, ?_⟩
  have hb := congrArg Subtype.val (block_imageSL ⟨m,hm⟩)
  change blockHom (imageSL ⟨m,hm⟩) = m at hb
  rw [hb]
  exact he.symm

omit [CharP F 2] in
private theorem radical_action (t : Fin 6 → F) (ht : t 4 = 0) (a b c : F) :
    (unipotentProduct t).val ![a,b,c,0,0,0,0,0] =
    ![a - t 3 * c - t 5 * b,b,c,0,0,0,0,0] := by
  funext i
  fin_cases i <;> simp [unipotentProduct,rootA,rootB,rootC,rootD,rootE,rootF,
    rootAEquiv,rootBEquiv,rootCEquiv,rootDEquiv,rootEEquiv,rootFEquiv,
    rootALinear,rootBLinear,rootCLinear,rootDLinear,rootELinear,rootFLinear,
    rootAApply,rootBApply,rootCApply,rootDApply,rootEApply,rootFApply,ht]
  ring
end Atlas.G2.LieParabolicSetup
namespace Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2]

private theorem factor_action (t : Fin 6 → F) (ht : t 4 = 0) (M : SL(2,F)) (a b c : F) :
    (unipotentProduct t * blockHom M).val ![a,b,c,0,0,0,0,0] =
    ![a - t 3 * (M 1 0*b + M 1 1*c) - t 5 * (M 0 0*b + M 0 1*c),
      M 0 0*b + M 0 1*c, M 1 0*b + M 1 1*c,0,0,0,0,0] := by
  change (unipotentProduct t).val (blockLinear M.val ![a,b,c,0,0,0,0,0]) = _
  have hb : blockLinear M.val ![a,b,c,0,0,0,0,0] =
      ![a,M 0 0*b + M 0 1*c,M 1 0*b + M 1 1*c,0,0,0,0,0] := by
    simp [blockLinear, sub_eq_add_neg, CharTwo.neg_eq]
  rw [hb, radical_action t ht]

/-- The four entries of the action on the plane modulo the first-vector line. -/
def longMatrix (g : Model F) : Matrix (Fin 2) (Fin 2) F :=
  !![g.val (E 1) 1,g.val (E 2) 1;g.val (E 1) 2,g.val (E 2) 2]

private theorem longMatrix_factor (t : Fin 6 → F) (ht : t 4 = 0) (M : SL(2,F)) :
    longMatrix (unipotentProduct t * blockHom M) = M.val := by
  have h1 : (E 1 : Carrier F) = ![0,1,0,0,0,0,0,0] := by
    funext i; fin_cases i <;> simp [E,basisVector]
  have h2 : (E 2 : Carrier F) = ![0,0,1,0,0,0,0,0] := by
    funext i; fin_cases i <;> simp [E,basisVector]
  unfold longMatrix
  rw [h1, h2, factor_action t ht, factor_action t ht]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem longMatrix_mul (g h : local₂ (F := F)) :
    longMatrix (g.val * h.val) = longMatrix g.val * longMatrix h.val := by
  obtain ⟨t,M,ht,hg⟩ := factor g
  obtain ⟨u,N,hu,hh⟩ := factor h
  rw [hg,hh,longMatrix_factor t ht,longMatrix_factor u hu]
  have h1 : (E 1 : Carrier F) = ![0,1,0,0,0,0,0,0] := by
    funext i; fin_cases i <;> simp [E,basisVector]
  have h2 : (E 2 : Carrier F) = ![0,0,1,0,0,0,0,0] := by
    funext i; fin_cases i <;> simp [E,basisVector]
  have act (x : Carrier F) :
      ((unipotentProduct t * blockHom M) * (unipotentProduct u * blockHom N)).val x =
      (unipotentProduct t * blockHom M).val ((unipotentProduct u * blockHom N).val x) := rfl
  unfold longMatrix
  rw [h1, h2, act, act, factor_action u hu, factor_action u hu,
    factor_action t ht, factor_action t ht]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The action on the distinguished plane modulo its first-vector line. -/
def longSLHom : local₂ (F := F) →* SL(2,F) where
  toFun g := ⟨longMatrix g.val, by
    obtain ⟨t,M,ht,hg⟩ := factor g
    rw [hg,longMatrix_factor t ht]
    exact M.property⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [longMatrix,E,basisVector]
  map_mul' g h := by exact Subtype.ext (longMatrix_mul g h)

end Atlas.G2.LieParabolicSetup
namespace Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2]

/-- The explicit SL₂ block is a section of the long-local quotient map. -/
def longSLSection : SL(2,F) →* local₂ (F := F) :=
  blockHom.codRestrict local₂ block_mem_local₂

@[simp] theorem longSLHom_section (M : SL(2,F)) :
    longSLHom (longSLSection M) = M := by
  apply Subtype.ext
  change longMatrix (blockHom M) = M.val
  simpa only [unipotentProduct_zero, one_mul] using
    (longMatrix_factor (0 : Fin 6 → F) rfl M)

theorem longSLHom_surjective : Function.Surjective (longSLHom (F := F)) :=
  fun M => ⟨longSLSection M, longSLHom_section M⟩

/-- The kernel consists exactly of the five positive roots other than root E. -/
theorem longSLHom_ker : (longSLHom (F := F)).ker = radical₂.subgroupOf local₂ := by
  ext g
  change longSLHom g = 1 ↔ g.val ∈ radical₂
  constructor
  · intro hg
    obtain ⟨t,M,ht,he⟩ := factor g
    have hm : M = 1 := by
      apply Subtype.ext
      have hx := congrArg Subtype.val hg
      change longMatrix g.val = _ at hx
      rwa [he,longMatrix_factor t ht] at hx
    rw [he,hm,map_one,mul_one]
    exact ⟨t,ht,rfl⟩
  · rintro ⟨t,ht,he⟩
    apply Subtype.ext
    change longMatrix g.val = _
    rw [← he]
    simpa only [map_one,mul_one] using (longMatrix_factor t ht (1 : SL(2,F)))

/-- Normality of the radical is relative to the actual long local group. -/
instance radical₂_normal_in_local₂ :
    ((radical₂ (F := F)).subgroupOf local₂).Normal := by
  rw [← longSLHom_ker]
  infer_instance

theorem local₂_le_normalizer_radical₂ :
    local₂ (F := F) ≤ Subgroup.normalizer (radical₂ (F := F) : Set (Model F)) :=
  Subgroup.le_normalizer_of_normal_subgroupOf radical₂_le_local₂

noncomputable def local₂RadicalQuotientEquivSL :
    local₂ (F := F) ⧸ radical₂.subgroupOf local₂ ≃* SL(2,F) :=
  (QuotientGroup.quotientMulEquivOfEq longSLHom_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective longSLHom longSLHom_surjective)

end Atlas.G2.LieParabolicSetup

namespace Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F] [CharP F 2]

/-- The concrete five-root subgroup is the entire two-core in the local group. -/
theorem local₂_pCore [Finite F] :
    pCore 2 (local₂ (F := F)) = radical₂.subgroupOf local₂ := by
  apply le_antisymm
  · rw [← longSLHom_ker, ← MonoidHom.comap_bot]
    apply Subgroup.map_le_iff_le_comap.mp
    have hn : ((pCore 2 (local₂ (F := F))).map longSLHom).Normal :=
      Subgroup.Normal.map inferInstance longSLHom longSLHom_surjective
    have hp : IsPGroup 2 ((pCore 2 (local₂ (F := F))).map longSLHom) :=
      pCore_isPGroup.map longSLHom
    have hle : (pCore 2 (local₂ (F := F))).map longSLHom ≤ pCore 2 SL(2,F) :=
      le_sSup ⟨hn, hp⟩
    simpa only [Matrix.SL2.twoCore_eq_bot] using hle
  · exact le_sSup ⟨inferInstance, radical₂_isTwoGroup.comap_subtype⟩

/-- The core equality viewed in the ambient octonion automorphism group. -/
theorem local₂_pCoreIn [Finite F] : (local₂ (F := F)).pCoreIn 2 = radical₂ := by
  rw [Subgroup.pCoreIn, local₂_pCore, Subgroup.map_subgroupOf_eq_of_le radical₂_le_local₂]

noncomputable def local₂CoreEquivRadical [Finite F] :
    pCore 2 (local₂ (F := F)) ≃* radical₂ (F := F) :=
  (MulEquiv.subgroupCongr local₂_pCore).trans
    (Subgroup.subgroupOfEquivOfLe radical₂_le_local₂)

theorem card_local₂_pCore [Finite F] :
    Nat.card (pCore 2 (local₂ (F := F))) = Nat.card F ^ 5 := by
  rw [Nat.card_congr local₂CoreEquivRadical.toEquiv, card_radical₂]

theorem card_local₂_pCore_binary :
    Nat.card (pCore 2 (local₂ (F := ZMod 2))) = 32 := by
  rw [card_local₂_pCore]
  norm_num

/-- In characteristic two the scalar center of SL₂ is trivial. -/
theorem longSL_center_eq_bot : Subgroup.center SL(2,F) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro A hA
  obtain ⟨r, hr, hs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr2 : r ^ 2 = 1 := by simpa only [Fintype.card_fin] using hr
  have hr1 : r = 1 := by
    rcases sq_eq_one_iff.mp hr2 with he | he
    · exact he
    · simpa only [CharTwo.neg_eq] using he
  apply Subtype.ext
  rw [← hs, hr1]
  simp

/-- The canonical central quotient, as an equivalence in characteristic two. -/
noncomputable def longSLEquivPSL : SL(2,F) ≃* PSL(2,F) :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center SL(2,F)))
    ⟨(MonoidHom.ker_eq_bot_iff _).mp (by
      rw [QuotientGroup.ker_mk', longSL_center_eq_bot]),
     QuotientGroup.mk'_surjective _⟩

/-- The long-local quotient by its actual two-core, including the binary field. -/
noncomputable def local₂CoreQuotientEquivPSL [Finite F] :
    local₂ (F := F) ⧸ pCore 2 (local₂ (F := F)) ≃* PSL(2,F) :=
  (QuotientGroup.quotientMulEquivOfEq local₂_pCore).trans
    (local₂RadicalQuotientEquivSL.trans longSLEquivPSL)

/-- The full G₂(2) local group has quotient PSL₂(2). -/
noncomputable def local₂BinaryCoreQuotientEquivPSL :
    local₂ (F := ZMod 2) ⧸ pCore 2 (local₂ (F := ZMod 2)) ≃* PSL(2,ZMod 2) :=
  local₂CoreQuotientEquivPSL

@[simp] theorem local₂CoreQuotientEquivPSL_mk [Finite F] (g : local₂ (F := F)) :
    local₂CoreQuotientEquivPSL (QuotientGroup.mk g) =
      QuotientGroup.mk (longSLHom g) := rfl

variable {K : Type*} [Field K] [CharP K 2]

/-- The quotient map commutes with entrywise transport, in particular every field automorphism. -/
theorem longSLHom_field (e : F ≃+* K) (g : local₂ (F := F)) :
    longSLHom (local₂FieldEquiv e g) =
      Matrix.SpecialLinearGroup.map e.toRingHom (longSLHom g) := by
  have he (i : Fin 8) : mapCoefficients e (E i) = E i := by
    funext j
    simp [mapCoefficients, E, basisVector, Pi.single_apply, apply_ite e]
  have ha (i : Fin 8) : (fieldEquiv e g.val).val (E i) =
      mapCoefficients e (g.val.val (E i)) := by
    simpa only [he] using fieldEquiv_action e g.val (E i)
  apply Subtype.ext
  change longMatrix (fieldEquiv e g.val) = (longMatrix g.val).map e
  unfold longMatrix
  rw [ha, ha]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

end Atlas.G2.LieParabolicSetup
