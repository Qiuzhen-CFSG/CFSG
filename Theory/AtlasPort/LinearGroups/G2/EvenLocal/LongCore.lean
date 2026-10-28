module

public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.GroupTheory.PCoreNormalizedOvergroup
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The full long parabolic in even-field G₂

The five-root two-core of the long local subgroup remains the two-core after
adjoining the split torus: the larger parabolic normalizes the local subgroup,
its core is characteristic, and both groups contain the standard Sylow subgroup.
The scalar/vector-stabilizer factorization then proves that this core is
self-centralizing inside the full parabolic. Commuting with root C kills the
scalar; commuting with roots A and B kills the remaining SL₂ block.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem
0.1.2(1), printed pp.3–4, and the G₂ local structure in F.1.12(I)(3), pp.262–264.
The coordinate definitions and factorization come from the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. This extension adds the
full-parabolic core and centralizer calculations, including the binary field.
-/

open Atlas.G2 Atlas.G2.Explicit Atlas.G2.PairStabilizer
open scoped MatrixGroups Pointwise
namespace Atlas.G2.EvenLocal
open LieParabolicSetup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The full long parabolic normalizes the concrete five-root radical. -/
public theorem parabolic₂_le_normalizer_radical₂ :
    parabolic₂ (F := F) ≤ Subgroup.normalizer (radical₂ (F := F) : Set (Model F)) := by
  rw [← local₂_pCoreIn]
  exact parabolic₂_le_normalizer_local₂.trans
    (Subgroup.normalizer_le_normalizer_characteristic_image local₂ (pCore 2 local₂))

/-- Its intrinsic two-core, mapped into the ambient G₂ group. -/
public theorem parabolic₂_pCoreIn : (parabolic₂ (F := F)).pCoreIn 2 = radical₂ := by
  have h := Subgroup.mapped_pCore_eq_of_normalized_local_pCore (sylow (F := F))
    local₂ parabolic₂ unipotent_le_local₂ local₂_le_parabolic₂
    (by
      change parabolic₂ ≤ Subgroup.normalizer ((local₂ (F := F)).pCoreIn 2 : Set (Model F))
      rw [local₂_pCoreIn]
      exact parabolic₂_le_normalizer_radical₂)
  exact h.trans local₂_pCoreIn

omit [Finite F] in
private theorem long_factor (g : parabolic₂ (F := F)) :
    ∃ (l : Fˣ) (t : Fin 6 → F) (M : SL(2,F)), t 4 = 0 ∧
      g.val = torus l 1 * (unipotentProduct t * blockHom M) := by
  let gp : pointStabilizer (K := F) :=
    ⟨g.val, by rw [← parabolic_eq_pointStabilizer]; exact g.property⟩
  let h : fixingFirstVector (K := F) := normalizePoint gp
  have hl : h.val ∈ local₂ := by rw [local₂_eq_fixingFirstVector]; exact h.property
  rw [← SetLike.mem_coe, local₂_eq_radical₂_mul_fixingPair] at hl
  obtain ⟨u, ⟨t, ht, rfl⟩, m, hm, he⟩ := hl
  refine ⟨lineScalar gp, t, imageSL ⟨m, hm⟩, ht, ?_⟩
  have hb := congrArg Subtype.val (block_imageSL ⟨m, hm⟩)
  change blockHom (imageSL ⟨m, hm⟩) = m at hb
  change unipotentProduct t * m = h.val at he
  rw [hb, he]
  change g.val = torus (lineScalar gp) 1 * ((torus (lineScalar gp) 1)⁻¹ * g.val)
  exact (mul_inv_cancel_left _ _).symm

omit [Finite F] in
set_option maxHeartbeats 800000 in
private theorem factor_scalar (l : Fˣ) (t : Fin 6 → F) (M : SL(2,F)) (ht : t 4 = 0)
    (hc : Commute (torus l 1 * (unipotentProduct t * blockHom M)) (rootC 1)) : l = 1 := by
  have h := congrArg (fun g : Model F => g.val (Atlas.SplitOctonion.basisVector 7) 3) hc.eq
  simp [unipotentProduct, rootA, rootB, rootC, rootD, rootE, rootF,
    rootAEquiv, rootBEquiv, rootCEquiv, rootDEquiv, rootEEquiv, rootFEquiv,
    rootALinear, rootBLinear, rootCLinear, rootDLinear, rootELinear, rootFLinear,
    rootAApply, rootBApply, rootCApply, rootDApply, rootEApply, rootFApply,
    torus, torusEquiv, torusLinear, torusWeights, blockHom, blockEquiv, blockLinear,
    Atlas.SplitOctonion.basisVector, ht, CharTwo.neg_eq, CharTwo.sub_eq_add] at h
  apply Units.ext
  apply inv_eq_one.mp
  linear_combination -h


omit [Finite F] in
set_option maxHeartbeats 800000 in
private theorem factor_block (t : Fin 6 → F) (M : SL(2,F)) (ht : t 4 = 0)
    (ha : Commute (unipotentProduct t * blockHom M) (rootA 1))
    (hb : Commute (unipotentProduct t * blockHom M) (rootB 1)) : M = 1 := by
  have h10 := congrArg (fun g : Model F => g.val (Atlas.SplitOctonion.basisVector 5) 0) ha.eq
  have h00 := congrArg (fun g : Model F => g.val (Atlas.SplitOctonion.basisVector 7) 1) ha.eq
  have h11 := congrArg (fun g : Model F => g.val (Atlas.SplitOctonion.basisVector 6) 0) ha.eq
  have h01 := congrArg (fun g : Model F => g.val (Atlas.SplitOctonion.basisVector 6) 0) hb.eq
  simp [unipotentProduct, rootA, rootB, rootC, rootD, rootE, rootF,
    rootAEquiv, rootBEquiv, rootCEquiv, rootDEquiv, rootEEquiv, rootFEquiv,
    rootALinear, rootBLinear, rootCLinear, rootDLinear, rootELinear, rootFLinear,
    rootAApply, rootBApply, rootCApply, rootDApply, rootEApply, rootFApply,
    blockHom, blockEquiv, blockLinear,
    Atlas.SplitOctonion.basisVector, ht, CharTwo.neg_eq, CharTwo.sub_eq_add] at h10 h00 h11 h01
  have h00' : M 0 0 = 1 := by linear_combination h00
  have h11' : M 1 1 = 1 := by linear_combination -h11
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00', h11', h01, h10]

omit [Finite F] in
/-- The radical centralizer is computed inside the full parabolic. -/
public theorem long_radical_selfCentralizing :
    Subgroup.centralizer ((radical₂ (F := F)).subgroupOf parabolic₂ : Set (parabolic₂ (F := F))) ≤
      radical₂.subgroupOf parabolic₂ := by
  intro g hg
  have hc (r : Model F) (hr : r ∈ radical₂) : Commute g.val r := by
    exact (congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hg
      ⟨r, local₂_le_parabolic₂ (radical₂_le_local₂ hr)⟩ hr)).symm
  have ha := hc (rootA 1) ⟨![1,0,0,0,0,0], rfl, by simp [unipotentProduct]⟩
  have hb := hc (rootB 1) ⟨![0,1,0,0,0,0], rfl, by simp [unipotentProduct]⟩
  have hd := hc (rootC 1) ⟨![0,0,1,0,0,0], rfl, by simp [unipotentProduct]⟩
  obtain ⟨l,t,M,ht,he⟩ := long_factor g
  have hl : l = 1 := factor_scalar l t M ht (he ▸ hd)
  have htor : torus (1 : Fˣ) 1 = 1 := (torusHom (K := F)).map_one
  rw [hl, htor, one_mul] at he
  have hm : M = 1 := factor_block t M ht (he ▸ ha) (he ▸ hb)
  change g.val ∈ radical₂
  rw [he, hm, map_one, mul_one]
  exact ⟨t,ht,rfl⟩


/-- Equality with the intrinsic two-core, not an ambient normality claim. -/
public theorem parabolic₂_pCore :
    pCore 2 (parabolic₂ (F := F)) = radical₂.subgroupOf parabolic₂ := by
  apply Subgroup.map_injective (parabolic₂ (F := F)).subtype_injective
  change (parabolic₂ (F := F)).pCoreIn 2 = _
  rw [parabolic₂_pCoreIn, Subgroup.map_subgroupOf_eq_of_le
    (radical₂_le_local₂.trans local₂_le_parabolic₂)]

/-- The full long parabolic has characteristic two. -/
public theorem parabolic₂_centralizer_pCore :
    Subgroup.centralizer (pCore 2 (parabolic₂ (F := F)) : Set (parabolic₂ (F := F))) ≤
      pCore 2 (parabolic₂ (F := F)) := by
  rw [parabolic₂_pCore]
  exact long_radical_selfCentralizing
end Atlas.G2.EvenLocal
