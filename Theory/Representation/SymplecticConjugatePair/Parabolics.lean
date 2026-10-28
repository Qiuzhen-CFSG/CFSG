module

public import Theory.Representation.SymplecticConjugatePair
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank

/-!
# The plane-radical witness on the conjugate symplectic pair

The actual kernel of the plane-local restriction map, placed in Sp₄(F),
consists of symmetric upper shears. Its fixed space on the natural-plus-graph
pair is the natural plane times the conjugate point. Testing the two long
roots gives necessity, and the shear matrices and exceptional-minor formula
give sufficiency. Thus its binary fixed codimension is 5n, while its order
is 2^(3n) and its binary rank is 3n.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.7,
printed pp.388–389. This is the plane-parabolic radical calculation; the
other parabolic and arbitrary elementary subgroups require further geometry.
-/

@[expose] public section

open scoped Matrix
open Matrix Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
namespace SymplecticConjugatePair
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

noncomputable def planeRadical : Subgroup (Sp F) :=
  (Plane.radical (F := F)).map planeLocal.subtype

omit [CharP F 2] [Finite F] [Algebra (ZMod 2) F] in
lemma mem_planeRadical_iff (g : Sp F) : g ∈ planeRadical ↔
    ∃ B : Plane.symmetricMatrices F, Plane.shearSp B = g := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨(Plane.radicalEquiv ⟨q,hq⟩).toAdd, ?_⟩
    exact congrArg (fun z : Plane.radical => z.val.val)
      (Plane.radicalEquiv.symm_apply_apply ⟨q,hq⟩)
  · rintro ⟨B, rfl⟩
    exact ⟨Plane.shear B, Plane.quotientMap_shear B, rfl⟩

omit [CharP F 2] [Finite F] [Algebra (ZMod 2) F] in
private lemma upperLong_mem (i : Fin 2) (t : F) :
    rootElement (if i = 0 then 0 else 2) t ∈ planeRadical := by
  apply (mem_planeRadical_iff _).mpr
  refine ⟨⟨Matrix.single i i t, ?_⟩, ?_⟩
  · change (Matrix.single i i t)ᵀ = Matrix.single i i t
    simp only [Matrix.transpose_single]
  · fin_cases i <;> rfl

lemma planeRadical_fixedSpace : fixedSpace (graphPair (F := F)) planeRadical =
    ((plane F).prod (point F)).restrictScalars (ZMod 2) := by
  ext v
  constructor
  · intro hv
    have h0 := (root_fixed_iff 0 (one_ne_zero : (1 : F) ≠ 0) v).mp
      (hv ⟨_, upperLong_mem 0 1⟩)
    have h2 := (root_fixed_iff 2 (one_ne_zero : (1 : F) ≠ 0) v).mp
      (hv ⟨_, upperLong_mem 1 1⟩)
    simp only [rootCoordinates, funext_iff, Fin.forall_fin_succ,
      Matrix.cons_val_zero, Pi.zero_apply] at h0 h2
    change v.1 ∈ plane F ∧ v.2 ∈ point F
    simp only [mem_plane, mem_point_iff, Fin.forall_fin_two]
    tauto
  · intro hv g
    change v.1 ∈ plane F ∧ v.2 ∈ point F at hv
    rcases hv with ⟨hx,hy⟩
    have hxc := hx 0
    have hxd := hx 1
    obtain ⟨hyb, hycd⟩ := (mem_point_iff _).mp hy
    have hyc := hycd 0
    have hyd := hycd 1
    obtain ⟨B,hB⟩ := (mem_planeRadical_iff g.val).mp g.property
    change pair graphAut g.val v = v
    rw [← hB]
    change (symplecticNatural 2 (Plane.shearSp B) v.1,
      symplecticNatural 2 (graphAut (Plane.shearSp B)) v.2) = v
    rw [graphAut_apply]
    simp [Prod.ext_iff, funext_iff, Sum.forall, Fin.forall_fin_two,
      symplecticNatural_apply, Plane.shearSp, graphEnd, graphMatrix, minor,
      first, second, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Fin.sum_univ_two, fromBlocks, one_apply, hxc,hxd,hyb,hyc,hyd]

lemma planeRadical_fixedCodim {n : ℕ} (hF : Nat.card F = 2^n) :
    fixedCodim (graphPair (F := F)) planeRadical = 5*n := by
  have hdim := fixedCodim_add_finrank (graphPair (F := F)) planeRadical
  rw [planeRadical_fixedSpace, finrank_space hF] at hdim
  have hf : Module.finrank (ZMod 2)
      (((plane F).prod (point F)).restrictScalars (ZMod 2)) = 3*n := by
    rw [← Module.finrank_mul_finrank (ZMod 2) F, coefficient_finrank hF]
    have he : ((plane F).prod (point F)) ≃ₗ[F] (plane F × point F) := {
      toFun v := (⟨v.val.1, v.property.1⟩,⟨v.val.2,v.property.2⟩)
      invFun v := ⟨(v.1.val,v.2.val),⟨v.1.property,v.2.property⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    rw [(((plane F).prod (point F)).restrictScalarsEquiv (ZMod 2)).finrank_eq,
      he.finrank_eq, Module.finrank_prod, finrank_plane, finrank_point]
    omega
  rw [hf] at hdim
  omega

omit [CharP F 2] [Algebra (ZMod 2) F] in
lemma card_planeRadical : Nat.card (planeRadical (F := F)) = Nat.card F^3 := by
  have he := (Plane.radical (F := F)).equivMapOfInjective
    planeLocal.subtype Subtype.val_injective
  exact (Nat.card_congr he.toEquiv).symm.trans EvenTwoRank.card_plane_radical

omit [CharP F 2] [Algebra (ZMod 2) F] in
lemma rank_planeRadical {n : ℕ} (hF : Nat.card F = 2^n) :
    rank (planeRadical (F := F)) = 3*n := by
  rw [Representation.BinaryOffender.rank, card_planeRadical, hF, ← pow_mul]
  simp [Nat.mul_comm]

omit [Finite F] [Algebra (ZMod 2) F] in
lemma planeRadical_elementary : IsElementaryAbelian 2 (planeRadical (F := F)) :=
  IsElementaryAbelian.map_subtype
end SymplecticConjugatePair
