module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceComparison.Edge
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.TenConjugacy

/-!
# The dihedral marking and shared S₃ in the source comparison

After aligning the pointwise edge fixers, conjugacy of their order-ten
subgroups aligns the actual dihedral subgroups. The adjustment lies in
the target edge fixer, so it preserves that fixer and the cubic marking.
Their centralizers inside the vertex groups are therefore identified.
These are precisely the shared S₃ subgroups of the local A₅ groups.

The final theorem applies these maps to the literal source and ATLAS
uniqueness systems. Extension to the local A₅ and preservation of the
local setwise edge stabilizer remain separate obligations.
Source: Aschbacher, *Sporadic Groups* (1994), 47.10, pp.266–267.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceComparison
open SourceLocal SourceLocal.PrimeNormalizers.ThreeLocal
open Theory.GroupTheory.GraphUniquenessSystem
open Sporadic.LeechRelated.J2
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
variable (D : Seed G) (F : EdgeFrame D)

/-- Align the dihedral markings while retaining the cubic and full edge fixer. -/
theorem marked_edge_comparison :
    ∃ e : M D ≃* RecognitionGeometry.M,
      (∀ m : M D, m ∈ XM D ↔ e m ∈ RecognitionGeometry.VertexExtension.XM) ∧
      (∀ m : M D, (m : G) ∈ edgeFixer G D.base F.y ↔
        (e m : Carrier) ∈ RecognitionGeometry.E) ∧
      (∀ m : M D, (m : G) ∈ F.B ↔ (e m : Carrier) ∈ RecognitionGeometry.B) := by
  obtain ⟨_, eM, _, hX, hE⟩ := edge_comparison D F
  let EM := (edgeFixer G D.base F.y).subgroupOf (M D)
  let TM := RecognitionGeometry.E.subgroupOf RecognitionGeometry.M
  have hEle : edgeFixer G D.base F.y ≤ M D := by
    change edgeFixer G D.base F.y ≤ normalizer (D.base.val : Set G)
    rw [← D.stabilizer_eq_normalizer D.base]
    exact inf_le_left
  let eE : EM ≃* TM :=
    { toFun := fun x => ⟨eM x, (hE x).mp x.property⟩
      invFun := fun y => ⟨eM.symm y, (hE _).mpr (by rw [eM.apply_symm_apply]; exact y.property)⟩
      left_inv := fun _ => Subtype.ext (eM.symm_apply_apply _)
      right_inv := fun _ => Subtype.ext (eM.apply_symm_apply _)
      map_mul' := fun _ _ => Subtype.ext (map_mul eM _ _) }
  let eT : TM ≃* RecognitionGeometry.E :=
    subgroupOfEquivOfLe (show RecognitionGeometry.E ≤ RecognitionGeometry.M from inf_le_left)
  let e' := eE.trans eT
  let BM := F.B.subgroupOf (M D)
  have hBM : BM ≤ EM := fun _ hx => F.B_le hx
  let BE := BM.subgroupOf EM
  let BT := RecognitionGeometry.B.subgroupOf RecognitionGeometry.E
  have hBE : Nat.card BE = 10 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (F.B_le.trans hEle)).toEquiv, F.card_B]
  have hBT : Nat.card BT = 10 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe RecognitionGeometry.B_le_E).toEquiv,
      RecognitionGeometry.card_B]
  obtain ⟨c, hc⟩ := alternatingGroup.FiveLocalGeometry.ten_subgroups_conjugate
    RecognitionGeometry.LocalA5.edgeEquiv (BE.map e'.toMonoidHom) BT
    (by rw [card_map_of_injective e'.injective, hBE]) hBT
  let m : RecognitionGeometry.M := ⟨c, c.property.1⟩
  let d := eM.trans (MulAut.conj m)
  have hBforward (x : M D) (hx : (x : G) ∈ F.B) :
      (d x : Carrier) ∈ RecognitionGeometry.B := by
    have hxe : x ∈ EM := F.B_le hx
    have him := mem_map_of_mem (MulAut.conj c).toMonoidHom
      (mem_map_of_mem e'.toMonoidHom (show (⟨x, hxe⟩ : EM) ∈ BE from hx))
    rw [hc] at him
    exact him
  have hmE : m ∈ TM := c.property
  have hconjE (x : RecognitionGeometry.M) :
      x ∈ TM ↔ m * x * m⁻¹ ∈ TM :=
    (mem_normalizer_iff.mp (TM.le_normalizer hmE)) x
  have hBback (x : M D) (hx : (d x : Carrier) ∈ RecognitionGeometry.B) :
      (x : G) ∈ F.B := by
    have hxe : x ∈ EM := (hE x).mpr
      ((hconjE (eM x)).mpr (RecognitionGeometry.B_le_E hx))
    have him : (MulAut.conj c) (e' ⟨x, hxe⟩) ∈ BT := hx
    rw [← hc, mem_map_equiv, MulEquiv.symm_apply_apply, mem_map_equiv,
      MulEquiv.symm_apply_apply] at him
    exact him
  refine ⟨d, ?_, ?_, fun x => ⟨hBforward x, hBback x⟩⟩
  · intro x
    rw [hX]
    exact (mem_normalizer_iff.mp (show m ∈ normalizer
      (RecognitionGeometry.VertexExtension.XM : Set RecognitionGeometry.M) from
      by rw [normalizer_eq_top]; trivial)) (eM x)
  · intro x
    exact (hE x).trans (hconjE (eM x))

omit [IsSimpleGroup G] in
/-- Preserving B transports its centralizer inside the vertex normalizer.
This is the actual shared S₃ of the two local A₅ groups. -/
theorem vertex_overlap_of_marked (e : M D ≃* RecognitionGeometry.M)
    (hB : ∀ m : M D, (m : G) ∈ F.B ↔ (e m : Carrier) ∈ RecognitionGeometry.B) :
    ∀ m : M D, (m : G) ∈ F.K ↔ (e m : Carrier) ∈ RecognitionGeometry.K := by
  have hBle : F.B ≤ M D := by
    apply F.B_le.trans
    change edgeFixer G D.base F.y ≤ normalizer (D.base.val : Set G)
    rw [← D.stabilizer_eq_normalizer D.base]
    exact inf_le_left
  intro m
  constructor
  · intro hm
    apply mem_centralizer_iff.mpr
    intro b hb
    let bM : RecognitionGeometry.M := ⟨b, (RecognitionGeometry.B_le_E hb).1⟩
    have he : (e.symm bM : G) ∈ F.B := (hB _).mpr (by simpa using hb)
    have hc : (e.symm bM : M D) * m = m * e.symm bM :=
      Subtype.ext (mem_centralizer_iff.mp hm _ he)
    have hh := congrArg e hc
    rw [map_mul, map_mul, e.apply_symm_apply] at hh
    exact congrArg Subtype.val hh
  · intro hm
    apply mem_centralizer_iff.mpr
    intro b hb
    let bM : M D := ⟨b, hBle hb⟩
    have he := (hB bM).mp hb
    have hc : e bM * e m = e m * e bM :=
      Subtype.ext (mem_centralizer_iff.mp hm _ he)
    have hh : bM * m = m * bM := e.injective (by simpa only [map_mul] using hc)
    exact congrArg Subtype.val hh

/-- The vertex comparison now also aligns the actual local vertex overlap. -/
theorem vertex_marked_comparison (D : Seed G) :
    ∃ e : (sourceSystem D).vertexGroup ≃* ConcreteSystem.system.vertexGroup,
      (∀ a : (sourceSystem D).vertexGroup,
        (a : G) ∈ D.X ↔ (e a : Carrier) ∈ RecognitionGeometry.X) ∧
      (∀ a : (sourceSystem D).vertexGroup,
        (a : G) ∈ (sourceSystem D).edgeGroup ↔
          (e a : Carrier) ∈ ConcreteSystem.system.edgeGroup) ∧
      (∀ a : (sourceSystem D).vertexGroup,
        (a : G) ∈ (sourceSystem D).H ↔ (e a : Carrier) ∈ ConcreteSystem.system.H) := by
  obtain ⟨eM, hX, hE, hB⟩ := marked_edge_comparison D (sourceFrame D)
  have hK := vertex_overlap_of_marked D (sourceFrame D) eM hB
  have hsource : (sourceSystem D).vertexGroup = M D :=
    D.stabilizer_eq_normalizer D.base
  let e := (MulEquiv.subgroupCongr hsource).trans
    (eM.trans (MulEquiv.subgroupCongr ConcreteSystem.system_vertexGroup.symm))
  refine ⟨e, fun a => hX (MulEquiv.subgroupCongr hsource a), ?_, ?_⟩
  · intro a
    rw [ConcreteSystem.system_edgeGroup]
    exact hE (MulEquiv.subgroupCongr hsource a)
  · intro a
    rw [ConcreteSystem.system_local]
    exact hK (MulEquiv.subgroupCongr hsource a)

end CFSG.Quasithin.Janko23.J2Recognition.SourceComparison
