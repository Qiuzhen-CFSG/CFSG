module

public import Theory.SpecificGroups.PSL3.LinearThreeFieldTransport
public import Theory.SpecificGroups.PSL3.LinearThreeOuterExtensions.Diagram

/-!
# Field transport of the literal degree-three parabolics and diagram action

Entrywise field transport preserves the zero-coordinate conditions defining
both standard maximal parabolics and their common Borel. The projective
transport keeps the actual scalar quotient. Transport of automorphisms then
preserves their action on the two inner-conjugacy classes with the same Bool
node labels, so the geometric diagram permutations agree exactly.

This lets the actual Mc action in Aschbacher–Smith 14.2.12–13, printed
pp.983–984, be transferred from any field of order four to the canonical
field without replacing the marked parabolic classes. The coefficient
transport is the attributed ATLAS construction in the imported module.
-/

public section

open scoped MatrixGroups
open Subgroup

namespace Matrix.PSL3.LinearThree.FieldTransport
open Matrix.PSL3.LinearThree.OuterExtensions Matrix.PSL3.RootPlaneGeometry
variable {F K : Type*} [Field F] [Finite F] [Field K] [Finite K]

theorem mem_pointParabolicSL_field_iff (s : F ≃+* K) (g : SL(3,F)) :
    Atlas.fieldEquivSL 3 s g ∈ pointParabolicSL K ↔ g ∈ pointParabolicSL F := by
  rw [mem_pointParabolicSL_iff, mem_pointParabolicSL_iff]
  change (s (g.val 1 0) = 0 ∧ s (g.val 2 0) = 0) ↔ _
  simp

theorem mem_lineParabolicSL_field_iff (s : F ≃+* K) (g : SL(3,F)) :
    Atlas.fieldEquivSL 3 s g ∈ lineParabolicSL K ↔ g ∈ lineParabolicSL F := by
  rw [mem_lineParabolicSL_iff, mem_lineParabolicSL_iff]
  change (s (g.val 2 0) = 0 ∧ s (g.val 2 1) = 0) ↔ _
  simp

private theorem map_eq_of_mem_iff {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (P : Subgroup X) (Q : Subgroup Y)
    (h : ∀ x, e x ∈ Q ↔ x ∈ P) : P.map e.toMonoidHom = Q := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact (h x).mpr hx
  · intro y hy
    refine ⟨e.symm y, (h _).mp ?_, e.apply_symm_apply y⟩
    simpa only [e.apply_symm_apply] using hy

omit [Finite F] [Finite K] in
private theorem field_map_projective (s : F ≃+* K)
    (P : Subgroup SL(3,F)) (Q : Subgroup SL(3,K))
    (h : ∀ x, Atlas.fieldEquivSL 3 s x ∈ Q ↔ x ∈ P) :
    (P.map (projection F)).map (Atlas.fieldEquivPSL 3 s).toMonoidHom =
      Q.map (projection K) := by
  have hc : (Atlas.fieldEquivPSL 3 s).toMonoidHom.comp (projection F) =
      (projection K).comp (Atlas.fieldEquivSL 3 s).toMonoidHom := by
    ext x
    exact Atlas.fieldEquivPSL_mk 3 s x
  rw [Subgroup.map_map, hc, ← Subgroup.map_map, map_eq_of_mem_iff _ P Q h]

theorem field_map_pointParabolic (s : F ≃+* K) :
    (pointParabolic F).map (Atlas.fieldEquivPSL 3 s).toMonoidHom = pointParabolic K := by
  exact field_map_projective s _ _ (mem_pointParabolicSL_field_iff s)

theorem field_map_lineParabolic (s : F ≃+* K) :
    (lineParabolic F).map (Atlas.fieldEquivPSL 3 s).toMonoidHom = lineParabolic K := by
  exact field_map_projective s _ _ (mem_lineParabolicSL_field_iff s)

theorem field_map_borel (s : F ≃+* K) :
    (borel F).map (Atlas.fieldEquivPSL 3 s).toMonoidHom = borel K := by
  apply field_map_projective s
  intro x
  simp only [borelSL, mem_inf, mem_pointParabolicSL_field_iff,
    mem_lineParabolicSL_field_iff]

theorem field_map_parabolic (s : F ≃+* K) (b : Bool) :
    (parabolic F b).map (Atlas.fieldEquivPSL 3 s).toMonoidHom = parabolic K b := by
  cases b
  · exact field_map_lineParabolic s
  · exact field_map_pointParabolic s

private theorem map_congr {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (a : MulAut X) (P : Subgroup X) :
    (P.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom =
      (P.map a.toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

private theorem map_conj {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (P : Subgroup X) (g : X) :
    (P.map e.toMonoidHom).map (MulAut.conj (e g)).toMonoidHom =
      (P.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulAut.conj_apply, map_mul, map_inv]

theorem mapsParabolicType_congr_iff (s : F ≃+* K) (a : MulAut PSL(3,F))
    (b c : Bool) :
    MapsParabolicType K (MulAut.congr (Atlas.fieldEquivPSL 3 s) a) b c ↔
      MapsParabolicType F a b c := by
  let e := Atlas.fieldEquivPSL 3 s
  constructor
  · rintro ⟨g,hg⟩
    refine ⟨e.symm g,?_⟩
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [← map_congr, ← map_conj, e.apply_symm_apply]
    simpa only [e,field_map_parabolic] using hg
  · rintro ⟨g,hg⟩
    refine ⟨e g,?_⟩
    have hm := congrArg (fun P => P.map e.toMonoidHom) hg
    rw [← map_congr, ← map_conj] at hm
    simpa only [e,field_map_parabolic] using hm

theorem preservesPointType_congr_iff (s : F ≃+* K) (a : MulAut PSL(3,F)) :
    PreservesPointType K (MulAut.congr (Atlas.fieldEquivPSL 3 s) a) ↔
      PreservesPointType F a := mapsParabolicType_congr_iff s a true true

theorem preservesLineType_congr_iff (s : F ≃+* K) (a : MulAut PSL(3,F)) :
    PreservesLineType K (MulAut.congr (Atlas.fieldEquivPSL 3 s) a) ↔
      PreservesLineType F a := mapsParabolicType_congr_iff s a false false

theorem movesDiagram_congr_iff (s : F ≃+* K) (a : MulAut PSL(3,F)) :
    ¬ (PreservesPointType K (MulAut.congr (Atlas.fieldEquivPSL 3 s) a) ∧
      PreservesLineType K (MulAut.congr (Atlas.fieldEquivPSL 3 s) a)) ↔
    ¬ (PreservesPointType F a ∧ PreservesLineType F a) := by
  rw [preservesPointType_congr_iff, preservesLineType_congr_iff]

theorem diagramAction_congr {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^n) (hK : Nat.card K = 2^n)
    (s : F ≃+* K) (a : MulAut PSL(3,F)) :
    diagramAction K hn hK (MulAut.congr (Atlas.fieldEquivPSL 3 s) a) =
      diagramAction F hn hF a := by
  ext b
  apply (diagramAction_apply_iff K hn hK _ b _).mpr
  exact (mapsParabolicType_congr_iff s a b _).mpr (diagramAction_spec F hn hF a b)

theorem diagramAction_ne_one_congr_iff {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2^n) (hK : Nat.card K = 2^n)
    (s : F ≃+* K) (a : MulAut PSL(3,F)) :
    diagramAction K hn hK (MulAut.congr (Atlas.fieldEquivPSL 3 s) a) ≠ 1 ↔
      diagramAction F hn hF a ≠ 1 := by
  rw [diagramAction_congr hn hF hK]

end Matrix.PSL3.LinearThree.FieldTransport
