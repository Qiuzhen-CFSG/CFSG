module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.IncidenceTransport
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.ResidueCharts

/-!
# All five line labels under the literal point chart

Reindexing the restriction pairing by an actual M24 permutation transports
each Golay octad radical. The same action transports their sum and its octad
membership tests, including both radical-defined line labels. Consequently
all five native labels agree with the unchanged ambient LineType under the
original Todd chart at every point. Restricting that equivalence identifies
each ambient valency with its native valency.

These are transport theorems, not the unproved five-orbit classification or
its numerical valencies. They supply the exact maps for the remaining
AS91 (5.4) assembly without adding an orbital premise to LocalData.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (3.4), (5.4),
pp.594,600–601, DOI 10.1007/BF01232280.
-/

public section
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeOrbitals
open Sporadic.Mathieu SourceCycleBase.Native MathieuCode

theorem radical_transport (g : M24) (A : Finset (Fin 24))
    (v : golay) (hv : v ∈ radical A) : golayRepresentation g v ∈ radical (g • A) := by
  intro w
  change (∑ i ∈ A.image (fun i => g • i), v.val (g⁻¹ • i) * w.val i) = 0
  rw [Finset.sum_image (fun _ _ _ _ he => (MulAction.injective g) he)]
  have hh := hv (golayRepresentation g⁻¹ w)
  change (∑ i ∈ A, v.val i * w.val (g • i)) = 0 at hh
  simpa only [inv_smul_smul] using hh

theorem radicalSum_transport (g : M24) (l : Line) (v : golay)
    (hv : v ∈ radicalSum l) : golayRepresentation g v ∈ radicalSum (g • l) := by
  have hh : radicalSum l ≤ (radicalSum (g • l)).comap (golayRepresentation g) := by
    apply iSup_le
    intro A w hw
    exact (le_iSup (fun B : {B // B ∈ (g • l).parts} => radical B.val)
      ⟨g • A.val,Finset.smul_mem_smul_finset A.property⟩) (radical_transport g A.val w hw)
  exact hh hv

theorem octads_transport (g : M24) (l m : Line) (A : Finset (Fin 24))
    (hA : A ∈ octadsInRadicalSum l m) :
    g • A ∈ octadsInRadicalSum (g • l) (g • m) := by
  obtain ⟨hA,v,hv,he⟩ := hA
  refine ⟨Finset.smul_mem_smul_finset hA,golayRepresentation g v,
    radicalSum_transport g l v hv,?_⟩
  change fullRepresentation g v.val = wordOfSet (g • A)
  rw [he]
  exact permute_wordOfSet g.val A

theorem octads_transport_iff (g : M24) (l m : Line) (A : Finset (Fin 24)) :
    g • A ∈ octadsInRadicalSum (g • l) (g • m) ↔ A ∈ octadsInRadicalSum l m := by
  refine ⟨fun hh => ?_,octads_transport g l m A⟩
  simpa only [inv_smul_smul] using octads_transport g⁻¹ (g • l) (g • m) (g • A) hh

theorem octads_card_transport (g : M24) (l m : Line) :
    (octadsInRadicalSum (g • l) (g • m)).ncard = (octadsInRadicalSum l m).ncard := by
  rw [←Nat.card_coe_set_eq,←Nat.card_coe_set_eq]
  symm
  exact Nat.card_congr ((MulAction.toPerm g).subtypeEquiv
    (p := fun A => A ∈ octadsInRadicalSum l m)
    (q := fun A => A ∈ octadsInRadicalSum (g • l) (g • m))
    (fun A => (octads_transport_iff g l m A).symm))

theorem delta_transport (g : M24) (i : Fin 5) (l m : Line)
    (ht : Delta i l m) : Delta i (g • l) (g • m) := by
  fin_cases i
  · exact congrArg (g • ·) ht
  · change (g • l.parts) ≠ (g • m.parts) ∧ _
    refine ⟨(MulAction.injective g).ne ht.1,?_⟩
    obtain ⟨A,hA⟩ := ht.2
    exact ⟨g • A,Finset.mem_inter.mpr ⟨Finset.smul_mem_smul_finset (Finset.mem_inter.mp hA).1,
      Finset.smul_mem_smul_finset (Finset.mem_inter.mp hA).2⟩⟩
  · refine ⟨?_,coplanar_transport g rfl rfl ht.2⟩
    rw [Finset.disjoint_left]
    intro A hA hB
    obtain ⟨B,hB',rfl⟩ := Finset.mem_smul_finset.mp hA
    exact Finset.disjoint_left.mp ht.1 hB' ((Finset.smul_mem_smul_finset_iff g).mp hB)
  · exact (octads_card_transport g l m).trans ht
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro A hA
    have hh := octads_transport g⁻¹ (g • l) (g • m) A hA
    simp only [inv_smul_smul] at hh
    rw [ht] at hh
    exact hh

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence.NativeOrbitals

namespace Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
open Subgroup SourceCycleBase GraphUniquenessSystem
open Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {P : LocalGeometry.LocalSubgroups.PointData z}
variable {L : LocalGeometry.LocalSubgroups.LineData z P}

/-- All five labels, including the literal Golay radical tests, are independent
of the chosen representative of the base point. -/
theorem lineType_base (c : ResidueChart P L) (i : Fin 5)
    (l m : {l : Line L // OnLine L (Cosets.vertex P.M 1) l}) :
    LineType c i (Cosets.vertex P.M 1) l.val m.val ↔
      Native.Delta i (c.lines l) (c.lines m) := by
  constructor
  · rintro ⟨g,l',m',hg,hl,hm,ht⟩
    let n : P.M := ⟨g,(Cosets.vertex_eq_base _ _).mp hg⟩
    have hl' : P.projection n • c.lines l' = c.lines l :=
      Native.line_parts_injective (c.lines_equivariant n l' l hl).symm
    have hm' : P.projection n • c.lines m' = c.lines m :=
      Native.line_parts_injective (c.lines_equivariant n m' m hm).symm
    have hh := NativeOrbitals.delta_transport (P.projection n) i _ _ ht
    rwa [hl',hm'] at hh
  · intro ht
    exact ⟨1,l,m,rfl,one_smul _ _,one_smul _ _,ht⟩

/-- The same full native label comparison at every point, using the original
Todd chart and the same left-coset representative for both lines. -/
theorem lineType_at (c : ResidueChart P L) (i : Fin 5) (x : Point P)
    (l m : {l : Line L // OnLine L x l}) :
    LineType c i x l.val m.val ↔ Native.Delta i (c.linesAt x l) (c.linesAt x m) := by
  change _ ↔ Native.Delta i (c.lines _) (c.lines _)
  rw [←lineType_base]
  change LineType c i x l.val m.val ↔ LineType c i (Cosets.vertex P.M 1)
    ((representative x)⁻¹ • l.val) ((representative x)⁻¹ • m.val)
  rw [←ResidueChart.representative_inv_point x]
  exact (lineType_smul_iff c i x l.val m.val (representative x)⁻¹).symm

/-- The ambient valency of each of the five labels is its literal native
valency. This reduces the pending source orbit counts without assuming them. -/
theorem lineType_card (c : ResidueChart P L) (i : Fin 5) (x : Point P)
    (l : {l : Line L // OnLine L x l}) :
    {m | LineType c i x l.val m}.ncard =
      {m | Native.Delta i (c.linesAt x l) m}.ncard := by
  have incident (m : Line L) (hm : LineType c i x l.val m) : OnLine L x m := by
    obtain ⟨g,b,d,hx,_,rfl,_⟩ := hm
    have hh := incident_smul g d.property
    simpa only [OnLine,Cosets.smul_vertex,mul_one,hx] using hh
  let e := c.linesAt x
  let f : {m : Line L // LineType c i x l.val m} ≃
      {m : Native.Line // Native.Delta i (e l) m} := {
    toFun m := ⟨e ⟨m.val,incident m.val m.property⟩,
      (lineType_at c i x l ⟨m.val,incident m.val m.property⟩).mp m.property⟩
    invFun m := ⟨(e.symm m.val).val,(lineType_at c i x l (e.symm m.val)).mpr
      (by change Native.Delta i (e l) (e (e.symm m.val)); rw [e.apply_symm_apply]; exact m.property)⟩
    left_inv m := by
      apply Subtype.ext
      change (e.symm (e ⟨m.val,incident m.val m.property⟩)).val = m.val
      exact congrArg Subtype.val (e.symm_apply_apply _)
    right_inv m := by
      apply Subtype.ext
      change e (e.symm m.val) = m.val
      exact e.apply_symm_apply _ }
  rw [←Nat.card_coe_set_eq,←Nat.card_coe_set_eq]
  exact Nat.card_congr f

end Theory.GroupTheory.Recognition.JankoFour.SourceIncidence
