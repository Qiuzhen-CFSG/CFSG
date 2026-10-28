module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.FarPair
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.ResidueOvals

/-!
# Native incidence hitting in the original Todd residue

The native δ₄ representative and orbital transitivity prove (3.13.2)
for the actual ambient lines. Disjoint octads transport through the same
surjective Todd marking, giving (3.11.1) for each point-plane residue.
The ordinal partition then puts every nonfar two-step path in Rhat₂.
No finite geometry assertion is added to the earlier-source Input.

Source: Aschbacher–Segev (1991), (3.11.1), (3.13.2), and §7.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open GraphUniquenessSystem
open Theory.SpecificGroups.SymmetricSix
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {P : LocalGeometry.LocalSubgroups.PointData z} {L : LocalGeometry.LocalSubgroups.LineData z P}

namespace ResidueChart
variable (c : ResidueChart P L)

theorem lineType_of_native_at (x : Point P) (a b : {l : Line L // OnLine L x l})
    {i : Fin 5} (hd : Native.Delta i (c.linesAt x a) (c.linesAt x b)) :
    LineType c i x a.val b.val := by
  refine ⟨representative x,_,_,vertex_representative x,?_,?_,hd⟩
  · exact smul_inv_smul _ _
  · exact smul_inv_smul _ _

theorem not_delta_four_of_disjoint_base
    (a b : {l : Line L // OnLine L (Cosets.vertex P.M 1) l})
    {A B : Finset (Fin 24)} (hA : A ∈ (c.lines a).parts) (hB : B ∈ (c.lines b).parts)
    (hd : Disjoint A B) : ¬ LineType c 4 (Cosets.vertex P.M 1) a.val b.val := by
  rintro ⟨g,a',b',hg,ha,hb,ht⟩
  have hgM := (Cosets.vertex_eq_base P.M g).mp hg
  let m := P.projection ⟨g,hgM⟩
  have hea := c.lines_equivariant ⟨g,hgM⟩ a' a ha
  have heb := c.lines_equivariant ⟨g,hgM⟩ b' b hb
  have hA' : m⁻¹ • A ∈ (c.lines a').parts := by
    rw [hea] at hA
    simpa only [m,inv_smul_smul] using Finset.smul_mem_smul_finset (a := m⁻¹) hA
  have hB' : m⁻¹ • B ∈ (c.lines b').parts := by
    rw [heb] at hB
    simpa only [m,inv_smul_smul] using Finset.smul_mem_smul_finset (a := m⁻¹) hB
  exact Native.not_delta_four_of_disjoint hA' hB' (Native.disjoint_smul_octads m⁻¹ hd) ht

theorem not_delta_four_of_disjoint_at (x : Point P) (a b : {l : Line L // OnLine L x l})
    {A B : Finset (Fin 24)}
    (hA : A ∈ (c.linesAt x a).parts) (hB : B ∈ (c.linesAt x b).parts)
    (hd : Disjoint A B) : ¬ LineType c 4 x a.val b.val := by
  intro ht
  have ht' := lineType_smul (representative x)⁻¹ ht
  rw [representative_inv_point x] at ht'
  exact c.not_delta_four_of_disjoint_base _ _ hA hB hd ht'
end ResidueChart

namespace Input
variable {h : IsTypeJ4 z} (d : Input h)

/-- The literal ambient (3.13.2). The two δ₂ incidences are transported
from the native far pair by the retained transitivity of the actual orbital. -/
theorem delta_four_common_delta_two {x : Point d.P} {l m : Line d.L}
    (ht : LineType d.residue 4 x l m) :
    ∃ k, LineType d.residue 2 x l k ∧ LineType d.residue 2 x m k := by
  let e := d.residue.linesAt x
  let a := e.symm (Native.FarOrbit.seedLine 2)
  let b := e.symm Native.FarPair.line
  let c := e.symm (Native.FarOrbit.seedLine 5)
  have hab : LineType d.residue 4 x a.val b.val := by
    apply d.residue.lineType_of_native_at x a b
    simpa only [a,b,e,Equiv.apply_symm_apply] using Native.FarPair.delta_four
  have hac : LineType d.residue 2 x a.val c.val := by
    apply d.residue.lineType_of_native_at x a c
    simpa only [a,c,e,Equiv.apply_symm_apply] using Native.FarPair.common_delta_two.1
  have hbc : LineType d.residue 2 x b.val c.val := by
    apply d.residue.lineType_of_native_at x b c
    simpa only [b,c,e,Equiv.apply_symm_apply] using Native.FarPair.common_delta_two.2
  obtain ⟨g,hgx,hga,hgb⟩ := d.lineType_pair_transitive hab ht
  exact ⟨g • c.val,by simpa only [hgx,hga] using lineType_smul g hac,
    by simpa only [hgx,hgb] using lineType_smul g hbc⟩

/-- Source (3.11.1) in the original point-plane marking: each disc or oval
has a line outside the far orbital of any line through the point. -/
theorem residue_hits_nonfar {x : Point d.P} {π : Plane z}
    (hxπ : OnPlane d.P x π) (S : Finset Syntheme)
    (hS : Native.Polar.Oval S ∨ ∃ s, S = Native.Polar.disc s)
    {l : Line d.L} (hxl : OnLine d.L x l) :
    ∃ m : {m : Line d.L // OnLine d.L x m ∧ LineOnPlane d.L m π},
      d.residue.flagLines x π hxπ m ∈ S ∧ ¬ LineType d.residue 4 x l m.val := by
  let σ := d.residue.planesAt x ⟨π,hxπ⟩
  let a := d.residue.linesAt x ⟨l,hxl⟩
  obtain ⟨n,hn,A,hA,B,hB,hd⟩ := Native.residue_hits_nonfar σ
    (ResidueChart.tetradLabel σ) S hS a
  let m := (d.residue.flagLinesNative x π hxπ).symm n
  have he := (d.residue.flagLinesNative x π hxπ).apply_symm_apply n
  have parts : d.residue.linesAt x ⟨m.val,m.property.1⟩ = n.val := congrArg Subtype.val he
  refine ⟨m,?_,?_⟩
  · change Native.residueEquiv σ _ (d.residue.flagLinesNative x π hxπ m) ∈ S
    rw [he]
    exact hn
  · apply d.residue.not_delta_four_of_disjoint_at x ⟨l,hxl⟩ ⟨m.val,m.property.1⟩ hA
    · exact parts.symm ▸ hB
    · exact hd

/-- Every nonfar pair of lines gives the second source relation. This uses
the actual orbital partition, without identifying δ₃ with an arbitrary tag. -/
theorem ternary_two_of_not_delta_four {x u y : Point d.P} {l m : Line d.L}
    (hxu : Adj d.L x u) (huy : Adj d.L u y)
    (hul : OnLine d.L u l) (hxl : OnLine d.L x l)
    (hum : OnLine d.L u m) (hym : OnLine d.L y m)
    (hn : ¬ LineType d.residue 4 u l m) : d.ternary 2 x u y := by
  obtain ⟨i,hi,_⟩ := d.orbital_partition u l m hul hum
  refine ⟨hxu,huy,?_⟩
  have hc {i : Fin 5} (hi : LineType d.residue i u l m) (hle : i.val ≤ 2) :
      d.coplanarStep x u y :=
    ⟨l,m,hul,hxl,hum,hym,(d.delta_coplanar u l m hul hum).mpr ⟨i,hle,hi⟩⟩
  fin_cases i
  · exact Or.inl (hc hi (by decide))
  · exact Or.inl (hc hi (by decide))
  · exact Or.inl (hc hi (by decide))
  · exact Or.inr ⟨l,m,hul,hxl,hum,hym,hi⟩
  · exact (hn hi).elim

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
