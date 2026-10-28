/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/HSSideParameters.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.HSSideShapes
public import Theory.AtlasPort.OtherSporadic.Conway.Co3TriangleParameterInjective

/-!
Explicit parametrizations of the five possible side families.
Coordinate formulas give injectivity, disjointness, and coverage of the side parameters.

Source: Gerald Höhn, `Atlas/Conway/HSSideParameters.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

abbrev HSPairSupports (a : Omega) := {T // T ∈
  ((Finset.univ : Finset Omega).powersetCard 2).filter (fun T => {a} ⊆ T)}

abbrev HSSideParameters (a : Omega) : Fin 5 → Type
  | 0 => (T : HSPairSupports a) × {s : T.val → Bit //
      s ⟨a,Finset.singleton_subset_iff.mp (Finset.mem_filter.mp T.prop).2⟩ = 0 ∧ hammingNorm s = 1}
  | 1 => Co3OutsideOctads a
  | 2 => (T : Co3ThroughOctads a) × {s : T.val → Bit //
      s ⟨a,(Finset.mem_filter.mp T.prop).2⟩ = 0 ∧ hammingNorm s = 2}
  | 3 => Co3OddFlags a 8 0 1
  | 4 => GolayCoordinateWeight 12 a 1

def hsSignedFourVector (T : Finset Omega) (hT : T.card = 2) (s : T → Bit) : leech :=
  ⟨disjointFourVector ∅ ⟨⟨T,Finset.disjoint_empty_left _,hT⟩,s⟩,
    (twoFourFamily_properties 0 2 _ (disjointFourVector_mem ∅
      ⟨⟨T,Finset.disjoint_empty_left _,hT⟩,s⟩)).1⟩

def hsSideParameterVector (a : Omega) : (t : Fin 5) → HSSideParameters a t → leech
  | 0, p => hsSignedFourVector p.1.val
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp p.1.prop).1).2 p.2.val
  | 1, T => co3SignedOctadVector T.val (Finset.mem_filter.mp T.prop).1 (fun _ => 0) (by simp)
  | 2, p => co3SignedOctadVector p.1.val (Finset.mem_filter.mp p.1.prop).1 p.2.val
      (by rw [bit_sum_eq_weight,p.2.prop.2]; decide)
  | 3, p => oddMinimumVector p.2.val p.1.val
  | 4, c => oddMinimumVector a c.val

theorem hs_side_parameter_shape (a : Omega) (t : Fin 5) (p : HSSideParameters a t) :
    HSSideShape a t (hsSideParameterVector a t p) := by
  fin_cases t
  · refine ⟨p.1.val,(Finset.mem_powersetCard.mp (Finset.mem_filter.mp p.1.prop).1).2,
      p.2.val,⟨_,p.2.prop.1⟩,?_,rfl⟩
    rw [supportNegativeCount_eq_weight,p.2.prop.2]; norm_num
  · refine ⟨p.val,(Finset.mem_filter.mp p.prop).1,(Finset.mem_filter.mp p.prop).2,?_⟩
    funext i
    change 2*signedSupport p.val (fun _ => 0) i = constantSupportVector 2 p.val i
    by_cases hi : i ∈ p.val <;> simp [signedSupport,constantSupportVector,hi]
  · refine ⟨p.1.val,(Finset.mem_filter.mp p.1.prop).1,p.2.val,
      ⟨_,p.2.prop.1⟩,?_,rfl⟩
    rw [supportNegativeCount_eq_weight,p.2.prop.2]; norm_num
  · exact ⟨p.2.val,p.1.val,p.2.prop.1,p.1.prop.1,p.1.prop.2,p.2.prop.2,rfl⟩
  · exact ⟨p.val,p.prop.1,p.prop.2,rfl⟩

theorem hs_side_parameter_represents (a : Omega) (t : Fin 5) (y : leech)
    (hy : HSSideShape a t y) : ∃ p : HSSideParameters a t, hsSideParameterVector a t p = y := by
  fin_cases t
  · obtain ⟨T,hT,s,⟨ha,hz⟩,hn,he⟩ := hy
    have hw : hammingNorm s = 1 := by rw [supportNegativeCount_eq_weight] at hn; omega
    exact ⟨⟨⟨T,Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _,hT⟩,Finset.singleton_subset_iff.mpr ha⟩⟩,⟨s,hz,hw⟩⟩,Subtype.ext he.symm⟩
  · obtain ⟨T,hT,ha,he⟩ := hy
    refine ⟨⟨T,Finset.mem_filter.mpr ⟨hT,ha⟩⟩,Subtype.ext ?_⟩
    rw [he]
    funext i
    change 2*signedSupport T (fun _ => 0) i = constantSupportVector 2 T i
    by_cases hi : i ∈ T <;> simp [signedSupport,constantSupportVector,hi]
  · obtain ⟨T,hT,s,⟨ha,hz⟩,hn,he⟩ := hy
    have hw : hammingNorm s = 2 := by rw [supportNegativeCount_eq_weight] at hn; omega
    exact ⟨⟨⟨T,Finset.mem_filter.mpr ⟨hT,ha⟩⟩,⟨s,hz,hw⟩⟩,Subtype.ext he.symm⟩
  · obtain ⟨b,c,hb,hw,ha,hc,he⟩ := hy
    exact ⟨⟨⟨c,hw,ha⟩,⟨b,hb,hc⟩⟩,he.symm⟩
  · obtain ⟨c,hw,ha,he⟩ := hy
    exact ⟨⟨c,hw,ha⟩,he.symm⟩

theorem hsSideParameterVector_injective (a : Omega) (t : Fin 5) :
    Function.Injective (hsSideParameterVector a t) := by
  fin_cases t
  · rintro ⟨T,s⟩ ⟨U,r⟩ h
    have he := disjointFourVector_injective ∅ (congrArg Subtype.val h)
    have hTU : T = U := Subtype.ext (congrArg (fun p : DisjointFourParameters ∅ => p.1.val) he)
    subst U
    have hsr : s = r := Subtype.ext (signedSupport_injective T.val (by
      funext i
      have hi := congrArg (fun y : leech => y.val i) h
      change 4*signedSupport T.val s.val i = 4*signedSupport T.val r.val i at hi
      omega))
    subst r
    rfl
  · intro T U h
    apply Subtype.ext
    have he := congrArg (fun y : leech => evenMagnitudeSupport y.val 2) h
    simpa only [hsSideParameterVector,co3SignedOctadVector_support] using he
  · rintro ⟨T,s⟩ ⟨U,r⟩ h
    have hTU : T = U := Subtype.ext (by
      have he := congrArg (fun y : leech => evenMagnitudeSupport y.val 2) h
      simpa only [hsSideParameterVector,co3SignedOctadVector_support] using he)
    subst U
    have hsr : s = r := Subtype.ext (signedSupport_injective T.val (by
      funext i
      have hi := congrArg (fun y : leech => y.val i) h
      change 2*signedSupport T.val s.val i = 2*signedSupport T.val r.val i at hi
      omega))
    subst r
    rfl
  · rintro ⟨c,b⟩ ⟨d,e⟩ h
    obtain ⟨hb,hc⟩ := oddMinimumVector_injective_parameters b.val e.val c.val d.val h
    have hcd : c = d := Subtype.ext hc
    subst d
    have hbe : b = e := Subtype.ext hb
    subst e
    rfl
  · intro c d h
    exact Subtype.ext (oddMinimumVector_injective_parameters a a c.val d.val h).2

end Atlas.Conway
