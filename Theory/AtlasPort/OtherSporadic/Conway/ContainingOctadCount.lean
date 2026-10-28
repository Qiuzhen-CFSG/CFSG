/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/ContainingOctadCount.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.DisjointOctadCount
public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalContainingOctadOrbit
public import Theory.AtlasPort.OtherSporadic.Lattices.OctadOppositeSigns
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/ContainingOctadCount.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

abbrev ContainingOctadSupports (i j : Omega) := {T : Finset Omega // T ∈ octads ∧ i ∈ T ∧ j ∈ T}
abbrev ContainingOctadParameters (i j : Omega) := (T : ContainingOctadSupports i j) ×
  OppositeParitySigns T.val ⟨i,T.prop.2.1⟩ ⟨j,T.prop.2.2⟩

def containingOctadVector (i j : Omega) (p : ContainingOctadParameters i j) : IntegerCoordinates :=
  fun k => 2 * signedSupport p.1.val p.2.val k

theorem containingOctadVector_mem (i j : Omega) (p : ContainingOctadParameters i j) :
    containingOctadVector i j p ∈ twoFourFamily 8 0 :=
  disjointOctadVector_mem ∅ ⟨⟨p.1.val,p.1.prop.1,Finset.disjoint_empty_right _⟩,⟨p.2.val,p.2.prop.1⟩⟩

theorem containingOctadVector_support (i j : Omega) (p : ContainingOctadParameters i j) :
    evenMagnitudeSupport (containingOctadVector i j p) 2 = p.1.val :=
  disjointOctadVector_support ∅ ⟨⟨p.1.val,p.1.prop.1,Finset.disjoint_empty_right _⟩,⟨p.2.val,p.2.prop.1⟩⟩

theorem containingOctadVector_injective (i j : Omega) : Function.Injective (containingOctadVector i j) := by
  rintro ⟨T,s⟩ ⟨U,t⟩ he
  have hTU : T = U := Subtype.ext (by
    have h := congrArg (fun x => evenMagnitudeSupport x 2) he
    simpa only [containingOctadVector_support] using h)
  subst U
  have hs : s = t := Subtype.ext (signedSupport_injective T.val (by
    funext k
    have h := congrFun he k
    change 2 * signedSupport T.val s.val k = 2 * signedSupport T.val t.val k at h
    omega))
  subst t
  rfl

def ContainingOctadClass (i j : Omega) :=
  {x : leech // x.val ∈ twoFourFamily 8 0 ∧
    integerDot (minimumPairPlus i j).val x.val = 0 ∧ x.val i ≠ 0}

def containingOctadMap (i j : Omega) (p : ContainingOctadParameters i j) : ContainingOctadClass i j :=
  ⟨⟨containingOctadVector i j p,(twoFourFamily_properties 8 0 _ (containingOctadVector_mem i j p)).1⟩,
    containingOctadVector_mem i j p,by
      rw [minimumPairPlus_dot]
      change 4 * (containingOctadVector i j p i + containingOctadVector i j p j) = 0
      have hs := p.2.prop.2
      simp only [containingOctadVector,signedSupport,dif_pos p.1.prop.2.1,dif_pos p.1.prop.2.2]
      rcases bit_cases (p.2.val ⟨i,p.1.prop.2.1⟩) with hi | hi <;>
        rcases bit_cases (p.2.val ⟨j,p.1.prop.2.2⟩) with hj | hj <;> simp_all,
    mul_ne_zero (by decide) (signedSupport_nonzero_on p.1.val p.2.val i p.1.prop.2.1)⟩

def containingOctadEquiv (i j : Omega) : ContainingOctadParameters i j ≃ ContainingOctadClass i j :=
  Equiv.ofBijective (containingOctadMap i j) ⟨fun p q h => containingOctadVector_injective i j
    (congrArg (fun x : ContainingOctadClass i j => x.val.val) h),by
      intro x
      obtain ⟨T,hT,hCT,s,hps,hs⟩ := minimum_octad_parameterization x.val x.prop.1
      have hsum : x.val.val i + x.val.val j = 0 := by
        have h := x.prop.2.1
        rw [minimumPairPlus_dot] at h
        omega
      have hiT : i ∈ T := by
        by_contra hn
        exact x.prop.2.2 (by rw [hs]; simp [signedSupport,hn])
      have hjT : j ∈ T := by
        by_contra hn
        have hj : x.val.val j = 0 := by rw [hs]; simp [signedSupport,hn]
        exact x.prop.2.2 (by omega)
      have hneq : s ⟨i,hiT⟩ ≠ s ⟨j,hjT⟩ := by
        intro he
        have hsame : x.val.val i = x.val.val j := by
          rw [hs]
          simp only [signedSupport,dif_pos hiT,dif_pos hjT]
          rw [he]
        exact x.prop.2.2 (by omega)
      refine ⟨⟨⟨T,codeSupport_octad T hT hCT,hiT,hjT⟩,⟨s,hps,hneq⟩⟩,?_⟩
      apply Subtype.ext
      exact Subtype.ext hs.symm⟩

theorem containingOctadClass_card (i j : Omega) (hij : i ≠ j) :
    Nat.card (ContainingOctadClass i j) = 4928 := by
  rw [← Nat.card_congr (containingOctadEquiv i j),Nat.card_sigma]
  have he (T : ContainingOctadSupports i j) : Nat.card (OppositeParitySigns T.val
      ⟨i,T.prop.2.1⟩ ⟨j,T.prop.2.2⟩) = 64 :=
    oppositeParitySigns_eight_card T.val (by rw [Fintype.card_coe,octad_size _ T.prop.1]) _ _
      (fun h => hij (congrArg Subtype.val h))
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
  have e : ContainingOctadSupports i j ≃ {T // T ∈ octads.filter (fun T => i ∈ T ∧ j ∈ T)} :=
    Equiv.subtypeEquivRight (fun T => by simp)
  rw [Fintype.card_congr e,Fintype.card_coe,octads_through_pair_card i j hij]
  norm_num

end Atlas.Conway
