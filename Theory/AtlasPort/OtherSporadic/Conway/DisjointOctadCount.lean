/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/DisjointOctadCount.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalDisjointOrbits
public import Theory.AtlasPort.OtherSporadic.Mathieu.OctadPairCounts
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/DisjointOctadCount.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem octad_supportWord_mem (T : Finset Omega) (hT : T ∈ octads) : supportWord T ∈ golay := by
  obtain ⟨c,hc,hs⟩ := (octads_mem T).mp hT
  have he : supportWord (support c.val) = c.val := binarySupportEquiv.left_inv c.val
  rw [hs] at he
  rw [he]
  exact c.prop

abbrev DisjointOctadSupports (J : Finset Omega) := {T : Finset Omega // T ∈ octads ∧ Disjoint T J}
abbrev DisjointOctadParameters (J : Finset Omega) := (T : DisjointOctadSupports J) × ParitySigns T.val 0

def disjointOctadVector (J : Finset Omega) (p : DisjointOctadParameters J) : IntegerCoordinates :=
  fun i => 2 * signedSupport p.1.val p.2.val i

theorem disjointOctadVector_mem (J : Finset Omega) (p : DisjointOctadParameters J) :
    disjointOctadVector J p ∈ twoFourFamily 8 0 := by
  let T : CodeSupports 8 := ⟨p.1.val,octad_supportWord_mem p.1.val p.1.prop.1,octad_size _ p.1.prop.1⟩
  let U : OutsideSupports T.val 0 := ⟨∅,by simp⟩
  let s : TwoFourSigns T.val U.val := (⟨p.2.val,p.2.prop⟩,fun _ => 0)
  refine Finset.mem_image.mpr ⟨⟨T,U,s⟩,Finset.mem_univ _,?_⟩
  funext i
  simp [twoFourFamilyVector,twoFourSignedVector,twoFourVector,T,U,s,disjointOctadVector,signedSupport]

theorem disjointOctadVector_support (J : Finset Omega) (p : DisjointOctadParameters J) :
    evenMagnitudeSupport (disjointOctadVector J p) 2 = p.1.val := by
  ext i
  simp only [evenMagnitudeSupport,Finset.mem_filter,Finset.mem_univ,true_and]
  change (2 * signedSupport p.1.val p.2.val i) * (2 * signedSupport p.1.val p.2.val i) = (2 : ℤ)*2 ↔ i ∈ p.1.val
  by_cases hi : i ∈ p.1.val
  · simp only [signedSupport,dif_pos hi]
    split_ifs <;> simp_all
  · simp [signedSupport,hi]

theorem disjointOctadVector_injective (J : Finset Omega) : Function.Injective (disjointOctadVector J) := by
  rintro ⟨T,s⟩ ⟨U,t⟩ he
  have hTU : T = U := Subtype.ext (by
    have h := congrArg (fun x => evenMagnitudeSupport x 2) he
    simpa only [disjointOctadVector_support] using h)
  subst U
  have hs : s = t := Subtype.ext (signedSupport_injective T.val (by
    funext i
    have h := congrFun he i
    change 2 * signedSupport T.val s.val i = 2 * signedSupport T.val t.val i at h
    omega))
  subst t
  rfl

def DisjointOctadClass (J : Finset Omega) :=
  {x : leech // x.val ∈ twoFourFamily 8 0 ∧ ∀ i ∈ J, x.val i = 0}

def disjointOctadMap (J : Finset Omega) (p : DisjointOctadParameters J) : DisjointOctadClass J :=
  ⟨⟨disjointOctadVector J p,(twoFourFamily_properties 8 0 _ (disjointOctadVector_mem J p)).1⟩,
    disjointOctadVector_mem J p,by
      intro i hi
      have hn : i ∉ p.1.val := fun h => Finset.disjoint_left.mp p.1.prop.2 h hi
      simp [disjointOctadVector,signedSupport,hn]⟩

def disjointOctadEquiv (J : Finset Omega) : DisjointOctadParameters J ≃ DisjointOctadClass J :=
  Equiv.ofBijective (disjointOctadMap J) ⟨fun p q h => disjointOctadVector_injective J
    (congrArg (fun x : DisjointOctadClass J => x.val.val) h),by
      intro x
      obtain ⟨T,hT,hCT,s,hps,hs⟩ := minimum_octad_parameterization x.val x.prop.1
      have hTJ := support_disjoint_of_zero T J s 2 (by decide) x.val hs x.prop.2
      refine ⟨⟨⟨T,codeSupport_octad T hT hCT,hTJ⟩,⟨s,hps⟩⟩,?_⟩
      apply Subtype.ext
      exact Subtype.ext hs.symm⟩

theorem disjointOctadClass_card (J : Finset Omega) :
    Nat.card (DisjointOctadClass J) = Nat.card (DisjointOctadSupports J) * 128 := by
  rw [← Nat.card_congr (disjointOctadEquiv J),Nat.card_sigma]
  have he (T : DisjointOctadSupports J) : Nat.card (ParitySigns T.val 0) = 128 := by
    rw [paritySigns_card _ _ (by simp only [Fintype.card_coe]; rw [octad_size _ T.prop.1]; decide),
      Fintype.card_coe,octad_size _ T.prop.1]
    norm_num
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,Nat.card_eq_fintype_card]

theorem disjointOctadPair_card (i j : Omega) (hij : i ≠ j) :
    Nat.card (DisjointOctadClass {i,j}) = 42240 := by
  have he : DisjointOctadSupports {i,j} ≃ {T // T ∈ octads.filter (fun T => i ∉ T ∧ j ∉ T)} :=
    Equiv.subtypeEquivRight (fun T => by simp)
  rw [disjointOctadClass_card,Nat.card_congr he,Nat.card_eq_fintype_card,Fintype.card_coe,
    octads_avoiding_pair_card i j hij]

end Atlas.Conway
