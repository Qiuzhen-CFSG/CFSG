/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/DisjointFourCount.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalDisjointOrbits
/-!
Orthogonal minimum-vector geometry in the concrete Leech lattice.
The proofs use coordinate shapes, Golay support counts, and stabilizer orbit transport.

Source: Gerald Höhn, `Atlas/Conway/DisjointFourCount.lean`, ATLAS revision
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

abbrev DisjointFourParameters (J : Finset Omega) := (T : OutsideSupports J 2) × (T.val → Bit)
def disjointFourVector (J : Finset Omega) (p : DisjointFourParameters J) : IntegerCoordinates :=
  fun i => 4 * signedSupport p.1.val p.2 i

theorem disjointFourVector_mem (J : Finset Omega) (p : DisjointFourParameters J) :
    disjointFourVector J p ∈ twoFourFamily 0 2 := by
  let T : CodeSupports 0 := ⟨∅,by
    constructor
    · have hz : supportWord ∅ = (0 : BinaryWord) := by funext i; simp [supportWord]
      rw [hz]; exact golay.zero_mem
    · simp⟩
  let U : OutsideSupports T.val 2 := ⟨p.1.val,by exact ⟨Finset.disjoint_empty_left _,p.1.prop.2⟩⟩
  let s : TwoFourSigns T.val U.val := (⟨fun _ => 0,by simp [T,U,p.1.prop.2,Bit]⟩,p.2)
  refine Finset.mem_image.mpr ⟨⟨T,U,s⟩,Finset.mem_univ _,?_⟩
  funext i
  simp [twoFourFamilyVector,twoFourSignedVector,twoFourVector,T,U,s,disjointFourVector,signedSupport]

theorem disjointFourVector_support (J : Finset Omega) (p : DisjointFourParameters J) :
    evenMagnitudeSupport (disjointFourVector J p) 4 = p.1.val := by
  ext i
  simp only [evenMagnitudeSupport,Finset.mem_filter,Finset.mem_univ,true_and]
  change (4 * signedSupport p.1.val p.2 i) * (4 * signedSupport p.1.val p.2 i) = (4 : ℤ)*4 ↔ i ∈ p.1.val
  by_cases hi : i ∈ p.1.val
  · simp only [signedSupport,dif_pos hi]
    split_ifs <;> simp_all
  · simp [signedSupport,hi]

theorem disjointFourVector_injective (J : Finset Omega) : Function.Injective (disjointFourVector J) := by
  rintro ⟨T,s⟩ ⟨U,t⟩ he
  have hTU : T = U := Subtype.ext (by
    have h := congrArg (fun x => evenMagnitudeSupport x 4) he
    simpa only [disjointFourVector_support] using h)
  subst U
  have hs : s = t := signedSupport_injective T.val (by
    funext i
    have h := congrFun he i
    change 4 * signedSupport T.val s i = 4 * signedSupport T.val t i at h
    omega)
  subst t
  rfl

def DisjointFourClass (J : Finset Omega) :=
  {x : leech // x.val ∈ twoFourFamily 0 2 ∧ ∀ i ∈ J, x.val i = 0}

def disjointFourMap (J : Finset Omega) (p : DisjointFourParameters J) : DisjointFourClass J :=
  ⟨⟨disjointFourVector J p,(twoFourFamily_properties 0 2 _ (disjointFourVector_mem J p)).1⟩,
    disjointFourVector_mem J p,by
      intro i hi
      have hn : i ∉ p.1.val := fun h => Finset.disjoint_left.mp p.1.prop.1 hi h
      simp [disjointFourVector,signedSupport,hn]⟩

def disjointFourEquiv (J : Finset Omega) : DisjointFourParameters J ≃ DisjointFourClass J :=
  Equiv.ofBijective (disjointFourMap J) ⟨fun p q h => disjointFourVector_injective J
    (congrArg (fun x : DisjointFourClass J => x.val.val) h),by
      intro x
      obtain ⟨T,hT,s,hs⟩ := minimum_four_parameterization x.val x.prop.1
      have hTJ := support_disjoint_of_zero T J s 4 (by decide) x.val hs x.prop.2
      refine ⟨⟨⟨T,hTJ.symm,hT⟩,s⟩,?_⟩
      apply Subtype.ext
      exact Subtype.ext hs.symm⟩

theorem disjointFourClass_card (J : Finset Omega) :
    Nat.card (DisjointFourClass J) = Nat.choose (24-J.card) 2 * 4 := by
  rw [← Nat.card_congr (disjointFourEquiv J),Nat.card_sigma]
  have he (T : OutsideSupports J 2) : Nat.card (T.val → Bit) = 4 := by
    rw [Nat.card_fun,Nat.card_eq_fintype_card (α := T.val),Fintype.card_coe,T.prop.2]
    norm_num [Bit]
  simp_rw [he]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card,outsideSupports_card]
  simp only [Nat.cast_id]

theorem disjointFourPair_card (i j : Omega) (hij : i ≠ j) :
    Nat.card (DisjointFourClass {i,j}) = 924 := by
  rw [disjointFourClass_card]
  norm_num [Finset.card_pair hij,Nat.choose]

end Atlas.Conway
