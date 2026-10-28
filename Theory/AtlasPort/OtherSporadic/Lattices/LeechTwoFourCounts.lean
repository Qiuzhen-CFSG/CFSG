/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechTwoFourCounts.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Proof syntax and simplifier arguments are adjusted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechTwoFour
public import Theory.AtlasPort.OtherSporadic.Codes.BinaryCounting

/-!
Injective support and sign parametrizations for two-four coordinate vectors.
Golay support counts and parity-constrained signs determine the parameter cardinalities.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators

theorem twoFour_support_two (T U : Finset Omega) (hd : Disjoint T U)
    (s : T → Bit) (t : U → Bit) : evenMagnitudeSupport (twoFourVector T U s t) 2 = T := by
  ext i
  have h : ¬(i ∈ T ∧ i ∈ U) := fun h => Finset.disjoint_left.mp hd h.1 h.2
  simp only [evenMagnitudeSupport]
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ,true_and,twoFourVector,signedSupport]
  split_ifs <;> simp_all

theorem twoFour_support_four (T U : Finset Omega) (hd : Disjoint T U)
    (s : T → Bit) (t : U → Bit) : evenMagnitudeSupport (twoFourVector T U s t) 4 = U := by
  ext i
  have h : ¬(i ∈ T ∧ i ∈ U) := fun h => Finset.disjoint_left.mp hd h.1 h.2
  simp only [evenMagnitudeSupport]
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ,true_and,twoFourVector,signedSupport]
  split_ifs <;> simp_all

theorem twoFour_signs_injective (T U : Finset Omega) (hd : Disjoint T U) :
    Function.Injective (fun p : (T → Bit) × (U → Bit) => twoFourVector T U p.1 p.2) := by
  intro p q he
  apply Prod.ext
  · funext i
    have hu : i.val ∉ U := fun hi => Finset.disjoint_left.mp hd i.prop hi
    have hi := congrFun he i.val
    simp only [twoFourVector,signedSupport,dif_pos i.prop,dif_neg hu] at hi
    rcases bit_cases (p.1 i) with h | h <;> rcases bit_cases (q.1 i) with hq | hq <;> simp_all
  · funext i
    have ht : i.val ∉ T := fun hi => Finset.disjoint_left.mp hd hi i.prop
    have hi := congrFun he i.val
    simp only [twoFourVector,signedSupport,dif_pos i.prop,dif_neg ht] at hi
    rcases bit_cases (p.2 i) with h | h <;> rcases bit_cases (q.2 i) with hq | hq <;> simp_all

abbrev CodeSupports (k : ℕ) := {T : Finset Omega // supportWord T ∈ golay ∧ T.card = k}

def codeSupportsEquiv (k : ℕ) : CodeSupports k ≃ {c : golay // hammingNorm c.val = k} where
  toFun T := ⟨⟨supportWord T.val,T.prop.1⟩,by simpa [hammingNorm,supportWord] using T.prop.2⟩
  invFun c := ⟨support c.val.val,by
    have he : supportWord (support c.val.val) = c.val.val := binarySupportEquiv.left_inv c.val.val
    exact ⟨by rw [he]; exact c.val.prop,c.prop⟩⟩
  left_inv T := by
    apply Subtype.ext
    exact binarySupportEquiv.right_inv T.val
  right_inv c := by
    apply Subtype.ext; apply Subtype.ext
    exact binarySupportEquiv.left_inv c.val.val

theorem codeSupports_card (k : ℕ) : Nat.card (CodeSupports k) = golayWeightCount k := by
  exact Nat.card_congr (codeSupportsEquiv k)

abbrev OutsideSupports (T : Finset Omega) (u : ℕ) :=
  {U : Finset Omega // Disjoint T U ∧ U.card = u}

def outsideSupportsEquiv (T : Finset Omega) (u : ℕ) :
    OutsideSupports T u ≃ {U : Finset {i : Omega // i ∉ T} // U.card = u} where
  toFun U := ⟨U.val.subtype (fun i => i ∉ T),by
    have hm : (U.val.subtype (fun i => i ∉ T)).map (Function.Embedding.subtype _) = U.val :=
      Finset.subtype_map_of_mem (fun i hi ht => Finset.disjoint_left.mp U.prop.1 ht hi)
    have hh := congrArg Finset.card hm
    simpa [U.prop.2] using hh⟩
  invFun U := ⟨U.val.map (Function.Embedding.subtype _),by
    constructor
    · apply Finset.disjoint_left.mpr
      intro i hi hu
      obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hu
      exact j.prop hi
    · simpa using U.prop⟩
  left_inv U := by
    apply Subtype.ext
    exact Finset.subtype_map_of_mem (fun i hi ht => Finset.disjoint_left.mp U.prop.1 ht hi)
  right_inv U := by
    apply Subtype.ext
    apply Finset.map_injective (Function.Embedding.subtype _)
    rw [Finset.subtype_map_of_mem]
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hi
    exact j.prop

theorem outsideSupports_card (T : Finset Omega) (u : ℕ) :
    Nat.card (OutsideSupports T u) = Nat.choose (24 - T.card) u := by
  rw [Nat.card_congr (outsideSupportsEquiv T u),Nat.card_eq_fintype_card,Fintype.card_finset_len]
  congr 1
  simp [Fintype.card_subtype_compl,Omega,HexIndex]

abbrev TwoFourSigns (T U : Finset Omega) := ParitySigns T (U.card : Bit) × (U → Bit)
instance (T U : Finset Omega) : Fintype (TwoFourSigns T U) :=
  inferInstanceAs (Fintype ({s : T → Bit // ∑ i, s i = (U.card : Bit)} × (U → Bit)))

def twoFourSignedVector (T U : Finset Omega) (p : TwoFourSigns T U) := twoFourVector T U p.1.val p.2

theorem twoFourSignedVector_injective (T U : Finset Omega) (hd : Disjoint T U) :
    Function.Injective (twoFourSignedVector T U) := by
  intro p q h
  have hh := twoFour_signs_injective T U hd (a₁ := (p.1.val,p.2)) (a₂ := (q.1.val,q.2)) h
  exact Prod.ext (Subtype.ext (Prod.mk.inj hh).1) (Prod.mk.inj hh).2

theorem twoFourSigns_card (T U : Finset Omega) (hT : 0 < T.card) :
    Nat.card (TwoFourSigns T U) = 2 ^ (T.card - 1) * 2 ^ U.card := by
  rw [Nat.card_prod,paritySigns_card T (U.card : Bit) (by simpa using hT)]
  simp [Nat.card_eq_fintype_card,ZMod.card]

end Atlas.Lattices
