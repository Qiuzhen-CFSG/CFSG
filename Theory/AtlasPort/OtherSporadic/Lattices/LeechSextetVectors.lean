/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/LeechSextetVectors.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

CFSG adaptation: module/public-import boundaries, relocated imports, and
exposed definition bodies preserving upstream cross-module reduction.
Adapted for CFSG Lean 4.33.0.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechCrossAction
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetCounting

/-!
Explicit Leech crosses arising from Golay sextets and a parity choice.
Tetrad-supported vectors share a mod-two class; support recovery distinguishes and counts the resulting crosses.

The definitions and public statements follow the ATLAS source cited above.
-/

@[expose] public section

noncomputable section
namespace Atlas.Lattices
open Atlas.Codes
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The signed norm-eight vector supported on one tetrad. -/
def tetradFourVector (T : Finset Omega) (s : T → Bit) : IntegerCoordinates :=
  twoFourVector ∅ T (fun i => Finset.notMem_empty i.val i.prop |>.elim) s

theorem tetradFourVector_apply (T : Finset Omega) (s : T → Bit) (i : Omega) :
    tetradFourVector T s i = 4 * signedSupport T s i := by
  simp [tetradFourVector,twoFourVector,signedSupport]

theorem tetradFourVector_mem (T : Finset Omega) (hT : T.card = 4) (s : T → Bit) :
    tetradFourVector T s ∈ leech := by
  apply (twoFour_mem_iff ∅ T _ s (by convert golay.zero_mem using 1; ext i; simp [supportWord])).mpr
  simp [hT]

theorem tetradFourVector_norm (T : Finset Omega) (hT : T.card = 4) (s : T → Bit) :
    integerDot (tetradFourVector T s) (tetradFourVector T s) = 64 := by
  rw [tetradFourVector,twoFour_norm _ _ (by simp)]; simp [hT]

theorem tetradFourVector_support (T : Finset Omega) (s : T → Bit) :
    evenMagnitudeSupport (tetradFourVector T s) 4 = T :=
  twoFour_support_four ∅ T (by simp) _ s

theorem tetradFourVector_injective (T : Finset Omega) :
    Function.Injective (tetradFourVector T) := by
  intro s t h
  apply signedSupport_injective T
  funext i
  have hi := congrFun h i
  simp only [tetradFourVector_apply] at hi
  omega

/-- Six tetrad choices, each carrying the eight signs of a fixed parity. -/
abbrev SextetVectorParameters (S : UnorderedSextet) (b : Bit) :=
  (T : {T // T ∈ S.val}) × ParitySigns T.val b

instance (S : UnorderedSextet) (b : Bit) : Fintype (SextetVectorParameters S b) :=
  inferInstance

def sextetVector (S : UnorderedSextet) (b : Bit)
    (p : SextetVectorParameters S b) : IntegerCoordinates :=
  tetradFourVector p.1.val p.2.val

theorem sextetVector_injective (S : UnorderedSextet) (b : Bit) :
    Function.Injective (sextetVector S b) := by
  rintro ⟨T,s⟩ ⟨U,t⟩ h
  have hTU : T = U := by
    apply Subtype.ext
    have hh := congrArg (fun x => evenMagnitudeSupport x 4) h
    simpa only [sextetVector,tetradFourVector_support] using hh
  subst U
  have hs : s = t := Subtype.ext (tetradFourVector_injective T.val h)
  subst t
  rfl

def sextetIntegerVectors (S : UnorderedSextet) (b : Bit) : Finset IntegerCoordinates :=
  Finset.univ.image (sextetVector S b)

theorem sextetVectorParameters_card (S : UnorderedSextet) (b : Bit) :
    Fintype.card (SextetVectorParameters S b) = 48 := by
  rw [Fintype.card_sigma]
  have hc (T : {T // T ∈ S.val}) : Fintype.card (ParitySigns T.val b) = 8 := by
    rw [← Nat.card_eq_fintype_card,paritySigns_card]
    · simp [S.prop.tetrad_size T.val T.prop]
    · simp [S.prop.tetrad_size T.val T.prop]
  simp_rw [hc]
  simp [S.prop.six_parts]

theorem sextetIntegerVectors_card (S : UnorderedSextet) (b : Bit) :
    (sextetIntegerVectors S b).card = 48 := by
  rw [sextetIntegerVectors,Finset.card_image_of_injective _ (sextetVector_injective S b),
    Finset.card_univ,sextetVectorParameters_card]

theorem sextetIntegerVectors_properties (S : UnorderedSextet) (b : Bit)
    (x : IntegerCoordinates) (hx : x ∈ sextetIntegerVectors S b) :
    x ∈ leech ∧ integerDot x x = 64 := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
  exact ⟨tetradFourVector_mem _ (S.prop.tetrad_size _ p.1.prop) _,
    tetradFourVector_norm _ (S.prop.tetrad_size _ p.1.prop) _⟩

theorem sextet_support_difference_mem (S : UnorderedSextet)
    (T U : {T // T ∈ S.val}) : supportWord T.val - supportWord U.val ∈ golay := by
  by_cases h : T = U
  · subst U; simp only [sub_self]; exact golay.zero_mem
  · have hn : T.val ≠ U.val := fun e => h (Subtype.ext e)
    have hd := S.prop.parts_disjoint T.prop U.prop hn
    obtain ⟨w,_,hw⟩ := (octads_mem _).mp (S.prop.pair_octads _ T.prop _ U.prop hn)
    have he : supportWord T.val - supportWord U.val = w.val := by
      rw [← binarySupportEquiv.left_inv w.val]
      change supportWord T.val - supportWord U.val = supportWord (support w.val)
      rw [hw]
      ext i
      have hi : ¬(i ∈ T.val ∧ i ∈ U.val) := fun hh => Finset.disjoint_left.mp hd hh.1 hh.2
      simp only [Pi.sub_apply,supportWord,Finset.mem_union]
      split_ifs <;> simp_all
    rw [he]; exact w.prop

theorem sextet_half_difference_mem (S : UnorderedSextet) (b : Bit)
    (p q : SextetVectorParameters S b) :
    (fun i => 2 * (signedSupport p.1.val p.2.val i - signedSupport q.1.val q.2.val i)) ∈ leech := by
  let v := signedSupport p.1.val p.2.val
  let w := signedSupport q.1.val q.2.val
  apply (mem_leech _).mpr
  refine ⟨0,Or.inl rfl,fun i => by change (2 * _) % 2 = 0; omega,?_,?_⟩
  · have he : halfResidue (fun i => 2 * (v i - w i)) 0 =
        supportWord p.1.val - supportWord q.1.val := by
      change integerReduction (fun i => (2 * (v i - w i) - 0) / 2) = _
      have hh : (fun i => (2 * (v i - w i) - 0) / 2) = v - w := by
        funext i; simp
      rw [hh,map_sub,signedSupport_reduction,signedSupport_reduction]
    rw [he]; exact sextet_support_difference_mem S p.1 q.1
  · have hp := signedSupport_negative_parity p.1.val p.2.val
    have hq := signedSupport_negative_parity q.1.val q.2.val
    rw [p.2.prop] at hp
    rw [q.2.prop] at hq
    have hm := (ZMod.intCast_eq_intCast_iff' _ _ 2).mp (hp.trans hq.symm)
    simp only [← Finset.mul_sum,Finset.sum_sub_distrib,signedSupport_sum]
    rw [S.prop.tetrad_size _ p.1.prop,S.prop.tetrad_size _ q.1.prop]
    omega

def sextetLatticeVector (S : UnorderedSextet) (b : Bit)
    (p : SextetVectorParameters S b) : leech :=
  ⟨sextetVector S b p,tetradFourVector_mem _ (S.prop.tetrad_size _ p.1.prop) _⟩

theorem sextetVector_class (S : UnorderedSextet) (b : Bit)
    (p q : SextetVectorParameters S b) :
    leechReduction (sextetLatticeVector S b p) = leechReduction (sextetLatticeVector S b q) := by
  apply (leechReduction_eq_iff _ _).mpr
  refine ⟨⟨_,sextet_half_difference_mem S b p q⟩,?_⟩
  apply Subtype.ext
  ext i
  change sextetVector S b p i = sextetVector S b q i + 2 * (2 * (_ - _))
  simp only [sextetVector,tetradFourVector_apply]
  ring

def sextetBaseParameter (S : UnorderedSextet) (b : Bit) : SextetVectorParameters S b :=
  Classical.choice (Fintype.card_pos_iff.mp (by rw [sextetVectorParameters_card]; decide))

/-- The intrinsic cross associated with the sextet and common sign parity. -/
def sextetCross (S : UnorderedSextet) (b : Bit) : LeechCross :=
  ⟨leechReduction (sextetLatticeVector S b (sextetBaseParameter S b)),
    (minimumEightClass_iff _).mpr (by
      refine Finset.mem_image.mpr ⟨⟨sextetLatticeVector S b (sextetBaseParameter S b),?_⟩,
        Finset.mem_univ _,rfl⟩
      exact tetradFourVector_norm _ (S.prop.tetrad_size _ (sextetBaseParameter S b).1.prop) _)⟩

theorem sextetCross_vectors (S : UnorderedSextet) (b : Bit) :
    crossIntegerVectors (sextetCross S b) = sextetIntegerVectors S b := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
    refine Finset.mem_image.mpr ⟨sextetLatticeVector S b p,?_,rfl⟩
    apply (crossVectors_mem _ _).mpr
    exact ⟨sextetVector_class S b p (sextetBaseParameter S b),
      tetradFourVector_norm _ (S.prop.tetrad_size _ p.1.prop) _⟩
  · rw [crossIntegerVectors_card,sextetIntegerVectors_card]

theorem sextetCross_supports (S : UnorderedSextet) (b : Bit) :
    (crossIntegerVectors (sextetCross S b)).image (fun x => evenMagnitudeSupport x 4) = S.val := by
  rw [sextetCross_vectors]
  apply Finset.Subset.antisymm
  · intro T hT
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
    simpa only [sextetVector,tetradFourVector_support] using p.1.prop
  · intro T hT
    have hc : Fintype.card (ParitySigns T b) = 8 := by
      rw [← Nat.card_eq_fintype_card,paritySigns_card]
      · simp [S.prop.tetrad_size T hT]
      · simp [S.prop.tetrad_size T hT]
    obtain ⟨s⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card (ParitySigns T b) by omega)
    refine Finset.mem_image.mpr ⟨tetradFourVector T s.val,?_,tetradFourVector_support T s.val⟩
    exact Finset.mem_image.mpr ⟨⟨⟨T,hT⟩,s⟩,Finset.mem_univ _,rfl⟩

theorem sextetCross_injective : Function.Injective (fun p : UnorderedSextet × Bit => sextetCross p.1 p.2) := by
  rintro ⟨S,b⟩ ⟨R,d⟩ h
  change sextetCross S b = sextetCross R d at h
  have hS : S = R := by
    apply Subtype.ext
    rw [← sextetCross_supports S b,← sextetCross_supports R d,h]
  subst R
  have hp := sextetBaseParameter S b
  have hm : sextetVector S b hp ∈ sextetIntegerVectors S d := by
    rw [← sextetCross_vectors,← h,sextetCross_vectors]
    exact Finset.mem_image.mpr ⟨hp,Finset.mem_univ _,rfl⟩
  obtain ⟨⟨T,t⟩,_,ht⟩ := Finset.mem_image.mp hm
  obtain ⟨U,u⟩ := hp
  have hTU : T = U := by
    apply Subtype.ext
    have hh := congrArg (fun x => evenMagnitudeSupport x 4) ht
    simpa only [sextetVector,tetradFourVector_support] using hh
  subst T
  have hs : t.val = u.val := tetradFourVector_injective U.val ht
  have hb : b = d := u.prop.symm.trans ((congrArg (fun s : U.val → Bit => ∑ i, s i) hs).symm.trans t.prop)
  subst d
  rfl

def sextetCrosses : Finset LeechCross := Finset.univ.image (fun p : UnorderedSextet × Bit => sextetCross p.1 p.2)

theorem sextetCrosses_card : sextetCrosses.card = 3542 := by
  rw [sextetCrosses,Finset.card_image_of_injective _ sextetCross_injective,Finset.card_univ,
    ← Nat.card_eq_fintype_card,Nat.card_prod,unordered_sextets_card]
  norm_num [Nat.card_zmod]

end Atlas.Lattices
