module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeAmbientSource
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreeCrossCoreFour

/-!
# The opposite-core action survives in the original point quotient

Write C = C_G(z), J = LS, and Qᵍ for the original opposite commutator
core. The established containment O₂(C) ≤ O₂(J) shows that an element
centralizing the image of Qᵍ in C/O₂(C) centralizes its image under the
original projection J → SL₃(2). That latter image is a self-centralizing
four-group. Its centralizer preimage in J is therefore a two-group,
and so is its image in C/O₂(C).

The source consumer retains the literal quotient map, full Sylow, original
local component, shortened third commutator, and normal containing component.
This bounds the centralizer inside the image of LS only. It makes no claim
about the full centralizer in C/O₂(C), and does not construct a third cubic
or exclude the large-distance branch. The MS93 Earlier input remains explicit.

Source: Aschbacher–Smith 15.3.23, printed pp.1128–1129, with the original
point-centralizer construction and the binary parabolic model I.5.4, I.5.7.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem centralizer_image_le_of_ker_le
    {A B D : Type*} [Group A] [Group B] [Group D]
    (f : A →* B) (k : A →* D) (hk : f.ker ≤ k.ker) (Q : Subgroup A) :
    (centralizer (Q.map f : Set B)).comap f ≤
      (centralizer (Q.map k : Set D)).comap k := by
  intro x hx
  apply mem_centralizer_iff.mpr
  rintro _ ⟨y,hy,rfl⟩
  have hxy : f (y * x) = f (x * y) := by
    simpa only [map_mul] using mem_centralizer_iff.mp hx (f y) (mem_map_of_mem f hy)
  simpa only [map_mul] using (k.eq_iff).mpr (hk ((f.eq_iff).mp hxy))

omit [Finite G] in
private theorem point_image_centralizer_two
    (J Q C : Subgroup G) (hJC : J ≤ C) (hQJ : Q ≤ J)
    (hcore : C.pCoreIn 2 ≤ J.pCoreIn 2)
    (k : J →* Matrix.PSL3Two.SL) (hk : k.ker = pCore 2 J)
    (hN : IsPGroup 2 ((Q.subgroupOf J).map k))
    (hNC : centralizer ((Q.subgroupOf J).map k : Set Matrix.PSL3Two.SL) ≤
      (Q.subgroupOf J).map k) :
    let q := QuotientGroup.mk' (pCore 2 C)
    IsPGroup 2 (((J.subgroupOf C).map q) ⊓
      centralizer ((Q.subgroupOf C).map q : Set (C ⧸ pCore 2 C)) : Subgroup _) := by
  let q := QuotientGroup.mk' (pCore 2 C)
  let f : J →* (C ⧸ pCore 2 C) := q.comp (inclusion hJC)
  have hfk : f.ker ≤ k.ker := by
    intro x hx
    rw [hk]
    have hxC : inclusion hJC x ∈ pCore 2 C := (QuotientGroup.eq_one_iff _).mp hx
    have hxG := hcore (mem_map_of_mem C.subtype hxC)
    obtain ⟨y,hy,he⟩ := hxG
    exact (Subtype.ext he : y = x) ▸ hy
  have hQmap : (Q.subgroupOf J).map (inclusion hJC) = Q.subgroupOf C := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x,hQJ hx⟩,hx,rfl⟩
  have hD : (Q.subgroupOf J).map f = (Q.subgroupOf C).map q := by
    rw [← map_map,hQmap]
  have hker : IsPGroup 2 k.ker := hk ▸ pCore_isPGroup
  have hK : IsPGroup 2 ((centralizer ((Q.subgroupOf J).map f : Set _)).comap f) :=
    (hN.comap_of_ker_isPGroup k hker).to_le
      ((centralizer_image_le_of_ker_le f k hfk (Q.subgroupOf J)).trans (comap_mono hNC))
  have hF : f.range = (J.subgroupOf C).map q := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x,hx⟩,rfl⟩
  have him := hK.map f
  rw [map_comap_eq,hD,hF] at him
  exact him

/-- The centralizer of the opposite image inside the original overgroup image
is a two-group. In particular its action by an odd-order element survives
passage to the point-centralizer quotient. -/
theorem binary_three_source_point_opposite_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (z : G) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    let C := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (pCore 2 C)
    let Jbar := ((c.L ⊔ d.S).subgroupOf C).map q
    let D := (((LinearThree.commutatorCore c.L).conjBy g).subgroupOf C).map q
    IsPGroup 2 (Jbar ⊓ centralizer (D : Set (C ⧸ pCore 2 C)) : Subgroup _) := by
  obtain ⟨hcore,_,_,_⟩ := binary_three_source_point_opposite_core
    hG d hempty hM hu hmany hI htwo hf c e z hLS P hP g hgT hgS
  obtain ⟨hQS,_,_⟩ := binary_three_source_conjugate_core_nonvanishing
    hG d hempty hM hu hmany hI htwo hf c e g hgT hgS
  obtain ⟨hN,_,hNC⟩ := binary_three_source_conjugate_core_four
    hG d hempty hM hu hmany hI htwo hf c e b g hgT hgS
  let := hN
  exact point_image_centralizer_two (c.L ⊔ d.S)
    ((LinearThree.commutatorCore c.L).conjBy g) (centralizer ({z} : Set G))
    hLS (hQS.trans le_sup_right) hcore b.coreProjection b.coreProjection_kernel
    (IsElementaryAbelian.isPGroup 2 _) hNC

/-- The literal original point quotient has a two-group centralizer for the
opposite core in the original overgroup image, while retaining the normal
containing component and its original local marking. -/
theorem binary_three_source_point_quotient_opposite_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (d : LocalData G)
    (hempty : MainForward.faithfulLocalComponents d.T = ∅)
    (hM : ChapterA.Section05To06.IsOrderingMaximal d.T d.M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions d.T : Set G)) = {d.Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (d.T : Subgroup G)).ncard)
    {I : Subgroup G} (hI : I ∈ d.Hplus) (htwo : OutsideStructure.RankTwoCase d I)
    (hf : HasCharacteristicTwo I) (c : ComponentWitness d I)
    (e : (c.L ⧸ pCore 2 c.L) ≃* PSL(3,ZMod 2))
    (b : BinaryMS.Input KnownSimple.IsKnownSimple
      (c.L.subgroupOf (c.L ⊔ d.S)) (d.S.subgroupOf (c.L ⊔ d.S)))
    (t : InputSetup b)
    (common : CommonFacts t.reduction.radical t.source t.geometry)
    (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ z : G, z ∈ intrinsicFour c.L ∧ orderOf z = 2 ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      let C := centralizer ({z} : Set G)
      let q := QuotientGroup.mk' (pCore 2 C)
      let B := (c.L.subgroupOf C).map q
      let D := (((LinearThree.commutatorCore c.L).conjBy g).subgroupOf C).map q
      IsSQTK KnownSimple.IsKnownSimple (C ⧸ pCore 2 C) ∧
      pCore 2 (C ⧸ pCore 2 C) = ⊥ ∧
      Nat.card (intrinsicFour B) ≤ 2 ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) ∧
      C.pCoreIn 2 ≤ (c.L ⊔ d.S).pCoreIn 2 ∧
      D ≠ ⊥ ∧ IsPGroup 2 D ∧ ¬ B ≤ normalizer (D : Set (C ⧸ pCore 2 C)) ∧
      IsPGroup 2 ((((c.L ⊔ d.S).subgroupOf C).map q) ⊓
        centralizer (D : Set (C ⧸ pCore 2 C)) : Subgroup _) ∧
      ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = d.S ∧
        B ∈ ChapterA.Section03.localCComponents
          (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))) ∧
        ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
          (K.map q).IsCComponent ∧ (K.map q).Normal ∧ B ≤ K.map q := by
  obtain ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,hcore,hD,hDtwo,hBD,
    P,hP,hB,K,hK,hKn,hLK,hKq,hKnq,hBKq⟩ :=
    binary_three_source_point_quotient_opposite_pair
      hG d hempty hM hu hmany hI htwo hf c e b t common earlier g hgT hgS
  exact ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,he,hcore,hD,hDtwo,hBD,
    binary_three_source_point_opposite_centralizer
      hG d hempty hM hu hmany hI htwo hf c e b z hLS P hP g hgT hgS,
    P,hP,hB,K,hK,hKn,hLK,hKq,hKnq,hBKq⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
