module
public import Theory.GroupTheory.PGroup.OrderTwentySevenMarkedCenter
public import Theory.SpecificGroups.PSL3Four.SylowThreeNoncommutative
public import Theory.GroupTheory.SubgroupCenterImageBound
public import Theory.GroupTheory.SylowCoprimeEquivalence
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.LinearExtraspecialDisplacement

/-!
# The original marked extraspecial Sylow subgroup in the linear triangle

The actual KX/O₂(KX) quotient has order 60480, hence its Sylow three-subgroups
have order 27. Quasithinness and the full three-rank of its normal PSL₃(4)
component make the component centralizer prime to three. The pointwise-fixer
bound forces a nonabelian Sylow, and coprime lifting preserves its structure.
Extend the original Cartan X to a Sylow P. Its order-nine subgroup contains
Z(P), while the cyclic component quotient forces Z(P) into K. Both Z(P) and
X intersect K have order three, giving the literal equality required by the
extraspecial action argument.

The chosen-module application constructs this P and proves both nonzero
cubic displacements. Its common-Q consumer retains all original centralizer
span, core and normalization conclusions without any marked-subgroup premise.
The common normal Q remains explicit. The two subsequent centralizer/module
branches, original SL₃(4) exclusion and both triangle orientations remain open.
In particular, recognition of the restricted adjoint action alone does not
select its PGL₃ extension; the determinant twist in Section04.Adjoint must
still be excluded from the actual source chief section.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.2, printed p.763, the extraspecial Sylow-three paragraph.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
open Theory.GroupAction.ComponentRankAction
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
public noncomputable section
variable {H : Type*} [Group H] [Finite H]

/-- The actual two-core quotient produces a Sylow subgroup with its original center marking. -/
theorem marked_extraspecial_sylow_of_projective
    (K X : Subgroup H) [K.Normal] (hK : K.IsCComponent)
    (hr : primeRank 3 H ≤ 2) (hX : Nat.card X = 9) (hgen : K ⊔ X = ⊤)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour (H ⧸ pCore 2 H)) :
    ∃ P : Sylow 3 H, X ≤ P ∧ IsExtraspecial 3 P ∧ Nat.card P = 27 ∧
      (center P).map (P : Subgroup H).subtype = X ⊓ K := by
  have hX3 : IsPGroup 3 X := IsPGroup.of_card (n := 2) (by simpa using hX)
  have hq3 := isPGroup_quotient_of_sup_eq_top K X hX3 hgen
  have hcore : pCore 2 H ≤ K := by
    let q := QuotientGroup.mk' K
    have h2 : IsPGroup 2 ((pCore 2 H).map q) := pCore_isPGroup.map q
    have h3 : IsPGroup 3 ((pCore 2 H).map q) := hq3.to_subgroup _
    have hz : (pCore 2 H).map q = ⊥ :=
      disjoint_self.mp (h2.disjoint_of_coprime h3 (by decide : Nat.Coprime 2 3))
    simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := K.map q
  let : B.Normal := (inferInstance : K.Normal).map q (QuotientGroup.mk'_surjective _)
  obtain ⟨F,_,_,hF,⟨eK⟩⟩ := hm
  let eB : B ≃* PSL(3,F) := (cComponentTwoCoreQuotientEquiv hK).symm.trans eK
  let : Fintype F := Fintype.ofFinite F
  let : Fintype Matrix.PSL3Four.F := Fintype.ofFinite _
  let ef : F ≃+* Matrix.PSL3Four.F := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Matrix.PSL3Four.card_F] using hF)
  let e : B ≃* Matrix.PSL3Four.PSL := eB.trans (Atlas.fieldEquivPSL 3 ef)
  have hBcard : Nat.card B = 20160 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Four.card_PSL
  have hB : ClassicalGroup.IsPSL B 3 4 := ⟨F,inferInstance,inferInstance,hF,⟨eB⟩⟩
  have hc : Nat.card (H ⧸ pCore 2 H) = 60480 := by
    rw [CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.card_pgl_sign_eq_three_mul_psl_sign
      false 4 hB hp (by norm_num [CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.SignedCongruence]),hBcard]
  have hi : B.index = 3 := by
    have hh := B.card_mul_index
    rw [hc,hBcard] at hh
    omega
  have hiK : K.index = 3 := by
    rw [←K.index_map_eq (QuotientGroup.mk'_surjective (pCore 2 H))
      (by simpa only [QuotientGroup.ker_mk'] using hcore)]
    exact hi
  have hz : center B = ⊥ := by
    apply bot_unique
    intro x hx
    apply eB.map_eq_one_iff.mp
    exact (Group.IsPerfect.center_quotient_center_eq_bot SL(3,F)).le
      ((centerCongr eB) ⟨x,hx⟩).property
  have hcop : Nat.Coprime 3 (Nat.card (centralizer (B : Set (H ⧸ pCore 2 H)))) := by
    apply centralizer_coprime B
    · rw [hz,card_bot]; decide
    · rw [primeRank_congr 3 eB]
      exact Theory.SpecificGroups.SignedThreeCubicRank.linear_projective
        (show Nat.card F = 2^2 by simpa using hF) (by decide)
    · exact (primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hr
  obtain ⟨P,hXP⟩ := hX3.exists_le_sylow
  let R := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hqcop : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  let j : P ≃* R := P.equivOfSurjectiveCoprime q (QuotientGroup.mk'_surjective _) hqcop R
  have hR : Nat.card R = 27 := by
    rw [Sylow.card_eq_multiplicity,hc]
    decide +kernel
  have hP : Nat.card P = 27 := (Nat.card_congr j.toEquiv).trans hR
  have hnR := Matrix.PSL3Four.sylow_three_noncomm_of_normal_simple B e hcop R hR
  have hn : ¬ IsMulCommutative P := by
    intro hh
    let : IsMulCommutative P := hh
    apply hnR
    exact IsMulCommutative.of_comm (fun a b => j.symm.injective (by simp only [map_mul,mul_comm]))
  have hex := OrderTwentySeven.extraspecial hP hn
  refine ⟨P,hXP,hex,hP,?_⟩
  have hZX : (center P).map (P : Subgroup H).subtype ≤ X := by
    rintro _ ⟨z,hz,rfl⟩
    exact OrderTwentySeven.center_le_of_card_nine hP hn (X.subgroupOf P)
      (by rw [Nat.card_congr (subgroupOfEquivOfLe hXP).toEquiv]; exact hX) hz
  have hZK : (center P).map (P : Subgroup H).subtype ≤ K := by
    let : IsCyclic (H ⧸ K) := isCyclic_of_card_dvd_prime (p := 3) (by
      rw [←index_eq_card,hiK])
    have hderived : commutator H ≤ K :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
    rw [OrderTwentySeven.center_eq_commutator hP hn,map_subtype_commutator]
    exact (commutator_mono le_top le_top).trans hderived
  apply eq_of_le_of_card_ge (le_inf hZX hZK)
  rw [card_map_of_injective (P : Subgroup H).subtype_injective,
    OrderTwentySeven.center_card hP hn,
    card_inf_component_of_projective K X hK hX hgen
      (show ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 from
        ⟨F,inferInstance,inferInstance,hF,⟨eK⟩⟩) hp]
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The source PGL₃(4) quotient constructs the Sylow subgroup containing the
original Cartan, with center exactly its original component intersection. -/
theorem linear_marked_extraspecial_sylow
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G))) :
    ∃ P : Subgroup G, P ≤ K ⊔ X ∧ X ≤ P ∧ IsExtraspecial 3 P ∧ Nat.card P = 27 ∧
      (center P).map P.subtype = X ⊓ K ∧
      ∃ R : Sylow 3 (K ⊔ X : Subgroup G), (R : Subgroup (K ⊔ X : Subgroup G)).map
        (K ⊔ X : Subgroup G).subtype = P := by
  let J := K ⊔ X
  let B := K.subgroupOf J
  let Y := X.subgroupOf J
  have hKJ : K ≤ J := le_sup_left
  have hXJ : X ≤ J := le_sup_right
  have hu : f.IsInnerUnique := by
    intro i U hU hT
    exact (SL3.flag_inner_unique D S m i U hU hT).trans
      (SL3.flag_inner_unique D S m i (f.space i) (f.dimension i)
        (inf_le_left.trans (f.invariant i))).symm
  have hJH : J ≤ normalizer (f.Vi 0 : Set G) :=
    sup_le hK.1.1 (f.cartan_normalizes hu hX 0)
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (hJH.trans ((normal_subgroupOf_iff_le_normalizer hK.1.1).mp hK.2))
  let k : B ≃* K := subgroupOfEquivOfLe hKJ
  have hB : B.IsCComponent := hK.1.2.subgroupOf_of_le hKJ hJH
  have hr : primeRank 3 J ≤ 2 :=
    (_root_.primeRank_le_of_injective 3 (inclusion hJH) (inclusion_injective hJH)).trans
      ((S.source.simpleQTKE.twoLocal_sqtk (f.normalizer_twoLocal 0)).stronglyQuasithin
        3 Nat.prime_three (by decide))
  have hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 4 := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hk
    exact ⟨F,inferInstance,inferInstance,hF,
      ⟨(QuotientGroup.congr _ _ k (pCore_map_iso 2 k)).trans e⟩⟩
  obtain ⟨R,hYR,hR,hcard,hZ⟩ := marked_extraspecial_sylow_of_projective B Y hB hr
    (by rw [Nat.card_congr (subgroupOfEquivOfLe hXJ).toEquiv,
      (Coordinates.sl3 m).cartan_card hX,hd]; norm_num)
    (by rw [←subgroupOf_sup hKJ hXJ]; exact subgroupOf_self J) hm hp
  let P := (R : Subgroup J).map J.subtype
  let e : R ≃* P := (R : Subgroup J).equivMapOfInjective J.subtype J.subtype_injective
  refine ⟨P,map_subtype_le _,?_,IsExtraspecial.of_mulEquiv e hR,
    (Nat.card_congr e.toEquiv).symm.trans hcard,?_,R,rfl⟩
  · have hh := map_mono (f := J.subtype) hYR
    change (X.subgroupOf J).map J.subtype ≤ P at hh
    rwa [map_subgroupOf_eq_of_le hXJ] at hh
  · have hh := congrArg (map J.subtype) hZ
    rw [map_subgroup_center_eq J.subtype J.subtype_injective,
      Subgroup.map_inf _ _ _ J.subtype_injective,
      map_subgroupOf_eq_of_le hXJ,map_subgroupOf_eq_of_le hKJ] at hh
    exact hh

/-- Nonzero cubic displacement follows from the original projective quotient;
there is no extraspecial-subgroup or faithfulness premise on the span. -/
theorem linear_cubic_displacement_of_projective
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K X : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 ≤ K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 0) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 0) ≤ centralizer (f.Vi 0 : Set G)) :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    ⁅U ⊓ centralizer (E : Set G),X ⊓ K⁆ ≠ ⊥ ∧
      ⁅U ⊓ centralizer (E : Set G),X⁆ ≠ ⊥ := by
  obtain ⟨P,hP,hXP,hPex,_,hZ,_⟩ := linear_marked_extraspecial_sylow D S m f hd hX hK hk hp
  let : IsExtraspecial 3 P := hPex
  exact linear_cubic_displacement_of_marked_extraspecial D S m f hd hfix hX hK.1 hLK
    hcard hmove hP hXP hZ

/-- The complete common-Q span and core dichotomy now uses the original
projective quotient, with the marked extraspecial subgroup constructed. -/
theorem linear_triangle_cubic_displacement_of_projective_common_normal
    (f : InvariantFlag (.sl3 m)) (hd : S.field.degree = 2)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    {K K₀ X Q : Subgroup G} (hX : IsCartan T L X)
    (hK : Source.NormalComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hLK : f.Li 0 < K) (hK₀ : K₀ ∈ Chapter1.L G T) (hK₀K : K₀ < K)
    (hTK₀ : (T : Subgroup G) ≤ normalizer (K₀ : Set G))
    (hgen : f.Li 0 ⊔ K₀ = K)
    (hk : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4)
    (hp : IsPGLThreeFour ((K ⊔ X : Subgroup G) ⧸ pCore 2 (K ⊔ X : Subgroup G)))
    (hcard : Nat.card (X ⊓ Closure.coreQuotientCentralizer (f.Li 1) : Subgroup G) = 3)
    (hmove : ¬ X ⊓ Closure.coreQuotientCentralizer (f.Li 1) ≤ centralizer (f.Vi 0 : Set G))
    (hQ : Q ≠ ⊥) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G))
    (hKQ : K₀ ≤ normalizer (Q : Set G)) (hLQ : f.Li 1 ≤ normalizer (Q : Set G))
    :
    let E := X ⊓ Closure.coreQuotientCentralizer (f.Li 0)
    let H := localResidual L E
    let U := conjugateSpanBy V (centralizer (f.Vi 0 : Set G))
    ⁅U ⊓ centralizer (E : Set G),X⁆ ≠ ⊥ ∧
    (let C := centralizer (f.Vi 0 : Set G)
     let P := (f.Vi 0).subgroupOf C
     let : P.Normal := normal_subgroupOf_of_le_normalizer (Subgroup.centralizer_le_normalizer _)
     (U.subgroupOf C).map (QuotientGroup.mk' P) ≤
       (center (pCore 2 (C ⧸ P))).map (pCore 2 (C ⧸ P)).subtype) ∧
    U ≤ (centralizer (f.Vi 0 : Set G)).pCoreIn 2 ∧
    U ≤ (T : Subgroup G) ∧ (frattini U).map U.subtype ≤ f.Vi 0 ∧
    ⁅U,U⁆ ≤ f.Vi 0 ∧ (K ⊔ X) ⊔ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
    (U.subgroupOf (T : Subgroup G)).Normal ∧ E ≤ H ∧ X ≤ H ∧ H ≤ centralizer (E : Set G) ∧
    Source.IsSL (H ⧸ pCore 2 H) 3 4 ∧
    H.pCoreIn 2 = H ⊓ L.pCoreIn 2 ∧ H ⊔ L.pCoreIn 2 = L ∧
    V = ⁅V,H⁆ ∧ ¬ normalizer (E : Set G) ≤ normalizer (L : Set G) ∧
    (⁅H.pCoreIn 2,H⁆ ≠ ⊥ ∨
      (¬ ⁅U ⊓ centralizer (E : Set G),X⁆ ≤
        (L ⊔ (T : Subgroup G)).pCoreIn 2) ∧
      ¬ U ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2) := by
  obtain ⟨P,hP,hXP,hPex,_,hZ,_⟩ := linear_marked_extraspecial_sylow D S m f hd hX hK hk hp
  let : IsExtraspecial 3 P := hPex
  exact linear_triangle_cubic_displacement_of_common_normal D S m f hd hfix hX hK hLK
    hK₀ hK₀K hTK₀ hgen hk hp hcard hmove hQ hQT hTQ hKQ hLQ hP hXP hZ

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
