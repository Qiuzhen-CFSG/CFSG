module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointBinaryFixedSpan
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFiniteFourMovement
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# A faithful carrier on the original point-kernel section

The actual C-span U of the original four H lies in N=O2(C), and U/<z>
is elementary with the literal C/N conjugation action. The containing
component cannot normalize H by the full four-normalizer obstruction.
Consequently its simple quotient acts nontrivially, hence faithfully, on
this very section. The statement also records an actual moved H/<z>
element, preserving the original point and all section kernels.

Source: Aschbacher--Smith15.3.23, printed pp.1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource ChapterC BinaryMS.MS93
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem faithful_section_of_four_movement
    (C H U Z : Subgroup G) (hHU : H ≤ U) (hZH : Z ≤ H)
    (hCU : C ≤ normalizer U) (K : Subgroup C)
    [IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 C)))]
    (hmove : ¬ K.map C.subtype ≤ normalizer H)
    (hn : (Z.subgroupOf U).Normal) :
    letI := hn
    ∀ ρ : (C ⧸ pCore 2 C) →* MulAut (U ⧸ Z.subgroupOf U),
      (∀ (x : C) (u v : U), (v : G) = x*(u : G)*(x : G)⁻¹ →
        ρ (QuotientGroup.mk' (pCore 2 C) x) (QuotientGroup.mk' (Z.subgroupOf U) u) =
          QuotientGroup.mk' (Z.subgroupOf U) v) →
      Function.Injective (ρ.comp (K.map (QuotientGroup.mk' (pCore 2 C))).subtype) ∧
      ∃ (k : K.map (QuotientGroup.mk' (pCore 2 C))) (h : H),
        ρ k (QuotientGroup.mk' (Z.subgroupOf U) ⟨h,hHU h.property⟩) ≠
          QuotientGroup.mk' (Z.subgroupOf U) ⟨h,hHU h.property⟩ := by
  let := hn
  intro ρ hρ
  let q := QuotientGroup.mk' (pCore 2 C)
  let π := QuotientGroup.mk' (Z.subgroupOf U)
  let A := K.map q
  let σ := ρ.comp A.subtype
  have hnot : ¬ ∀ (k : A) (h : H), ρ k (π ⟨h,hHU h.property⟩) = π ⟨h,hHU h.property⟩ := by
    intro hfix
    apply hmove
    apply le_normalizer_iff_commutator_le_right.mpr
    apply commutator_le.mpr
    rintro g ⟨g,hg,rfl⟩ h hh
    let u : U := ⟨h,hHU hh⟩
    let v : U := ⟨(g : G)*h*(g : G)⁻¹,
      (mem_normalizer_iff.mp (hCU g.property) h).mp (hHU hh)⟩
    have hv : π v = π u := (hρ g u v rfl).symm.trans
      (hfix ⟨q g,mem_map_of_mem q hg⟩ ⟨h,hh⟩)
    have hz : (g : G)*h*(g : G)⁻¹/h ∈ Z :=
      (QuotientGroup.eq_iff_div_mem (N := Z.subgroupOf U)).mp hv
    change ⁅(g : G),h⁆ ∈ H
    exact hZH (by simpa only [commutatorElement_def,div_eq_mul_inv] using hz)
  have hinj : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    rcases (inferInstance : σ.ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exfalso
      apply hnot
      intro k h
      have hk : σ k = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [ht]
        trivial
      exact congrArg (fun f : MulAut (U ⧸ Z.subgroupOf U) => f (π ⟨h,hHU h.property⟩)) hk
  push Not at hnot
  exact ⟨hinj,hnot⟩

/-- The actual binary carrier acts faithfully on the original invariant
point-kernel section and moves an element of the unchanged four modulo z. -/
theorem binary_three_source_binary_faithful_span
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
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (z : G) (hzH : z ∈ LinearThree.OriginalSource.intrinsicFour c.L)
    (hz2 : orderOf z = 2) (hLS : c.L ⊔ d.S ≤ centralizer ({z} : Set G))
    (P : Sylow 2 (centralizer ({z} : Set G)))
    (hP : (P : Subgroup _).map (centralizer ({z} : Set G)).subtype = d.S)
    (K : Subgroup (centralizer ({z} : Set G)))
    (hK : K.IsCComponent) (hKn : K.Normal)
    (hLK : c.L.subgroupOf (centralizer ({z} : Set G)) ≤ K)
    [IsSimpleGroup (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))]
    (eB : (((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) ⧸
      pCore 2 ((c.L.subgroupOf (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) ≃* PSL(3,ZMod 2))
    (hrX : primeRank 3 (centralizer ({z} : Set G) ⧸ pCore 2 (centralizer ({z} : Set G))) = 2)
    (hrB : primeRank 3 (normalizer ((c.L.subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))) ≤ 1)
    {n : ℕ} (hn : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) n 2) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let H := intrinsicFour c.L
    let Z := zpowers z
    let U := conjugateSpanBy H C
    let q := QuotientGroup.mk' (pCore 2 C)
    Z ≤ H ∧ Z.relIndex H = 2 ∧ H ≤ U ∧ U ≤ N ∧
      C ≤ normalizer U ∧ ⁅U,N⁆ ≤ Z ∧
      ∃ hZ : (Z.subgroupOf U).Normal,
        letI := hZ
        IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U) ∧
        ∃ ρ : (C ⧸ pCore 2 C) →* MulAut (U ⧸ Z.subgroupOf U),
          (∀ (x : C) (u v : U), (v : G) = x*(u : G)*(x : G)⁻¹ →
            ρ (q x) (QuotientGroup.mk' (Z.subgroupOf U) u) =
              QuotientGroup.mk' (Z.subgroupOf U) v) ∧
          Function.Injective (ρ.comp (K.map q).subtype) ∧
          (∀ (x : C), (x : G) ∈ c.L ⊔ d.S → ∀ h : H,
            ρ (q x) (QuotientGroup.mk' (Z.subgroupOf U)
              ⟨h,le_conjugateSpanBy H C h.property⟩) =
            QuotientGroup.mk' (Z.subgroupOf U) ⟨h,le_conjugateSpanBy H C h.property⟩) ∧
          ∃ (k : K.map q) (h : H),
            ρ k (QuotientGroup.mk' (Z.subgroupOf U)
              ⟨h,le_conjugateSpanBy H C h.property⟩) ≠
            QuotientGroup.mk' (Z.subgroupOf U) ⟨h,le_conjugateSpanBy H C h.property⟩ := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let H := intrinsicFour c.L
  let Z := zpowers z
  let U := conjugateSpanBy H C
  let : K.Normal := hKn
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  have hBK := map_mono (f := q) hLK
  obtain ⟨hZH,hi,hHU,hUN,hCU,hcomm,hZ,hel,ρ,hρ⟩ :=
    binary_three_source_binary_fixed_span
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP
      (K.map q) hBK hn hm
  let := hZ
  have hmodel : BinaryThreeFiniteSimpleCarrier (K.map q) := Or.inr (Or.inl ⟨n,hn,hm⟩)
  have hmove := (binary_three_source_finite_component_moves_four
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH
    K hK hKn hLK eB hrX hrB hmodel).1
  obtain ⟨hinj,hmoved⟩ := faithful_section_of_four_movement C H U Z hHU hZH hCU K hmove hZ ρ hρ
  let J := c.L ⊔ d.S
  have hJL : J ≤ normalizer (c.L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show c.L ≤ J from le_sup_left)).mp b.component_normal
  have hJH : J ≤ normalizer H := hJL.trans (intrinsicFour_normalized c.L)
  have hCZ : C ≤ centralizer (Z : Set G) := by
    apply le_centralizer_iff.mpr
    apply zpowers_le.mpr
    intro x hx
    exact mem_centralizer_singleton_iff.mp hx
  have hJZ : J ≤ normalizer Z := (hLS.trans hCZ).trans (Subgroup.centralizer_le_normalizer _)
  have hJcomm : ⁅J,H⁆ ≤ Z := by
    rw [commutator_comm]
    exact commutator_le_of_normalized_index_two H Z J hZH hi hJH hJZ
  have hfixed (x : C) (hx : (x : G) ∈ J) (h : H) :
      ρ (q x) (QuotientGroup.mk' (Z.subgroupOf U) ⟨h,hHU h.property⟩) =
        QuotientGroup.mk' (Z.subgroupOf U) ⟨h,hHU h.property⟩ := by
    let u : U := ⟨h,hHU h.property⟩
    let v : U := ⟨(x : G)*(h : G)*(x : G)⁻¹,
      (mem_normalizer_iff.mp (hCU x.property) h).mp (hHU h.property)⟩
    rw [hρ x u v rfl]
    apply (QuotientGroup.eq_iff_div_mem (N := Z.subgroupOf U)).mpr
    change (x : G)*(h : G)*(x : G)⁻¹/(h : G) ∈ Z
    simpa only [commutatorElement_def,div_eq_mul_inv] using
      hJcomm (commutator_mem_commutator hx h.property)
  exact ⟨hZH,hi,hHU,hUN,hCU,hcomm,hZ,hel,ρ,hρ,hinj,hfixed,hmoved⟩

/-- The full original finite point packet keeps all flags and equips each
binary carrier with its actual faithful section and original LS-fixed point. -/
theorem binary_three_large_distance_binary_point_faithful_span
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
    (hc : ¬ IsMulCommutative (BinaryMS.commutatorCore (c.L.subgroupOf (c.L ⊔ d.S))))
    (hb : 4 < t.geometry.b t.reduction.radical)
    (g : G) (hgT : g ∈ (d.T : Subgroup G)) (hgS : g ∉ d.S) :
    ∃ z : G, z ∈ intrinsicFour c.L ∧ orderOf z = 2 ∧
      c.L ⊔ d.S ≤ centralizer ({z} : Set G) ∧
      ¬ centralizer ({z} : Set G) ≤ d.M ∧
      let C := centralizer ({z} : Set G)
      let q := QuotientGroup.mk' (pCore 2 C)
      let B := (c.L.subgroupOf C).map q
      IsSQTK KnownSimple.IsKnownSimple (C ⧸ pCore 2 C) ∧
      pCore 2 (C ⧸ pCore 2 C) = ⊥ ∧
      Nat.card (intrinsicFour B) ≤ 2 ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) ∧
      primeRank 3 (C ⧸ pCore 2 C) = 2 ∧
      primeRank 3 (normalizer (B : Set (C ⧸ pCore 2 C))) ≤ 1 ∧
      ∃ P : Sylow 2 C, (P : Subgroup C).map C.subtype = d.S ∧
        B ∈ ChapterA.Section03.localCComponents
          (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C))) ∧
        (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) : Subgroup _) ≤
          normalizer (B : Set (C ⧸ pCore 2 C)) ∧
        Nonempty (((B ⊔ (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) :
          Subgroup (C ⧸ pCore 2 C)) : Subgroup (C ⧸ pCore 2 C)) ⧸
          pCore 2 (B ⊔ (P.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 C)) :
            Subgroup (C ⧸ pCore 2 C)) : Subgroup (C ⧸ pCore 2 C))) ≃*
          PSL(3,ZMod 2)) ∧
        ∃ K : Subgroup C, K.IsCComponent ∧ K.Normal ∧ c.L.subgroupOf C ≤ K ∧
          (K.map q).IsCComponent ∧ (K.map q).Normal ∧ B < K.map q ∧
          IsSimpleGroup (K.map q) ∧ BinaryThreeFiniteSimpleCarrier (K.map q) ∧
          ¬ IsAlternating (K.map q) 7 ∧
          ¬ K.map C.subtype ≤ normalizer (intrinsicFour c.L) ∧
          ¬ C ≤ normalizer (intrinsicFour c.L) ∧
          (∀ n : ℕ, (n = 4 ∨ n = 5) → ClassicalGroup.IsPSL (K.map q) n 2 →
            let H := intrinsicFour c.L
            let Z := zpowers z
            let U := conjugateSpanBy H C
            U ≤ C.pCoreIn 2 ∧ ⁅U,C.pCoreIn 2⁆ ≤ Z ∧
            ∃ hZ : (Z.subgroupOf U).Normal,
              letI := hZ
              IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U) ∧
              ∃ ρ : (C ⧸ pCore 2 C) →* MulAut (U ⧸ Z.subgroupOf U),
                Function.Injective (ρ.comp (K.map q).subtype) ∧
                (∀ (x : C) (u v : U), (v : G) = x*(u : G)*(x : G)⁻¹ →
                  ρ (q x) (QuotientGroup.mk' (Z.subgroupOf U) u) =
                    QuotientGroup.mk' (Z.subgroupOf U) v) ∧
                (∀ (x : C), (x : G) ∈ c.L ⊔ d.S → ∀ h : H,
                  ρ (q x) (QuotientGroup.mk' (Z.subgroupOf U)
                    ⟨h,le_conjugateSpanBy H C h.property⟩) =
                  QuotientGroup.mk' (Z.subgroupOf U) ⟨h,le_conjugateSpanBy H C h.property⟩) ∧
                ∃ (k : K.map q) (h : H),
                  ρ k (QuotientGroup.mk' (Z.subgroupOf U)
                    ⟨h,le_conjugateSpanBy H C h.property⟩) ≠
                  QuotientGroup.mk' (Z.subgroupOf U) ⟨h,le_conjugateSpanBy H C h.property⟩) := by
  obtain ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,⟨eB⟩,hr,hn,
    P,hP,hB,hSB,hjoin,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hmodel,hnot7,hKmove,hCmove⟩ :=
    binary_three_large_distance_finite_point_four_movement
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb g hgT hgS
  refine ⟨z,hz,hz2,hLS,hout,hsq,hzero,hfour,⟨eB⟩,hr,hn,
    P,hP,hB,hSB,hjoin,K,hK,hKn,hLK,hKq,hKnq,hBKq,hsimple,hmodel,hnot7,hKmove,hCmove,?_⟩
  intro n hn₀ hm
  let := hsimple
  obtain ⟨_,_,_,hUN,_,hcomm,hZ,hel,ρ,hρ,hinj,hfix,hmoved⟩ :=
    binary_three_source_binary_faithful_span
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hz hz2 hLS P hP
      K hK hKn hLK eB hr hn hn₀ hm
  exact ⟨hUN,hcomm,hZ,hel,ρ,hinj,hρ,hfix,hmoved⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
