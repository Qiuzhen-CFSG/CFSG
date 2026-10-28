module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointFourFixedCover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointBinaryFaithfulSpan

/-!
# The faithful original fifteen-coset fixed-line quotient

The same actual action supplied by the original fixed cover is faithful on
the original containing component image: a trivial action would normalize
H, contrary to the original finite-component movement theorem. Simplicity
then kills the action kernel. This keeps the same rho, seed, quotient map
and fifteen-coset surjection, rather than selecting an unrelated action.

Source context: Aschbacher--Smith 15.3.23, original binary-four carrier.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open LinearThree LinearThree.OriginalSource CoreActions ChapterC BinaryMS.MS93
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem faithful_fixed_section_of_movement
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

omit [Finite G] in
private theorem faithful_elementary_action {A E : Type*} [Group A] [Group E]
    [IsElementaryAbelian 2 E] (ρ : A →* MulAut E) (hρ : Function.Injective ρ) :
    Function.Injective (elementaryRepresentation (p := 2) ρ) := by
  intro x y h
  apply hρ
  apply MulEquiv.ext
  intro w
  exact Additive.ofMul.injective (LinearMap.congr_fun h (Additive.ofMul w))

/-- The exact earlier original component packet supplies a faithful,
nontrivial fifteen-coset quotient on the unchanged original U/<z>. -/
theorem binary_three_source_four_faithful_fixed_cover
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
    (hm : ClassicalGroup.IsPSL
      (K.map (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))) 4 2) :
    let C := centralizer ({z} : Set G)
    let N := C.pCoreIn 2
    let q := QuotientGroup.mk' (pCore 2 C)
    let Kbar := K.map q
    let B := (c.L.subgroupOf C).map q
    let H := intrinsicFour c.L
    let Z := zpowers z
    let U := conjugateSpanBy H C
    Z ≤ H ∧ Z.relIndex H = 2 ∧ H ≤ U ∧ U ≤ N ∧
      C ≤ normalizer U ∧ ⁅U,N⁆ ≤ Z ∧ (B.subgroupOf Kbar).index = 15 ∧
      ∃ hZ : (Z.subgroupOf U).Normal,
        let := hZ
        ∃ hel : IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U),
          let := hel
          ∃ ρ : (C ⧸ pCore 2 C) →* MulAut (U ⧸ Z.subgroupOf U),
            (∀ (x : C) (u v : U), (v : G) = x*(u : G)*(x : G)⁻¹ →
              ρ (q x) (QuotientGroup.mk' (Z.subgroupOf U) u) =
                QuotientGroup.mk' (Z.subgroupOf U) v) ∧
            Function.Injective (ρ.comp Kbar.subtype) ∧
            ∃ h : H,
              let w := Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U)
                (inclusion (le_conjugateSpanBy H C) h))
              let τ := elementaryRepresentation (p := 2) (ρ.comp Kbar.subtype)
              Function.Injective τ ∧ w ≠ 0 ∧
              (∀ a : H, QuotientGroup.mk' (Z.subgroupOf U)
                (inclusion (le_conjugateSpanBy H C) a) = 1 ∨
                QuotientGroup.mk' (Z.subgroupOf U)
                  (inclusion (le_conjugateSpanBy H C) a) = w.toMul) ∧
              (∀ b : B.subgroupOf Kbar, τ b.val w = w) ∧
              Submodule.span (ZMod 2) (Set.range (fun k : Kbar => τ k w)) = ⊤ ∧
              ∃ f : ((Kbar ⧸ B.subgroupOf Kbar) →₀ ZMod 2) →ₗ[ZMod 2]
                  Additive (U ⧸ Z.subgroupOf U),
                Function.Surjective f ∧
                (∀ k : Kbar, f (Finsupp.single (QuotientGroup.mk k) 1) = τ k w) ∧
                (∀ (k : Kbar) v, f (Finsupp.lmapDomain (ZMod 2) (ZMod 2)
                  (fun a : Kbar ⧸ B.subgroupOf Kbar => k • a) v) = τ k (f v)) := by
  let C := centralizer ({z} : Set G)
  let q := QuotientGroup.mk' (pCore 2 C)
  let H := intrinsicFour c.L
  let Z := zpowers z
  let U := conjugateSpanBy H C
  let := hKn
  let : (K.map q).Normal := hKn.map q (QuotientGroup.mk'_surjective _)
  have hBK := map_mono (f := q) hLK
  obtain ⟨hZH,hi,hHU,hUN,hCU,hcomm,hindex,hZ,hel,ρ,hρ,h,hw,hseed,hfix,hspan,f,hfs,hfp,hfe⟩ :=
    binary_three_source_four_fixed_cover
      hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH hz2 hLS P hP (K.map q) hBK hm
  let := hZ
  let := hel
  have hmodel : BinaryThreeFiniteSimpleCarrier (K.map q) := Or.inr (Or.inl ⟨4,Or.inl rfl,hm⟩)
  have hmove := (binary_three_source_finite_component_moves_four
    hG d hempty hM hu hmany hI htwo hf c e b t hc hb z hzH
    K hK hKn hLK eB hrX hrB hmodel).1
  have hinj := (faithful_fixed_section_of_movement C H U Z hHU hZH hCU K hmove hZ ρ hρ).1
  exact ⟨hZH,hi,hHU,hUN,hCU,hcomm,hindex,hZ,hel,ρ,hρ,hinj,h,
    faithful_elementary_action (ρ.comp (K.map q).subtype) hinj,
    hw,hseed,hfix,hspan,f,hfs,hfp,hfe⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
