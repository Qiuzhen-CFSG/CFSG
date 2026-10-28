module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryCoreDisplacement
public import Theory.GroupTheory.PResidual.PrimeToSubnormal
public import Theory.GroupAction.ThirteenSmallTwoGroup

/-!
# Small invariant subgroups and growth of the retained binary kernel

Write X = CT, U = ⟨Ω₁(Z(T))ᴸ⟩ and E = U ∩ O₂(X) in the surviving
binary-triality row. The original whole-module bound gives |U| ≤ 256.
Thirteen-elements generate the two-perfect component C, whereas thirteen
cannot act on a two-group of order below 4096. Thus C centralizes every
subgroup of U that it normalizes. Characteristic two then forces
|O₂(X)| ≥ 4096.

The actual X-span N = ⟨Eˣ⟩ stays inside O₂(X). If |N| < 4096, C
centralizes N, so T-invariance of E gives N = E. In that branch the
previous quintic displacement result applies to E with its invariance
premise proved: a quintic in O²(C_L(B)) moves E, and U is not contained
in O₂(X). Otherwise |N| ≥ 4096. No invariance or triviality of E is
assumed, and this dichotomy does not yet exclude binary triality.

Source: the retained-core configuration in Aschbacher--Smith 5.1.10--13,
printed pp.634--638, refs/quasithin.pdf. The cardinal estimate uses the
coprime fixed-point counting argument in ThirteenSmallTwoGroup.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]

private theorem triality_small_action_trivial
    {J V : Type*} [Group J] [Finite J] [Group V] [Finite V]
    (hJ : IsPPerfect 2 J)
    (e : (J ⧸ pCore 2 J) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one)
    (hV : IsPGroup 2 V) (hc : Nat.card V < 4096) (f : J →* MulAut V) :
    ∀ j, f j = 1 := by
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  let : IsSimpleGroup (J ⧸ pCore 2 J) := e.isSimpleGroup
  have hd : 13 ∣ Nat.card (J ⧸ pCore 2 J) := by
    rw [Nat.card_congr e.toEquiv,
      Triality.Standard.ConcreteBruhat.FixedCellCount.card_carrier,
      Triality.Standard.ConcreteBruhat.FixedCellCount.card_borel]
    norm_num [Triality.Standard.binaryParameters_q]
  have hr := primeToResidual_eq_top_of_simple_quotient 13 2 (pCore 2 J)
    pCore_isPGroup hJ hd
  have hk := primeToResidual_le_ker f (MulAut.thirteen_coprime_of_twoGroup_card_lt hV hc)
  rw [hr] at hk
  exact fun j => hk (mem_top j)


private theorem small_two_subgroup_centralized
    {Y N : Subgroup G} (C : Subgroup Y) (hC : C.IsCComponent)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C))
    (hN : IsPGroup 2 N) (hc : Nat.card N < 4096)
    (hn : C.map Y.subtype ≤ normalizer (N : Set G)) :
    C.map Y.subtype ≤ centralizer (N : Set G) := by
  let f : C →* MulAut N := N.normalizerMonoidHom.comp
    ((Y.subtype.comp C.subtype).codRestrict (normalizer (N : Set G))
      (fun c => hn (mem_map_of_mem Y.subtype c.property)))
  let := hC.perfect
  have hp : IsPPerfect 2 C := by
    intro K hK hquot
    let := hK
    let : Group.IsNilpotent (C ⧸ K) := hquot.isNilpotent
    exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ K)
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ 1 Nat.zero_lt_one).mp
    (show Triality.Standard.IsTrialityGroupAt (2^1) (C ⧸ pCore 2 C) by simpa using hm)
  have hf := triality_small_action_trivial hp e hN hc f
  rintro x ⟨y,hy,rfl⟩ z hz
  have he := congrArg (fun a : MulAut N => (a ⟨z,hz⟩ : G)) (hf ⟨y,hy⟩)
  change (y : G) * z * (y : G)⁻¹ = z at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The original omega-span has order at most 256. Any of its subgroups
normalized by the actual containing component is centralized by it. -/
theorem original_binary_triality_small_invariant
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    Nat.card U ≤ 256 ∧
      ∀ N : Subgroup G, N ≤ U → C.map Y.subtype ≤ normalizer (N : Set G) →
        C.map Y.subtype ≤ centralizer (N : Set G) := by
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  obtain ⟨hu,_,_,_,_⟩ := original_binary_triality_fixed_omega_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨hn,_,_,hBorel,_,_⟩ := original_binary_triality_module_and_hall
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hHC := (original_container_module_restrictions h hH hgen c hKH hK hKT horbit
    hY hescape C hC hKC hm).2.1
  obtain ⟨F,_,_,hF,⟨f⟩⟩ := h.linear
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (show Nat.card F = 4 by simpa [hn] using hF)
  have hd := (h.whole_deleted_bound_of_borel hH hHC (f.trans a) hBorel).2
  have hw : Nat.card (Chapter12.Section02.RankOneModule.wholeReduced T L) ≤ 256 := by
    rw [←Nat.card_congr (Chapter12.Section02.RankOneModule.wholeSpaceEquiv T L).toEquiv]
    change Nat.card (Chapter12.Section02.RankOneModule.wholeSpace T L) ≤ 256
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hd
  have hU : Nat.card U ≤ 256 := (Nat.card_le_card_of_injective
    (inclusion hu.le_wholeReduced) (inclusion_injective _)).trans hw
  refine ⟨hU,?_⟩
  intro N hNU hCN
  exact small_two_subgroup_centralized C hC hm
    (T.isPGroup'.to_le (hNU.trans hu.reduced_le_sylow))
    ((Nat.card_le_card_of_injective (inclusion hNU) (inclusion_injective hNU)).trans_lt
      (hU.trans_lt (by decide))) hCN

/-- The retained two-core has order at least 4096: a smaller core would
be centralized by C, contradicting characteristic two of the same CT. -/
theorem original_binary_triality_core_size
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    4096 ≤ Nat.card ((C.map Y.subtype ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  obtain ⟨_,hX,_,_⟩ := original_binary_triality_core_bound
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  by_contra hn
  have hXQ : X ≤ normalizer (Q : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hCQ := small_two_subgroup_centralized C hC hm
    (isPGroup_pCoreIn 2 X) (Nat.lt_of_not_ge hn) (le_sup_left.trans hXQ)
  have hchar := Chapter1.lemma_1_1_4_6 T (h.qtke.evenCharacteristic T)
    (show X ∈ Chapter1.HOver G (T : Set G) from ⟨hX.1,show (T : Subgroup G) ≤ X from le_sup_right⟩)
  have hCP : C.map Y.subtype ≤ Q := (le_inf le_sup_left hCQ).trans hchar
  have hp : IsPGroup 2 C := (isPGroup_pCoreIn 2 X).of_injective
    ((Y.subtype.comp C.subtype).codRestrict Q (fun c => hCP (mem_map_of_mem Y.subtype c.property)))
    (by intro x y he; exact Subtype.ext (Subtype.ext (congrArg (fun z : Q => (z : G)) he)))
  exact hC.not_isSolvable (let := hp.isNilpotent; inferInstance)

/-- The actual CT-span of the kernel either has order at least 4096 or
equals the kernel. In the latter branch the component centralizes it,
a quintic in the original seven-centralizer residual moves it, and the
whole omega-span is not contained in the two-core. -/
theorem original_binary_triality_kernel_growth
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let E := U ⊓ X.pCoreIn 2
    let N := conjugateSpanBy E X
    N ≤ X.pCoreIn 2 ∧ X ≤ normalizer (N : Set G) ∧
      (C.map Y.subtype ≤ normalizer (E : Set G) ↔
        C.map Y.subtype ≤ centralizer (E : Set G)) ∧
      ((N = E ∧ C.map Y.subtype ≤ centralizer (E : Set G) ∧ Nat.card N ≤ 256 ∧
        ¬ U ≤ X.pCoreIn 2 ∧
        ∃ F : Subgroup G, F ≤ residual (L ⊓ centralizer (B : Set G)) ∧
          Nat.card F = 5 ∧ F ≤ centralizer (B : Set G) ∧
          ¬ F ≤ normalizer (E : Set G)) ∨ 4096 ≤ Nat.card N) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ Q
  let N := conjugateSpanBy E X
  obtain ⟨hu,_,_,_,_⟩ := original_binary_triality_fixed_omega_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨hU,hnorm⟩ := original_binary_triality_small_invariant
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hXQ : X ≤ normalizer (Q : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hTE : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_inf (le_sup_right.trans (reduced_normalizes hu.reduced))
      (le_sup_right.trans hXQ)).trans inf_normalizer_le_normalizer_inf
  have hNQ : N ≤ Q := conjugateSpanBy_le inf_le_right hXQ
  have hXN : X ≤ normalizer (N : Set G) := le_normalizer_conjugateSpanBy _ _
  refine ⟨hNQ,hXN,⟨hnorm E inf_le_left,
    fun hc => hc.trans (Subgroup.centralizer_le_normalizer _)⟩,?_⟩
  by_cases hlarge : 4096 ≤ Nat.card N
  · exact .inr hlarge
  have hCN := small_two_subgroup_centralized C hC hm
    ((isPGroup_pCoreIn 2 X).to_le hNQ) (Nat.lt_of_not_ge hlarge)
    (le_sup_left.trans hXN)
  have hCE : C.map Y.subtype ≤ centralizer (E : Set G) :=
    hCN.trans (centralizer_le (le_conjugateSpanBy E X))
  have hXE : X ≤ normalizer (E : Set G) :=
    sup_le (hCE.trans (Subgroup.centralizer_le_normalizer _)) hTE
  have he : N = E := le_antisymm (conjugateSpanBy_le le_rfl hXE) (le_conjugateSpanBy E X)
  have hsmall : Nat.card N ≤ 256 := by
    rw [he]
    exact (Nat.card_le_card_of_injective
      (inclusion (show E ≤ U from inf_le_left)) (inclusion_injective _)).trans hU
  obtain ⟨_,_,_,_,_,_,_,_,hlower⟩ := original_binary_triality_core_bound
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hE0 : E ≠ ⊥ := by
    intro hz
    change 2 ≤ Nat.card E at hlower
    rw [hz,card_bot] at hlower
    omega
  obtain ⟨F,hFR,hF,hFB,_,_,_,_,hmoves⟩ :=
    original_binary_triality_quintic_core_displacement
      h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hmove := hmoves E ((isPGroup_pCoreIn 2 X).to_le inf_le_right) hE0 hXE
  have hnot : ¬ U ≤ X.pCoreIn 2 := by
    intro hUQ
    have hRE := (original_binary_triality_kernel_span
      h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm).2.2.mpr hUQ
    exact hmove (hFR.trans hRE)
  exact .inl ⟨he,hCE,hsmall,hnot,F,hFR,hF,hFB,hmove⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
