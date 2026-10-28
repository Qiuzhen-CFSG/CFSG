module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationQuasisimple
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.SymplecticCubicResidual
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.G2CubicResidual
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.ReeCubicResidual
public import Theory.SpecificGroups.BinaryComponentResidual
public import Theory.SpecificGroups.SymplecticFour.Binary
public import Theory.SpecificGroups.Tits.OuterOddSubgroups
/-!
# The nonlinear binary Cartan-container sieve

Apply the existing Sp4, G2 and Ree cubic-residual theorems to the literal
image of the containing C-component modulo the ambient two-core. Its
cubic-prime index lifts through that two-core. Hence the original Cartan
plane would lie in the containing component, contradicting A intersect J
of order three. The small derived and Tits rows have two-group outer
automorphisms and are already excluded by the original normalization cases.

Consequently the genuine Theorem C rank-two branch can only be binary
PSL3. The final consumer retains all original tensor, local A5-section,
full-Sylow and Cartan-intersection markings; no universal classification
or action premise is introduced.

Source: Aschbacher--Smith A.3.18 and Proposition 9.3.1,
printed pp.51--53,732--733.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)
private theorem image_setup (J : Subgroup G)
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    [IsQuasisimple (J ⧸ pCore 2 J)]
    (hz : Nat.Coprime 3 (Nat.card (center (J ⧸ pCore 2 J)))) :
    let N := normalizer (m.tensorLine : Set G)
    let q := QuotientGroup.mk' (pCore 2 N)
    let I := (J.subgroupOf N).map q
    IsSQTK KnownSimple.IsKnownSimple (N ⧸ pCore 2 N) ∧
      IsComponent (N ⧸ pCore 2 N) I ∧ center I = ⊥ ∧
      Nonempty (I ≃* (J ⧸ pCore 2 J)) := by
  intro N q I
  let K := J.subgroupOf N
  let j : K ≃* J := subgroupOfEquivOfLe hJU
  let b : (K ⧸ pCore 2 K) ≃* (J ⧸ pCore 2 J) :=
    QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  let c : (K ⧸ pCore 2 K) ≃* I := cComponentTwoCoreQuotientEquiv hJ
  let d : I ≃* (J ⧸ pCore 2 J) := c.symm.trans b
  let : IsQuasisimple I := IsQuasisimple.of_mulEquiv d.symm
  obtain ⟨_,hz0,_⟩ := m.cartan_quasisimple_container_catalogue J hJU hz
  let : Group.IsNilpotent (pCore 2 N) := pCore_isNilpotent
  have hI : IsComponent (N ⧸ pCore 2 N) I :=
    ⟨(hJ.map_quotient (pCore 2 N)).subnormal,inferInstance⟩
  have hzI : center I = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact d.map_eq_one_iff.mp (hz0.le ((centerCongr d) ⟨x,hx⟩).property)
  have hN := D.simpleQTKE.twoLocal_sqtk (show IsTwoLocal N from
    ⟨m.tensorLine,m.tensorLine_ne_bot,IsPGroup.of_card (n := 2) m.card_tensorLine,rfl⟩)
  refine ⟨⟨?_,hN.isKGroup.quotient _⟩,hI,hzI,⟨d⟩⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (hN.stronglyQuasithin p hp ho)
private theorem not_cubic_image
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hA9 : Nat.card A = 9) (hB3 : Nat.card B = 3)
    (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (_hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hnJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal)
    (hAJB : A ⊓ J = B)
    (he : (J.subgroupOf (normalizer (m.tensorLine : Set G))).map
      (QuotientGroup.mk' (pCore 2 (normalizer (m.tensorLine : Set G)))) =
      primeToResidual 3 ((normalizer (m.tensorLine : Set G)) ⧸
        pCore 2 (normalizer (m.tensorLine : Set G)))) : False := by
  let N := normalizer (m.tensorLine : Set G)
  let I := J.subgroupOf N
  let C := A.subgroupOf N
  let Q := pCore 2 N
  let := hnJ
  have hi := primeToResidual_index_coprime (G := N ⧸ Q) 3
  rw [←he,index_map,QuotientGroup.ker_mk',
    MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Q),index_top,mul_one] at hi
  have hidx : Nat.Coprime 3 I.index := by
    rw [←relIndex_mul_index (show I ≤ I ⊔ Q from le_sup_left)]
    apply Nat.Coprime.mul_right _ hi
    rw [relIndex_sup_left]
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := N)).exists_card_eq
    have hcop : Nat.Coprime 3 (Nat.card Q) := by
      change Nat.Coprime 3 (Nat.card (pCore 2 N))
      rw [hn]
      exact (by decide : Nat.Coprime 3 2).pow_right n
    exact hcop.coprime_dvd_right (relIndex_dvd_card _ _)
  have hCI : C ≤ I := (le_primeToResidual_of_isPGroup
    (IsElementaryAbelian.isPGroup 3 A).comap_subtype).trans (primeToResidual_le I hidx)
  have hAJ : A ≤ J := by
    intro x hx
    exact hCI (show (⟨x,hAU hx⟩ : N) ∈ C from hx)
  have hc := congrArg (fun K : Subgroup G => Nat.card K)
    ((inf_eq_left.mpr hAJ).symm.trans hAJB)
  rw [hA9,hB3] at hc
  omega

/-- The symplectic cubic residual contradicts the marked order-three intersection. -/
theorem cartan_container_not_binary_symplectic
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hA9 : Nat.card A = 9) (hB3 : Nat.card B = 3)
    (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hnJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal)
    (hAJB : A ⊓ J = B) [IsQuasisimple (J ⧸ pCore 2 J)]
    (hz : Nat.Coprime 3 (Nat.card (center (J ⧸ pCore 2 J))))
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (a : (J ⧸ pCore 2 J) ≃* Matrix.symplecticGroup (Fin 2) F) : False := by
  obtain ⟨hN,hI,hzI,⟨d⟩⟩ := m.image_setup J hJU hJ hz
  let c := ((QuotientGroup.quotientMulEquivOfEq hzI).trans QuotientGroup.quotientBot).trans d
  exact m.not_cubic_image A B J hA9 hB3 hAU hJU hnJ hAJB
    (ChapterA.Section03.OddPrime.SourceModels.SymplecticCubicResidual.component_eq_primeClosure_and_residual
      hN hI (by rw [hzI]; exact IsPGroup.of_card (n := 0) (by simp)) hF (c.trans a)).2

/-- The G2 cubic residual contradicts the marked order-three intersection. -/
theorem cartan_container_not_binary_g2
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hA9 : Nat.card A = 9) (hB3 : Nat.card B = 3)
    (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hnJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal)
    (hAJB : A ⊓ J = B) [IsQuasisimple (J ⧸ pCore 2 J)]
    (hz : Nat.Coprime 3 (Nat.card (center (J ⧸ pCore 2 J))))
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : 2 < Nat.card F)
    (a : (J ⧸ pCore 2 J) ≃* Atlas.G2.Model F) : False := by
  obtain ⟨hN,hI,hzI,⟨d⟩⟩ := m.image_setup J hJU hJ hz
  let c := ((QuotientGroup.quotientMulEquivOfEq hzI).trans QuotientGroup.quotientBot).trans d
  exact m.not_cubic_image A B J hA9 hB3 hAU hJU hnJ hAJB
    (ChapterA.Section03.OddPrime.SourceModels.G2CubicResidual.component_eq_primeClosure_and_residual
      hN hI (by rw [hzI]; exact IsPGroup.of_card (n := 0) (by simp)) hF (c.trans a)).2

/-- The Ree cubic residual contradicts the marked order-three intersection. -/
theorem cartan_container_not_ree
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hA9 : Nat.card A = 9) (hB3 : Nat.card B = 3)
    (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hnJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal)
    (hAJB : A ⊓ J = B) [IsQuasisimple (J ⧸ pCore 2 J)]
    (hz : Nat.Coprime 3 (Nat.card (center (J ⧸ pCore 2 J))))
    {n : ℕ} (hn : 1 ≤ n) (a : (J ⧸ pCore 2 J) ≃* ReeF4.Model n) : False := by
  obtain ⟨hN,hI,hzI,⟨d⟩⟩ := m.image_setup J hJU hJ hz
  let c := ((QuotientGroup.quotientMulEquivOfEq hzI).trans QuotientGroup.quotientBot).trans d
  exact m.not_cubic_image A B J hA9 hB3 hAU hJU hnJ hAJB
    (ChapterA.Section03.OddPrime.SourceModels.ReeCubicResidual.component_eq_primeClosure_and_residual
      hN hI (by rw [hzI]; exact IsPGroup.of_card (n := 0) (by simp)) hn (c.trans a)).2

/-- Every surviving binary rank-two model is projective linear of degree three. -/
theorem cartan_container_binary_rank_two_isLinear
    (A B J : Subgroup G) [IsElementaryAbelian 3 A]
    (hA9 : Nat.card A = 9) (hB3 : Nat.card B = 3)
    (hAU : A ≤ normalizer (m.tensorLine : Set G))
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hnJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal)
    (hAJB : A ⊓ J = B) [IsQuasisimple (J ⧸ pCore 2 J)]
    (hz : Nat.Coprime 3 (Nat.card (center (J ⧸ pCore 2 J))))
    (hout : ¬ IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J)))
    (n : ℕ) (hm : ChapterA.Section02.IsTheoremCRankTwoModel (J ⧸ pCore 2 J) n) :
    ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 (2 ^ n) := by
  cases hm with
  | linear _ h => exact h
  | symplectic hn h =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := h
    let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
      norm_num at hh
      omega
    exact (m.cartan_container_not_binary_symplectic A B J hA9 hB3 hAU hJU hJ hnJ hAJB hz hlarge
      (a.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm)).elim
  | g2 hn h =>
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := h
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
      norm_num at hh
      omega
    exact (m.cartan_container_not_binary_g2 A B J hA9 hB3 hAU hJU hJ hnJ hAJB hz hlarge a).elim
  | triality hn h =>
    exact (m.cartan_container_not_triality_model A B J hA9 hB3 hAU hJU hJ hAJB
      n (by omega) h).elim
  | ree_f4 k hk _ h =>
    exact (m.cartan_container_not_ree A B J hA9 hB3 hAU hJU hJ hnJ hAJB hz hk h.some).elim
  | symplectic_derived _ h =>
    let a := h.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
    exact (hout ((IsPGroup.of_card (n := 2) AlternatingSix.ShadowLocal.outer_card).of_injective
      (MulAut.outerCongr a).toMonoidHom (MulAut.outerCongr a).injective)).elim
  | g2_derived _ h =>
    exact (hout (Theory.SpecificGroups.BinaryComponentResidual.g2_outer_two.of_injective
      (MulAut.outerCongr h.some).toMonoidHom (MulAut.outerCongr h.some).injective)).elim
  | tits _ h =>
    exact (hout (Tits.OuterOddSubgroups.parrott_outer_isPGroup.of_injective
      (MulAut.outerCongr h.some).toMonoidHom (MulAut.outerCongr h.some).injective)).elim

/-- The actual original source reduction excludes every nonlinear binary
rank-two family, while preserving the proper local A5 section and Cartan marking. -/
theorem nonzero_core_cartan_normalization_binary_sieve
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hcore : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) ∨
    ∃ J : Subgroup G,
      J ≤ normalizer (m.tensorLine : Set G) ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal ∧
      (pResidual 2 H).map H.subtype < J ∧
      A ≤ normalizer (J : Set G) ∧
      J ≤ centralizer (m.tensorLine : Set G) ∧
      J.pCoreIn 2 ≤ (T : Subgroup G) ∧
      A ⊓ J = B ∧ primeRank 3 J ≤ 2 ∧
      ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 4 ∧
      Nat.Coprime 3 (Nat.card (center (J ⧸ pCore 2 J))) ∧
      (IsQuasisimple (J ⧸ pCore 2 J) →
        IsSimpleGroup (J ⧸ pCore 2 J) ∧ center (J ⧸ pCore 2 J) = ⊥ ∧
        ChapterA.Section02.IsTheoremCModel (J ⧸ pCore 2 J) ∧
        ¬ IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J)) ∧
        (∀ n : ℕ, 0 < n →
          ¬ Triality.Standard.IsTrialityGroupAt (2 ^ n) (J ⧸ pCore 2 J)) ∧
        ∀ n : ℕ, ChapterA.Section02.IsTheoremCRankTwoModel (J ⧸ pCore 2 J) n →
          ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 (2 ^ n)) := by
  obtain hAK | ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,hpsl,hz3,hqs⟩ :=
    m.nonzero_core_cartan_normalization_quasisimple_sieve hH hlarge
      A B hAB hA9 hAe hB3 hBK hBC hcore
  · exact Or.inl hAK
  refine Or.inr ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,hpsl,hz3,?_⟩
  intro hq
  let := hq
  let := hAe
  obtain ⟨hs,hz,hm,hout,htrial⟩ := hqs hq
  exact ⟨hs,hz,hm,hout,htrial,fun n hmodel =>
    m.cartan_container_binary_rank_two_isLinear A B J hA9 hB3
      (hAB.trans m.borel_normalizes_tensorLine) hJU hJ hnJ hAJB hz3 hout n hmodel⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
