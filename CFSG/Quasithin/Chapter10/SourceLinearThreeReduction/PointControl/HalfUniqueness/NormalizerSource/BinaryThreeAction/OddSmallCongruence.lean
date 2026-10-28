module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.OddSmallCollapsed
public import Theory.SpecificGroups.PSL2.CubicNormalizerCongruence

/-!
# Cubic congruences in the collapsed-radical enlargement

If O₂(X) lies in O₂(K), the actual image of X in K/O₂(K) is the
image of its original cubic complement. It is normalized by the full
quotient Sylow. The rank-two bound makes a nontrivial coordinate image
cyclic of order three, normalized by a four-group. The reflected-torus
centralizer calculation therefore forces p congruent to 11 or 13 modulo
24. All other small-congruence normalizers are consequently settled.

The final application retains both original contracts, the literal
half-join, and every source guard on the remaining collapsed configuration.
Excluding that configuration remains with qt-d-10-nona5-half-sylow-unique;
this is a reduction, not the completed 10.2.5--6. ModuleChoiceAt is the only
external premise, finally discharged by qt-d-10-nona5-point-control.
Source: Aschbacher--Smith 10.2.5--6, printed pp.748--749.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding

private theorem small_pair_cubic_congruence
    {Q B : Type*} [Group Q] [Finite Q] [Group B] [Finite B]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL Q 2 p) (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (e : B ≃* Q × Q) (S : Sylow 2 B) (A : Subgroup B)
    [IsElementaryAbelian 3 A] (hA : A ≠ ⊥)
    (hr : primeRank 3 (Q × Q) ≤ 2)
    (hn : (S : Subgroup B) ≤ normalizer (A : Set B)) :
    p % 24 = 11 ∨ p % 24 = 13 := by
  let : Fact p.Prime := ⟨hp⟩
  let A' := A.map e.toMonoidHom
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hA' : A' ≠ ⊥ := by
    intro hh
    exact hA ((map_eq_bot_iff_of_injective A e.injective).mp hh)
  obtain ⟨f,hf,hfA⟩ : ∃ f : (Q × Q) →* Q, Function.Surjective f ∧ A'.map f ≠ ⊥ := by
    by_cases hfst : A'.map (MonoidHom.fst Q Q) = ⊥
    · refine ⟨MonoidHom.snd Q Q,fun x => ⟨(1,x),rfl⟩,?_⟩
      intro hsnd
      apply hA'
      apply bot_unique
      intro x hx
      exact Prod.ext (mem_bot.mp (hfst ▸ mem_map_of_mem (MonoidHom.fst Q Q) hx))
        (mem_bot.mp (hsnd ▸ mem_map_of_mem (MonoidHom.snd Q Q) hx))
    · exact ⟨MonoidHom.fst Q Q,fun x => ⟨(x,1),rfl⟩,hfst⟩
  let C := A'.map f
  let V := S'.mapSurjective hf
  let : IsElementaryAbelian 3 A' := IsElementaryAbelian.map e.toMonoidHom
  let : IsElementaryAbelian 3 C := IsElementaryAbelian.map f
  let : IsCyclic C := SwappedFactorsProof.cyclic_pSubgroup_of_product_rank
    (by decide : Odd 3) hr C (IsElementaryAbelian.isPGroup 3 C)
  let : Nontrivial C := (nontrivial_iff_ne_bot C).mpr hfA
  have hC : Nat.card C = 3 := by
    rw [← IsCyclic.exponent_eq_card,IsElementaryAbelian.exponent_eq_prime (p := 3)]
  have hVC : (V : Subgroup Q) ≤ normalizer (C : Set Q) :=
    (map_mono ((map_mono hn).trans (le_normalizer_map e.toMonoidHom))).trans
      (le_normalizer_map f)
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let c : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let j := eF.trans (Atlas.fieldEquivPSL 2 c)
  let W := V.mapSurjective (f := j.toMonoidHom) j.surjective
  let C' := C.map j.toMonoidHom
  have hodd : GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p,1,hp,ho,by decide,by simp⟩
  have h8 : ¬ 8 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :=
    Theory.PSL2.not_eight_dvd_card_of_small_mod_eight (by simpa using ho) (by simpa using hmod)
  let : IsKleinFour W := Theory.PSL2.small_sylow_kleinFour hodd h8 W
  apply Theory.PSL2.prime_mod24_of_four_normalizes_cubic ho hmod
    (W : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))) C'
  · rw [card_map_of_injective j.injective]
    exact hC
  · exact (map_mono hVC).trans (le_normalizer_map j.toMonoidHom)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {H P I : Subgroup G}

/-- Killing the actual radical identifies the residual image with its
original complement, through the same quotient map. -/
theorem Data.quotient_residual_eq_complement_of_core_le (h : Data D H)
    (hi : LocalInput 3 (T : Subgroup G) (residual H) P (enlargement T L H))
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    quotientImage (enlargedResidual T L H) (residual H) =
      quotientImage (enlargedResidual T L H) P := by
  have hCK : (residual H).pCoreIn 2 ≤ enlargedResidual T L H :=
    (pCoreIn_le 2 _).trans h.residual_le_enlargedResidual
  have hPK : P ≤ enlargedResidual T L H := hi.complement_le.trans h.residual_le_enlargedResidual
  have he := congrArg (fun A : Subgroup G => A.subgroupOf (enlargedResidual T L H)) hi.complement
  rw [subgroupOf_sup hCK hPK] at he
  have he' := congrArg (Subgroup.map (QuotientGroup.mk' (pCore 2 (enlargedResidual T L H)))) he
  rw [Subgroup.map_sup] at he'
  change quotientImage _ ((residual H).pCoreIn 2) ⊔ quotientImage _ P =
    quotientImage _ (residual H) at he'
  rw [h.quotient_core_eq_bot_iff.mpr hc,bot_sup_eq] at he'
  exact he'.symm

/-- The collapsed source radical forces the cubic-normalizer congruence
on the original prime-field model. -/
theorem Data.collapsed_small_prime_mod24 (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (hc : (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2) :
    p % 24 = 11 ∨ p % 24 = 13 := by
  obtain ⟨e,_,_,_⟩ := h.swapped_quotient_intersection hn hs hK
  let K := enlargedResidual T L H
  let A := quotientImage K P
  have hpc := hs.toLocalInput.complement_elementary_of_commutative
    (SwappedFactorsProof.complement_commutative hs.toSwappedInput (hK ▸ e))
  let : IsElementaryAbelian 3 P := hpc.1
  let : IsElementaryAbelian 3 (P.subgroupOf K) :=
    IsElementaryAbelian.subgroupOf (hs.toLocalInput.complement_le.trans h.residual_le_enlargedResidual)
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.map (QuotientGroup.mk' (pCore 2 K))
  have hep : Nonempty (P ≃* quotientImage (enlargedResidual T L H) P) :=
    hK.symm ▸ ⟨SwappedSylow.quotientComplementEquiv hs.toSwappedInput⟩
  obtain ⟨ep⟩ := hep
  have hA : A ≠ ⊥ := by
    intro he
    have hh : Nat.card P = Nat.card A := Nat.card_congr ep.toEquiv
    rw [hpc.2,he,card_bot] at hh
    norm_num at hh
  have hr : primeRank 3 (XiQuotient I × XiQuotient I) ≤ 2 := by
    rw [← primeRank_congr 3 e,hK]
    exact (SwappedSylow.orbit_quotient_sqtk hs.toSwappedInput).stronglyQuasithin 3 (by decide) (by decide)
  obtain ⟨S,hS⟩ := h.quotient_sylow
  apply small_pair_cubic_congruence hp ho hm hmod e S A hA hr
  rw [hS,show A = quotientImage K (residual H) from
    (h.quotient_residual_eq_complement_of_core_le hs.toLocalInput hc).symm]
  have hnorm : (T : Subgroup G).subgroupOf K ≤ normalizer ((residual H).subgroupOf K : Set K) := by
    rw [← subgroupOf_normalizer_eq h.residual_le_enlargedResidual]
    exact subgroupOf_mono K hs.invariant
  exact (map_mono hnorm).trans (le_normalizer_map (QuotientGroup.mk' (pCore 2 K)))

/-- Both intersection indices are settled outside the two remaining cubic-normalizer residues. -/
theorem Data.normalizes_residual_of_odd_small_not_mod24 (h : Data D H)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hs : SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G)
      (residual H) P (enlargement T L H) I)
    (hK : enlargedResidual T L H = componentOrbit I (T : Subgroup G))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (XiQuotient I) 2 p)
    (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (h24 : ¬ (p % 24 = 11 ∨ p % 24 = 13)) :
    normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      normalizer (residual H : Set G) := by
  by_cases hR : stabilizerIntersection T L H = (T : Subgroup G) ⊓ enlargedResidual T L H
  · apply h.normalizes_residual_of_odd_small_full_positive hn hs hK hp ho hm hmod hR
    intro hc
    exact h24 (h.collapsed_small_prime_mod24 hn hs hK hp ho hm hmod
      (h.quotient_core_eq_bot_iff.mp hc))
  · exact h.normalizes_residual_of_odd_small_half hn hs hK hp ho hm hmod hR

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction.Parabolics

namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02 Chapter1 Chapter1.XiEmbedding BinaryThreeAction.Parabolics
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The remaining collapsed image must have the cubic-normalizer congruence. -/
def CubicNormalizerEnlargement (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  ∃ (H P I : Subgroup G) (p : ℕ), Data D H ∧
    SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) (residual H) P
      (enlargement T L H) I ∧
    enlargedResidual T L H = componentOrbit I (T : Subgroup G) ∧
    p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient I) 2 p ∧
    (p % 8 = 3 ∨ p % 8 = 5) ∧
    (p % 24 = 11 ∨ p % 24 = 13) ∧
    (enlargement T L H).pCoreIn 2 ≠ ⊥ ∧
    residual H < enlargedResidual T L H ∧
    stabilizerIntersection T L H = (T : Subgroup G) ⊓ enlargedResidual T L H ∧
    (residual H).pCoreIn 2 ≤ (enlargedResidual T L H).pCoreIn 2

/-- All original source guards remain attached to the narrowed obstruction. -/
def SourceCubicNormalizerEnlargement
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard ∧
    D.IsMinimalFullModule ∧ D.fullModule = D.moduleSubgroup ∧
    ¬ (T : Subgroup G) ≤ normalizer (L : Set G) ∧
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) ∧
    Selection.BinaryThreeNatural D ∧ sourceMovedFixed D = ⊥ ∧
    ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) ∧
    CubicNormalizerEnlargement D

/-- The same collapsed configuration supplies the sharper congruence; no
new model, radical or quotient witness is selected. -/
theorem SourceCollapsedSmallOddPrimeEnlargement.to_cubicNormalizer
    {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
    (hc : SourceCollapsedSmallOddPrimeEnlargement D) : SourceCubicNormalizerEnlargement D := by
  obtain ⟨hmany,hmin,hfull,hn,hna,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,hmod,hcore,hlt,hR,hc⟩ := hc
  exact ⟨hmany,hmin,hfull,hn,hna,hmodel,hzero,hJ,H,P,I,p,h,hs,hK,hp,ho,hm,hmod,
    h.collapsed_small_prime_mod24 hn hs hK hp ho hm hmod hc,hcore,hlt,hR,hc⟩

/-- Both requested contracts are reduced to the remaining 11/13 modulo 24
configuration, with the literal half-join consumer and all source guards. -/
theorem sourceContracts_or_cubicNormalizerEnlargement
    (hchoice : Selection.ModuleChoiceAt T) :
    (StabilizerNormalizerAt T ∧ HalfSylowUniqueAt T) ∨
      ∃ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L),
        SourceCubicNormalizerEnlargement D := by
  rcases stabilizerNormalizerAt_or_collapsedSmallOddPrimeEnlargement hchoice with hN | hc
  · exact Or.inl ⟨hN,halfSylowUniqueAt_of_moduleChoice_and_normalizer hchoice hN⟩
  · obtain ⟨L,D,hc⟩ := hc
    exact Or.inr ⟨L,D,hc.to_cubicNormalizer⟩

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
