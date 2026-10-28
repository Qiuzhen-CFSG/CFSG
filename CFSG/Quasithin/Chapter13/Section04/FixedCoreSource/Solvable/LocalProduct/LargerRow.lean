module
public import Theory.GroupTheory.CubicResidualSelection.ActorRank
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.LargerSelection
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.CoveredResidual

/-!
# The covered-row exclusion with the larger action kernel

Write H=C_G(z), U=⟨Ω₁(Z(T))^H⟩ and K=C_H(U). Since K is larger
than O₂(H), its embedded two-residual is nontrivial. The fixed-line
centralizer bound puts K inside M=N_G(L). Earlier 13.3.9 consequently
identifies O²(K) with its actual selected residual and gives its cubic
core quotient; neither fact is a new local premise.

The original R₁ is Sylow in C_H(O²(K)/O₂(O²(K))) by earlier 13.4.4(ii).
In the Baumann-bound branch this constructs the noncentral Thompson action.
The normal S₃ image in H/O₂(H) has a residual-intersection lift inside L₁.
Earlier 13.3.9 puts that lift in K, where the kernel-intersection theorem
kills it. Thus m₃(L₁)≤1, and the five-dimensional marking excludes the
covered A₆ row. The final consumer recovers the literal O²(K)=L₁ identity
and applies the checked pair quotient, moved-plane, local-product and
IT-uniqueness theorems. No ordinary-row assumption is retained.

The explicit 13.3.9 input retains its original row-dependent residual and
the order-three consequence proved on printed p.887. Its discharge, the
original 13.4.4(ii) Sylow placement and earlier Chapter12/13.3 inputs belong
to qt-d-1341-fixed-core-source and its existing earlier producers. The
short-block noncentrality case, original R₁ identification, C₃ geometry
and ambient fusion remain with qt-d-1341-solvable-source. This is a checked
larger-kernel branch, not full source 13.4.8–9.
Source: Aschbacher–Smith 13.3.9, p.887, and 13.4.8, pp.904–905.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The non-two-group kernel and the earlier 13.3.9 conclusion construct
its nontrivial cubic residual, with the literal ambient embedding. -/
theorem centralizer_kernel_residual_of_source1339
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hlarge : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) ≠
      pCore 2 (centralizer ({z.val} : Set G)))
    (Aplus : Subgroup G)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = Aplus ∧ Nat.card (Y ⧸ pCore 2 Y) = 3)) :
    let H := centralizer ({z.val} : Set G)
    let K := centralizer ((centralizerOmegaOrbit T z.val).subgroupOf H : Set H)
    let A := (pResidual 2 K).map K.subtype
    A.map H.subtype = Aplus ∧ Nat.card (A ⧸ pCore 2 A) = 3 := by
  let H := centralizer ({z.val} : Set G)
  let U := (centralizerOmegaOrbit T z.val).subgroupOf H
  have hU := centralizerOmegaOrbit_reduced h₀ hz (fun he => hzL (he ▸ one_mem _))
  let := hU.normal
  let K := centralizer (U : Set H)
  let A := (pResidual 2 K).map K.subtype
  let Z := A.map H.subtype
  have hQK : pCore 2 H ≤ K := le_centralizer_iff.mp hU.le_centralizer_pCore
  have hAK : A ≤ K := map_subtype_le _
  have hZM : Z ≤ normalizer (L : Set G) := by
    apply le_trans _ (centralizerOmegaOrbit_centralizer_le_normalizer h structural D m z.val)
    rintro x ⟨a,ha,rfl⟩ v hv
    exact congrArg Subtype.val ((hAK ha) ⟨v,centralizerOmegaOrbit_le hz hv⟩ hv)
  have hZn : H ≤ normalizer (Z : Set G) := by
    have hh := A.le_normalizer_map H.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
  have hp : IsPPerfect 2 Z := (isPPerfect_embedded_pResidual 2 K).of_surjective
    (H.subtype.subgroupMap A) (H.subtype.subgroupMap_surjective A)
  have hne : Z ≠ ⊥ := by
    intro he
    have hA : A = ⊥ := (map_eq_bot_iff_of_injective _ H.subtype_injective).mp he
    have hres : pResidual 2 K = ⊥ :=
      (map_eq_bot_iff_of_injective _ K.subtype_injective).mp hA
    have hpK : IsPGroup 2 K := (isPGroup_quotient_pResidual 2).of_equiv
      ((QuotientGroup.quotientMulEquivOfEq hres).trans QuotientGroup.quotientBot)
    exact hlarge (le_antisymm (le_sSup ⟨inferInstance,hpK⟩) hQK)
  obtain ⟨he,hc⟩ := (h1339 Z (map_subtype_le _) hZn hZM hp).resolve_left hne
  refine ⟨he,?_⟩
  let e := A.equivMapOfInjective H.subtype H.subtype_injective
  exact (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).trans hc

/-- The residual-intersection lift in H/O₂(H) bounds the original L₁'s
three-rank even when the kernel of the action on V_H is larger. -/
theorem centralizer_firstResidual_threeRank_of_larger_source1339
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hlarge : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) ≠
      pCore 2 (centralizer ({z.val} : Set G)))
    (Aplus : Subgroup G)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = Aplus ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (R : Subgroup G) (hRT : R ≤ T)
    (S : Sylow 2 (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
        (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))))))
    (hR : ((S : Subgroup _).map (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
        (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))))).subtype).map
          (centralizer ({z.val} : Set G)).subtype = R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ centralizer (centralizerOmegaOrbit T z.val : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G))) :
    primeRank 3 (firstCentralizerResidual L z.val) ≤ 1 := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  let H := centralizer ({z.val} : Set G)
  let U := (centralizerOmegaOrbit T z.val).subgroupOf H
  have hU := centralizerOmegaOrbit_reduced h₀ hz hz1
  let := hU.normal
  let K := centralizer (U : Set H)
  let A := (pResidual 2 K).map K.subtype
  let C := residualSectionCentralizer 2 K
  let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
  let N := I.subgroupOf H
  let B := (firstCentralizerResidual L z.val).subgroupOf H
  have hTH : (T : Subgroup G) ≤ H := original_sylow_le_centralizer hz
  have hIH : I ≤ H := conjugateSpanBy_le_self
    ((sSup_le fun _ hA => hA.1).trans (hRT.trans hTH))
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hIH).mpr
    (le_normalizer_conjugateSpanBy _ _)
  let : A.Normal := inferInstance
  let : (A.pCoreIn 2).Normal := inferInstanceAs ((pCore 2 A).map A.subtype).Normal
  obtain ⟨hc,_,hIC,_⟩ := centralizer_larger_kernel_local_data h₀ hz hz1 R hRT S hR
  have hQR := hc.symm.le.trans inf_le_left
  have hnC : N ≤ C := by
    intro x hx
    exact (mem_map_iff_mem H.subtype_injective).mp (hIC hx)
  have hcomm : ⁅N,A⁆ ≤ A.pCoreIn 2 :=
    (commutator_mono hnC le_rfl).trans
      (commutator_commutatorPreimage_le ⊤ A (A.pCoreIn 2) le_normalizer_of_normal)
  let eN : N ≃* I := subgroupOfEquivOfLe hIH
  have hpJ : IsPGroup 2 (elementaryAbelianMaxJ R) :=
    (T.isPGroup'.to_le hRT).to_le (sSup_le fun _ hA => hA.1)
  obtain ⟨n,hn⟩ := hpJ.exists_card_eq
  have hperf : IsPPerfect 3 I := isPPerfect_conjugateSpanBy_of_coprime _ _
    (by rw [hn]; exact (by decide : Nat.Coprime 3 2).pow_right n)
  have hperfN := hperf.of_surjective eN.symm.toMonoidHom eN.symm.surjective
  obtain ⟨hAplus,hcard⟩ := centralizer_kernel_residual_of_source1339 h₀ h structural
    D m z hz hzL hlarge Aplus h1339
  have hQK : pCore 2 H ≤ K := le_centralizer_iff.mp hU.le_centralizer_pCore
  have hm := centralizer_thompson_span_models h₀ hz hz1 R hRT hQR hJ hsolv
  have hrank : primeRank 3 H ≤ 2 :=
    (isQuasithin_iff_twoLocal.mp h₀.qtke.quasithin) H
      (isTwoLocal_involution_centralizer
        (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1 hz1))
      3 (by decide) (by decide)
  have hBH : firstCentralizerResidual L z.val ≤ H :=
    (firstCentralizerResidual_le L z.val).trans inf_le_right
  have hSB : (T.subtype hTH : Subgroup H) ≤ normalizer (B : Set H) := by
    rw [← subgroupOf_normalizer_eq hBH]
    exact subgroupOf_mono H (firstCentralizerResidual_sylow_normalizes D hz)
  let eB : B ≃* firstCentralizerResidual L z.val := subgroupOfEquivOfLe hBH
  have hBperf : IsPPerfect 2 B := (firstCentralizerResidual_twoPerfect L z.val).of_surjective
    eB.symm.toMonoidHom eB.symm.surjective
  let := h.quasisimple
  obtain ⟨ho,hthree⟩ := firstCentralizerResidual_order_of_marking D m z hzL
  have hoB : ∃ a b : ℕ, Nat.card B ∣ 2 ^ a * 3 ^ b := by
    rwa [Nat.card_congr eB.toEquiv]
  have hthreeB : 3 ∣ Nat.card B := by rwa [Nat.card_congr eB.toEquiv]
  have hclass : ∀ Y : Subgroup H, Y.Normal → IsPPerfect 2 Y → Y ≤ B → Y ≤ K := by
    intro Y hYn hYp hYB
    let := hYn
    let Z := Y.map H.subtype
    have hZB : Z ≤ firstCentralizerResidual L z.val := by
      have hh := map_mono (f := H.subtype) hYB
      rwa [map_subgroupOf_eq_of_le hBH] at hh
    have hZn : H ≤ normalizer (Z : Set G) := by
      have hh := Y.le_normalizer_map H.subtype
      simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
    have hZp : IsPPerfect 2 Z := hYp.of_surjective
      (H.subtype.subgroupMap Y) (H.subtype.subgroupMap_surjective Y)
    have hZM : Z ≤ normalizer (L : Set G) :=
      hZB.trans ((firstCentralizerResidual_le L z.val).trans (inf_le_left.trans L.le_normalizer))
    rcases h1339 Z (map_subtype_le _) hZn hZM hZp with he | ⟨he,_⟩
    · have hY : Y = ⊥ := (map_eq_bot_iff_of_injective _ H.subtype_injective).mp he
      rw [hY]; exact bot_le
    · apply le_trans _ (map_subtype_le (pResidual 2 K))
      exact (map_le_map_iff_of_injective H.subtype_injective).mp (by
        change Z ≤ A.map H.subtype
        rw [hAplus,he])
  have hr := CubicResidualSelection.actor_rank_le_one K N B hQK hcard hperfN hcomm hm hrank
    (T.subtype hTH) hSB hBperf hoB hthreeB hclass
  rwa [primeRank_congr 3 eB] at hr

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open scoped Pointwise
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual residual selected by earlier 13.3.9: L₁ in the ordinary row,
and the literal L₁,+ of Notation 13.2.1 in the covered row. -/
@[expose] noncomputable def selectedFirstResidual
    (T : Sylow 2 G) (L V : Subgroup G) (z : G) : Subgroup G := by
  classical
  exact if Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) then
    firstCentralizerResidual L z else
    plus L (T : Subgroup G) (V ⊓ omegaOneCenterAmbient (T : Subgroup G))

/-- The larger action-kernel branch selects the ordinary row and constructs
its literal pair quotient, product and unique outside parabolic. The cubic
section and its residual identity are consequences of the earlier 13.3.9
input, rather than additional local hypotheses. -/
theorem centralizer_pair_quotient_of_larger_source1339
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hlarge : centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
      (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))) ≠
      pCore 2 (centralizer ({z.val} : Set G)))
    (R : Subgroup G) (hRT : R ≤ T)
    (S : Sylow 2 (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
        (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))))))
    (hR : ((S : Subgroup _).map (residualSectionCentralizer 2
      (centralizer ((centralizerOmegaOrbit T z.val).subgroupOf
        (centralizer ({z.val} : Set G)) : Set (centralizer ({z.val} : Set G))))).subtype).map
          (centralizer ({z.val} : Set G)).subtype = R)
    (hB : normalizer (ChapterB.baumann R : Set G) ≤ normalizer (L : Set G))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
        (normalizer (L : Set G)).subtype = L) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ R) H
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      Nonempty ((I ⧸ pCore 2 I) ≃* Equiv.Perm (Fin 3)) ∧
      Representation.BinaryOffender.rank (⁅centralizerOmegaOrbit T z.val,I⁆ : Subgroup G) = 2 ∧
      H = firstCentralizerResidual L z.val ⊔ I ⊔ (T : Subgroup G) ∧
      H ⊓ normalizer (L : Set G) = firstCentralizerResidual L z.val ⊔ (T : Subgroup G) ∧
      (H : Set G) = (firstCentralizerResidual L z.val : Set G) * (I : Set G) * (T : Set G) ∧
      I ⊔ (T : Subgroup G) ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ∀ Y : Subgroup G, Y ≤ H →
        (Y ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ↔
          Y = I ⊔ (T : Subgroup G)) := by
  classical
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨hc,_,_,_⟩ := centralizer_larger_kernel_local_data h₀ hz hz1 R hRT S hR
  have hJ := centralizer_thompson_noncentral_of_baumann_bound h₀ hz hz1 R hRT hc hB hout
  have hr := centralizer_firstResidual_threeRank_of_larger_source1339 h₀ h structural
    D m z hz hzL hlarge (selectedFirstResidual T L V z.val) h1339 R hRT S hR hJ hsolv
  let := h.quasisimple
  have ordinary := ordinary_of_firstCentralizerResidual_threeRank D m z hzL hr
  have hsel : selectedFirstResidual T L V z.val = firstCentralizerResidual L z.val := by
    simp only [selectedFirstResidual,if_pos ordinary]
  have hres := (centralizer_kernel_residual_of_source1339 h₀ h structural D m z hz hzL
    hlarge (selectedFirstResidual T L V z.val) h1339).1.trans hsel
  refine ⟨ordinary,centralizer_pair_quotient_of_ordinary_larger_kernel h₀ h structural D m
    ordinary z hz hzL R hRT S hR hres hB hsolv hout hindex ?_ (h1342 ordinary)⟩
  intro Y hYH hn hYM hp
  exact (h1339 Y hYH hn hYM hp).imp_right (fun hh => hh.2)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
