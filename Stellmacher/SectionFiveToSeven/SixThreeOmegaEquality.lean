module
public import Stellmacher.SectionFiveToSeven.SixThreeCrossNormalizers
public import Stellmacher.SectionFiveToSeven.HypothesisTwoSymmetry
public import Stellmacher.SectionFiveToSeven.PFamilyConjugation
public import Stellmacher.BaumannNormalizer
public import Stellmacher.SmallOmegaFixedHyperplane
public import Stellmacher.FourGroupHyperplaneExchange

/-!
# Equality of the Baumann and Sylow omega centers in (6.3)

Suppose the selected local groups E and F have shared Sylow subgroup B(S),
generate P1 and P2 with S, and have a core-free join. Each has fixed index
two on A=Omega_1(Z(B)). Suppose the nontrivial selected module
W1=[A,O^2(E)] lies in B and is normalized by its P1-normal closure L.
Then A equals Omega_1(Z(S)).

The two fixed hyperplanes N1 and N2 have trivial intersection: their
intersection is central in E join F and is a two-subgroup. Their indices
therefore bound the order of A by four. If S normalizes either hyperplane,
its corresponding full group Pi normalizes it, and the small fixed
hyperplane theorem gives the conclusion using Pi's nontrivial action.
Otherwise the two moved hyperplanes are S-conjugate. Choose s with
N2^s=N1. The join E join F^s centralizes nontrivial N1 and has nontrivial
two-core, so the cross-normalizer theorem makes F^s normalize W1.
Also E^s lies in L and normalizes W1. The nontrivial two-subgroup W1 then
lies in the two-core of E^s join F^s, contradicting conjugation covariance
of the original core-free join.

This gives the small-center and conjugate-pair reductions in Stellmacher
(6.3), Journal of Algebra 190 (1997), p.31,
refs/latex/stellmacher-n-group.tex. The moved-hyperplane argument packages
the source's two-factor contradiction without asserting an unproved
factor count. Both alternatives of (5.1) remain explicit at the second
cross-normalizer application, as do the exact selected-module hypotheses.
-/

namespace Stellmacher.SectionsFiveToSeven
universe u

private theorem subgroup_le_core {G : Type*} [Group G]
    (X K : Subgroup G) (hXK : X ≤ K)
    (hN : K ≤ Subgroup.normalizer (X : Set G)) (hXp : IsPGroup 2 X) :
    X ≤ twoCoreIn K := by
  have hn : (X.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr hN
  have hp : IsPGroup 2 (X.subgroupOf K) :=
    hXp.comap_of_injective K.subtype K.subtype_injective
  rw [← Subgroup.map_subgroupOf_eq_of_le hXK]
  exact Subgroup.map_mono (show X.subgroupOf K ≤ pCore 2 K from le_sSup ⟨hn, hp⟩)

public theorem sixThree_omega_eq
    {H : Type u} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (hcomm : ⁅P2, omegaOneCenter S⁆ ≠ ⊥)
    (E F W1 M : Subgroup H)
    (hE : E ∈ PFamily (⊤ : Subgroup H) (baumannIn S))
    (hF : F ∈ PFamily (⊤ : Subgroup H) (baumannIn S))
    (hEL : E ≤ sectionSixL (baumannIn S) P1)
    (hgenE : E ⊔ S = P1) (hgenF : F ⊔ S = P2)
    (hW1 : W1 = ⁅omegaOneCenter (baumannIn S), twoResidualIn E⁆)
    (hW1ne : W1 ≠ ⊥) (hW1B : W1 ≤ baumannIn S)
    (hLW1 : sectionSixL (baumannIn S) P1 ≤ Subgroup.normalizer (W1 : Set H))
    (hM : IsMaximalTwoLocalContaining (S0 : Subgroup H) M)
    (hcore : twoCoreIn (E ⊔ F) = ⊥)
    (hidxE : (omegaOneCenter (baumannIn S) ⊓ Subgroup.centralizer (E : Set H)).relIndex
      (omegaOneCenter (baumannIn S)) = 2)
    (hidxF : (omegaOneCenter (baumannIn S) ⊓ Subgroup.centralizer (F : Set H)).relIndex
      (omegaOneCenter (baumannIn S)) = 2) :
    omegaOneCenter (baumannIn S) = omegaOneCenter S := by
  classical
  let B := baumannIn S
  let A := omegaOneCenter B
  let N1 := A ⊓ Subgroup.centralizer (E : Set H)
  let N2 := A ⊓ Subgroup.centralizer (F : Set H)
  let L := sectionSixL B P1
  let _ : IsElementaryAbelian 2 A := omegaOneCenterAmbient_elementaryAbelian B
  have hAB : A ≤ B := Subgroup.map_subtype_le _
  have hBS : B ≤ S := inf_le_left
  have hAS : A ≤ S := hAB.trans hBS
  have hSp : IsPGroup 2 S := S0.isPGroup'.to_le h.fiveOne.S_le_S0
  have hAp : IsPGroup 2 A := hSp.to_le hAS
  have hBE : B ≤ E := hE.1.2.1.1
  have hSP1 : S ≤ P1 := by rw [← hgenE]; exact le_sup_right
  have hSP2 : S ≤ P2 := by rw [← hgenF]; exact le_sup_right
  have hSB : S ≤ Subgroup.normalizer (B : Set H) :=
    S.le_normalizer.trans (normalizer_le_normalizer_baumann S)
  have hSA : S ≤ Subgroup.normalizer (A : Set H) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hBm : B.map (MulAut.conj s).toMonoidHom = B :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hSB hs)
    change (omegaOneCenterAmbient B).map (MulAut.conj s).toMonoidHom = omegaOneCenterAmbient B
    rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj s).injective, hBm]
  have hOmega : omegaOneCenterAmbient S ≤ A := by
    intro x hx
    obtain ⟨hxS, hx2, hxc⟩ := (mem_omegaOneCenterAmbient_iff S x).mp hx
    have hxB : x ∈ B := by
      refine ⟨hxS, Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro z hz
      have hJS : elementaryAbelianMaxJ S ≤ S := sSup_le fun _ hJ => hJ.1
      exact hxc z (hJS (Subgroup.map_subtype_le _ hz))
    exact (mem_omegaOneCenterAmbient_iff B x).mpr ⟨hxB, hx2, fun b hb => hxc b (hBS hb)⟩
  have hEN1 : E ≤ Subgroup.centralizer (N1 : Set H) :=
    Subgroup.le_centralizer_iff.mp (show N1 ≤ Subgroup.centralizer (E : Set H) from inf_le_right)
  have hFN2 : F ≤ Subgroup.centralizer (N2 : Set H) :=
    Subgroup.le_centralizer_iff.mp (show N2 ≤ Subgroup.centralizer (F : Set H) from inf_le_right)
  have hNinf : N1 ⊓ N2 = ⊥ := by
    have hDcent : E ⊔ F ≤ Subgroup.centralizer (N1 ⊓ N2 : Set H) :=
      sup_le (hEN1.trans (Subgroup.centralizer_le inf_le_left))
        (hFN2.trans (Subgroup.centralizer_le inf_le_right))
    have hDcore := subgroup_le_core (N1 ⊓ N2) (E ⊔ F)
      (inf_le_left.trans (inf_le_left.trans (hAB.trans (hBE.trans le_sup_left))))
      (hDcent.trans (Subgroup.centralizer_le_normalizer _))
      (hAp.to_le (inf_le_left.trans inf_le_left))
    exact le_bot_iff.mp (hDcore.trans_eq hcore)
  have hcard : Nat.card A ≤ 4 := by
    have hidx1 : N1.relIndex A = 2 := hidxE
    have hidx2 : N2.relIndex A = 2 := hidxF
    have hi : (N1 ⊓ N2).relIndex A ≤ N1.relIndex A * N2.relIndex A :=
      Subgroup.relIndex_inf_le
    simpa only [hNinf, Subgroup.relIndex_bot_left, hidx1, hidx2] using hi
  have hsmall (P K N : Subgroup H) (hSP : S ≤ P) (hgen : K ⊔ S = P)
      (hNA : N ≤ A) (hKN : K ≤ Subgroup.centralizer (N : Set H))
      (hidx : N.relIndex A = 2) (hact : ⁅P, omegaOneCenterAmbient S⁆ ≠ ⊥)
      (hSN : S ≤ Subgroup.normalizer (N : Set H)) : A = omegaOneCenter S := by
    apply omega_eq_of_small_normal_fixed_hyperplane S P A N hSP hAS hSA hOmega hcard hNA
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hNA.trans (hAS.trans hSP))).mpr ?_) hidx hact
    rw [← hgen]
    exact sup_le (hKN.trans (Subgroup.centralizer_le_normalizer _)) hSN
  by_cases hSN1 : S ≤ Subgroup.normalizer (N1 : Set H)
  · exact hsmall P1 E N1 hSP1 hgenE inf_le_left hEN1 hidxE
      (h.left_commutator_ne_bot S0 S P1 P2 hcomm) hSN1
  by_cases hSN2 : S ≤ Subgroup.normalizer (N2 : Set H)
  · exact hsmall P2 F N2 hSP2 hgenF inf_le_left hFN2 hidxF hcomm hSN2
  obtain ⟨s, hs, hNmap⟩ := two_moved_hyperplanes_conjugate S A N1 N2 hSp hAS hSA
    hcard inf_le_left inf_le_left hidxE hidxF hNinf hSN1 hSN2
  have hNne : N1 ≠ ⊥ := by
    intro hn
    apply hSN1
    rw [hn, Subgroup.normalizer_eq_top]
    exact le_top
  have hFsfamily : conjugateBy F s ∈ PFamily (⊤ : Subgroup H) B :=
    (conjugateBy_mem_pFamily_iff B F s (hSB hs)).mpr hF
  have hFsN1 : conjugateBy F s ≤ Subgroup.centralizer (N1 : Set H) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [← hNmap]
    change ⁅F.map (MulAut.conj s).toMonoidHom, N2.map (MulAut.conj s).toMonoidHom⁆ = ⊥
    rw [← Subgroup.map_commutator, Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hFN2,
      Subgroup.map_bot]
  have hcore' : twoCoreIn (E ⊔ conjugateBy F s) ≠ ⊥ := by
    have hc := subgroup_le_core N1 (E ⊔ conjugateBy F s)
      (inf_le_left.trans (hAB.trans (hBE.trans le_sup_left)))
      ((sup_le hEN1 hFsN1).trans (Subgroup.centralizer_le_normalizer _))
      (hAp.to_le inf_le_left)
    exact fun hb => hNne (le_bot_iff.mp (hc.trans_eq hb))
  have halt : S = (S0 : Subgroup H) ∨ ¬ (E ⊔ conjugateBy F s) ≤ M := by
    cases h.fiveOne.alternative with
    | a hS _ _ => exact Or.inl hS
    | b hS _ => exact Or.inl hS
    | c M' hM' _ _ _ _ _ hP1 _ _ _ _ _ =>
      right
      have hMM' : M = M' := hM'.2 M hM
      subst M'
      intro hjoin
      apply hP1
      rw [← hgenE]
      exact sup_le (le_sup_left.trans hjoin) (h.fiveOne.S_le_S0.trans hM.2)
  have hFsW : conjugateBy F s ≤ Subgroup.normalizer (W1 : Set H) := by
    rw [hW1]
    exact (sixThree_cross_normalizers S0 S P1 P2 h E (conjugateBy F s) M
      hE hFsfamily hM hcore' halt).1
  have hP1L : P1 ≤ Subgroup.normalizer (L : Set H) := by
    rw [show L = conjugateClosure B P1 from rfl, conjugateClosure,
      Subgroup.le_normalizer_closure_iff]
    intro p hp x hx
    obtain ⟨q, b, rfl⟩ := hx
    apply Subgroup.subset_closure
    refine ⟨⟨p * (q : H), P1.mul_mem hp q.property⟩, b, ?_⟩
    change p * ((q : H) * (b : H) * (q : H)⁻¹) * p⁻¹ =
      (p * (q : H)) * (b : H) * (p * (q : H))⁻¹
    group
  have hEsW : conjugateBy E s ≤ Subgroup.normalizer (W1 : Set H) := by
    have hm := Subgroup.map_mono (f := (MulAut.conj s).toMonoidHom) hEL
    have hLm : L.map (MulAut.conj s).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hP1L (hSP1 hs))
    change conjugateBy E s ≤ L.map (MulAut.conj s).toMonoidHom at hm
    rw [hLm] at hm
    exact hm.trans hLW1
  have hEsfamily : conjugateBy E s ∈ PFamily (⊤ : Subgroup H) B :=
    (conjugateBy_mem_pFamily_iff B E s (hSB hs)).mpr hE
  have hconjCore : twoCoreIn (conjugateBy E s ⊔ conjugateBy F s) ≠ ⊥ := by
    have hc := subgroup_le_core W1 (conjugateBy E s ⊔ conjugateBy F s)
      (hW1B.trans (hEsfamily.1.2.1.1.trans le_sup_left)) (sup_le hEsW hFsW)
      (hSp.to_le (hW1B.trans hBS))
    exact fun hb => hW1ne (le_bot_iff.mp (hc.trans_eq hb))
  apply (hconjCore ?_).elim
  let J := E ⊔ F
  let eJ : J ≃* J.map (MulAut.conj s).toMonoidHom :=
    J.equivMapOfInjective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective
  have hmapcore := pCore_map_iso 2 eJ
  have hco : twoCoreIn (J.map (MulAut.conj s).toMonoidHom) =
      (twoCoreIn J).map (MulAut.conj s).toMonoidHom := by
    unfold twoCoreIn
    rw [← hmapcore, Subgroup.map_map, Subgroup.map_map]
    rfl
  change twoCoreIn ((E.map (MulAut.conj s).toMonoidHom) ⊔
    (F.map (MulAut.conj s).toMonoidHom)) = ⊥
  rw [← Subgroup.map_sup]
  change twoCoreIn (J.map (MulAut.conj s).toMonoidHom) = ⊥
  rw [hco, hcore, Subgroup.map_bot]

end Stellmacher.SectionsFiveToSeven

