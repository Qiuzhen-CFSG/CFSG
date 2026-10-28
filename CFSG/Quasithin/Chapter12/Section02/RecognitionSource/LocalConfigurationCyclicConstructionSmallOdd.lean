module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSelectionFrattini
public import CFSG.Quasithin.ChapterA.Section01.PStructure.RankTwo
public import Theory.GroupTheory.PGroup.FixedFrattiniInversion
public import Theory.GroupTheory.OddPrimeRankOneSylow
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Small odd Sylow subgroups before invariant selection

The actual Φ(P) lies in N_G(L), and V lies in O₂(L). Their commutator is
therefore a two-group. Its image in H/O₂(H) also lies in the normal odd core,
so it is trivial. Transporting the chosen involution action through the
original odd-Sylow quotient equivalence gives fixation of Φ(P), alongside
the already proved inversion on P/Φ(P). The fixed-Frattini argument yields
class at most two and exponent p.

H has nontrivial two-core, so quasithin bounds the prime rank of P by two.
The rank-one case is cyclic of order p. The rank-two theorem A.1.24 gives
the elementary plane or the extraspecial group of order p³ and exponent p.
LocalConfigurationCyclicConstructionSmallAssembly applies these alternatives
to the invariant odd-subgroup construction and cyclic-block consumer.

Source: Aschbacher–Smith, construction before 12.2.22, printed pp.802–803,
and A.1.24, p.25. This proves the class condition needed by A.1.24 rather
than inferring it merely from generation by elements of order p.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open Theory.GroupTheory
open ChapterI.Section06To08
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d p : ℕ} {g : G}
namespace CyclicConstructionSeed
variable (S : CyclicConstructionSeed T L V d p H P U g)
include S

omit [Finite G] in
/-- The original component two-core forces the Frattini commutators into
O₂(H), before any small-group classification or invariant Sylow choice. -/
theorem frattini_commutator_le_hstar_core (D : ChosenModule T L V) :
    ⁅(frattini P).map P.subtype, V⁆ ≤ H.pCoreIn 2 := by
  let : Fact p.Prime := ⟨S.prime⟩
  let Φ := (frattini P).map P.subtype
  let C := ⁅Φ, V⁆
  let q := QuotientGroup.mk' (pCore 2 H)
  let R := pCore p (H ⧸ pCore 2 H)
  have hPH : P ≤ H := S.overgroup ▸ le_sup_left
  have hΦH : Φ ≤ H := (map_subtype_le _).trans hPH
  have hVH : V ≤ H := D.le_sylow.trans S.hstar.1.1.2
  have hCH : C ≤ H := (Subgroup.commutator_le_sup _ _).trans (sup_le hΦH hVH)
  have hΦM : Φ ≤ normalizer (L : Set G) := by
    rw [show Φ = P ⊓ normalizer (L : Set G) from S.frattini_intersection]
    exact inf_le_right
  have hΦQ : Φ ≤ normalizer (L.pCoreIn 2 : Set G) :=
    hΦM.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hCQ : C ≤ L.pCoreIn 2 :=
    (commutator_mono le_rfl D.le_componentCore).trans
      (le_normalizer_iff_commutator_le_right.mp hΦQ)
  have htwo : IsPGroup 2 ((C.subgroupOf H).map q) :=
    ((isPGroup_pCoreIn 2 L).to_le hCQ).comap_subtype.map q
  have hCeq : C.subgroupOf H = ⁅Φ.subgroupOf H, V.subgroupOf H⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hCH,
      map_subgroupOf_eq_of_le hΦH, map_subgroupOf_eq_of_le hVH]
  have hCR : (C.subgroupOf H).map q ≤ R := by
    rw [hCeq, map_commutator]
    have hΦR : (Φ.subgroupOf H).map q ≤ R := by
      dsimp only [R]
      rw [← S.quotient_core]
      exact map_mono (subgroupOf_mono H (map_subtype_le _))
    exact (commutator_mono hΦR le_top).trans (commutator_le_left _ _)
  have hbot : (C.subgroupOf H).map q = ⊥ := by
    apply bot_unique
    exact (le_inf le_rfl hCR).trans
      (htwo.disjoint_of_coprime (pCore_isPGroup (p := p)) S.odd_prime.coprime_two_left).le_bot
  have hk : C.subgroupOf H ≤ pCore 2 H := by
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hbot
  have hm := map_mono (f := H.subtype) hk
  rwa [map_subgroupOf_eq_of_le hCH] at hm

/-- The original odd Sylow has class at most two and exponent p. Its
automorphism is transported from conjugation in the literal H/O₂(H). -/
theorem class_two_and_exponent
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V) :
    _root_.commutator P ≤ center P ∧ Monoid.exponent P = p := by
  let : Fact p.Prime := ⟨S.prime⟩
  let hPH : P ≤ H := S.overgroup ▸ le_sup_left
  let hVH : V ≤ H := D.le_sylow.trans S.hstar.1.1.2
  let q := QuotientGroup.mk' (pCore 2 H)
  let R := pCore p (H ⧸ pCore 2 H)
  let e := S.quotientOddEquiv
  obtain ⟨v, hv, hvQ⟩ := SetLike.not_le_iff_exists.mp (A.hstar_movement H S.hstar)
  let vH : H := ⟨v, hVH hv⟩
  let b : MulAut R := R.normalizerMonoidHom ⟨q vH, by rw [R.normalizer_eq_top]; trivial⟩
  let a : MulAut P := e.trans (b.trans e.symm)
  have ha (x : P) :
      q (⟨(a x : G), hPH (a x).property⟩ : H) =
        q vH * q (⟨(x : G), hPH x.property⟩ : H) * (q vH)⁻¹ := by
    have hh : e (a x) = b (e x) := by simp only [a, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    exact congrArg Subtype.val hh
  have hQM : H.pCoreIn 2 ≤ normalizer (L : Set G) := by
    have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := pCoreIn_le_sylow H (T.subtype S.hstar.1.1.2) hx
      exact hy
    exact hQT.trans D.sylow_normalizes_component
  have haPhi (x : P) : a x * x ∈ frattini P := by
    let T' := T.subtype S.hstar.1.1.2
    let hmin := chosen_hstar_intrinsic_minimalParabolic D A S.hstar
    let J := ChapterB.minimalParabolicCore T' hmin
    have hmax : (H ⊓ normalizer (L : Set G)).subgroupOf H =
        ChapterB.minimalParabolicMax T' hmin := by
      obtain ⟨hTB, hBH, _⟩ := Chapter3.HStar.unique_maximal T D.sylow_normalizes_component S.hstar
      have hp := Chapter3.HStar.minimalParabolic T D.sylow_normalizes_component S.hstar
        (Or.inr ((ChapterB.isMinimalParabolicOver_top_iff T').mp hmin).2)
      exact ChapterB.minimalParabolicMax_unique T' hmin
        (ChapterB.intrinsic_minimalParabolic T H (H ⊓ normalizer (L : Set G)) hp hTB hBH).2
        (comap_mono hTB)
    have hJM : J ≤ (normalizer (L : Set G)).comap H.subtype := by
      have hh : J ≤ ChapterB.minimalParabolicMax T' hmin := normalCore_le _
      rw [← hmax] at hh
      exact hh.trans (comap_mono inf_le_right)
    have hTV' : (T' : Subgroup H) ≤ normalizer (V.subgroupOf H : Set H) := by
      intro t ht
      exact V.le_normalizer_comap H.subtype (hTV ht)
    have hi := ChapterB.minimalParabolic_solvable_inverts_star_residual T' hmin
      (A.hstar_solvable H S.hstar) (V.subgroupOf H)
      (subgroupOf_mono H D.le_sylow) hTV'
      (chosen_hstar_quotient_module_card_two D A hTV hTI S.hstar) vH hv
      (fun hv' => hvQ (mem_map_of_mem H.subtype hv'))
    have hPK := odd_prime_subgroup_le_twoResidual S.odd_prime (P.subgroupOf H)
      S.pgroup.comap_subtype
    have hxM : v * (x : G) * v⁻¹ * x ∈ normalizer (L : Set G) :=
      hJM (hi ⟨x, hPH x.property⟩ (hPK x.property))
    have hdiff : (a x : G) * (v * (x : G) * v⁻¹)⁻¹ ∈ H.pCoreIn 2 := by
      refine ⟨(⟨(a x : G), hPH (a x).property⟩ : H) *
        (vH * (⟨(x : G), hPH x.property⟩ : H) * vH⁻¹)⁻¹, ?_, rfl⟩
      apply (QuotientGroup.eq_one_iff _).mp
      change q ((⟨(a x : G), hPH (a x).property⟩ : H) *
        (vH * (⟨(x : G), hPH x.property⟩ : H) * vH⁻¹)⁻¹) = 1
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, ha]
      exact mul_inv_cancel _
    have hprod : ((a x * x : P) : G) ∈ normalizer (L : Set G) := by
      have hm := (normalizer (L : Set G)).mul_mem (hQM hdiff) hxM
      have hid : (a x : G) * (v * (x : G) * v⁻¹)⁻¹ *
          (v * (x : G) * v⁻¹ * x) = (a x : G) * x := by group
      rwa [hid] at hm
    have hp : ((a x * x : P) : G) ∈ (frattini P).map P.subtype :=
      S.frattini_intersection.symm ▸ ⟨(a x * x).property, hprod⟩
    obtain ⟨y, hy, hyx⟩ := hp
    exact (Subtype.ext hyx : y = a x * x) ▸ hy
  have hfix (z : P) (hz : z ∈ frattini P) : a z = z := by
    have hm := S.frattini_commutator_le_hstar_core D
      (commutator_mem_commutator (mem_map_of_mem P.subtype hz) hv)
    have hc : Commute (q (⟨z, hPH z.property⟩ : H)) (q vH) := by
      apply commutatorElement_eq_one_iff_mul_comm.mp
      rw [← map_commutatorElement]
      apply (QuotientGroup.eq_one_iff _).mpr
      obtain ⟨y, hy, he⟩ := hm
      exact (Subtype.ext he : y = ⁅(⟨z, hPH z.property⟩ : H), vH⁆) ▸ hy
    apply e.injective
    apply Subtype.ext
    change q (⟨(a z : G), hPH (a z).property⟩ : H) = q (⟨z, hPH z.property⟩ : H)
    rw [ha, hc.eq.symm, mul_inv_cancel_right]
  have ha2 : Function.Involutive a := by
    let := D.elementary
    have hv2 : vH ^ 2 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian v hv)
    intro x
    apply e.injective
    apply Subtype.ext
    change q (⟨(a (a x) : G), hPH (a (a x)).property⟩ : H) = q (⟨x, hPH x.property⟩ : H)
    rw [ha, ha]
    have hq2 : q vH * q vH = 1 := by rw [← pow_two, ← map_pow, hv2, map_one]
    calc
      q vH * (q vH * q (⟨x, hPH x.property⟩ : H) * (q vH)⁻¹) * (q vH)⁻¹ =
          (q vH * q vH) * q (⟨x, hPH x.property⟩ : H) * (q vH * q vH)⁻¹ := by group
      _ = q (⟨x, hPH x.property⟩ : H) := by rw [hq2]; simp
  obtain ⟨hclass, hexp⟩ := MulAut.class_two_exponent_of_fixed_frattini_inversion
    S.pgroup S.odd_prime a ha2 hfix haPhi
  refine ⟨hclass, ?_⟩
  rcases (Nat.dvd_prime S.prime).mp hexp with he | he
  · let hs : Subsingleton P := Monoid.exp_eq_one_iff.mp he
    have hb : P = ⊥ := Subgroup.eq_bot_of_subsingleton P
    exact (S.escapes (hb ▸ bot_le)).elim
  · exact he

end CyclicConstructionSeed
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open Theory.GroupTheory
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d p : ℕ} {g : G}
namespace CyclicConstructionSeed
variable (S : CyclicConstructionSeed T L V d p H P U g)
include S

/-- The source small odd-group alternatives, with all class, exponent and
rank hypotheses discharged from the original local setting. -/
theorem small_odd_alternatives
    {K : GroupClass} (h : Hypothesis1223 K T L)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V) :
    Nat.card P = p ∨
      (IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
      (IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧ Monoid.exponent P = p) := by
  let : Fact p.Prime := ⟨S.prime⟩
  have hp2 : p ≠ 2 := fun he => S.odd_prime.not_two_dvd_nat (by rw [he])
  have hr : primeRank p P ≤ 2 :=
    (Chapter3.sqtk_of_mem_H h.simpleQTKE S.hstar.1.1.1).stronglyQuasithin.of_injective
      (inclusion (show P ≤ H from S.overgroup ▸ le_sup_left))
      (inclusion_injective _) p S.prime S.odd_prime
  obtain ⟨hclass, hexp⟩ := S.class_two_and_exponent D A hTV hTI
  by_cases htwo : primeRank p P = 2
  · rcases ChapterA.rankTwo_models hp2 S.pgroup hexp htwo hclass with ⟨hc, ⟨e⟩⟩ | ⟨hc, he, _⟩
    · let : IsMulCommutative P := ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
      exact Or.inr (Or.inl ⟨{ exponent_dvd_p := hexp ▸ dvd_refl p }, hc⟩)
    · exact Or.inr (Or.inr ⟨he, hc, hexp⟩)
  · have hone : primeRank p P ≤ 1 := by omega
    let hc : IsCyclic P := S.pgroup.isCyclic_of_odd_of_elementary_card_le S.odd_prime
      (fun E hE => by
        let := hE
        exact IsElementaryAbelian.card_le_prime_of_primeRank_le_one hone E)
    exact Or.inl (hc.exponent_eq_card.symm.trans hexp)

end CyclicConstructionSeed
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
