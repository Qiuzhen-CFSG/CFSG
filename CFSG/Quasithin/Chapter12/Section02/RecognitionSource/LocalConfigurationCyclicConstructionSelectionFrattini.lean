module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSelectionInversion
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSelectionOrbit
public import Theory.GroupTheory.CentralQuotientInversionFixedDerived
public import Theory.Representation.NormalInvariants
import all CFSG.Quasithin.ChapterB.Section06To07.Structure

/-!
# Frattini control before invariant Sylow selection

Identify P with the odd core of H/O₂(H) through the literal quotient map.
The star-quotient inversion then fixes its extraspecial center, giving
[Φ(P),V] ≤ O₂(H). The nonzero subgroup C_U(O₂(H)V) is Φ(P)-invariant
and lies in V. The TI property forces Φ(P) to normalize V. Coprime action
on V now supplies a Φ(P)-fixed element outside O₂(H), hence outside U.

These conclusions precede the choice of an inverter-invariant Sylow. The
last theorem supplies the proved Frattini, inversion and residual clauses
when that choice and the small odd alternatives are available. The actual
source consumer is in LocalConfigurationCyclicConstructionSelectionFrattiniAssembly.
The remaining selection and terminal contradiction stay with
qt-d-12213-cyclic-block; no unconditional source theorem is asserted here.
Source: Aschbacher–Smith, 12.2.21–22, printed pp.802–803.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d p : ℕ} {g : G}
namespace CyclicConstructionSeed
variable (S : CyclicConstructionSeed T L V d p H P U g)
include S

omit [Finite G] in
/-- The original odd Sylow maps isomorphically onto the literal quotient p-core. -/
@[expose] def quotientOddEquiv : P ≃* pCore p (H ⧸ pCore 2 H) := by
  let hPH : P ≤ H := S.overgroup ▸ le_sup_left
  let q := QuotientGroup.mk' (pCore 2 H)
  let f : P →* H := inclusion hPH
  let j := q.comp f
  have hker : Function.Injective j := by
    apply (MonoidHom.ker_eq_bot_iff j).mp
    apply bot_unique
    intro x hx
    apply Subtype.ext
    have hxQ : (x : G) ∈ H.pCoreIn 2 :=
      mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff (f x)).mp hx)
    exact (S.pgroup.disjoint_of_coprime (isPGroup_pCoreIn 2 H)
      S.odd_prime.coprime_two_right).le_bot ⟨x.property, hxQ⟩
  have hj : j.range = pCore p (H ⧸ pCore 2 H) := by
    rw [← S.quotient_core]
    ext x
    exact ⟨fun ⟨y, he⟩ => ⟨f y, y.property, he⟩,
      fun ⟨y, hy, he⟩ => ⟨⟨y, hy⟩, he⟩⟩
  exact (MonoidHom.ofInjective hker).trans (MulEquiv.subgroupCongr hj)

end CyclicConstructionSeed
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H P U : Subgroup G} {d p : ℕ} {g : G}
namespace CyclicConstructionSeed
variable (S : CyclicConstructionSeed T L V d p H P U g)
include S

omit [Finite G] in
/-- The quotient equivalence uses the original inclusion and quotient map. -/
theorem quotientOddEquiv_apply (x : P) :
    (S.quotientOddEquiv x : H ⧸ pCore 2 H) =
      QuotientGroup.mk' (pCore 2 H) ⟨x, (S.overgroup ▸ le_sup_left) x.property⟩ := rfl

/-- In the extraspecial branch V centralizes Φ(P) modulo the original two-core. -/
theorem frattini_commutator_chosen_le_core
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (he : IsExtraspecial p P) :
    ⁅(frattini P).map P.subtype, V⁆ ≤ H.pCoreIn 2 := by
  let : Fact p.Prime := ⟨S.prime⟩
  let : IsExtraspecial p P := he
  let hPH : P ≤ H := S.overgroup ▸ le_sup_left
  let hVH : V ≤ H := D.le_sylow.trans S.hstar.1.1.2
  let q := QuotientGroup.mk' (pCore 2 H)
  let R := pCore p (H ⧸ pCore 2 H)
  let e := S.quotientOddEquiv
  have hQM : H.pCoreIn 2 ≤ normalizer (L : Set G) := by
    have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := pCoreIn_le_sylow H (T.subtype S.hstar.1.1.2) hx
      exact hy
    exact hQT.trans D.sylow_normalizes_component
  apply commutator_le.mpr
  rintro z ⟨z, hz, rfl⟩ v hv
  let vH : H := ⟨v, hVH hv⟩
  let b : MulAut R := R.normalizerMonoidHom ⟨q vH, by rw [R.normalizer_eq_top]; trivial⟩
  let a : MulAut P := e.trans (b.trans e.symm)
  have ha (x : P) :
      q (⟨(a x : G), hPH (a x).property⟩ : H) =
        q vH * q (⟨(x : G), hPH x.property⟩ : H) * (q vH)⁻¹ := by
    have hh : e (a x) = b (e x) := by simp only [a, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have hh' := congrArg Subtype.val hh
    change (e (a x) : H ⧸ pCore 2 H) = q vH * (e x : H ⧸ pCore 2 H) * (q vH)⁻¹ at hh'
    exact hh'
  have finish (hc : Commute (q (⟨(z : G), hPH z.property⟩ : H)) (q vH)) :
      ⁅(z : G), v⁆ ∈ H.pCoreIn 2 := by
    have hh : ⁅(⟨(z : G), hPH z.property⟩ : H), vH⁆ ∈ pCore 2 H := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q _ = 1
      rw [map_commutatorElement]
      exact hc.commutator_eq
    exact mem_map_of_mem H.subtype hh
  by_cases hvQ : vH ∈ pCore 2 H
  · apply finish
    rw [show q vH = 1 from (QuotientGroup.eq_one_iff _).mpr hvQ]
    exact Commute.one_right _
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
        (chosen_hstar_quotient_module_card_two D A hTV hTI S.hstar) vH hv hvQ
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
  have hfix : a z = z := by
    apply (MulAut.mem_fixedSubgroup a z).mp
    apply a.fixes_derived_of_inverts_mod_center
      (IsExtraspecial.commutator_eq_center (p := p) (P := P)).le
      (fun x => by rw [← IsExtraspecial.frattini_eq_center (p := p)]; exact haPhi x)
    rwa [IsExtraspecial.commutator_eq_center (p := p),
      ← IsExtraspecial.frattini_eq_center (p := p)]
  apply finish
  have hh := ha z
  rw [hfix] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm

omit [Finite G] in
/-- The two-core of H normalizes both axes of the original pair. -/
theorem hstar_core_normalizes_pair_core
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    H.pCoreIn 2 ≤ normalizer (U : Set G) := by
  let Q := H.pCoreIn 2
  let B := Q ⊓ V
  have hHQ : H ≤ normalizer (Q : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hQT : Q ≤ (T : Subgroup G) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := pCoreIn_le_sylow H (T.subtype S.hstar.1.1.2) hx
    exact hy
  have hQB : Q ≤ normalizer (B : Set G) :=
    (le_inf Q.le_normalizer (hQT.trans hTV)).trans inf_normalizer_le_normalizer_inf
  have hgH : g ∈ H := (S.overgroup ▸ le_sup_left) S.generator_mem
  have hQg : Q.map (MulAut.conj g).toMonoidHom = Q :=
    mem_normalizer_iff_map_conj_eq.mp (hHQ hgH)
  have hQBg : Q ≤ normalizer (B.map (MulAut.conj g).toMonoidHom : Set G) := by
    rw [← hQg]
    exact (map_mono hQB).trans (B.le_normalizer_map (MulAut.conj g).toMonoidHom)
  have hU : U = B ⊔ B.map (MulAut.conj g).toMonoidHom := by
    rw [S.core_generated, ← S.core_intersection D A]
  rw [hU]
  exact (le_inf hQB hQBg).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- A nonidentity common fixed point in the pair core lies on its original axis. -/
theorem pair_core_common_fixed_ne_bot
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V) :
    U ⊓ centralizer ((H.pCoreIn 2 ⊔ V : Subgroup G) : Set G) ≠ ⊥ := by
  let R := H.pCoreIn 2 ⊔ V
  let W := componentOrbit (H.pCoreIn 2 ⊓ V) H
  let : IsElementaryAbelian 2 W := S.orbit_elementary D hTV hTI
  have hUW : U ≤ W := (le_componentOrbit U P).trans_eq (S.orbit_eq D A hTV).symm
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUW
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hc := S.hyperplane
    rw [hbot, bot_inf_eq, card_bot] at hc
    have hd : 0 < d - 1 := by have := A.dimension.1; omega
    have hh := Nat.one_lt_pow hd.ne' (by decide : 1 < 2)
    omega
  let : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot _).mpr hUne
  have hRU : R ≤ normalizer (U : Set G) := by
    refine sup_le (S.hstar_core_normalizes_pair_core D A hTV) ?_
    rw [← S.pair_core]
    exact (show V ≤ cyclicPairJoin (zpowers g) U V from le_sup_right).trans
      ((cyclicPairJoin (zpowers g) U V).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hR2 : IsPGroup 2 R := by
    have hQT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := pCoreIn_le_sylow H (T.subtype S.hstar.1.1.2) hx
      exact hy
    exact T.isPGroup'.to_le (sup_le hQT D.le_sylow)
  let a : R →* MulAut U := U.normalizerMonoidHom.comp (inclusion hRU)
  let ρ := Representation.elementaryRepresentation (p := 2) a
  obtain ⟨x, hx, hfix⟩ := Representation.pGroup_fix_nonzero_vector
    (by rw [ZMod.ringChar_zmod_n]; decide : ringChar (ZMod 2) ≠ 0)
    (by simpa only [ZMod.ringChar_zmod_n] using hR2) ρ
  intro hbot
  have hm : (x.toMul : G) ∈ U ⊓ centralizer (R : Set G) := by
    refine ⟨x.toMul.property, ?_⟩
    intro r hr
    have hh := congrArg (fun y : Additive U => y.toMul.val) (hfix (⟨r, hr⟩ : R))
    change r * (x.toMul : G) * r⁻¹ = (x.toMul : G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  exact hx (congrArg Additive.ofMul (Subtype.ext (mem_bot.mp (hbot ▸ hm))))

/-- Before invariant Sylow selection, the extraspecial Frattini subgroup
already normalizes the original V. -/
theorem frattini_normalizes_chosen_of_extraspecial
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (he : IsExtraspecial p P) :
    (frattini P).map P.subtype ≤ normalizer (V : Set G) := by
  let Φ := (frattini P).map P.subtype
  let Q := H.pCoreIn 2
  let R := Q ⊔ V
  let C := U ⊓ centralizer (R : Set G)
  have hΦH : Φ ≤ H := (map_subtype_le _).trans (S.overgroup ▸ le_sup_left)
  have hΦQ : Φ ≤ normalizer (Q : Set G) := hΦH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hm : ⁅Φ, V⁆ ≤ Q := S.frattini_commutator_chosen_le_core D A hTV hTI he
  have hΦR : Φ ≤ normalizer (R : Set G) := by
    apply le_normalizer_iff.mpr
    intro z hz x hx
    have hmap : R.map (MulAut.conj z).toMonoidHom ≤ R := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro y ⟨q, hq, rfl⟩
        exact mem_sup_left ((mem_normalizer_iff.mp (hΦQ hz) q).mp hq)
      · rintro y ⟨v, hv, rfl⟩
        have hh := R.mul_mem (mem_sup_left (hm (commutator_mem_commutator hz hv)))
          (mem_sup_right hv)
        change z * v * z⁻¹ ∈ R
        simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
    exact hmap (mem_map_of_mem (MulAut.conj z).toMonoidHom hx)
  have hΦC : Φ ≤ normalizer (C : Set G) :=
    (le_inf (S.frattini_normalizes_core_of_extraspecial D A hTV he)
      (hΦR.trans (normalizer_le_normalizer_centralizer R))).trans
        inf_normalizer_le_normalizer_inf
  have hCV : C ≤ V := by
    apply le_trans ?_ (inf_le_right : U ⊓ V ≤ V)
    rw [← S.action_kernel]
    exact inf_le_inf_left U (centralizer_le (show V ≤ R from le_sup_right))
  have hC : C ≠ ⊥ := S.pair_core_common_fixed_ne_bot D A hTV hTI
  let : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot _).mpr hC
  obtain ⟨c, hc1⟩ := exists_ne (1 : C)
  intro z hz
  exact hTI.mem_normalizer_of_conj_mem (hCV c.property)
    (fun hh => hc1 (Subtype.ext hh))
    (hCV ((mem_normalizer_iff.mp (hΦC hz) c).mp c.property))

/-- Coprime action chooses an involution outside U that centralizes Φ(P),
without assuming invariant Sylow selection or the later fixed-free branch. -/
theorem exists_frattini_fixed_outside_pair_core
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (he : IsExtraspecial p P) :
    ∃ v ∈ V, v ∉ H.pCoreIn 2 ∧ v ∉ U ∧
      v ∈ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) := by
  let Φ := (frattini P).map P.subtype
  let C := V ⊓ centralizer (Φ : Set G)
  let := D.elementary
  let : Fact p.Prime := ⟨S.prime⟩
  have hn := S.frattini_normalizes_chosen_of_extraspecial D A hTV hTI he
  have hc : Nat.Coprime (Nat.card Φ) (Nat.card V) := by
    obtain ⟨a, ha⟩ := (S.pgroup.to_le (map_subtype_le (frattini P))).exists_card_eq
    obtain ⟨b, hb⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    rw [ha, hb]
    exact S.odd_prime.coprime_two_right.pow a b
  have hs : V = ⁅V, Φ⁆ ⊔ C :=
    eq_commutator_sup_centralizer_of_solvable_coprime V Φ hn
      (Group.isSolvable_of_comm fun x y => mul_comm x y) hc
  have hm : ⁅V, Φ⁆ ≤ H.pCoreIn 2 := by
    rw [commutator_comm]
    exact S.frattini_commutator_chosen_le_core D A hTV hTI he
  have hC : ¬ C ≤ H.pCoreIn 2 := by
    intro hle
    exact A.hstar_movement H S.hstar (hs ▸ sup_le hm hle)
  obtain ⟨v, hv, hvQ⟩ := Set.not_subset.mp hC
  exact ⟨v, hv.1, hvQ, fun hvU => hvQ (S.core_in_hstar_core D hvU), hv.2⟩

/-- Every small odd alternative has the Frattini normalization required in
12.2.22; only the extraspecial alternative requires the fixed-subgroup argument. -/
theorem frattini_normalizes_chosen_of_alternatives
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (halt : Nat.card P = p ∨
      (IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
      (IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧ Monoid.exponent P = p)) :
    (frattini P).map P.subtype ≤ normalizer (V : Set G) := by
  let : Fact p.Prime := ⟨S.prime⟩
  let : Fact (IsPGroup p P) := ⟨S.pgroup⟩
  rcases halt with hc | ⟨he, _⟩ | ⟨he, _, _⟩
  · let : IsCyclic P := isCyclic_of_prime_card hc
    let : IsElementaryAbelian p P := {
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
        rw [← hc]; exact pow_card_eq_one' }
    rw [frattini_eq_bot_of_isElementaryAbelian (p := p), Subgroup.map_bot]
    exact bot_le
  · let := he
    rw [frattini_eq_bot_of_isElementaryAbelian (p := p), Subgroup.map_bot]
    exact bot_le
  · exact S.frattini_normalizes_chosen_of_extraspecial D A hTV hTI he

/-- Assemble all invariant-selection fields once the small alternatives and
an invariant inverter have been constructed. Inversion on the Frattini quotient,
Frattini normalization of V and the residual equality are proved here. -/
theorem invariantSelection_of_small_invariant_inverter
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (halt : Nat.card P = p ∨
      (IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
      (IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧ Monoid.exponent P = p))
    (hg : orderOf g = p) {v : G} (hv : v ∈ V) (hvU : v ∉ U)
    (hi : v * g * v⁻¹ = g⁻¹) (hvP : v ∈ normalizer (P : Set G)) :
    CyclicInvariantSelection T L V d p H P U g v := {
  toCyclicConstructionSeed := S
  alternatives := halt
  generator_order := hg
  inverter_mem := hv
  inverter_outside := hvU
  inverts_generator := hi
  inverter_normalizes := hvP
  inverts_frattini_quotient := S.inverts_frattini_quotient_of_normalizes D A hTV hTI hv hvU hvP
  frattini_normalizes := S.frattini_normalizes_chosen_of_alternatives D A hTV hTI halt
  residual := S.residual D A hTV }
end CyclicConstructionSeed
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
