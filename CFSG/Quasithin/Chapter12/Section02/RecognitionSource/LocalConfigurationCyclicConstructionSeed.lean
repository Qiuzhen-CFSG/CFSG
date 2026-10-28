module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSeedInverter
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.InvertedCore
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionDefs

/-!
# Constructing the literal cyclic-pair seed

Choose an inverted odd-prime rotation in the original moving H-star subgroup,
and then a Sylow subgroup containing it. The solvable parabolic structure
identifies its prime and gives the exact Frattini intersection and product
H = PT. The inverted-pair theorem identifies the literal pair two-core,
its two conjugate axes, commutators, fixed points and action kernel.
The natural marking converts the index-two axis into its required order.

This proves the complete initial CyclicConstructionSeed. The stronger
existence theorem retains the prime-order rotation and its actual inverter.
Invariant Sylow selection and the noncyclic exclusion remain with
qt-d-12213-cyclic-block; LocalConfigurationCyclicConstructionSource applies
this seed to that task's existing invariant-selection and cyclic consumers.
Source: Aschbacher–Smith, the construction after 12.2.21, pp.802–803.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V H : Subgroup G} {d : ℕ}

private theorem odd_supplement_of_sylow (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hr : pResidual 2 (H ⧸ pCore 2 H) = pCore p (H ⧸ pCore 2 H))
    (hPhi : ChapterB.minimalParabolicCoreImage (T.subtype hH.1.1.2)
      (chosen_hstar_intrinsic_minimalParabolic D A hH) =
      Stellmacher.frattiniAmbient (pCore p (H ⧸ pCore 2 H)))
    (R : Sylow p H) :
    CyclicOddSupplement T L p H ((R : Subgroup H).map H.subtype) := by
  let S := T.subtype hH.1.1.2
  have hmin := chosen_hstar_intrinsic_minimalParabolic D A hH
  have hq := (pResidual_le_iff_isPGroup_quotient 2 _).mp hr.le
  let P : Subgroup G := (R : Subgroup H).map H.subtype
  have hPH : P ≤ H := map_subtype_le _
  have hsub : P.subgroupOf H = (R : Subgroup H) := by
    change ((R : Subgroup H).map H.subtype).comap H.subtype = _
    rw [comap_map_eq, H.subtype.ker_eq_bot H.subtype_injective, sup_bot_eq]
  have hfac : ∀ x ∈ H, ∃ a ∈ P, ∃ t ∈ (T : Subgroup G), x = a * t := by
    intro x hx
    obtain ⟨a, ha, t, ht, he⟩ := odd_sylow_two_sylow_factorization ho hr R S ⟨x, hx⟩
    exact ⟨a, mem_map_of_mem H.subtype ha, t, ht, congrArg Subtype.val he⟩
  have hgen : H = P ⊔ (T : Subgroup G) := by
    apply le_antisymm
    · intro x hx
      obtain ⟨a, ha, t, ht, rfl⟩ := hfac x hx
      exact (P ⊔ (T : Subgroup G)).mul_mem (mem_sup_left ha) (mem_sup_right ht)
    · exact sup_le hPH hH.1.1.2
  have hmax : (H ⊓ normalizer (L : Set G)).subgroupOf H =
      ChapterB.minimalParabolicMax S hmin := by
    obtain ⟨hTB, hBH, _⟩ := Chapter3.HStar.unique_maximal T D.sylow_normalizes_component hH
    have hp := Chapter3.HStar.minimalParabolic T D.sylow_normalizes_component hH
      (Or.inr ((ChapterB.isMinimalParabolicOver_top_iff S).mp hmin).2)
    exact ChapterB.minimalParabolicMax_unique S hmin
      (ChapterB.intrinsic_minimalParabolic T H (H ⊓ normalizer (L : Set G)) hp hTB hBH).2
      (comap_mono hTB)
  have hphi := ChapterB.minimalParabolic_odd_sylow_frattini_intersection S hmin
    (A.hstar_solvable H hH) ho hr hPhi R
  have hphiG : (frattini P).map P.subtype = P ⊓ normalizer (L : Set G) := by
    rw [frattini_image_map (R : Subgroup H) H.subtype H.subtype_injective, hphi,
      map_inf _ _ H.subtype H.subtype_injective, ← hmax,
      map_subgroupOf_eq_of_le inf_le_left]
    change P ⊓ (H ⊓ normalizer (L : Set G)) = _
    rw [← inf_assoc, inf_eq_left.mpr hPH]
  refine ⟨hH, Fact.out, ho, R.isPGroup'.map H.subtype, ⟨R, rfl⟩, ?_, hgen,
    hfac, ?_, hq, hphiG⟩
  · intro hn
    apply hH.1.2
    rw [hgen]
    exact sup_le hn D.sylow_normalizes_component
  · rw [hsub]
    exact sylow_map_twoCoreQuotient_eq_odd_core ho hr R

/-- The odd supplement can be chosen to contain any specified element of odd
prime order in the original H-star subgroup. -/
theorem chosen_hstar_exists_odd_supplement_containing (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {r : ℕ} (hr : r.Prime) (hro : Odd r) (g : G) (hgH : g ∈ H)
    (hgr : orderOf g = r) :
    ∃ P, CyclicOddSupplement T L r H P ∧ g ∈ P := by
  have hmin := chosen_hstar_intrinsic_minimalParabolic D A hH
  obtain ⟨p, hp, ho, hres, _, hPhi, _⟩ := ChapterB.minimalParabolic_solvable_structure
    (T.subtype hH.1.1.2) hmin (A.hstar_solvable H hH)
  let : Fact p.Prime := ⟨hp⟩
  let a : H := ⟨g, hgH⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  have har : orderOf a = r := (Subgroup.orderOf_coe a).symm.trans hgr
  have hqa : q a ≠ 1 := by
    intro he
    have hm := (QuotientGroup.eq_one_iff a).mp he
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := H)) ⟨a, hm⟩
    have hd : r ∣ 2 ^ n := har ▸ orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hn)
    have he : r = 2 := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd)
    exact hro.not_two_dvd_nat (by rw [he])
  have haR : q a ∈ pCore p (H ⧸ pCore 2 H) := by
    rw [← hres]
    exact mem_pResidual_of_orderOf_coprime
      (Nat.coprime_two_left.mpr ((har.symm ▸ hro).of_dvd_nat (orderOf_map_dvd q a)))
  have hpr : p = r := by
    have hd := (pCore_isPGroup (p := p) (G := H ⧸ pCore 2 H)).dvd_orderOf
      (g := ⟨q a, haR⟩) (fun he => hqa (congrArg Subtype.val he))
    rw [← Subgroup.orderOf_coe] at hd
    exact (Nat.prime_dvd_prime_iff_eq hp hr).mp
      (hd.trans (har ▸ orderOf_map_dvd q a))
  rw [← hpr] at har ⊢
  have hz : IsPGroup p (zpowers a) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, har, pow_one])
  obtain ⟨R, hR⟩ := hz.exists_le_sylow
  refine ⟨(R : Subgroup H).map H.subtype,
    odd_supplement_of_sylow D A hH ho hres hPhi R, ?_⟩
  exact mem_map_of_mem H.subtype (hR (mem_zpowers a))


/-- Construct all the literal pair-core fields, using the selected inverted
prime conjugator. This is stronger than the initial seed's order-free contract. -/
theorem chosen_hstar_exists_cyclicConstructionSeed
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ p P U g v, CyclicConstructionSeed T L V d p H P U g ∧
      orderOf g = p ∧ v ∈ V ∧ v ∉ H.pCoreIn 2 ∧
      v ∉ U ∧ v * g * v⁻¹ = g⁻¹ := by
  let := D.elementary
  obtain ⟨p, g, v, hp, ho, hgK, hv, hvQ, hg, hinv, hgen, hd, hi⟩ :=
    chosen_hstar_exists_inverted_prime_hyperplane_pair D A hT hTI hH
  have hgH : g ∈ H := map_subtype_le _ hgK
  obtain ⟨P, S, hgP⟩ := chosen_hstar_exists_odd_supplement_containing D A hH hp ho g hgH hg
  let B := V.map (MulAut.conj g).toMonoidHom
  let N := V ⊓ normalizer (B : Set G)
  let U := N ⊔ (B ⊓ normalizer (V : Set G))
  let I := V ⊔ B
  have hgo : Odd (orderOf g) := hg.symm ▸ ho
  have hg1 : g ≠ 1 := by
    intro he
    apply hp.ne_one
    simpa only [he, orderOf_one] using hg.symm
  have hmod := ti_inverted_pair_module V hTI g v hgo hg1 hv hinv hd
  have hcore : I.pCoreIn 2 = U := ti_inverted_prime_pair_core V hTI hp ho g v hg hv hinv hd hi
  have hUI : U ≤ I := sup_le (inf_le_left.trans le_sup_left) (inf_le_left.trans le_sup_right)
  have hIgen : I = zpowers g ⊔ V := hgen
  have hgI : zpowers g ≤ I := by rw [hIgen]; exact le_sup_left
  have hpair : cyclicPairJoin (zpowers g) U V = I := by
    apply le_antisymm
    · exact sup_le (sup_le hgI hUI) le_sup_left
    · rw [hIgen]
      exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hUN : U ⊓ V = N := ti_pair_mutual_module_inf_left V B hd
  have hidx : (U ⊓ V).relIndex V = 2 := by
    rw [hUN, inf_relIndex_left]
    exact hi
  have hcV : Nat.card V = 2 ^ d := by
    obtain ⟨e, f, hf⟩ := A.natural
    rw [Nat.card_congr f.toEquiv]
    simp
  have hcard : Nat.card (U ⊓ V : Subgroup G) = 2 ^ (d - 1) := by
    have hc := relIndex_mul_relIndex (⊥ : Subgroup G) (U ⊓ V) V bot_le inf_le_right
    rw [relIndex_bot_left, relIndex_bot_left, hidx, hcV] at hc
    have hd : d = (d - 1) + 1 := by have := A.dimension.1; omega
    rw [hd, pow_succ] at hc
    exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) hc
  refine ⟨p, P, U, g, v, ?_, hg, hv, hvQ, hmod.2.2.2.2.2, hinv⟩
  exact {
    hstar := S.hstar
    prime := S.prime
    odd_prime := S.odd_prime
    pgroup := S.pgroup
    sylow := S.sylow
    escapes := S.escapes
    overgroup := S.overgroup
    factorization := S.factorization
    quotient_core := S.quotient_core
    quotient_two := S.quotient_two
    frattini_intersection := S.frattini_intersection
    generator_mem := hgP
    pair_core := by rw [hpair]; exact hcore
    pair_generated := hpair
    pair_disjoint := hd
    core_generated := hmod.1
    pair_fixed := hmod.2.1
    core_moved := hmod.2.2.1
    transvections := hmod.2.2.2.1
    action_kernel := hmod.2.2.2.2.1
    hyperplane_index := hidx
    hyperplane := hcard }

/-- The source seed exists from the permitted natural analysis and global TI
hypothesis. No invariant-Sylow or pair-core conclusion is assumed. -/
theorem exists_cyclicConstructionSeed (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V) :
    ∃ p H P U g, CyclicConstructionSeed T L V d p H P U g := by
  obtain ⟨H, hH⟩ := A.exists_hstar
  obtain ⟨p, P, U, g, v, S, _⟩ := chosen_hstar_exists_cyclicConstructionSeed D A hT hTI hH
  exact ⟨p, H, P, U, g, S⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
