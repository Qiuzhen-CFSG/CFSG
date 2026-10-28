module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicSolvable
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd.SolvableSupplement
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.SylowHyperplane
public import Theory.GroupTheory.PCoreFrattiniQuotient

/-!
# The odd Sylow supplement and its initial hyperplane pair

For the original moving solvable H-star subgroup, lift B.6.8(2) to a Sylow
p-subgroup P of H. This gives the actual product H = PT, its literal image
in H/O₂(H), and Φ(P) = P ∩ N_G(L). Movement of V and the self-centralizing
odd core make the quotient action nontrivial. Coprime action and the
prescribed-subgroup lifting theorem then choose g inside this same P so that
V and Vᵍ are disjoint and N_V(Vᵍ) has index two.

These are the supplement and pair-existence parts of the construction before
12.2.20. They do not assert the remaining I.6.2 odd-dihedral/core description,
inverter-invariant Sylow selection, or the later cyclicity conclusion. Those
local obligations and their application to CyclicConstructionSeed remain with
qt-d-12213-cyclic-block, together with the final cyclic-block assembly.

Source: Aschbacher–Smith, printed p.802, using B.6.8(2), pp.113–114,
and the elementary part of I.6.2, pp.424–425.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G]

/-- The odd Sylow supplement on the original ambient carrier, before pair-core
recognition or invariant-Sylow selection. -/
structure CyclicOddSupplement (T : Sylow 2 G) (L : Subgroup G)
    (p : ℕ) (H P : Subgroup G) : Prop where
  hstar : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))
  prime : p.Prime
  odd_prime : Odd p
  pgroup : IsPGroup p P
  sylow : ∃ S : Sylow p H, (S : Subgroup H).map H.subtype = P
  escapes : ¬ P ≤ normalizer (L : Set G)
  overgroup : H = P ⊔ (T : Subgroup G)
  factorization : ∀ x ∈ H, ∃ a ∈ P, ∃ t ∈ (T : Subgroup G), x = a * t
  quotient_core : (P.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) =
    pCore p (H ⧸ pCore 2 H)
  quotient_two : IsPGroup 2 ((H ⧸ pCore 2 H) ⧸ pCore p (H ⧸ pCore 2 H))
  frattini_intersection : (frattini P).map P.subtype = P ⊓ normalizer (L : Set G)

variable [Finite G] {T : Sylow 2 G} {L V H : Subgroup G} {d : ℕ}

/-- Every original H-star member has the genuine odd Sylow supplement. -/
theorem chosen_hstar_exists_odd_supplement (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ∃ p P, CyclicOddSupplement T L p H P := by
  let S := T.subtype hH.1.1.2
  have hmin := chosen_hstar_intrinsic_minimalParabolic D A hH
  obtain ⟨p, hp, ho, hr, hq, hPhi, _⟩ := ChapterB.minimalParabolic_solvable_structure
    S hmin (A.hstar_solvable H hH)
  let : Fact p.Prime := ⟨hp⟩
  let R : Sylow p H := Sylow.nonempty.some
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
  refine ⟨p, P, ⟨hH, hp, ho, R.isPGroup'.map H.subtype, ⟨R, rfl⟩, ?_, hgen,
    hfac, ?_, hq, hphiG⟩⟩
  · intro hn
    apply hH.1.2
    rw [hgen]
    exact sup_le hn D.sylow_normalizes_component
  · rw [hsub]
    exact sylow_map_twoCoreQuotient_eq_odd_core ho hr R

/-- Construct the solvable odd supplement under the permitted natural analysis. -/
theorem exists_cyclicOddSupplement (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d) :
    ∃ p H P, CyclicOddSupplement T L p H P := by
  obtain ⟨H, hH⟩ := A.exists_hstar
  obtain ⟨p, P, hP⟩ := chosen_hstar_exists_odd_supplement D A hH
  exact ⟨p, H, P, hP⟩

open ChapterI.Section06To08

/-- The odd supplement supplies a hyperplane pair with its conjugator inside P. -/
theorem CyclicOddSupplement.exists_hyperplane_pair {p : ℕ} {P : Subgroup G}
    (S : CyclicOddSupplement T L p H P) (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V) :
    ∃ g ∈ P, Odd (orderOf g) ∧ Disjoint V (V.map (MulAut.conj g).toMonoidHom) ∧
      (normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)).relIndex V = 2 := by
  let := D.elementary
  let : Fact p.Prime := ⟨S.prime⟩
  have hp2 : p ≠ 2 := by
    intro he
    exact S.odd_prime.not_two_dvd_nat (by rw [he])
  have hVH : V ≤ H := D.le_sylow.trans S.hstar.1.1.2
  let E := V.subgroupOf H
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hVH
  have hETI : IsTISubgroup E := by
    apply (isTISubgroup_iff E).mpr
    intro g hg x hx hgx
    apply Subtype.ext
    apply (isTISubgroup_iff V).mp hTI g ?_ x hx hgx
    intro hn
    exact hg (V.le_normalizer_comap H.subtype hn)
  let q := QuotientGroup.mk' (pCore 2 H)
  let R := pCore p (H ⧸ pCore 2 H)
  let F := E.map q
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map _
  have hF : F ≠ ⊥ := by
    intro he
    have hle := (map_eq_bot_iff E (f := q)).mp he
    have hEQ : E ≤ pCore 2 H := by simpa only [q, QuotientGroup.ker_mk'] using hle
    apply A.hstar_movement H S.hstar
    intro x hx
    exact mem_map_of_mem H.subtype (hEQ (show (⟨x, hVH hx⟩ : H) ∈ E from hx))
  have hk : q.ker ≤ normalizer (E : Set H) := by
    rw [QuotientGroup.ker_mk']
    have hQT := (pCore_isPGroup (p := 2) (G := H)).le_sylow_of_normal (T.subtype S.hstar.1.1.2)
    intro x hx
    exact V.le_normalizer_comap H.subtype (hT (hQT hx))
  have hdis : Disjoint F R := IsPGroup.disjoint_of_ne 2 p hp2.symm F R
    (IsElementaryAbelian.isPGroup 2 F) pCore_isPGroup
  have hcore : pCore 2 (H ⧸ pCore 2 H) = ⊥ := by
    rw [← pCore_map_mk'_eq_of_normal_isPGroup (p := 2) (pCore 2 H)
      (pCore_isPGroup (G := H) (p := 2))]
    exact (map_eq_bot_iff (f := q) (H := pCore 2 H)).mpr (by simp only [q, QuotientGroup.ker_mk']; exact le_rfl)
  have hmove : ⁅R, F⁆ ≠ ⊥ := by
    intro he
    have hFR : F ≤ R := (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp he)).trans
      (centralizer_pCore_le_of_quotient_isPGroup p 2
        hcore S.quotient_two)
    exact hF (bot_unique ((le_inf le_rfl hFR).trans hdis.le_bot))
  obtain ⟨g, hg, ho, _, hi⟩ := exists_pair_index_two_in_prime_subgroup E hETI q
    (QuotientGroup.mk'_surjective _) hk hp2 (P.subgroupOf H) S.pgroup.comap_subtype
    (by rw [S.quotient_core]; exact le_normalizer_of_normal)
    (by rw [S.quotient_core]; exact hmove)
  let B := V.map (MulAut.conj (g : G)).toMonoidHom
  have hBH : B ≤ H := by
    rintro x ⟨v, hv, rfl⟩
    exact H.mul_mem (H.mul_mem g.property (hVH hv)) (H.inv_mem g.property)
  have heB : E.map (MulAut.conj g).toMonoidHom = B.subgroupOf H := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact mem_map_of_mem (MulAut.conj (g : G)).toMonoidHom hv
    · rintro ⟨v, hv, hve⟩
      exact ⟨⟨v, hVH hv⟩, hv, Subtype.ext hve⟩
  rw [heB, ← subgroupOf_normalizer_eq hBH, relIndex_subgroupOf hVH] at hi
  have hne : B ≠ V := by
    intro he
    rw [he, relIndex_eq_one.mpr V.le_normalizer] at hi
    exact (by decide : (1 : ℕ) ≠ 2) hi
  exact ⟨g, hg, by simpa only [Subgroup.orderOf_coe] using ho,
    ((hTI.eq_or_disjoint_conjugate g).resolve_left hne).symm, hi⟩

/-- The genuine solvable entry and the prescribed-Sylow pair are assembled
on the same original H and P. The remaining pair-core and invariant selection
arguments stay with the cyclic-block owner. -/
theorem exists_cyclicOddSupplement_hyperplane_pair (D : ChosenModule T L V)
    (A : NaturalLocalAnalysis T L V d)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V) :
    ∃ p H P g, CyclicOddSupplement T L p H P ∧ g ∈ P ∧ Odd (orderOf g) ∧
      Disjoint V (V.map (MulAut.conj g).toMonoidHom) ∧
      (normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)).relIndex V = 2 := by
  obtain ⟨p, H, P, S⟩ := exists_cyclicOddSupplement D A
  obtain ⟨g, hg, ho, hd, hi⟩ := S.exists_hyperplane_pair D A hT hTI
  exact ⟨p, H, P, g, S, hg, ho, hd, hi⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
