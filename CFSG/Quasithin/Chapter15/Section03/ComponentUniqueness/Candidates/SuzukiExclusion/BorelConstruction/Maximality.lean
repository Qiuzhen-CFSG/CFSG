module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SuzukiExclusion.BorelConstruction.Invariance
public import Theory.GroupTheory.SylowNormalizerCommutingFamily.FactorControl
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.ComponentLocalOrbitCore

/-!
# Invariant maximality of the Suzuki orbit normalizer

Let L₀ = ⟨L^S⟩ and B = N_{L₀}(S ∩ L₀). Distinct components in the
S-orbit commute. Their Sylow intersections generate S ∩ L₀, and each
factor's Sylow normalizer lies in B. If an S-invariant overgroup D of B
contains an orbit component, it contains L₀. Otherwise F.1.3(1) identifies
each intersection of D with a component as its Sylow normalizer.

Each component is normal in L₀, so these intersections are normal in D.
Their characteristic two-cores are the Sylow intersections. Thus D normalizes
every factor of S ∩ L₀ and lies in B. All normality statements are relative
to the actual orbit; S need not normalize L. The argument works for any
number of orbit components, so the source index bound is not needed here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), proof of
15.3.34, printed p.1134, using F.1.3(1), printed pp.259--260, and the
component calculus of 1.2/A.3. The coordinate Sylow argument follows the
commuting-family construction in `SylowNormalizerCommutingFamily.FactorControl`.
-/

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion.BorelConstruction.Maximality
variable {G : Type*} [Group G] [Finite G]
variable {ι : Type*} [Fintype ι] {p : ℕ} [Fact p.Prime]

private theorem mem_pi_sylow_iff (K : ι → Type*) [∀ i, Group (K i)]
    [∀ i, Finite (K i)] (Q : Sylow p (∀ i, K i)) (x : ∀ i, K i) :
    x ∈ Q ↔ ∀ i, x i ∈ Q.map (Pi.evalMonoidHom K i) := by
  let R : Subgroup (∀ i, K i) := Subgroup.pi Set.univ
    (fun i => Q.map (Pi.evalMonoidHom K i))
  have hp : IsPGroup p R := by
    intro y
    choose n hn using fun i =>
      (Q.mapSurjective (Function.surjective_eval i)).isPGroup'
        ⟨y.val i, y.property i (Set.mem_univ i)⟩
    refine ⟨∑ i, n i, Subtype.ext (funext fun i => ?_)⟩
    have hi : n i ≤ ∑ j, n j := Finset.single_le_sum
      (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
    have he : y.val i ^ (p ^ n i) = 1 := congrArg Subtype.val (hn i)
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one he).trans
      (pow_dvd_pow p hi))
  have hQR : (Q : Subgroup (∀ i, K i)) ≤ R := by
    intro y hy i _
    exact mem_map_of_mem _ hy
  have he := Q.is_maximal' hp hQR
  change x ∈ (Q : Subgroup (∀ i, K i)) ↔ _
  conv_lhs => rw [← he]
  simp only [R, mem_pi, Set.mem_univ, forall_const]


private theorem sylow_generated_by_factors
    (C : ι → Subgroup G)
    (hcomm : Pairwise fun i j => C i ≤ centralizer (C j : Set G))
    (hgen : iSup C = ⊤) (P : Sylow p G) :
    (P : Subgroup G) = ⨆ i, ((P : Subgroup G) ⊓ C i) := by
  classical
  have hc : Pairwise fun i j => ∀ x y : G, x ∈ C i → y ∈ C j → Commute x y := by
    intro i j hij x y hx hy
    exact (hcomm hij hx y hy).symm
  let f : (∀ i, C i) →* G := noncommPiCoprod hc
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp
    (noncommPiCoprod_range.trans hgen)
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective hf p P
  have hQP : Q.map f = (P : Subgroup G) := congrArg Sylow.toSubgroup hQ
  apply le_antisymm _ (iSup_le fun _ => inf_le_left)
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (show x ∈ Q.map f from hQP.symm ▸ hx)
  rw [show f y = noncommPiCoprod hc y from rfl, noncommPiCoprod_apply]
  apply Subgroup.noncommProd_mem
  intro i _
  apply le_iSup (fun j => (P : Subgroup G) ⊓ C j) i
  refine ⟨?_, (y i).property⟩
  rw [← hQP]
  refine ⟨Pi.mulSingle i (y i), ?_, noncommPiCoprod_mulSingle i (y i)⟩
  apply (mem_pi_sylow_iff (fun j => C j) Q _).mpr
  intro j
  by_cases he : i = j
  · subst j
    simpa only [Pi.mulSingle_eq_same] using
      (mem_pi_sylow_iff (fun j => C j) Q y).mp hy i
  · simpa only [Pi.mulSingle_eq_of_ne (Ne.symm he)] using
      (Q.map (Pi.evalMonoidHom (fun j => C j) j)).one_mem

/-- Proper factor intersections force an overgroup of the Sylow normalizer
back into that normalizer. -/
private theorem overgroup_eq_of_proper_factor_intersections
    (C : ι → Subgroup G)
    (hcomm : Pairwise fun i j => C i ≤ centralizer (C j : Set G))
    (hgen : iSup C = ⊤) (P : Sylow 2 G) (D : Subgroup G)
    (hND : normalizer (P : Set G) ≤ D)
    (hproper : ∀ i, ¬ C i ≤ D)
    (hunique : ∀ i (R : Sylow 2 (C i)) (M : Subgroup (C i)),
      (R : Subgroup (C i)) ≤ M → M < ⊤ → M ≤ normalizer (R : Set (C i))) :
    D = normalizer (P : Set G) := by
  have hnorm (i : ι) : D ≤ normalizer (C i : Set G) := by
    have hh : (⊤ : Subgroup G) ≤ normalizer (C i : Set G) := by
      rw [← hgen]
      apply iSup_le
      intro j
      by_cases he : j = i
      · subst j; exact (C i).le_normalizer
      · exact (hcomm he).trans (Subgroup.centralizer_le_normalizer _)
    exact le_top.trans hh
  have hi (i : ι) : D ≤ normalizer (((P : Subgroup G) ⊓ C i : Subgroup G) : Set G) := by
    obtain ⟨R, hR, hRN⟩ := Sylow.factor_normalizer_control C hcomm hgen P i
    have he : D.subgroupOf (C i) = normalizer (R : Set (C i)) := by
      apply le_antisymm
      · apply hunique i R _
        · rw [hR]
          exact subgroupOf_mono (C i) (P.le_normalizer.trans hND)
        · exact lt_top_iff_ne_top.mpr (fun h => hproper i (subgroupOf_eq_top.mp h))
      · exact map_le_iff_le_comap.mp (hRN.trans hND)
    have hcore : (D ⊓ C i : Subgroup G).pCoreIn 2 = (P : Subgroup G) ⊓ C i := by
      have hh := congrArg (Subgroup.map (C i).subtype) (twoCore_sylow_normalizer R)
      change ((normalizer (R : Set (C i))).pCoreIn 2).map (C i).subtype =
        (R : Subgroup (C i)).map (C i).subtype at hh
      rw [← he, map_pCoreIn_of_injective 2 _ _ (C i).subtype_injective,
        subgroupOf_map_subtype, hR, subgroupOf_map_subtype] at hh
      exact hh
    rw [← hcore]
    exact (le_normalizer_inf D.le_normalizer (hnorm i)).trans
      (normalizer_le_normalizer_characteristic_image (D ⊓ C i) (pCore 2 (D ⊓ C i : Subgroup G)))
  apply le_antisymm _ hND
  change D ≤ normalizer ((P : Subgroup G) : Set G)
  rw [sylow_generated_by_factors C hcomm hgen P]
  exact (le_iInf hi).trans (iInf_normalizer_le_normalizer_iSup _)


private theorem exists_sylow_intersection_of_normalizes
    (S : Sylow 2 G) (J : Subgroup G) (hSJ : (S : Subgroup G) ≤ normalizer (J : Set G)) :
    ∃ P : Sylow 2 J, (P : Subgroup J) = (S : Subgroup G).subgroupOf J := by
  let W := J ⊔ (S : Subgroup G)
  have hJW : J ≤ W := le_sup_left
  let _ : (J.subgroupOf W).Normal :=
    (normal_subgroupOf_iff_le_normalizer hJW).mpr (sup_le J.le_normalizer hSJ)
  obtain ⟨P, hP⟩ := (S.subtype (show (S : Subgroup G) ≤ W from le_sup_right)).exists_subgroupOf_eq_of_normal (J.subgroupOf W)
  let e := subgroupOfEquivOfLe hJW
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (P : Subgroup _).map e.toMonoidHom = _
  rw [hP]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x, hJW x.property⟩, x.property⟩, hx, rfl⟩

private theorem suzuki_unique {K : Type*} [Group K] [Finite K] (m : ℕ)
    (e : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (R : Sylow 2 K) (M : Subgroup K) (hRM : (R : Subgroup K) ≤ M) (hM : M < ⊤) :
    M ≤ normalizer (R : Set K) := by
  have hMt : M.map e.toMonoidHom < ⊤ := by
    rw [← map_top_of_surjective e.toMonoidHom e.surjective]
    exact (map_lt_map_iff_of_injective e.injective).mpr hM
  have hh := (suzuki_rankOneSylowFacts m
    (R.mapSurjective (f := e.toMonoidHom) e.surjective)).unique_maximal
      (M.map e.toMonoidHom) (map_mono hRM) hMt
  change M.map e.toMonoidHom ≤ normalizer ((R : Subgroup K).map e.toMonoidHom : Set _) at hh
  rw [← map_equiv_normalizer_eq] at hh
  exact (map_le_map_iff_of_injective e.injective).mp hh

/-- In a Suzuki component orbit, the relative Sylow normalizer is maximal
among the subgroups preserved by the supplied ambient Sylow subgroup. -/
private theorem component_orbit_normalizer_maximal
    (L : Subgroup G) (hL : IsComponent G L) (P : Sylow 2 G)
    (m : ℕ) (e : L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (D : Subgroup G)
    (hBD : componentOrbit L (P : Subgroup G) ⊓
      normalizer (((P : Subgroup G) ⊓ componentOrbit L (P : Subgroup G) : Subgroup G) : Set G) ≤ D)
    (hDE : D ≤ componentOrbit L (P : Subgroup G))
    (hPD : (P : Subgroup G) ≤ normalizer (D : Set G)) :
    D = componentOrbit L (P : Subgroup G) ⊓
      normalizer (((P : Subgroup G) ⊓ componentOrbit L (P : Subgroup G) : Subgroup G) : Set G) ∨
      D = componentOrbit L (P : Subgroup G) := by
  classical
  let E := componentOrbit L (P : Subgroup G)
  by_cases hED : E ≤ D
  · exact Or.inr (le_antisymm hDE hED)
  left
  let J := {C : Subgroup G // ∃ a : P, L.map (MulAut.conj (a : G)).toMonoidHom = C}
  let a (i : J) : P := Classical.choose i.property
  have ha (i : J) : L.map (MulAut.conj (a i : G)).toMonoidHom = i.val :=
    Classical.choose_spec i.property
  have hCE (i : J) : i.val ≤ E := by
    rw [← ha i]
    exact le_iSup (fun b : P => L.map (MulAut.conj (b : G)).toMonoidHom) (a i)
  let C (i : J) : Subgroup E := i.val.subgroupOf E
  let : Fintype J := Fintype.ofFinite J
  have hcomm : Pairwise fun i j => C i ≤ centralizer (C j : Set E) := by
    intro i j hij x hx y hy
    apply Subtype.ext
    have hi : IsComponent G i.val := ha i ▸ hL.map_conj (a i)
    have hj : IsComponent G j.val := ha j ▸ hL.map_conj (a j)
    exact (commutator_eq_bot_iff_le_centralizer.mp
      (hi.commutator_eq_bot_of_ne hj (fun he => hij (Subtype.ext he)))) hx y.val hy
  have hgen : iSup C = ⊤ := by
    apply map_injective E.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, range_subtype]
    simp_rw [C, map_subgroupOf_eq_of_le (hCE _)]
    apply le_antisymm (iSup_le hCE)
    exact iSup_le fun b => le_iSup (fun i : J => i.val) ⟨_, b, rfl⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_intersection_of_normalizes P E
    (le_normalizer_componentOrbit L (P : Subgroup G))
  have hN : (E ⊓ normalizer (((P : Subgroup G) ⊓ E : Subgroup G) : Set G)).subgroupOf E =
      normalizer (Q : Set E) := by
    change _ = normalizer ((Q : Subgroup E) : Set E)
    rw [hQ, inf_subgroupOf_left, subgroupOf_normalizer_eq inf_le_right,
      inf_subgroupOf_right]
  have he := overgroup_eq_of_proper_factor_intersections C hcomm hgen Q (D.subgroupOf E)
    (hN ▸ subgroupOf_mono E hBD) (fun i hi => ?_) (fun i R M hRM hM => ?_)
  · have hh := congrArg (Subgroup.map E.subtype) he
    rw [← hN, map_subgroupOf_eq_of_le hDE,
      map_subgroupOf_eq_of_le (show E ⊓ normalizer (((P : Subgroup G) ⊓ E : Subgroup G) : Set G) ≤ E from inf_le_left)] at hh
    exact hh
  · apply hED
    apply iSup_conjugates_le_of_le_normalizer L (P : Subgroup G) D _ hPD
    intro l hl
    have hc : (MulAut.conj (a i : G)) l ∈ i.val := ha i ▸ mem_map_of_mem _ hl
    have hd : (MulAut.conj (a i : G)) l ∈ D := hi (show (⟨_, hCE i hc⟩ : E) ∈ C i from hc)
    have hh := le_normalizer_iff.mp hPD (a i : G)⁻¹ (P.inv_mem (a i).property) _ hd
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · let ei : L ≃* i.val := ((MulAut.conj (a i : G)).subgroupMap L).trans
      (MulEquiv.subgroupCongr (ha i))
    exact suzuki_unique m ((subgroupOfEquivOfLe (hCE i)).trans (ei.symm.trans e))
      R M hRM hM

end CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion.BorelConstruction.Maximality

namespace CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion.BorelConstruction
open Maximality
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem componentOrbit_eq_localSpan (L S : Subgroup G) :
    componentOrbit L S = localSpan L S :=
  le_antisymm (iSup_conjugates_le_of_le_normalizer L S _
    (le_conjugateSpanBy L S) (le_normalizer_conjugateSpanBy L S))
    (conjugateSpanBy_le (le_componentOrbit L S) (le_normalizer_componentOrbit L S))

/-- Invariant maximality of the literal relative normalizer, with no marking
or characteristic-two assumption. -/
public theorem orbitNormalizer_maximal
    {I L S : Subgroup G} (hLI : L ≤ I)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = S)
    (hL : IsComponent I (L.subgroupOf I)) (m : ℕ) (_hm : 0 < m)
    (e : L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (_hindex : (normalizer (L.subgroupOf I : Set I)).index ≤ 2)
    (D : Subgroup G) (hBD : orbitNormalizer L S ≤ D)
    (hDE : D ≤ localSpan L S) (hSD : S ≤ normalizer (D : Set G)) :
    D = orbitNormalizer L S ∨ D = localSpan L S := by
  let E := componentOrbit (L.subgroupOf I) (P : Subgroup I)
  have hE : E.map I.subtype = localSpan L S := by
    change (componentOrbit (L.subgroupOf I) (P : Subgroup I)).map I.subtype = _
    rw [map_componentOrbit, map_subgroupOf_eq_of_le hLI, hP,
      componentOrbit_eq_localSpan]
  have hEI : localSpan L S ≤ I := hE ▸ map_subtype_le E
  have hEs : E = (localSpan L S).subgroupOf I := by
    apply map_injective I.subtype_injective
    rw [hE, map_subgroupOf_eq_of_le hEI]
  have hPs : S.subgroupOf I = (P : Subgroup I) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective I.subtype_injective _
  have hB : E ⊓ normalizer (((P : Subgroup I) ⊓ E : Subgroup I) : Set I) =
      (orbitNormalizer L S).subgroupOf I := by
    change E ⊓ _ = (localSpan L S).subgroupOf I ⊓
      (normalizer ((S ⊓ localSpan L S : Subgroup G) : Set G)).subgroupOf I
    rw [subgroupOf_normalizer_eq (inf_le_right.trans hEI)]
    change E ⊓ _ = (localSpan L S).subgroupOf I ⊓
      normalizer ((S.subgroupOf I ⊓ (localSpan L S).subgroupOf I : Subgroup I) : Set I)
    rw [← hEs, hPs]
  have hDI : D ≤ I := hDE.trans hEI
  have hPD : (P : Subgroup I) ≤ normalizer (D.subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq hDI]
    intro p hp
    exact hSD (hP ▸ mem_map_of_mem I.subtype hp)
  have hh := component_orbit_normalizer_maximal (L.subgroupOf I) hL P m
    ((subgroupOfEquivOfLe hLI).trans e) (D.subgroupOf I)
    (hB ▸ subgroupOf_mono I hBD) (by
      change D.subgroupOf I ≤ E
      rw [hEs]
      exact subgroupOf_mono I hDE) hPD
  rcases hh with hh | hh
  · left
    have hh' := congrArg (Subgroup.map I.subtype) hh
    rw [map_subgroupOf_eq_of_le hDI, hB,
      map_subgroupOf_eq_of_le ((orbitNormalizer_le L S).trans hEI)] at hh'
    exact hh'
  · right
    have hh' := congrArg (Subgroup.map I.subtype) hh
    rw [map_subgroupOf_eq_of_le hDI, hE] at hh'
    exact hh'

end CFSG.Quasithin.Chapter15.Section03.Candidates.SuzukiExclusion.BorelConstruction
