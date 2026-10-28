module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.FixedSeed.Defs
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.FixedSeed.Factors
public import Theory.GroupTheory.ElementaryPairNorm

/-!
# Transitivity on the fixed-seed outside coset

The specified involution exchanges the two maximal elementary factors of R.
Their intersection V is central, contains the derived group, and has order
four, while each factor has order sixteen. The elementary-pair norm theorem
therefore conjugates t to every element of Vt. Factor comparison then conjugates
every square-one element of Rt to t by an element of R.

This is the orbit step in Aschbacher--Smith, Quasithin Groups, 14.3.21(2),
printed p.998. The factors are only required to normalize each other.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original fixed-seed outside coset has a single R-orbit of involutions. -/
theorem source_fixed_seed_coset_transitivity_of_solvable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    : FixedSeedCosetTransitivity F (sourceResidual M Mc) := by
  intro t ht ht2 htout htV x hx2 hxR
  obtain ⟨A,B,hAR,hBR,hEA,hEB,hAc,_,hi,hAB,_,hAN,hBN,hmax,hswap⟩ :=
    source_outside_element_exchanges_factors_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs t ht htout
  let := hEA
  let := hEB
  let R := (F.I₂ (sourceResidual M Mc)).pCoreIn 2
  let V := rankTwoSeed T M
  change A ⊔ B = R at hAB
  change A ⊓ B = V at hi
  have hRA : R ≤ normalizer (A : Set G) :=
    (pCoreIn_le 2 _).trans (le_sup_left.trans hAN)
  have hRB : R ≤ normalizer (B : Set G) :=
    (pCoreIn_le 2 _).trans (le_sup_left.trans hBN)
  have hder : ⁅R,R⁆ ≤ V := by
    rw [←hi]
    apply le_inf
    · rw [←hAB]
      exact commutator_sup_le_of_normalized_derived A B (hBR.trans hRA)
        (by rw [commutator_self_eq_bot_iff.mpr inferInstance]; exact bot_le)
    · rw [←hAB,sup_comm A B]
      exact commutator_sup_le_of_normalized_derived B A (hAR.trans hRB)
        (by rw [commutator_self_eq_bot_iff.mpr inferInstance]; exact bot_le)
  have hcent : V ≤ centralizer (R : Set G) := by
    rw [←hi]
    apply le_centralizer_iff.mp
    rw [←hAB]
    exact sup_le
      (le_centralizer_iff.mp (inf_le_left.trans (le_centralizer A)))
      (le_centralizer_iff.mp (inf_le_right.trans (le_centralizer B)))
  have hinv : ∀ r ∈ R, r ^ 2 = 1 → r ∈ A ∨ r ∈ B := by
    intro r hr hr2
    let : IsElementaryAbelian 2 (zpowers r) := IsElementaryAbelian.zpowers_of_pow_eq_one hr2
    rcases hmax (zpowers r) inferInstance (zpowers_le.mpr hr) with hA | hB
    · exact Or.inl (hA (mem_zpowers r))
    · exact Or.inr (hB (mem_zpowers r))
  have hVc : Nat.card V = 4 := by
    simpa only [F.last,show (2:ℕ)^2=4 from rfl] using F.card 2 le_rfl
  have hsquare : Nat.card A = Nat.card V ^ 2 := by rw [hAc,hVc]; rfl
  have htsq : t ^ 2 = 1 := by rw [←ht2]; exact pow_orderOf_eq_one t
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using htsq)
  let α := MulAut.conj t
  have hα2 (a : G) : α (α a) = a := by
    change t * (t * a * t⁻¹) * t⁻¹ = a
    calc
      _ = (t*t)*a*(t*t)⁻¹ := by group
      _ = a := by rw [←pow_two,htsq]; simp
  have hswap' : A.map α.toMonoidHom = B := by
    change A.map (MulAut.conj t⁻¹).toMonoidHom = B at hswap
    rwa [hti] at hswap
  have hback : B.map α.toMonoidHom = A := by
    apply le_antisymm
    · rintro _ ⟨b,hb,rfl⟩
      obtain ⟨a,ha,he⟩ := hswap'.symm ▸ hb
      change α a = b at he
      change α b ∈ A
      rw [←he,hα2]
      exact ha
    · intro a ha
      exact ⟨α a,hswap' ▸ mem_map_of_mem α.toMonoidHom ha,hα2 a⟩
  have htR : t ∈ normalizer (R : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change R.map α.toMonoidHom = R
    rw [←hAB,Subgroup.map_sup,hswap',hback,sup_comm]
  have hcentral := elementary_pair_conjugate_central_translate R A V t htsq hAR
    (hswap'.symm ▸ hBR) (hswap'.symm ▸ hi) hder hcent htV
    (hswap'.symm ▸ hinv) hsquare
  have hleft : t⁻¹*x ∈ R := by
    have hh := (mem_normalizer_iff.mp ((normalizer (R : Set G)).inv_mem htR)
      (x*t⁻¹)).mp hxR
    simpa only [inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hh
  obtain ⟨r,hr,he⟩ := elementary_pair_conjugate_involution_coset R A B V t htsq htR
    hAB hRA hswap' hi hcent hcentral (t⁻¹*x) hleft
    (by simpa only [mul_inv_cancel_left] using hx2)
  refine ⟨r,hr,?_⟩
  have he' : r*t*r⁻¹ = x := by simpa only [mul_inv_cancel_left] using he
  rw [←he']
  group

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
