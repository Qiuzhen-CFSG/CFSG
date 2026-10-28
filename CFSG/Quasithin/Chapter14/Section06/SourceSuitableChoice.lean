module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableNormalizer.LocalSylow
public import Theory.GroupTheory.IndependentSupportMovement
public import Theory.GroupAction.FixedModuloCentralLine

/-!
# Suitable vectors from the original invariant summands

For the fixed H, M and Mc of the rank-two source setup, movement by a
subgroup of the generalized-Fitting preimage of Mc forces movement by
O₂(Mc): an involution fixed by that core lies in its omega-center, which
14.6.1(5) centralizes.

A vector fixed modulo Z by an index-two subgroup S has quotient centralizer
exactly S when its other coset has an independent conjugate support. The
commutator product identity prevents cancellation between these supports,
supplying both clauses of (U2). The given source normalizer equality
N_Mc(S)=T then supplies (U3) and the local Sylow part of (U1).

If the support has no K-fixed vector modulo Z, orbit counting actually
selects the required nonzero vector. The last theorem applies original
14.6.3(4) to that vector, yielding its ambient normalizer and Sylow
centralizer. All maps and conjugations are the original ones.

These are conditional constructions, not proofs of 14.6.14--24: the
source branches must still supply the summands and their normalizer.
In particular the fixed-free theorem does not cover the five-dimensional
A₆ module with a nonzero central kernel.

Source: Aschbacher--Smith, combined 1 March 2004 manuscript,
14.6.1(5), (U0)--(U3), 14.6.17(3), and 14.6.24(1),
printed pp.1020--1021,1035--1036,1038--1039.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))

include hG hempty hM hunique hmany hcard e hab H hH

/-- Original 14.6.1(5) converts fitting-preimage movement into two-core movement. -/
theorem source_core_moves_of_fitting_moves
    (K : Subgroup G) (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hmove : ¬ K ≤ centralizer ({u} : Set G)) :
    ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G) := by
  have hHMc : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
      H hH.1 hH.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  have hTMc : (T : Subgroup G) ≤ Mc := hH.1.2.trans hHMc
  have hMcMax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).1
  have hMcOutside : Mc ∈ Chapter1.HOutside G (T : Set G) (M : Set G) :=
    ⟨⟨Chapter1.mem_H_of_isTwoLocal hMcMax.1,hTMc⟩,fun hh => hH.2 (hHMc.trans hh)⟩
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  have h : D.Hypothesis := source_rankTwo_f9_hypothesis
    hG T hempty hM hunique hmany hcard e hab Mc hMcOutside
  let : IsElementaryAbelian 2 D.UH := h.UH_elementary_of_V_le_QH
    ((le_conjugateSpanBy D.V D.H).trans h.UH_le_QH)
  have huU : u ∈ D.UH := (conjugateSpanBy_mono le_rfl hHMc) hu
  have hKC := hK.trans (source_generalizedFittingPreimage_centralizes_omegaCore
    hG T hempty hMcOutside h.H_centralizes)
  intro hc
  have huOmega : u ∈ omegaOneCenterAmbient D.QH :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨h.UH_le_QH huU,elemPow_eq_one_of_isElementaryAbelian u huU,
        fun q hq => mem_centralizer_singleton_iff.mp (hc hq)⟩
  apply hmove
  intro k hk
  exact mem_centralizer_singleton_iff.mpr ((hKC hk u huOmega).symm)

omit [Finite G] hG hempty hM hunique hmany hcard e hab H hH in
private theorem cyclic_square_one_cases (u : G) (hu2 : u ^ 2 = 1)
    (a : G) (ha : a ∈ zpowers u) : a = 1 ∨ a = u := by
  let A : Subgroup G := {
    carrier := {a | a = 1 ∨ a = u}
    one_mem' := Or.inl rfl
    mul_mem' := by rintro a b (rfl | rfl) (rfl | rfl) <;> simp_all [pow_two]
    inv_mem' := by
      rintro a (rfl | rfl)
      · simp
      · exact Or.inr (inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hu2)) }
  exact (zpowers_le.mpr (show u ∈ A from Or.inr rfl)) ha

/-- Construction shared by the natural summands in 14.6.17 and 14.6.24.
The vector is fixed modulo Z by S and moved modulo Z by K. Its other
S-coset has a separate K-invariant support. -/
theorem source_suitable_of_separated_support
    (K W S : Subgroup G)
    (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hWU : W ≤ conjugateSpanBy (localModule T M) H)
    (hZW : centralInvolutions T ≤ W)
    (hKW : K ≤ normalizer (W : Set G))
    (hST : S ≤ (T : Subgroup G)) (hindex : S.relIndex (T : Subgroup G) = 2)
    (hU3 : Mc ⊓ normalizer (S : Set G) = (T : Subgroup G))
    (hseparate : ∀ t ∈ (T : Subgroup G), t ∉ S →
      W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralInvolutions T ∧
      K ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G))
    (u : G) (huW : u ∈ W)
    (hfixed : ∀ s ∈ S, ⁅u,s⁆ ∈ centralInvolutions T)
    (hmoved : ∃ k ∈ K, ⁅u,k⁆ ∉ centralInvolutions T) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    suitableQuotientCentralizer h u = S ∧
      ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G) ∧
      (∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer h u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (H ⊓ centralizer ({u} : Set G)) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  have h : D.Hypothesis := source_rankTwo_f9_hypothesis
    hG T hempty hM hunique hmany hcard e hab H hH
  let : IsElementaryAbelian 2 D.UH := h.UH_elementary_of_V_le_QH
    ((le_conjugateSpanBy D.V D.H).trans h.UH_le_QH)
  have hu : u ∈ D.UH := hWU huW
  have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu
  have hKM : K ≤ Mc := hK.trans (map_subtype_le _)
  have hMcZ : Mc ≤ centralizer (centralInvolutions T : Set G) :=
    (plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard
      (plane_centralInvolutions_card T M hM.1.2 hcard e)).2.2.1.le
  have huZ : u ∉ centralInvolutions T := by
    intro hz
    obtain ⟨k,hk,hkz⟩ := hmoved
    apply hkz
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hMcZ (hKM hk) u hz)]
    exact one_mem _
  have hSle : S ≤ suitableQuotientCentralizer h u := by
    intro s hs
    refine ⟨hST hs,(h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mpr ?_⟩
    refine ⟨h.T_le_H (hST hs),?_⟩
    intro a ha
    rcases cyclic_square_one_cases u hu2 a ha with rfl | rfl
    · simp
    · exact hfixed s hs
  have hTnot : ¬ (T : Subgroup G) ≤ suitableQuotientCentralizer h u := by
    intro hT
    have hSnot : ¬ (T : Subgroup G) ≤ S := by
      intro hs
      have hi := relIndex_eq_one.mpr hs
      omega
    obtain ⟨t,ht,htS⟩ := SetLike.not_le_iff_exists.mp hSnot
    have htinv := hT ((T : Subgroup G).inv_mem ht)
    have hz : ⁅u,t⁻¹⁆ ∈ centralInvolutions T :=
      ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp htinv.2).2 u (mem_zpowers u)
    have hvW : (MulAut.conj t⁻¹) u ∈ W := by
      have hh := W.mul_mem (W.inv_mem (hZW hz)) huW
      simpa [commutatorElement_def, MulAut.conj_apply, mul_assoc] using hh
    have hvZ := (hseparate t ht htS).1
      ⟨hvW,mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom huW⟩
    apply huZ
    have htZ := (centralizer_le_normalizer (centralInvolutions T : Set G))
      ((le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T))
        ((T : Subgroup G).inv_mem ht))
    exact (htZ u).mpr hvZ
  have heq : suitableQuotientCentralizer h u = S := by
    have hd : (suitableQuotientCentralizer h u).relIndex (T : Subgroup G) ∣ 2 := by
      simpa only [hindex] using relIndex_dvd_of_le_left (T : Subgroup G) hSle
    have hi : (suitableQuotientCentralizer h u).relIndex (T : Subgroup G) = 2 :=
      (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left
        (fun he => hTnot (relIndex_eq_one.mp he))
    have hm := relIndex_mul_relIndex S (suitableQuotientCentralizer h u)
      (T : Subgroup G) hSle inf_le_left
    rw [hi,hindex] at hm
    have hrel : S.relIndex (suitableQuotientCentralizer h u) = 1 := by omega
    exact le_antisymm (relIndex_eq_one.mp hrel) hSle
  have hmove : ¬ K ≤ centralizer ({u} : Set G) := by
    intro hc
    obtain ⟨k,hk,hkz⟩ := hmoved
    apply hkz
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_centralizer_singleton_iff.mp (hc hk)).symm]
    exact one_mem _
  refine ⟨heq,source_core_moves_of_fitting_moves hG T hempty hM hunique hmany hcard e hab
    H hH K hK u hu hmove,?_,?_⟩
  · intro t ht ht0
    have htS : t ∉ S := by rwa [heq] at ht0
    let W' := W.map (MulAut.conj t⁻¹).toMonoidHom
    have hW'U : W' ≤ D.UH := by
      rintro v ⟨w,hw,rfl⟩
      exact ((le_normalizer_conjugateSpanBy D.V D.H)
        (h.T_le_H ((T : Subgroup G).inv_mem ht)) w).mp (hWU hw)
    have hWW' : W ≤ normalizer (W' : Set G) := by
      apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro w hw v hv
      exact setLike_mul_comm (hW'U hv) (hWU hw)
    have hm := product_not_centralized_of_disjoint_modulo K W W' (centralInvolutions T)
      hKW (hseparate t ht htS).2 hWW' (hseparate t ht htS).1 u
      ((MulAut.conj t⁻¹) u) huW (mem_map_of_mem _ huW) hmoved
    exact source_core_moves_of_fitting_moves hG T hempty hM hunique hmany hcard e hab
      H hH K hK _ (D.UH.mul_mem hu (hW'U (mem_map_of_mem _ huW))) hm
  · apply source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab H hH u hu
    rwa [heq]

/-- An actual suitable involution is selected whenever the chosen summand
has no K-fixed vector modulo the source central line. -/
theorem source_exists_suitable_of_fixed_free_support
    (K W S : Subgroup G)
    (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hWU : W ≤ conjugateSpanBy (localModule T M) H)
    (hZW : centralInvolutions T < W)
    (hKW : K ≤ normalizer (W : Set G))
    (hSW : S ≤ normalizer (W : Set G))
    (hST : S ≤ (T : Subgroup G)) (hindex : S.relIndex (T : Subgroup G) = 2)
    (hU3 : Mc ⊓ normalizer (S : Set G) = (T : Subgroup G))
    (hseparate : ∀ t ∈ (T : Subgroup G), t ∉ S →
      W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralInvolutions T ∧
      K ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G))
    (hfixedFree : ∀ u ∈ W, (∀ k ∈ K, ⁅u,k⁆ ∈ centralInvolutions T) →
      u ∈ centralInvolutions T) :
    let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧
      suitableQuotientCentralizer h u = S ∧
      ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G) ∧
      (∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer h u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (H ⊓ centralizer ({u} : Set G)) ∧
      normalizer (((T : Subgroup G) ⊓ centralizer ({u} : Set G) : Subgroup G) : Set G) = S ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
        (centralizer ({u} : Set G)) ∧
      ¬∃ S' : Sylow 2 G, (S' : Subgroup G) ≤ centralizer ({u} : Set G) := by
  classical
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  have h : D.Hypothesis := source_rankTwo_f9_hypothesis
    hG T hempty hM hunique hmany hcard e hab H hH
  let : IsElementaryAbelian 2 D.UH := h.UH_elementary_of_V_le_QH
    ((le_conjugateSpanBy D.V D.H).trans h.UH_le_QH)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (show W ≤ D.UH from hWU)
  obtain ⟨u,hu,huz,huf⟩ := Theory.GroupAction.exists_nonidentity_fixed_modulo S W
    (centralInvolutions T) (T.isPGroup'.to_le hST) hSW
    (hST.trans (le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T))) hZW
  have hmove : ∃ k ∈ K, ⁅u,k⁆ ∉ centralInvolutions T := by
    by_contra hn
    push Not at hn
    exact huz (hfixedFree u hu hn)
  obtain ⟨heq,hm,hp,hl⟩ := source_suitable_of_separated_support
    hG T hempty hM hunique hmany hcard e hab H hH
      K W S hK hWU hZW.le hKW hST hindex hU3 hseparate u hu huf hmove
  refine ⟨u,hu,elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu,
    fun he => huz (he ▸ one_mem _),heq,hm,hp,hl,?_⟩
  have hn := source_suitable_normalizer_of_local_normalizer
    hG T hempty hM hunique hmany hcard e hab H hH u (hWU hu)
      (by rwa [heq]) hm hp (by rwa [heq])
  simpa only [heq] using hn

end CFSG.Quasithin.Chapter14.Section06
