module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.PairGeometry
public import Theory.GroupTheory.CentralOverlapSupportMovement

/-!
# Suitability from covering supports that overlap in fixed points

The intersection of the two covering supports may contain more than Z.
It suffices that the intersection centralize the perfect component. The
three-subgroups argument prevents cancellation of its movement, and the
original central-line quotient centralizer is still exactly S. Thus all
(U0)--(U3) follow on the literal terminal group and section.

This is a conditional source implication, not module recognition or a proof
of 14.6.22. Its hatted-image input is exactly the weaker directness supplied
by F.9.18; the component modules and their source normalizers remain to be
constructed. Source: Aschbacher--Smith, printed pp.325,1038--1039.
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

omit [Finite G] hG hempty hM hunique hmany hcard e hab H hH in
private theorem square_one_cases (u : G) (hu2 : u ^ 2 = 1)
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
S-coset has a K-invariant support whose intersection with W centralizes K. -/
theorem source_suitable_of_central_overlap
    (K W S : Subgroup G) [Group.IsPerfect K]
    (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hWU : W ≤ conjugateSpanBy (localModule T M) H)
    (hZW : centralInvolutions T ≤ W)
    (hKW : K ≤ normalizer (W : Set G))
    (hST : S ≤ (T : Subgroup G)) (hindex : S.relIndex (T : Subgroup G) = 2)
    (hU3 : Mc ⊓ normalizer (S : Set G) = (T : Subgroup G))
    (hseparate : ∀ t ∈ (T : Subgroup G), t ∉ S →
      W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer (K : Set G) ∧
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
  have hmove : ¬ K ≤ centralizer ({u} : Set G) := by
    intro hc
    obtain ⟨k,hk,hkz⟩ := hmoved
    apply hkz
    rw [commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_centralizer_singleton_iff.mp (hc hk)).symm]
    exact one_mem _
  have hSle : S ≤ suitableQuotientCentralizer h u := by
    intro s hs
    refine ⟨hST hs,(h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mpr ?_⟩
    refine ⟨h.T_le_H (hST hs),?_⟩
    intro a ha
    rcases square_one_cases u hu2 a ha with rfl | rfl
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
    have htW'Z : centralInvolutions T ≤ W.map (MulAut.conj t⁻¹).toMonoidHom := by
      intro z hz
      have hc := (le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T))
        ((T : Subgroup G).inv_mem ht) z hz
      have he : (MulAut.conj t⁻¹) z = z := by
        change t⁻¹ * z * (t⁻¹)⁻¹ = z
        rw [hc.symm,mul_inv_cancel_right]
      exact he ▸ mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom (hZW hz)
    have huW' : u ∈ W.map (MulAut.conj t⁻¹).toMonoidHom := by
      have hh := (W.map (MulAut.conj t⁻¹).toMonoidHom).mul_mem
        (htW'Z hz) (mem_map_of_mem (MulAut.conj t⁻¹).toMonoidHom huW)
      simpa [commutatorElement_def,MulAut.conj_apply,mul_assoc] using hh
    have huC := (hseparate t ht htS).1 ⟨huW,huW'⟩
    exact hmove (fun k hk => mem_centralizer_singleton_iff.mpr (huC k hk))
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
    have hm := product_not_centralized_of_central_intersection K W W'
      hKW (hseparate t ht htS).2 hWW' (hseparate t ht htS).1 u
      ((MulAut.conj t⁻¹) u) hu2 huW (mem_map_of_mem _ huW) hmove
    exact source_core_moves_of_fitting_moves hG T hempty hM hunique hmany hcard e hab
      H hH K hK _ (D.UH.mul_mem hu (hW'U (mem_map_of_mem _ huW))) hm
  · apply source_suitable_local_sylow hG T hempty hM hunique hmany hcard e hab H hH u hu
    rwa [heq]


omit H hH
namespace ComponentSupports
open Representation Representation.OneCohomology

/-- The support geometry with component-fixed overlap allowed.
The branch producer must identify W and S with the literal source supports
and their normalizers; this record alone asserts no component classification. -/
structure CentralOverlapGeometry (T : Sylow 2 G) (Mc U K W S : Subgroup G) : Prop where
  fitting : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc
  support_le : W ≤ U
  point_le : centralInvolutions T ≤ W
  normalized : K ≤ normalizer (W : Set G)
  sylow_le : S ≤ (T : Subgroup G)
  index : S.relIndex (T : Subgroup G) = 2
  local_normalizer : Mc ⊓ normalizer (S : Set G) = (T : Subgroup G)
  separated : ∀ t ∈ (T : Subgroup G), t ∉ S →
    W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer (K : Set G) ∧
    K ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G)

omit [Finite G] hG hempty hM hunique hmany hcard e hab in
/-- A moved pair of supports gives the literal normalizer, its index two,
and all the separated conjugates in the right-conjugation source convention. -/
theorem centralOverlapGeometry_of_pair
    (T : Sylow 2 G) (Mc U K W W' : Subgroup G)
    (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hWU : W ≤ U) (hZW : centralInvolutions T ≤ W)
    (hKW : K ≤ normalizer (W : Set G))
    (hKW' : K ≤ normalizer (W' : Set G))
    (hsep : W ⊓ W' ≤ centralizer (K : Set G))
    (hpair : ∀ t ∈ (T : Subgroup G), W.map (MulAut.conj t).toMonoidHom = W ∨
      W.map (MulAut.conj t).toMonoidHom = W')
    (x : G) (hx : x ∈ (T : Subgroup G))
    (hmove : W.map (MulAut.conj x).toMonoidHom ≠ W)
    (hlocal : Mc ⊓ normalizer (((T : Subgroup G) ⊓ normalizer (W : Set G) : Subgroup G) : Set G) =
      (T : Subgroup G)) :
    CentralOverlapGeometry T Mc U K W ((T : Subgroup G) ⊓ normalizer (W : Set G)) := by
  refine ⟨hK,hWU,hZW,hKW,inf_le_left,?_,hlocal,?_⟩
  · rw [inf_relIndex_left]
    exact normalizer_relIndex_eq_two_of_pair (T : Subgroup G) W W' hpair x hx hmove
  · intro t ht htS
    have hn : W.map (MulAut.conj t⁻¹).toMonoidHom ≠ W := by
      intro he
      have hi : t⁻¹ ∈ normalizer (W : Set G) := mem_normalizer_iff_map_conj_eq.mpr he
      have htN : t ∈ normalizer (W : Set G) := by
        simpa only [inv_inv] using (normalizer (W : Set G)).inv_mem hi
      exact htS ⟨ht,htN⟩
    have he := (hpair t⁻¹ ((T : Subgroup G).inv_mem ht)).resolve_left hn
    rw [he]
    exact ⟨hsep,hKW'⟩

/-- A vector in the actual covering section supplies all suitability clauses.
The actor A may be the support normalizer, so W need not be Mc-invariant. -/
theorem source_exists_of_central_overlap_section_vector
    (K W S A : Subgroup G) [Group.IsPerfect K]
    (d : CentralOverlapGeometry T Mc (conjugateSpanBy (localModule T M) Mc) K W S)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) A V)
    (c : BinaryConjugationSection A W (centralInvolutions T) τ)
    (hSA : S ≤ A) (v : V)
    (hfixed : ∀ (s : G) (hs : s ∈ S), τ ⟨s,hSA hs⟩ v = v)
    (hmoved : v ∉ fixed (τ.comp (K.subgroupOf A).subtype)) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧ suitableQuotientCentralizer h u = S ∧
      Suitable h Mc u := by
  let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  obtain ⟨u,hu,huf,hum⟩ := c.exists_fixed_moving_lift K S hSA v hfixed hmoved
  obtain ⟨heq,hm,hp,hl⟩ := source_suitable_of_central_overlap
    hG T hempty hM hunique hmany hcard e hab Mc
      (terminal_outside hG T hempty hM hunique hmany hcard e)
      K W S d.fitting d.support_le d.point_le d.normalized
      d.sylow_le d.index d.local_normalizer d.separated u hu huf hum
  let : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc) :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hu2 : u ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (p := 2) u (d.support_le hu)
  have hune : u ≠ 1 := by
    rintro rfl
    obtain ⟨k,_,hk⟩ := hum
    exact hk (by simp)
  refine ⟨u,hu,hu2,hune,heq,d.support_le hu,hl,?_,hm,hp,?_⟩
  · change (suitableQuotientCentralizer h u).relIndex (T : Subgroup G) = 2
    rw [show suitableQuotientCentralizer h u = S from heq]
    exact d.index
  · change Mc ⊓ normalizer (suitableQuotientCentralizer h u : Set G) = _
    rw [show suitableQuotientCentralizer h u = S from heq]
    exact d.local_normalizer

end ComponentSupports
end CFSG.Quasithin.Chapter14.Section06
