module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.Exceptional
public import Theory.GroupTheory.NormalSylowQuotientAction.MarkedLift
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.SpecificGroups.SymmetricSix.Parabolics.SolvableGeneration

/-!
# The actual diagram action of a normal terminal component

For binary L₃ and A₆, the two maximal parabolics over a Sylow two-subgroup
are solvable and generate the group. The original normalizer acts through
the marked component quotient and permutes exactly this pair. If it fixed
both, their lifted joins with T would be solvable, so 14.6.18 would place
both in M. Generation would put K in M, contrary to the normal-component
reduction 14.6.1(4). Hence an actual element of T exchanges the two nodes.

For A₆ these are the duad and syntheme parabolics. This proves diagram
movement rather than merely non-inner action. Its three-rank also forces
relative normality, so the final A₆ theorem retains no normality premise.
The quotient action and its model marking are unchanged throughout.

Source: Aschbacher--Smith 14.6.20, printed p.1037. The individual model
isomorphisms and exchanged-component diagram branch remain with
qt-e-suitable-component-supports; original 14.6.18 remains with
qt-e-14625-source. No natural-module recognition is assumed or asserted.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Subgroup.NormalSylowQuotientAction
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Theory.SpecificGroups.SymmetricSix
variable {G B : Type*} [Group G] [Finite G] [Group B] [Finite B]

omit [Finite B] in
private theorem marked_solvable_le_image
    (T : Sylow 2 G) (M : Subgroup G)
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (T : Set G))
    (K : Subgroup G) (hKH : K ≤ H)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* B) (J : Subgroup B) [Group.IsSolvable J]
    (hinv : ∀ s : T, J.map (markedCoreAction 2 K eK ⟨s,hn s.property⟩).toMonoidHom = J) :
    J ≤ (M.subgroupOf K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) := by
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  let Jpre := J.comap q
  let Y := Jpre.map K.subtype ⊔ (T : Subgroup G)
  have hYover : Y ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T le_sup_right
      (sup_le ((map_subtype_le Jpre).trans hKH) hH.2) hH
  have hs : Group.IsSolvable Y := solvable_lift_sup_of_marked_invariant 2 T K hn eK J hinv
  have hpre : Jpre ≤ M.subgroupOf K :=
    (map_le_iff_le_comap).mp (le_sup_left.trans (hsolv Y hYover hs))
  have hm := map_mono (f := q) hpre
  rwa [map_comap_eq_self_of_surjective
    (eK.surjective.comp (QuotientGroup.mk'_surjective _))] at hm

omit [Finite B] in
private theorem pair_swap_of_solvable_placement
    (T : Sylow 2 G) (M : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOver G (T : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hout : ¬ K ≤ M)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* B)
    (P : Sylow 2 K) (hP : (P : Subgroup K) = (T : Subgroup G).subgroupOf K)
    (J L : Subgroup B) [Group.IsSolvable J] [Group.IsSolvable L]
    (hJ : IsCoatom J) (hL : IsCoatom L) (hne : J ≠ L) (hsup : J ⊔ L = ⊤)
    (hPJ : (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ≤ J)
    (hPL : (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ≤ L)
    (hall : ∀ N : Subgroup B, IsCoatom N →
      (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ≤ N → N = J ∨ N = L) :
    ∃ s : T, J.map (markedCoreAction 2 K eK ⟨s,hn s.property⟩).toMonoidHom = L ∧
      L.map (markedCoreAction 2 K eK ⟨s,hn s.property⟩).toMonoidHom = J := by
  let a (s : T) := markedCoreAction 2 K eK ⟨s,hn s.property⟩
  have hm (s : T) (N : Subgroup B) (hN : IsCoatom N)
      (hPN : (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ≤ N) :
      N.map (a s).toMonoidHom = J ∨ N.map (a s).toMonoidHom = L := by
    apply hall _ (((a s).mapSubgroup.isCoatom_iff N).mpr hN)
    have hh := map_mono (f := (a s).toMonoidHom) hPN
    rwa [markedCoreAction_preserves_sylow 2 T K hn eK P hP s] at hh
  have hmove : ∃ s : T, J.map (a s).toMonoidHom ≠ J := by
    by_contra! hf
    have hl (s : T) : L.map (a s).toMonoidHom = L := by
      rcases hm s L hL hPL with he | he
      · exact (hne ((a s).mapSubgroup.injective ((hf s).trans he.symm))).elim
      · exact he
    have hJM := marked_solvable_le_image T M hsolv H hH K hKH hn eK J hf
    have hLM := marked_solvable_le_image T M hsolv H hH K hKH hn eK L hl
    let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
    have hmap : (M.subgroupOf K).map q = ⊤ := by
      apply top_unique
      rw [←hsup]
      exact sup_le hJM hLM
    have hker : q.ker = pCore 2 K := by
      rw [MonoidHom.ker_comp_of_injective _ _ eK.injective, QuotientGroup.ker_mk']
    have hkM : q.ker ≤ M.subgroupOf K := by
      rw [hker]
      apply (pCore_isPGroup.le_sylow_of_normal P).trans
      rw [hP]
      exact fun _ hx => hTM hx
    have hMtop : M.subgroupOf K = ⊤ := by
      have hh := congrArg (Subgroup.comap q) hmap
      rwa [comap_map_eq,sup_eq_left.mpr hkM,comap_top] at hh
    exact hout fun k hk => show (⟨k,hk⟩ : K) ∈ M.subgroupOf K from hMtop ▸ mem_top _
  obtain ⟨s,hs⟩ := hmove
  have he : J.map (a s).toMonoidHom = L := (hm s J hJ hPJ).resolve_left hs
  refine ⟨s,he,?_⟩
  rcases hm s L hL hPL with hl | hl
  · exact hl
  · exact (hne ((a s).mapSubgroup.injective (he.trans hl.symm))).elim

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)

include hG hempty hM hunique hmany hcard e hab in
/-- A component normal in an outside H remains outside M, by the source
normal two-perfect subgroup reduction. Normality is relative to H. -/
theorem source_normal_component_not_le
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : (K.subgroupOf H).Normal) : ¬ K ≤ M := by
  let : Group.IsPerfect (K.subgroupOf H) := hK.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKH).toMonoidHom) (subgroupOfEquivOfLe hKH).surjective
  have hp : IsPPerfect 2 K := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  have hne : K ≠ ⊥ := by
    rintro rfl
    exact hK.ne_bot (by simp)
  have hout := source_lemma_14_6_1_4 hG T hempty hM hunique hmany hcard e hab H hH
    K hKH ((normal_subgroupOf_iff_le_normalizer hKH).mp hn) hp hne
  exact fun hk => hout.2 (sup_le hk hM.1.2)

/-- A nontrivial action on the two actual parabolics over the quotient Sylow.
This retains the same model isomorphism and the induced normalizer action. -/
@[expose] def QuotientParabolicSwap (T : Sylow 2 G) (K : Subgroup G)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* B) : Prop :=
  ∃ P : Sylow 2 K, (P : Subgroup K) = (T : Subgroup G).subgroupOf K ∧
    ∃ J L : Subgroup B, IsCoatom J ∧ IsCoatom L ∧ J ≠ L ∧
      J ⊓ L = (P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ∧
      (∀ N : Subgroup B, IsCoatom N →
        ((P : Subgroup K).map (eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) ≤ N ↔
          N = J ∨ N = L)) ∧
      ∃ s : T, J.map (markedCoreAction 2 K eK ⟨s,hn s.property⟩).toMonoidHom = L ∧
        L.map (markedCoreAction 2 K eK ⟨s,hn s.property⟩).toMonoidHom = J

include hG hempty hM hunique hmany hcard e hab hsolv in
/-- In the normal binary L₃ branch, an original Sylow element exchanges the
literal point and line parabolics of the marked quotient. -/
theorem source_normal_l3_parabolic_swap
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKN : (K.subgroupOf H).Normal)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL) :
    QuotientParabolicSwap T K
      (hH.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hKN)) eK := by
  let hn := hH.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hKN)
  obtain ⟨P,hP⟩ := intersection_sylow T K hn
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  let Pq := P.mapSurjective hq
  obtain ⟨J,L,hJ,hL,hne,hi,hcardJ,hcardL,hall⟩ := Matrix.PSL3Two.sylow_parabolics Pq
  have hPJ : (Pq : Subgroup Matrix.PSL3Two.PSL) ≤ J := hi ▸ inf_le_left
  have hPL : (Pq : Subgroup Matrix.PSL3Two.PSL) ≤ L := hi ▸ inf_le_right
  have hsup : J ⊔ L = ⊤ := hJ.2 _ (lt_of_le_of_ne le_sup_left (by
    intro he
    have hh : L ≤ J := sup_eq_left.mp he.symm
    exact hne ((eq_of_le_of_not_lt hh (fun hlt => hJ.1 (hL.2 J hlt))).symm)))
  have hpc : Nat.card (Pq : Subgroup Matrix.PSL3Two.PSL) = 8 :=
    (Nat.card_congr (Pq.equiv Matrix.PSL3Two.borelSylow).toEquiv).trans Matrix.PSL3Two.card_borel
  have hindexJ : (Pq : Subgroup Matrix.PSL3Two.PSL).relIndex J = 3 := by
    have hh := ((Pq : Subgroup Matrix.PSL3Two.PSL).subgroupOf J).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hPJ).toEquiv,hpc,hcardJ] at hh
    change 8 * (Pq : Subgroup Matrix.PSL3Two.PSL).relIndex J = 24 at hh
    omega
  have hindexL : (Pq : Subgroup Matrix.PSL3Two.PSL).relIndex L = 3 := by
    have hh := ((Pq : Subgroup Matrix.PSL3Two.PSL).subgroupOf L).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hPL).toEquiv,hpc,hcardL] at hh
    change 8 * (Pq : Subgroup Matrix.PSL3Two.PSL).relIndex L = 24 at hh
    omega
  let : Group.IsNilpotent (Pq : Subgroup Matrix.PSL3Two.PSL) := Pq.isPGroup'.isNilpotent
  let : Group.IsSolvable J := (Pq : Subgroup Matrix.PSL3Two.PSL).isSolvable_of_relIndex_le_four J (by omega)
  let : Group.IsSolvable L := (Pq : Subgroup Matrix.PSL3Two.PSL).isSolvable_of_relIndex_le_four L (by omega)
  refine ⟨P,hP,J,L,hJ,hL,hne,hi,hall,?_⟩
  exact pair_swap_of_solvable_placement T M hM.1.2 hsolv H hH.1 K hKH
    (source_normal_component_not_le hG T hempty hM hunique hmany hcard e hab H hH K hKH hK hKN)
    hn eK P hP J L hJ hL hne hsup hPJ hPL (fun N hN hp => (hall N hN).mp hp)

include hG hempty hM hunique hmany hcard e hab hsolv in
/-- In the normal A₆ branch the action exchanges duad and syntheme parabolics.
Thus the conclusion detects the diagram action, not just an outer automorphism. -/
theorem source_normal_a6_parabolic_swap
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKN : (K.subgroupOf H).Normal)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    QuotientParabolicSwap T K
      (hH.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hKN)) eK := by
  let hn := hH.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hKN)
  obtain ⟨P,hP⟩ := intersection_sylow T K hn
  let q := eK.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := eK.surjective.comp (QuotientGroup.mk'_surjective _)
  let Pq := P.mapSurjective hq
  obtain ⟨g,hg,hall⟩ := a6_coatoms_over_sylow Pq
  let a := (MulAut.conj g).mapSubgroup
  let J := a a6DuadStabilizer
  let L := a a6SynthemeStabilizer
  have hJ := (hall J).mpr (Or.inl rfl)
  have hL := (hall L).mpr (Or.inr rfl)
  have hne : J ≠ L := fun he => Theory.SpecificGroups.SymmetricSix.a6_parabolics_ne (a.injective he)
  have hi : J ⊓ L = (Pq : Subgroup (alternatingGroup (Fin 6))) := by
    rw [show J = a _ from rfl, show L = a _ from rfl, ← a.map_inf,
      Theory.SpecificGroups.SymmetricSix.a6_parabolics_inf,hg]
  have hs : J ⊔ L = ⊤ := by
    rw [show J = a _ from rfl, show L = a _ from rfl, ← a.map_sup,
      Theory.SpecificGroups.SymmetricSix.a6_parabolics_sup,a.map_top]
  let : Group.IsSolvable J := Group.isSolvable_of_surjective
    ((MulAut.conj g).toMonoidHom.subgroupMap_surjective _)
  let : Group.IsSolvable L := Group.isSolvable_of_surjective
    ((MulAut.conj g).toMonoidHom.subgroupMap_surjective _)
  have he : ∀ N : Subgroup (alternatingGroup (Fin 6)), IsCoatom N →
      ((Pq : Subgroup (alternatingGroup (Fin 6))) ≤ N ↔ N = J ∨ N = L) := by
    intro N hN
    exact ⟨fun hp => (hall N).mp ⟨hN,hp⟩,fun hh => ((hall N).mpr hh).2⟩
  refine ⟨P,hP,J,L,hJ.1,hL.1,hne,hi,he,?_⟩
  exact pair_swap_of_solvable_placement T M hM.1.2 hsolv H hH.1 K hKH
    (source_normal_component_not_le hG T hempty hM hunique hmany hcard e hab H hH K hKH hK hKN)
    hn eK P hP J L hJ.1 hL.1 hne hs hJ.2 hL.2 (fun N hN hp => (hall N).mp ⟨hN,hp⟩)
include hG hempty hM hunique hmany hcard e hab hsolv in
/-- Every actual A₆ component is normal by the rank bound and has nontrivial
diagram action on its marked quotient. No separate normality premise remains. -/
theorem source_a6_parabolic_swap
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    ∃ hn : H ≤ normalizer (K : Set G), QuotientParabolicSwap T K (hH.1.2.trans hn) eK := by
  have hr : 2 ≤ primeRank 3 (K ⧸ pCore 2 K) := by
    rw [primeRank_congr 3 eK]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  have hn := source_component_normal_of_quotient_threeRank
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hr
  exact ⟨hn, source_normal_a6_parabolic_swap hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK ((normal_subgroupOf_iff_le_normalizer hKH).mpr hn) eK⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Classification.Sieve
