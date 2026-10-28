module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankFiveNaturalSixFixedVector
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankFiveNaturalSixCrossingImage
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicComponent.RankFiveNaturalSixPlacement.ActorChoice

/-!
# Elimination of the original rank-five alternating-six branch

The second parabolic supplies the fixed all-ones vector in the original H-module.
Maximality of the Sylow intersection places the suitable involution in the same
core and identifies it with this vector. A plane-centralizing element of T₀/Tᵤ
conjugates it to the complementary duad. The two actual point-centralizer spans
force the conjugate core's image into that transposition group. The full-core
kernel calculation then contradicts its proved escape from O₂(I).

All marked vectors and spans use one coordinate map and the original ambient
conjugation. No independent placement, image or fusion premise remains.
Source: Aschbacher–Smith, 14.6.10(5), printed pp.1029–1030.
-/

public section
open Subgroup BinaryPermutation Module Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))

include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal


open RankFiveNaturalSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags

/-- The full rank-five natural-six branch of the original parabolic argument
is impossible. All plane marks, fixed-vector placement and crossing premises
are constructed on the same source component. -/
theorem source_parabolic_not_rankFive
    (I I2 K : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2I : I2 ≤ I) (hI2H : I2 ≤ H)
    (hI2quot : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hKI : K ≤ I) (hKN : (K.subgroupOf I).Normal)
    (hfirst : (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ≤ K)
    (hgen : K ⊔ ((T : Subgroup G) ⊓ I) = I)
    (hblock : ChapterC.IsAlternatingBlock K 6)
    (hW : Nat.card (sourceModule K) = 32)
    (hVW : localModule T M ≤ sourceModule K)
    (hpreferred : (T : Subgroup G) ⊓ I = (T : Subgroup G) ⊓ centralizer ({u} : Set G) →
      I ≤ centralizer ({u} : Set G)) : False := by
  let h := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
  let S0 := (T : Subgroup G) ⊓ I
  let W := sourceModule K
  have hIK : I ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hKI).mp hKN
  have hSN : S0 ≤ normalizer (K : Set G) := inf_le_right.trans hIK
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
  obtain ⟨E,f,he,hA,halign,hV,hZ⟩ := source_parabolic_rankFive_coordinates
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    I hI.1 hout K hKI hKN hfirst hblock hW hVW
  have hker := restrictedActor_kernel I K S0 hKI hIK hblock.2.1
    (T.isPGroup'.to_le inf_le_left) hgen E f he
  have hArange := alternating_le_restricted_range I K hKI hIK f hA
  let z := E.symm (Multiplicative.ofAdd CoreCrossing.z)
  let w := E.symm (Multiplicative.ofAdd CoreCrossing.w)
  have hz : (E z).toAdd = CoreCrossing.z := by simp [z]
  have hw : (E w).toAdd = CoreCrossing.w := by simp [w]
  have hzZ : z.val ∈ centralInvolutions T := by
    apply (mem_sourceImage W E (centralInvolutions T) z).mp
    rw [hZ,hz]
    exact Submodule.subset_span (Set.mem_singleton _)
  have hI2z : I2 ≤ centralizer ({z.val} : Set G) := by
    intro i hi
    exact mem_centralizer_singleton_iff.mpr (h.H_centralizes (hI2H hi) z hzZ).symm
  obtain ⟨a,ha,ha1,hIa,_⟩ := source_fixed_vector I K S0 I2 (localModule T M)
    hIK hI2I hSI2 hSyl E f he hker hArange hI2quot hVW hV z hz hI2z
  obtain ⟨hTI,hIu,huW⟩ := RankFiveNaturalSixPlacement.source_fixed_core_vector_placement
    hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
    I W hI hout hpreferred a (conjugateSpanBy_mono le_rfl hI2H ha) a.property ha1 hIa
  have hu1 : u ≠ 1 := by
    intro huone
    apply hmove
    intro q hq
    rw [huone]
    exact mem_centralizer_singleton_iff.mpr (by simp)
  let uW : W := ⟨u,huW⟩
  have hucoord := source_fixed_core_coordinate K E f he hA uW hu1 (hKI.trans hIu)
  obtain ⟨t,ht,htV,htI,htsq,htS,hescape⟩ :=
    RankFiveNaturalSixPlacement.source_plane_centralizing_block_escape
      hG T hempty hM hunique hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal
      I K hI hTI hKI hIK hgen hblock.2.1
  have hWQ : W ≤ I.pCoreIn 2 := (map_mono ChapterC.blockU_le_core).trans
    (pCoreIn_mono_of_normalizes hKI hIK)
  have hWS : W ≤ S0 := by
    obtain ⟨SI,hSI⟩ := hSyl
    have hh := pCoreIn_le_sylow I SI
    rw [hSI] at hh
    exact hWQ.trans hh
  have hconjS (r : G) (hr : r ∈ normalizer (S0 : Set G)) :
      W.map (MulAut.conj r).toMonoidHom ≤ S0 :=
    (map_mono hWS).trans (mem_normalizer_iff_map_conj_eq.mp hr).le
  have hBN := (hconjS t htS).trans hSN
  have hpreN := (hconjS t⁻¹ ((normalizer (S0 : Set G)).inv_mem htS)).trans hSN
  have hcommZ : ⁅t,u⁆ ∈ centralInvolutions T := by
    have hh := ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp ht.2).2 u (mem_zpowers u)
    rw [←commutatorElement_inv]
    exact (centralInvolutions T).inv_mem hh
  have hcomm1 : ⁅t,u⁆ ≠ 1 := by
    intro hh
    apply htI
    have htu : t ∈ (T : Subgroup G) ⊓ centralizer ({u} : Set G) :=
      ⟨ht.1,mem_centralizer_singleton_iff.mpr (commutatorElement_eq_one_iff_mul_comm.mp hh)⟩
    exact (hTI ▸ htu).2
  have hz1 : z.val ≠ 1 := by
    intro hh
    have hez : z = 1 := Subtype.ext hh
    rw [hez,map_one,toAdd_one] at hz
    exact (by decide : (0 : core (Fin 6)) ≠ CoreCrossing.z) hz
  have hcommz : ⁅t,u⁆ = z.val := by
    obtain ⟨p,_,hp⟩ := (Nat.card_eq_two_iff' (1 : centralInvolutions T)).mp h.point_card
    exact congrArg Subtype.val ((hp ⟨_,hcommZ⟩ (fun hh => hcomm1 (congrArg Subtype.val hh))).trans
      (hp ⟨_,hzZ⟩ (fun hh => hz1 (congrArg Subtype.val hh))).symm)
  have hut : (MulAut.conj t) u ∈ W := by
    rw [conj_eq_commutatorElement_mul,hcommz]
    exact W.mul_mem z.property huW
  have hutcoord : (E ⟨(MulAut.conj t) u,hut⟩).toAdd = CoreCrossing.pairWord 4 5 := by
    have hh : (⟨(MulAut.conj t) u,hut⟩ : W) = z * uW := by
      apply Subtype.ext
      exact (show (MulAut.conj t) u = ⁅t,u⁆ * u from conj_eq_commutatorElement_mul).trans (congrArg (· * u) hcommz)
    rw [hh,map_mul,toAdd_mul,hz,hucoord]
    decide
  have halignS : NaturalGeometry.T0 ≤ (S0.subgroupOf (normalizer (K : Set G))).map f := by
    apply halign.trans
    apply map_mono
    exact subgroupOf_mono (normalizer (K : Set G)) (inf_le_inf_left _ hKI)
  have himage := source_crossing_image_le K S0 (localModule T M) E f he hA hVW hV hWS hSN
    halignS z w hz hw t htS (fun p hp hp1 =>
      source_rankTwo_point_span_conjugate_commute hG T hempty hM hunique hmany hcard e hab
        K p t hp hp1 htV)
  have hcentral := source_crossing_centralizes K E f he uW hucoord t hut hutcoord hBN hpreN
    (fun b hb => himage (mem_map_of_mem f hb))
  have hcore := source_centralizer_eq_core I K S0 hKI hIK hblock.2.1
    (T.isPGroup'.to_le inf_le_left) hgen
  apply hescape
  intro b hb
  have hbI := (hconjS t htS hb).2
  have hbcore : (⟨b,hbI⟩ : I) ∈ pCore 2 I := hcore ▸ hcentral hb
  exact mem_map_of_mem I.subtype hbcore
end CFSG.Quasithin.Chapter14.Section06
