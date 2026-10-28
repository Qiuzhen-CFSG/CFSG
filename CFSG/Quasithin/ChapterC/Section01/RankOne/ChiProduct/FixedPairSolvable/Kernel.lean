module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.Solvable.Baumann
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.AlphaOrbit
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable
open ChapterB
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V}

theorem residual_disjoint_two (d : SolvableFFFactors ρ)
    (hr : pResidual 2 G ≤ offenderSubgroup ρ) (A : Subgroup G) (hA : IsPGroup 2 A) :
    Disjoint (pResidual 2 G) A := by
  classical
  apply Subgroup.disjoint_def.mpr
  intro x hxR hxA
  let y : offenderSubgroup ρ := ⟨x,hr hxR⟩
  have hz : d.groupProduct.symm y = 1 := by
    funext i
    let f : pResidual 2 G →* d.factor i :=
      (Pi.evalMonoidHom (fun j => d.factor j) i).comp
        (d.groupProduct.symm.toMonoidHom.comp (inclusion hr))
    have hm := map_pResidual_le 2 f
    rw [(pResidual_eq_top_iff 2 _).mpr (isPPerfect_pResidual 2)] at hm
    have hi : f ⟨x,hxR⟩ ∈ pResidual 2 (d.factor i) := hm (mem_map_of_mem f (mem_top _))
    let S : Sylow 2 (d.factor i) := Classical.choice inferInstance
    have hcS : Nat.card S = 2 := by
      have hh := d.factorSylow_card i S
      rwa [SolvableFFFactors.factorSylow,card_map_of_injective (d.factor i).subtype_injective] at hh
    have ho := S.odd_card_twoResidual_of_isCyclic (isCyclic_of_prime_card hcS)
    have hcop : Nat.Coprime 2 (orderOf (f ⟨x,hxR⟩)) :=
      (Nat.coprime_two_left.mpr ho).of_dvd_right
        ((pResidual 2 (d.factor i)).orderOf_dvd_natCard hi)
    obtain ⟨n,hn⟩ := hA.exists_orderOf_eq_pow (⟨x,hxA⟩ : A)
    have hd : orderOf (f ⟨x,hxR⟩) ∣ 2 ^ n := by
      calc
        orderOf (f ⟨x,hxR⟩) ∣ orderOf (⟨x,hxR⟩ : pResidual 2 G) := orderOf_map_dvd f _
        _ = orderOf x := (Subgroup.orderOf_coe _).symm
        _ = 2 ^ n := (Subgroup.orderOf_coe (⟨x,hxA⟩ : A)).trans hn
    have he : f ⟨x,hxR⟩ = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes (hcop.pow_left n) hd dvd_rfl)
    exact he
  have hy : y = 1 := d.groupProduct.symm.injective (hz.trans (map_one _).symm)
  exact congrArg Subtype.val hy

variable {H : Type*} [Group H] [Finite H]

omit [Finite G] [Finite H] in
theorem baumann_join_kernel_centralizes_alpha
    (T : Sylow 2 G) (U : Subgroup G) (q : G →* H)
    (hk : q.ker = centralizer (U : Set G))
    (ha : thompsonAlpha (T : Subgroup G) ≤ U ⊔
      (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)))
    (hd : Disjoint ((pResidual 2 G).map q) ((baumann (T : Subgroup G)).map q)) :
    (pResidual 2 G ⊔ baumann (T : Subgroup G)) ⊓ q.ker ≤
      centralizer (thompsonAlpha (T : Subgroup G) : Set G) := by
  rintro x ⟨hx,hkX⟩
  obtain ⟨r,hr,b,hb,rfl⟩ := mem_sup_of_normal_left.mp hx
  have he : q r * q b = 1 := (map_mul q r b).symm.trans hkX
  have hrq : q r = 1 := Subgroup.disjoint_def.mp hd
    (mem_map_of_mem q hr) (by rw [eq_inv_of_mul_eq_one_left he]; exact inv_mem (mem_map_of_mem q hb))
  have hrc : r ∈ centralizer (U : Set G) := hk ▸ hrq
  have hrA : r ∈ centralizer (thompsonAlpha (T : Subgroup G) : Set G) := by
    apply centralizer_le ha
    have hz : U ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ≤
        centralizer ({r} : Set G) := by
      apply sup_le
      · intro u hu z hz
        have hez : z = r := Set.mem_singleton_iff.mp hz
        subst z
        exact (hrc u hu).symm
      · intro u hu z hz
        have hez : z = r := Set.mem_singleton_iff.mp hz
        subst z
        exact hu.2 r hr
    intro u hu
    exact (hz hu r (Set.mem_singleton r)).symm
  exact mul_mem hrA hb.2

variable [FiniteDimensional (ZMod 2) V]

theorem solvable_baumann_kernel_and_layer
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (q : G →* H) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G)) (hcore : pCore 2 H = ⊥)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hrank : primeRank 3 G ≤ 2) (hs : Group.IsSolvable H) :
    let α := NormalElementaryQuotient.representation U q hq hk
    ∃ _d : ThreeConjugates.SolvableFFStructure α,
      (baumann (T : Subgroup G)).map q ≤ offenderSubgroup α ∧
      Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
        (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∧
      (pResidual 2 G ⊔ baumann (T : Subgroup G)) ⊓ q.ker ≤
        centralizer (thompsonAlpha (T : Subgroup G) : Set G) := by
  let α := NormalElementaryQuotient.representation U q hq hk
  obtain ⟨d,hc,_,ht⟩ := RankOneBaumann.SolvableSource.solvable_factors T hP U q hq hk hcore hs hJ hrank
  have hf := NormalElementaryQuotient.representation_injective U q hq hk
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hk ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T : Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := (isFFModule_iff_quadraticRatio_le_one α).mpr d.ratio_one.le
  have hr := (offender_generation (T.mapSurjective hq) hp α hff hcore).1
  have hBY : (baumann (T : Subgroup G)).map q ≤ offenderSubgroup α := by
    rcases hc with hc | hc
    · let j := d.toSolvableFFFactors.singleAmbientHom hc
      have hji := d.toSolvableFFFactors.singleAmbientHom_injective hf hcore hr hc
      intro a _
      obtain ⟨y,hy⟩ := (d.toSolvableFFFactors.singleActorCoordinates hc).surjective (j a)
      have hy' : j y = j a := (d.toSolvableFFFactors.singleAmbientHom_factor hc y).trans hy
      exact hji hy' ▸ y.property
    · exact (RankOneBaumann.SolvableSource.solvable_pair_images_of_factors
        T hP U q hq hk hcore (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)) hJ d hc ht).2.le.trans inf_le_right
  have hba : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
        (pResidual 2 G ⊔ baumann (T : Subgroup G)) ∧
      thompsonAlpha (T : Subgroup G) =
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ⊔
        (U ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) := by
    rcases hc with hc | hc
    · exact RankOneBaumann.SolvableSource.solvable_single_baumann_of_factors T hP U hU q hq hk hcore hJ d hc
    · exact RankOneBaumann.SolvableSource.solvable_pair_baumann_of_factors T hP U hU q hq hk hcore hJ d hc ht
  refine ⟨d,hBY,hba.1,baumann_join_kernel_centralizes_alpha T U q hk ?_ ?_⟩
  · rw [hba.2]
    apply sup_le
    · apply le_sup_of_le_right
      exact le_inf le_sup_left inf_le_right
    · exact inf_le_left.trans le_sup_left
  · rw [map_pResidual_of_surjective 2 q hq]
    exact residual_disjoint_two d.toSolvableFFFactors hr _ ((T.isPGroup'.to_le inf_le_left).map q)

omit [Finite H] in
theorem restricted_kernel_centralizes_omegaClosure
    (T : Sylow 2 G) (q : G →* H)
    (hk : (pResidual 2 G ⊔ baumann (T : Subgroup G)) ⊓ q.ker ≤
      centralizer (thompsonAlpha (T : Subgroup G) : Set G))
    (N : Subgroup G) (hN : N ≤ pResidual 2 G ⊔ baumann (T : Subgroup G))
    (S : Sylow 2 N) (hS : (S : Subgroup N).map N.subtype = baumann (T : Subgroup G)) :
    (q.comp N.subtype).ker ≤ centralizer
      (normalClosure (omegaOneCenterAmbient (S : Subgroup N) : Set N) : Set N) := by
  have hz : (omegaOneCenterAmbient (S : Subgroup N)).map N.subtype =
      thompsonAlpha (T : Subgroup G) := by
    rw [←omegaOneCenterAmbient_map_injective N.subtype N.subtype_injective,hS]
    exact SelectedRankOne.baumann_omega_eq_alpha _
  apply le_centralizer_iff.mp
  apply normalClosure_le_normal
  apply le_centralizer_iff.mpr
  intro x hx z hz'
  apply Subtype.ext
  exact hk ⟨hN x.property,hx⟩ z (hz ▸ mem_map_of_mem N.subtype hz')
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable
