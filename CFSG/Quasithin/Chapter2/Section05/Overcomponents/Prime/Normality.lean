module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.CoreNormality
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.RankTerminal
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.CompanionNormalizer
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.OrbitPerfectActor
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.OrbitRank
public import CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource.PairedResidual

/-!
# Normality of the original source component

At a maximal bad involution the actual index-two kernel gives either the
four-group alternative, which forces component normality, or centrality
on N_S(K). In the latter case the nonnormal companion's Sylow subgroup
cuts out the source graph subgroup. Its involution centralizers normalize
the actual overcomponent, hence the companion normalizes it. Perfectness
and the retained pointwise-fixer calculation then give centralization,
contradicting the original two-local cubic-rank bound. This proves the
bad-involution implication; the already proved paired-residual argument
then supplies original component normality.

Source: Aschbacher–Smith 2.5.19–20, printed pp.562–565.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection OvercomponentsSource CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

private theorem source_no_commuting_three_rank_two_conjugate
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (u : G) (X : Subgroup G)
    (hc : K.map (MulAut.conj u).toMonoidHom ≤ centralizer (X : Set G))
    (hr : 2 ≤ primeRank 3 X) : False := by
  let P := X.map (MulAut.conj u⁻¹).toMonoidHom
  have hPK : P ≤ centralizer (K : Set G) := by
    rintro x ⟨x,hx,rfl⟩ k hk
    have hh := hc (mem_map_of_mem (MulAut.conj u).toMonoidHom hk) x hx
    have he := congrArg (MulAut.conj u⁻¹) hh
    rw [map_mul,map_mul] at he
    change (MulAut.conj u⁻¹) x * (MulAut.conj u⁻¹) ((MulAut.conj u) k) =
      (MulAut.conj u⁻¹) ((MulAut.conj u) k) * (MulAut.conj u⁻¹) x at he
    have heK : (MulAut.conj u⁻¹) ((MulAut.conj u) k) = k := by
      simp [MulAut.conj_apply,mul_assoc]
    rw [heK] at he
    exact he.symm
  have hrP : 2 ≤ primeRank 3 P := by
    rwa [primeRank_equiv 3 ((MulAut.conj u⁻¹).subgroupMap X)] at hr
  exact source_no_commuting_three_rank_two c hG hempty hgen hb P hPK hrP

/-- Original 2.5.19(1): failure of component persistence forces normality
of the original component in H. -/
theorem source_bad_involution_component_normal
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (i₀ : G)
    (hi₀ : BadInvolution ((S : Subgroup H).map H.subtype) K i₀) :
    (K.subgroupOf H).Normal := by
  by_contra hn
  obtain ⟨p,hp,hp7,⟨eK⟩⟩ := MathieuSourceSetup.nonnormal_component_prime_model
    c hG hempty hgen hb hn
  obtain ⟨t,ht,htC,htZ⟩ := MathieuSourceSetup.exists_central_core_involution c
  obtain ⟨i,hi⟩ := exists_maximal_bad_involution ((S : Subgroup H).map H.subtype) K ⟨i₀,hi₀⟩
  rcases source_maximal_prime_dichotomy c hG hempty hgen hb hstar hp hp7 eK
    t i ht htC htZ hi with hfour | ⟨_,hiZ⟩
  · exact hn (source_component_normal_of_four_core_centralizer c hG hempty hgen hb
      i hi.1.1.1 hi.1.1.2 hfour)
  · have hidx := (source_component_normal_or_index_two hG.quasithin c.gamma
      ⟨c.component_le,c.component⟩).resolve_left hn
    obtain ⟨u,hu,hcomm,_⟩ := TwoComponentCenter.exists_two_component_orbit
      H K c.component_le c.component S hidx
    let C := K.map (MulAut.conj u).toMonoidHom
    let Gi := centralizer ({i} : Set G)
    let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
    let XA := X.map Gi.subtype
    let e : K ≃* C := (MulAut.conj u).subgroupMap K
    let : IsQuasisimple K := (show IsComponentIn K H from ⟨c.component_le,c.component⟩).quasisimple
    let : Group.IsPerfect C := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    have hCH : C ≤ H := by
      rintro _ ⟨k,hk,rfl⟩
      exact H.mul_mem (H.mul_mem (map_subtype_le _ hu) (c.component_le hk))
        (H.inv_mem (map_subtype_le _ hu))
    have hCt : C ≤ centralizer ({t} : Set G) := hCH.trans
      (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ).1
    have hCN := source_companion_normalizes_prime_orbit c hG hempty hgen hb hstar
      hp hp7 eK t i ht htC htZ hi.1 hiZ u hu hcomm
    have hCX := source_prime_orbit_perfect_centralizer c hG hempty hgen hb hstar
      hp hp7 eK t i ht htC htZ hi.1 C (le_centralizer_iff.mp hcomm) hCt hCN
    exact source_no_commuting_three_rank_two_conjugate c hG hempty hgen hb u XA hCX
      (source_prime_orbit_three_rank c hG hempty hgen hb hstar hp hp7 eK t i ht htC htZ hi.1)

/-- Source 2.5.20 on the original tuple, with 2.5.19(1) fully discharged. -/
theorem source_component_normal
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M) :
    (K.subgroupOf H).Normal := by
  exact source_component_normal_of_bad_involution_normal c hG hempty hgen hb
    (fun i hi hi2 hbad => source_bad_involution_component_normal c hG hempty hgen hb hstar
      i ⟨hi,hi2,hbad⟩)
end CFSG.Quasithin.Chapter2.Section05.Overcomponents
