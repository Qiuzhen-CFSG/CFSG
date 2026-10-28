module
public import CFSG.Quasithin.Chapter14.Section06.SourceSolvableFactorization
public import CFSG.Quasithin.Chapter14.Section06.SourceInvariantSubgroups

/-!
# Solvable invariant subgroups in the original parabolic argument

The invariant-subgroup dichotomy needs the 14.6.9 factorization only for
P(T∩I). If P is solvable and invariant under the first parabolic, this
subgroup is solvable, and the proved solvable case supplies the factorization.
Thus the ambient I may remain nonsolvable. The actual consumer places the
prime-to-three kernel in C_M(V) in SourceParabolicComponent.SolvableKernel.

Source: Aschbacher–Smith, 14.6.9 and 14.6.10(3), printed pp.1026–1028.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem residual_sup_le (P S : Subgroup G)
    (hn : S ≤ normalizer (P : Set G)) (hp : IsPGroup 2 S) :
    (pResidual 2 (P ⊔ S : Subgroup G)).map (P ⊔ S).subtype ≤ P := by
  let J := P ⊔ S
  let : (P.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer (sup_le P.le_normalizer hn)
  have hq : IsPGroup 2 (J ⧸ P.subgroupOf J) :=
    isPGroup_quotient_of_sup_eq_top (P.subgroupOf J) (S.subgroupOf J)
      hp.comap_subtype (by rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self])
  have hr : pResidual 2 J ≤ P.subgroupOf J := sInf_le ⟨inferInstance,hq⟩
  rintro x ⟨a,ha,rfl⟩
  exact hr ha

private theorem invariant_residual_le_of_cover (L I J P : Subgroup G)
    (hJI : J ≤ I)
    (hn : (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype ≤
      normalizer (P : Set G))
    (hRP : (pResidual 2 (L ⊓ J : Subgroup G)).map (L ⊓ J).subtype ≤ P)
    (hcover : (L : Set G) =
      ((pResidual 2 (L ⊓ J : Subgroup G)).map (L ⊓ J).subtype : Set G) *
        (L.pCoreIn 2 : Set G)) :
    (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype ≤ P := by
  let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
  let D := (pResidual 2 (L ⊓ J : Subgroup G)).map (L ⊓ J).subtype
  have hDR : D ≤ R := embedded_pResidual_mono 2 (inf_le_inf_left L hJI)
  have hRL : R ≤ L := (map_subtype_le _).trans inf_le_left
  let N := P.subgroupOf R
  let Q := (L.pCoreIn 2).subgroupOf R
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  have hsup : N ⊔ Q = ⊤ := by
    apply top_unique
    intro x _
    have hx : (x : G) ∈ (L : Set G) := hRL x.property
    rw [hcover] at hx
    obtain ⟨d,hd,q,hq,he⟩ := Set.mem_mul.mp hx
    have hdR : d ∈ R := hDR hd
    have hqR : q ∈ R := by
      have heq : q = d⁻¹ * (x : G) := by rw [←he]; group
      rw [heq]
      exact R.mul_mem (R.inv_mem hdR) x.property
    have hmem := (N ⊔ Q).mul_mem (mem_sup_left (show (⟨d,hdR⟩ : R) ∈ N from hRP hd))
      (mem_sup_right (show (⟨q,hqR⟩ : R) ∈ Q from hq))
    have he' : (⟨d,hdR⟩ : R) * ⟨q,hqR⟩ = x := Subtype.ext he
    exact he' ▸ hmem
  have htop : N = ⊤ := (isPPerfect_embedded_pResidual 2 (L ⊓ I)) N inferInstance
    (isPGroup_quotient_of_sup_eq_top N Q (isPGroup_pCoreIn 2 L).comap_subtype hsup)
  intro r hr
  exact (show (⟨r,hr⟩ : R) ∈ N from htop ▸ mem_top _)

namespace CFSG.Quasithin.Chapter14.Section06
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


/-- Original 14.6.10(3) for a solvable invariant subgroup: the only new
factorization is supplied by the solvable case of 14.6.9. -/
theorem source_invariant_solvable_subgroup_of_escape
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I P : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    [Group.IsSolvable P]
    (hout : ¬ I ⊓ M ≤ Mc)
    (hPI : P ≤ I)
    (hN : (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I) ≤
        normalizer (P : Set G)) :
    (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ≤ P ∨
        P ≤ M ⊓ centralizer (localModule T M : Set G) := by
  have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct I hI.1.2.1 hout).1
  by_cases hPM : P ≤ M ∨ P ≤ Mc
  · exact source_invariant_subgroup_in_local hG T hempty hM hunique hmany hcard e hab
      H hH u hu hindex hmove hproduct hU3 hlocal I P hI.1 hcover hPI hN hPM
  have hnotM : ¬ P ≤ M := fun hh => hPM (Or.inl hh)
  have hnotMc : ¬ P ≤ Mc := fun hh => hPM (Or.inr hh)
  left
  let S := (T : Subgroup G) ⊓ I
  let J := P ⊔ S
  have hJI : J ≤ I := sup_le hPI inf_le_right
  have hSJ : S ≤ J := le_sup_right
  obtain ⟨hSyl,_⟩ := source_suitable_intersection_sylow hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1
  obtain ⟨SI,hSI⟩ := hSyl
  have hQIS : I.pCoreIn 2 ≤ S := by
    change I.pCoreIn 2 ≤ (T : Subgroup G) ⊓ I
    rw [← hSI]
    exact pCoreIn_le_sylow I SI
  have hIn : I ≤ normalizer (I.pCoreIn 2 : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hcoreJ : I.pCoreIn 2 ≤ J.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I) (hQIS.trans hSJ) (hJI.trans hIn)
  have hJH : J ∈ Chapter1.H G := by
    intro hz
    exact hI.1.1 (le_bot_iff.mp (hz ▸ hcoreJ))
  have hJout : J ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M :=
    ⟨hJH,(le_inf inf_le_left hI.1.2.1).trans hSJ,
      fun hh => hnotMc (le_sup_left.trans hh),fun hh => hnotM (le_sup_left.trans hh)⟩
  have hJstar := (lemma14_6_4 hI hJout hSJ).1
  let : (P.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le P.le_normalizer (le_sup_right.trans hN))
  let : Group.IsSolvable (P.subgroupOf J) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show P ≤ J from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show P ≤ J from le_sup_left)).injective
  have hq : IsPGroup 2 (J ⧸ P.subgroupOf J) :=
    isPGroup_quotient_of_sup_eq_top (P.subgroupOf J) (S.subgroupOf J)
      (T.isPGroup'.to_le inf_le_left).comap_subtype
      (by rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self])
  let : Group.IsNilpotent (J ⧸ P.subgroupOf J) := hq.isNilpotent
  let : Group.IsSolvable J := (Group.isSolvable_iff_subgroup_quotient (P.subgroupOf J)).mpr
    ⟨inferInstance,inferInstance⟩
  have hfactor := source_lemma_14_6_9_of_solvable hG T hempty hM hunique hmany hcard e hab
    H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank J hJstar
  apply invariant_residual_le_of_cover (sourceResidual M Mc) I J P hJI
    (le_sup_left.trans hN) _ hfactor
  exact (embedded_pResidual_mono 2 (inf_le_right : sourceResidual M Mc ⊓ J ≤ J)).trans
    (residual_sup_le P S (le_sup_right.trans hN) (T.isPGroup'.to_le inf_le_left))



end CFSG.Quasithin.Chapter14.Section06
