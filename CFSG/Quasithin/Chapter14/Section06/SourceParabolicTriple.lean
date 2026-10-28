module

public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicCore
public import CFSG.Quasithin.ChapterF.Section06.Basic
/-!
# The actual Goldschmidt triple in the rank-two source branch

The point stabilizer in the four-element seed action of LT is a two-group:
its image has order at most two and its kernel lies in O₂(LT). Since it
contains T, it is precisely T. The second parabolic centralizes the original
Sylow central point, so its intersection with the first parabolic is T ∩ I.

Suitability makes this intersection Sylow in I. Together with the source
first-parabolic quotient, the specified second-parabolic quotient, and the
literal generation equality, this constructs Definition F.6.1 inside I.
The final application obtains the residual factorization from 14.6.6(3)
when I ∩ M escapes the partner, keeping that construction noncircular.

Source: Aschbacher–Smith, refs/quasithin.pdf, 14.6.6(6), printed pp.1023–1024,
and the parabolic pair in 14.6.10, printed p.1028.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
open CFSG.Quasithin CFSG.Quasithin.Chapter12.Section08

namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]
private theorem rankTwo_intersection_pointCentralizer
    {K : GroupClass} {T : Sylow 2 G} {L M : Subgroup G}
    (h : RankTwoHypothesis K T L M) :
    (L ⊔ (T : Subgroup G)) ⊓ centralizer (sylowOmega T : Set G) = (T : Subgroup G) := by
  let J := L ⊔ (T : Subgroup G)
  let N := J ⊓ centralizer (sylowOmega T : Set G)
  let V := rankTwoSeed T M
  let f := setupSeedAction N V ((inf_le_left.trans (sup_le h.L_le h.sylow_le)).trans
    RankTwoHypothesis.M_normalizes_seed)
  have hZV : sylowOmega T ≤ V := le_conjugateSpanBy _ _
  have hZcard : Nat.card (sylowOmega T) = 2 := by
    obtain ⟨_, F, _⟩ := h.exists_flag_geometry
    rw [h.sylowOmega_eq_point F]
    simpa using F.card 1 (by decide)
  obtain ⟨z, hz⟩ := ne_bot_iff_exists_ne_one.mp (show sylowOmega T ≠ ⊥ by
    intro hh; simp [hh] at hZcard)
  let v : V := ⟨z, hZV z.property⟩
  have hv : v ≠ 1 := fun he => hz (Subtype.ext (congrArg (fun w : V => (w : G)) he))
  have hfix : ∀ a ∈ f.range, a v = v := by
    rintro a ⟨x,rfl⟩
    apply Subtype.ext
    change (x : G) * (z : G) * (x : G)⁻¹ = z
    rw [← x.property.2 z z.property, mul_inv_cancel_right]
  have hbound := card_mulAut_subgroup_le_two_of_fixed_point (rankTwoSeed_card h) v hv f.range hfix
  have hfp : IsPGroup 2 f.range := by
    change Nat.card f.range ≤ 2 at hbound
    have hp : 0 < Nat.card f.range := Nat.card_pos
    rcases (show Nat.card f.range = 1 ∨ Nat.card f.range = 2 by omega) with he | he
    · exact IsPGroup.of_card (n := 0) he
    · exact IsPGroup.of_card (n := 1) he
  have hker : IsPGroup 2 f.ker := by
    have hc : f.ker ≤ (J.pCoreIn 2).subgroupOf N := by
      intro x hx
      apply h.centralizer.le
      exact ⟨x.property.1,(setupSeedAction_ker N V _).le hx⟩
    exact (isPGroup_pCoreIn 2 J).comap_subtype.to_le hc
  have hNp : IsPGroup 2 N := by
    have ht := hfp.comap_of_ker_isPGroup f hker
    rw [MonoidHom.comap_range_self] at ht
    exact ht.of_equiv (Subgroup.topEquiv : (⊤ : Subgroup N) ≃* N)
  apply T.is_maximal' hNp
  exact le_inf le_sup_right (le_centralizer_iff.mpr (sylowOmega_centralizes T))
private theorem quotient_model_subgroupOf {P I : Subgroup G}
    (hPI : P ≤ I) (hq : Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))) :
    Nonempty (((P.subgroupOf I) ⧸ pCore 2 (P.subgroupOf I)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨eq⟩ := hq
  let eP := subgroupOfEquivOfLe hPI
  let eQ := eP.toMonoidHom.pCoreQuotientEquiv (p := 2) eP.surjective
    (IsPGroup.ker_isPGroup_of_injective eP.injective)
  exact ⟨eQ.trans eq⟩

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

omit hab hu hindex hmove hproduct hU3 hlocal in
/-- The actual two parabolics meet in the original Sylow intersection. -/
theorem source_parabolic_intersection
    (I I2 : Subgroup G)
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H) :
    ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊓ I2 =
        (T : Subgroup G) ⊓ I := by
  let L := sourceResidual M Mc
  let S := (T : Subgroup G) ⊓ I
  let I1 := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype ⊔ S
  have hfirst : I1 ≤ L ⊔ (T : Subgroup G) := sup_le
    (((map_subtype_le _).trans inf_le_left).trans le_sup_left)
    (inf_le_left.trans le_sup_right)
  have hI1I : I1 ≤ I := sup_le ((map_subtype_le _).trans inf_le_right) inf_le_right
  have hHC := (Section02.source_lemma_14_2_3 hG T hempty hM hunique hmany hcard e
    H hH.1 hH.2).2
  have he := rankTwo_intersection_pointCentralizer
    (Section02.source_lemma_14_2_4 hG T hempty hM hunique hmany hcard e)
  rw [Section02.sylowOmega_eq_centralInvolutions] at he
  exact le_antisymm (le_inf
    ((inf_le_inf hfirst (hI2H.trans hHC)).trans he.le)
    (inf_le_left.trans hI1I)) (le_inf le_sup_right hSI2)

/-- Original 14.6.10 uses an actual Goldschmidt triple in I. Its ambient
Sylow condition follows from suitability; its quotient maps are those of
the literal parabolics. -/
theorem source_parabolic_goldschmidtTriple
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H)
    (hquot2 : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hcover : (sourceResidual M Mc : Set G) =
      ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
        (sourceResidual M Mc ⊓ I).subtype : Set G) *
          ((sourceResidual M Mc).pCoreIn 2 : Set G))
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I) :
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)
    ChapterF.IsGoldschmidtTriple (I1.subgroupOf I) (I2.subgroupOf I) := by
  let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
    (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)
  have hI1I : I1 ≤ I := sup_le ((map_subtype_le _).trans inf_le_right) inf_le_right
  have hI2I : I2 ≤ I := le_sup_right.trans_eq hgen
  have hSyl := (source_suitable_intersection_sylow hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal I hI.1).1
  have hquot1 := (source_intersection_parabolic_data hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct I hI.1.2.1 hSyl hcover).1
  have hint := source_parabolic_intersection hG T hempty hM hunique hmany hcard e
    H hH I I2 hSI2 hI2H
  refine ⟨?_,quotient_model_subgroupOf hI1I hquot1,
    quotient_model_subgroupOf hI2I hquot2,?_⟩
  · rw [← subgroupOf_sup hI1I hI2I, hgen, subgroupOf_self]
  · obtain ⟨P,hP⟩ := hSyl
    refine ⟨P,?_⟩
    change (I1 ⊓ I2).subgroupOf I = (P : Subgroup I)
    apply map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le (inf_le_left.trans hI1I), hint]
    exact hP.symm

/-- The actual escaping-intersection application discharges the residual
factorization through original 14.6.6(3). -/
theorem source_parabolic_goldschmidtTriple_of_escape
    (I I2 : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M))
    (hSI2 : (T : Subgroup G) ⊓ I ≤ I2) (hI2H : I2 ≤ H)
    (hquot2 : Nonempty ((I2 ⧸ pCore 2 I2) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ I ⊓ M ≤ Mc)
    (hgen : ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔ I2 = I) :
    let I1 := (pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
      (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)
    ChapterF.IsGoldschmidtTriple (I1.subgroupOf I) (I2.subgroupOf I) := by
  have hcover := (source_lemma_14_6_6_3 hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct I hI.1.2.1 hout).1
  exact source_parabolic_goldschmidtTriple hG T hempty hM hunique hmany hcard e
    hab H hH u hu hindex hmove hproduct hU3 hlocal I I2 hI hSI2 hI2H hquot2 hcover hgen

end CFSG.Quasithin.Chapter14.Section06
