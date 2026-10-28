module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.SingleAmalgam

/-!
# Thompson and Baumann heredity for the original Borel core

The two-perfect Borel residual has nontrivial image on the A5 quotient and
normalizes its chosen Sylow subgroup. Its normal two-core therefore acts
by inner automorphisms, hence by even permutations on the original module.
The proved even-action theorem identifies the Thompson and Baumann
subgroups of O₂(L₁T) with those of O₂(LT). Their full Thompson normalizer
lies in N_G(L), so an outside residual cannot normalize that subgroup.

These are the heredity and nonnormality steps used in 13.2.13; the middle
Baumann-Sylow transfer is separate. OriginalCentralization/BorelSylow
applies all four results to the literal Borel-join quotient argument.

Source: Aschbacher--Smith 13.2.4(1) and13.2.13, printed pp.879,883.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The original Borel core acts by even permutations on the original module. -/
theorem borel_core_even_action :
    let P := borelResidual T L ⊔ (T : Subgroup G)
    ((P.pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G))).map d.localActor ≤
      alternatingGroup (Fin 5) := by
  let K := L ⊔ (T : Subgroup G)
  let A := borelResidual T L
  let P := A ⊔ (T : Subgroup G)
  have hAB : A ≤ ChapterF.Source.borel L (T : Subgroup G) := by
    rw [show A = borelResidual T L from rfl,borelResidual_eq_point_residual d,
      d.borel_eq_point_centralizer]
    exact Section05.A5Source.ThirdSpace.residual_le_centralizer
  have hAL : A ≤ L := hAB.trans inf_le_left
  have hPK : P ≤ K := sup_le_sup hAL le_rfl
  have hPM : P ≤ normalizer (L : Set G) := sup_le (hAL.trans L.le_normalizer) d.normalizes_L
  have hnS : P ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    sup_le (hAB.trans inf_le_right)
      ((le_inf (T : Subgroup G).le_normalizer d.normalizes_L).trans inf_normalizer_le_normalizer_inf)
  let q := d.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let a := d.quotientNormalizerAction.comp (inclusion hPM)
  have ha (x : P) (k : L) : a x (q k) =
      q (L.normalizerMonoidHom ⟨x,hPM x.property⟩ k) :=
    d.quotientNormalizerAction_mk _ _
  obtain ⟨S,hS⟩ := d.local_sylow
  let S' := S.mapSurjective (f := q) (d.quotient.surjective.comp (QuotientGroup.mk'_surjective _))
  have haS (x : P) : (S' : Subgroup (alternatingGroup (Fin 5))).map (a x).toMonoidHom = S' := by
    apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (a x).injective])
    rintro z ⟨w,hw,rfl⟩
    obtain ⟨k,hk,rfl⟩ := hw
    change a x (q k) ∈ (S' : Subgroup (alternatingGroup (Fin 5)))
    rw [ha]
    apply mem_map_of_mem
    apply (mem_map_iff_mem L.subtype_injective).mp
    rw [hS]
    exact le_normalizer_iff.mp hnS x x.property k (hS ▸ mem_map_of_mem L.subtype hk)
  let D := A.subgroupOf P
  let eD := subgroupOfEquivOfLe (show A ≤ P from le_sup_left)
  have hD : IsPPerfect 2 D := borelResidual_twoPerfect.of_surjective
    eD.symm.toMonoidHom eD.symm.surjective
  have hnon : ∃ b : D, a b ≠ 1 := by
    by_contra hall
    push Not at hall
    have hAQ : A ≤ K.pCoreIn 2 := by
      intro x hx
      let p : P := ⟨x,mem_sup_left hx⟩
      let k : K := ⟨x,hPK p.property⟩
      have he : MulAut.conjNormal (d.localActor k) = (1 : MulAut (alternatingGroup (Fin 5))) := by
        rw [← d.quotientNormalizerAction_eq_localActor k]
        exact hall ⟨p,hx⟩
      have hk : d.localActor k = 1 := by
        apply (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
          (by decide) (by decide)).1
        simpa only [MulAut.conjNormal_val, map_one] using he
      have hk' : k ∈ pCore 2 K := by
        rw [←d.localActor_kernel_eq_core d.normalizes_L]
        exact hk
      exact mem_map_of_mem K.subtype hk'
    have htwo : IsPGroup 2 A := (isPGroup_pCoreIn 2 K).to_le hAQ
    have hh := htwo.of_surjective (QuotientGroup.mk' (pCore 2 A))
      (QuotientGroup.mk'_surjective _)
    rcases hh.card_eq_or_dvd with h | h <;>
      rw [borelResidual_quotient_card d] at h <;> norm_num at h
  have hi := Theory.SpecificGroups.Alternating.FiveSylowRadical.normal_two_action_inner
    S' a haS D (pCore 2 P) hD pCore_isPGroup hnon
  dsimp only
  rintro x ⟨r,hr,rfl⟩
  apply d.localActor_even_of_quotientNormalizerAction_inner
  obtain ⟨p,hp,hpr⟩ := hr
  have hip := hi ⟨p,hp⟩
  change d.quotientNormalizerAction _ ∈ MulAut.innerSubgroup _ at hip
  convert hip using 1
  congr 1
  exact Subtype.ext hpr.symm

/-- Source 13.2.4(1) on the literal core O₂(L₁T) used in 13.2.13. -/
theorem borel_core_thompson_baumann :
    let R₁ := (borelResidual T L ⊔ (T : Subgroup G)).pCoreIn 2
    let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
    elementaryAbelianMaxJ R₁ = elementaryAbelianMaxJ Q ∧
      ChapterB.baumann R₁ = ChapterB.baumann Q := by
  let P := borelResidual T L ⊔ (T : Subgroup G)
  let K := L ⊔ (T : Subgroup G)
  have hAL : borelResidual T L ≤ L := by
    rw [borelResidual_eq_point_residual d]
    exact Section05.A5Source.ThirdSpace.residual_le_centralizer.trans inf_le_left
  have hPK : P ≤ K := sup_le_sup hAL le_rfl
  have hQT : K.pCoreIn 2 ≤ (T : Subgroup G) :=
    (d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left
  have hQP : K.pCoreIn 2 ≤ P.pCoreIn 2 := le_pCoreIn_of_normalizes
    (isPGroup_pCoreIn 2 K) (hQT.trans le_sup_right)
    ((hPK.trans K.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
  have hRT : P.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow P (T.subtype (show (T : Subgroup G) ≤ P from le_sup_right))
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ P from le_sup_right)] at hh
  exact d.thompson_baumann_eq_core_of_even_action (P.pCoreIn 2) hQP hRT
    (borel_core_even_action d)

/-- The full normalizer of the Thompson subgroup of the literal Borel core
lies in the original component normalizer. -/
theorem borel_core_thompson_normalizer :
    normalizer (elementaryAbelianMaxJ
      ((borelResidual T L ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) ≤
        normalizer (L : Set G) := by
  rw [(borel_core_thompson_baumann d).1, ←d.even_sylow_thompson_baumann.1]
  exact d.even_sylow_thompson_normalizer

/-- The outside residual fails to normalize J(O₂(L₁T)), as used before E.2.3
in the middle of the proof of 13.2.13. -/
theorem residual_not_normalizes_borel_core_thompson {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    ¬ (pResidual 2 H).map H.subtype ≤ normalizer
      (elementaryAbelianMaxJ ((borelResidual T L ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) := by
  let P := borelResidual T L ⊔ (T : Subgroup G)
  intro hn
  have hTN : (T : Subgroup G) ≤ normalizer (elementaryAbelianMaxJ (P.pCoreIn 2) : Set G) :=
    (((le_sup_right : (T : Subgroup G) ≤ P).trans P.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image P (pCore 2 P))).trans
        (normalizer_le_normalizer_elementaryAbelianMaxJ _)
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  let S := T.subtype hTH
  have hgen := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top S)
  rw [Subgroup.map_sup, ←MonoidHom.range_eq_map, range_subtype] at hgen
  change (pResidual 2 H).map H.subtype ⊔
    ((T : Subgroup G).subgroupOf H).map H.subtype = H at hgen
  rw [map_subgroupOf_eq_of_le hTH] at hgen
  exact hH.1.2 ((hgen.ge.trans (sup_le hn hTN)).trans (borel_core_thompson_normalizer d))

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
