module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.Basic
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceSplitting
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.LocalAnalysisCentralizersThompsonSourceOmega

/-!
# LocalAnalysisCentralizersThompsonSourceSplitting at the original ambient group and Sylow subgroup

These are the same source arguments as `LocalAnalysisCentralizersThompsonSourceSplitting`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender

open scoped IsMulCommutative Pointwise commutatorElement

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}

namespace Setup.NaturalCoordinates

variable (E : S.NaturalCoordinates)

include E in

theorem core_omega_maxElementary_commutator_le_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G)) :
    ⁅A, omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2)⁆ ≤ V := by
  classical
  let U := omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2)
  let B := (A.subgroupOf (normalizer (V : Set G))).map
    (E.sourceNormalizerModel_at structural).permutation
  have hAN : A ≤ normalizer (V : Set G) :=
    hA.1.trans (((structural L S.hypothesis).2.2 V S.chosen).1)
  by_cases hb : B = ⊥
  · have hAC : A ≤ centralizer (V : Set G) := by
      have hk := (Subgroup.map_eq_bot_iff _).mp hb
      rw [normalizerModel_kernel] at hk
      intro a ha v hv
      exact congrArg Subtype.val
        (hk (show (⟨a,hAN ha⟩ : normalizer (V : Set G)) ∈
          A.subgroupOf (normalizer (V : Set G)) from ha) ⟨v,V.le_normalizer hv⟩ hv)
    have hAQ : A ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
      rw [← RecognitionSource.chosen_sylow_centralizer_eq_core_at S.hypothesis S.chosen structural]
      exact le_inf hA.1 hAC
    have hc : U ≤ centralizer (A : Set G) :=
      fun u hu => centralizer_le hAQ ((mem_omegaCenterIn_iff _ _).mp hu).2.1
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr hc]
    exact bot_le
  · rw [E.core_omega_eq_sup_fixed_maxElementary_at structural A hA hb,commutator_comm]
    let C := U ⊓ centralizer (A : Set G)
    have hUV : U ≤ normalizer (V : Set G) :=
      (le_centralizer_iff.mp ((chosen_le_core_omega (S := S)).trans (le_centralizer U))).trans
        (Subgroup.centralizer_le_normalizer _)
    exact commutator_sup_le_of_relative_normal U V C A V hUV
      (chosen_le_core_omega (S := S)) inf_le_left
      (le_normalizer_iff_commutator_le_left.mp hAN)
      ((commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le)

include E in

theorem core_omega_commutator_eq_chosen_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hgen : L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆) :
    ⁅omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2),L⁆ = V := by
  let H := L ⊔ (T : Subgroup G)
  let U := omegaCenterIn (H.pCoreIn 2)
  let C := commutatorPreimage H U V
  have hHV : H ≤ normalizer (V : Set G) :=
    sup_le S.chosen.normalizes (((structural L S.hypothesis).2.2 V S.chosen).1)
  have hHC : H ≤ normalizer (C : Set G) :=
    commutatorPreimage_normalized H U V H hHV H.le_normalizer
      (core_omega_normalized (T := T) (L := L)) hHV
  have hJC : elementaryAbelianMaxJ (T : Subgroup G) ≤ C := by
    apply sSup_le
    intro A hA
    exact le_commutatorPreimage (hA.1.trans le_sup_right)
      (E.core_omega_maxElementary_commutator_le_at structural A hA)
  have hLC : L ≤ C := by
    rw [hgen]
    exact (commutator_mono le_rfl hJC).trans
      (le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hHC))
  apply le_antisymm
  · rw [commutator_comm]
    exact (commutator_mono hLC le_rfl).trans (commutator_commutatorPreimage_le H U V hHV)
  · exact S.chosen.eq_commutator.le.trans
      (commutator_mono (chosen_le_core_omega (S := S)) le_rfl)

include E in

theorem core_omega_eq_sup_component_fixed_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hgen : L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆) :
    omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
      V ⊔ (omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊓
        centralizer (L : Set G)) := by
  let U := omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2)
  let ρ := BinaryPermutation.alternatingNaturalRepresentation (Fin 7)
  let : Subsingleton (OneCohomology.H1 ρ) :=
    (Module.finrank_zero_iff (R := ZMod 2)).mp
      (BinaryPermutation.alternatingSeven_natural_finrank_H1)
  let e := E.coordinates.trans evenWordsEquivNatural.toAddEquiv.toMultiplicative
  let d : BinaryConjugationSection L V ⊥ (ρ.comp S.projection) := {
    section_le := S.chosen.le_component
    kernel_le := bot_le
    normalized := S.chosen.normalizes
    coordinates := e.toMonoidHom
    onto := e.surjective
    kernel_eq := by
      ext v
      change e v = 1 ↔ (v : G) = 1
      rw [e.map_eq_one_iff]
      exact Subtype.ext_iff
    equivariant := by
      intro l v
      change evenWordsEquivNatural (E.coordinates _).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 7) (S.projection l).val
          (evenWordsEquivNatural (E.coordinates v).toAdd)
      rw [← evenWordsEquivNatural_equivariant]
      exact congrArg evenWordsEquivNatural (E.equivariant l v) }
  have hc := E.core_omega_commutator_eq_chosen_at structural hgen
  have hk := E.projection_kernel_centralizes_core_omega hc.le
  apply le_antisymm ?_ (sup_le (chosen_le_core_omega (S := S)) inf_le_left)
  intro x hx
  obtain ⟨v,hv⟩ := d.exists_fixed_mod_kernel S.projection S.projection_surjective U
    (by rw [commutator_comm]; exact hc.le)
    (fun l hl x hx => mem_bot.mpr
      (commutatorElement_eq_one_iff_mul_comm.mpr (hk (mem_map_of_mem L.subtype hl) x hx).symm))
    ⟨x,hx⟩
  have hf : (v : G)⁻¹ * x ∈ U ⊓ centralizer (L : Set G) := by
    refine ⟨U.mul_mem (U.inv_mem ((chosen_le_core_omega (S := S)) v.property)) hx,?_⟩
    intro l hl
    exact commutatorElement_eq_one_iff_mul_comm.mp (mem_bot.mp (hv ⟨l,hl⟩))
  have hm := mul_mem_sup v.property hf
  simpa only [mul_inv_cancel_left] using hm

include E in

theorem sylow_even_le_component_sup_core_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (t : G) (ht : t ∈ T)
    (heven : (E.sourceNormalizerModel_at structural).permutation
      ⟨t, ((structural L S.hypothesis).2.2 V S.chosen).1 ht⟩ ∈
        alternatingGroup (Fin 7)) :
    t ∈ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let H := L ⊔ (T : Subgroup G)
  let D := E.sourceNormalizerModel_at structural
  have hHV : H ≤ normalizer (V : Set G) :=
    sup_le S.chosen.normalizes (((structural L S.hypothesis).2.2 V S.chosen).1)
  let q : H →* Equiv.Perm (Fin 7) := D.permutation.comp (inclusion hHV)
  let B := L.subgroupOf H
  let R := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let : B.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer S.chosen.sylow_normalizes_component)
  obtain ⟨P,hP⟩ := R.exists_sylow_map_eq_inf_of_normal B
  have hmap := R.map_image_eq_inf B ((R : Subgroup H) ⊓ B) P hP inf_le_left q
  have hBq : B.map q = alternatingGroup (Fin 7) := by
    apply le_antisymm
    · rintro _ ⟨l,hl,rfl⟩
      have hp := E.sourceNormalizerModel_component_at structural ⟨l,hl⟩
      change q l = _ at hp
      rw [hp]
      exact (S.projection ⟨l,hl⟩).property
    · intro a ha
      obtain ⟨l,hl⟩ := S.projection_surjective ⟨a,ha⟩
      refine ⟨⟨l,(show L ≤ H from le_sup_left) l.property⟩,l.property,?_⟩
      exact (E.sourceNormalizerModel_component_at structural l).trans (congrArg Subtype.val hl)
  let t' : H := ⟨t,mem_sup_right ht⟩
  have hm : q t' ∈ ((R : Subgroup H) ⊓ B).map q := by
    rw [hmap,hBq]
    exact ⟨mem_map_of_mem q (show t' ∈ R from ht),heven⟩
  obtain ⟨l,hl,he⟩ := hm
  have hc : t * (l : G)⁻¹ ∈ H.pCoreIn 2 := by
    rw [← RecognitionSource.chosen_sylow_centralizer_eq_core_at S.hypothesis S.chosen structural]
    refine ⟨(T : Subgroup G).mul_mem ht ((T : Subgroup G).inv_mem hl.1),?_⟩
    have hz : q (t' * l⁻¹) = 1 := by rw [map_mul,map_inv,he,mul_inv_cancel]
    have hk : inclusion hHV (t' * l⁻¹) ∈ D.permutation.ker := hz
    rw [normalizerModel_kernel] at hk
    intro v hv
    exact congrArg Subtype.val (hk ⟨v,V.le_normalizer hv⟩ hv)
  have hm := (L ⊔ H.pCoreIn 2).mul_mem (mem_sup_right hc) (mem_sup_left hl.2)
  simpa only [Subgroup.subtype_apply,inv_mul_cancel_right] using hm

include E in

theorem join_eq_component_maxElementary_core_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G))
    (hne : (A.subgroupOf (normalizer (V : Set G))).map
      (E.sourceNormalizerModel_at structural).permutation ≠ ⊥) :
    L ⊔ (T : Subgroup G) = L ⊔ A ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let D := E.sourceNormalizerModel_at structural
  have hTV := ((structural L S.hypothesis).2.2 V S.chosen).1
  obtain ⟨a,ha,hodd⟩ := SetLike.not_le_iff_exists.mp
    (natural_bestOffender_not_le_alternating _
      (E.maxElementary_image_bestOffender_at structural A hA hne))
  obtain ⟨b,hb,rfl⟩ := ha
  have hbT := hA.1 hb
  have hsup : L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      L ⊔ A ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  apply le_antisymm (sup_le (le_sup_left.trans le_sup_left) ?_)
    (sup_le (sup_le le_sup_left (hA.1.trans le_sup_right)) (pCoreIn_le 2 _))
  intro t ht
  by_cases he : D.permutation ⟨t,hTV ht⟩ ∈ alternatingGroup (Fin 7)
  · exact hsup (E.sylow_even_le_component_sup_core_at structural t ht he)
  · have hbt : D.permutation (b * ⟨t,hTV ht⟩) ∈ alternatingGroup (Fin 7) := by
      rw [map_mul, Subgroup.mul_mem_iff_of_index_two alternatingGroup.index_eq_two]
      exact iff_of_false hodd he
    have hm := hsup (E.sylow_even_le_component_sup_core_at structural ((b : G)*t)
      ((T : Subgroup G).mul_mem hbT ht) hbt)
    have hr := (L ⊔ A ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2).mul_mem
      (mem_sup_left (mem_sup_right (A.inv_mem hb))) hm
    simpa only [Subgroup.subtype_apply,inv_mul_cancel_left] using hr

include E in

theorem core_omega_component_fixed_eq_sylow_fixed_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G))
    (hne : (A.subgroupOf (normalizer (V : Set G))).map
      (E.sourceNormalizerModel_at structural).permutation ≠ ⊥) :
    omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) ⊓ centralizer (L : Set G) =
      omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G) := by
  let H := L ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  let U := omegaCenterIn Q
  let C := U ⊓ centralizer (L : Set G)
  have hTC : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (le_inf (le_sup_right.trans (core_omega_normalized (T := T) (L := L)))
      (S.chosen.sylow_normalizes_component.trans (normalizer_le_normalizer_centralizer L))).trans
        inf_normalizer_le_normalizer_inf
  have hAC : A ≤ centralizer (C : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    intro x hx
    have hxV : x ∈ V := E.core_omega_maxElementary_commutator_le_at structural A hA
      ((commutator_mono le_rfl inf_le_left) hx)
    have hxC : x ∈ C :=
      (le_normalizer_iff_commutator_le_right.mp (hA.1.trans hTC)) hx
    exact mem_bot.mpr (congrArg (fun v : V => (v : G))
      (SylowNormalizer.Points.natural_fixed_eq_one (E := E) (v := ⟨x,hxV⟩) hxC.2))
  have hQC : Q ≤ centralizer (C : Set G) :=
    le_centralizer_iff.mp (fun c hc => ((mem_omegaCenterIn_iff _ _).mp hc.1).2.1)
  have hHC : H ≤ centralizer (C : Set G) := by
    dsimp only [H]
    rw [E.join_eq_component_maxElementary_core_at structural A hA hne]
    exact sup_le (sup_le (le_centralizer_iff.mp inf_le_right) hAC) hQC
  apply le_antisymm
  · intro c hc
    exact ⟨(mem_omegaCenterIn_iff _ _).mpr
      ⟨core_omega_le_sylow (T := T) (L := L) hc.1,
        le_centralizer_iff.mp (le_sup_right.trans hHC) hc,
        ((mem_omegaCenterIn_iff _ _).mp hc.1).2.2⟩,hc.2⟩
  · let F := omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)
    let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le (show F ≤
      omegaCenterIn (T : Subgroup G) from inf_le_left)
    have hFH : F ≤ H := fun f hf => mem_sup_right ((mem_omegaCenterIn_iff _ _).mp hf.1).1
    have hFC : F ≤ centralizer (H : Set G) := by
      apply le_centralizer_iff.mp
      exact sup_le (le_centralizer_iff.mp inf_le_right)
        (le_centralizer_iff.mp (fun f hf => ((mem_omegaCenterIn_iff _ _).mp hf.1).2.1))
    have hFQ : F ≤ Q := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 F)
      hFH ((le_centralizer_iff.mp hFC).trans (Subgroup.centralizer_le_normalizer _))
    intro f hf
    refine ⟨(mem_omegaCenterIn_iff _ _).mpr ⟨hFQ hf,?_,
      ((mem_omegaCenterIn_iff _ _).mp hf.1).2.2⟩,hf.2⟩
    exact centralizer_le (pCoreIn_le 2 H) (hFC hf)

theorem core_omega_decomposition_of_weight_six_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
      V ⊔ (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
    Disjoint V (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  have hg := E.thompson_generation_of_weight_six_at structural escape hsix
  obtain ⟨A,hA,hne,_⟩ := E.core_omega_maxElementary_splitting_of_weight_six_at structural escape hsix
  exact ⟨(E.core_omega_eq_sup_component_fixed_at structural hg).trans
    (congrArg (fun C => V ⊔ C)
      (E.core_omega_component_fixed_eq_sylow_fixed_at structural A hA hne)),
    E.core_omega_factors_disjoint⟩

theorem source_1237_one_of_weight_six_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
    Function.Surjective (E.sourceNormalizerModel_at structural).permutation ∧
    omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
      V ⊔ (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
    Disjoint V (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  obtain ⟨hg,hs⟩ := E.thompson_and_symmetric_of_weight_six_at structural escape hsix
  exact ⟨hg,hs,E.core_omega_decomposition_of_weight_six_at structural escape hsix⟩

end Setup.NaturalCoordinates

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

