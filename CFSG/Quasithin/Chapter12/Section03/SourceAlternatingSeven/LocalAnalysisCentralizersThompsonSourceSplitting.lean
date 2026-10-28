module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisCentralizersThompsonSourceOmega
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.Representation.BinaryConjugationSection.FixedSplitting
public import Theory.Representation.BinaryAlternatingNaturalCohomology
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.SylowImageIntersection
/-!
# The actual core omega-center decomposition in source 12.3.7(1)

Every maximum elementary subgroup A of T centralizes the core omega center
U modulo V: a moving A has the sharp offender supplement, while a nonmoving
A lies in O₂(LT). The relatively normal commutator preimage therefore contains
J(T), and L=[L,J(T)] gives [U,L]=V.

The original O₂,Z(L) kernel centralizes U. Indeed its displacement lies in V;
the three-subgroups lemma makes it L-fixed, and the natural A₇ module has no
fixed points. Thus the displacement cocycle descends through the original
projection to A₇. Vanishing first cohomology gives U=V C_U(L), retaining the
possible central cover throughout.

Sylow intersection transport and an odd permutation in a moving offender give
LT=LAO₂(LT). The fixed factor centralizes A, L and O₂(LT), so it is exactly
C_{Ω₁Z(T)}(L). The final theorem assembles all of 12.3.7(1), including the
literal permutation map and disjoint factors. Only the allowed weight-six
input remains for `qt-d-1236-1238-point-centralizers` to discharge.

Source: Aschbacher--Smith, Lemma 12.3.7(1), printed p.809, using I.1.6(1).
The weight-two point-residual conclusions of 12.3.7(2) remain separate.
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

omit [Finite G] in
theorem core_omega_normalized : L ⊔ (T : Subgroup G) ≤
    normalizer (omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) :=
  ((L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))).trans
      (normalizer_le_normalizer_omegaCenterIn _)

omit [Finite G] in
theorem core_omega_le_sylow :
    omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) ≤ (T : Subgroup G) := by
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  exact fun u hu => hQT ((mem_omegaCenterIn_iff _ _).mp hu).1

include E in
/-- Every maximum elementary subgroup acts trivially on the core omega center modulo V. -/
theorem core_omega_maxElementary_commutator_le
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G)) :
    ⁅A, omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2)⁆ ≤ V := by
  classical
  let U := omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2)
  let B := (A.subgroupOf (normalizer (V : Set G))).map
    (E.sourceNormalizerModel structural).permutation
  have hAN : A ≤ normalizer (V : Set G) :=
    hA.1.trans (((structural G T L S.hypothesis).2.2 V S.chosen).1)
  by_cases hb : B = ⊥
  · have hAC : A ≤ centralizer (V : Set G) := by
      have hk := (Subgroup.map_eq_bot_iff _).mp hb
      rw [normalizerModel_kernel] at hk
      intro a ha v hv
      exact congrArg Subtype.val
        (hk (show (⟨a,hAN ha⟩ : normalizer (V : Set G)) ∈
          A.subgroupOf (normalizer (V : Set G)) from ha) ⟨v,V.le_normalizer hv⟩ hv)
    have hAQ : A ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
      rw [← RecognitionSource.chosen_sylow_centralizer_eq_core S.hypothesis S.chosen structural]
      exact le_inf hA.1 hAC
    have hc : U ≤ centralizer (A : Set G) :=
      fun u hu => centralizer_le hAQ ((mem_omegaCenterIn_iff _ _).mp hu).2.1
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr hc]
    exact bot_le
  · rw [E.core_omega_eq_sup_fixed_maxElementary structural A hA hb,commutator_comm]
    let C := U ⊓ centralizer (A : Set G)
    have hUV : U ≤ normalizer (V : Set G) :=
      (le_centralizer_iff.mp ((chosen_le_core_omega (S := S)).trans (le_centralizer U))).trans
        (Subgroup.centralizer_le_normalizer _)
    exact commutator_sup_le_of_relative_normal U V C A V hUV
      (chosen_le_core_omega (S := S)) inf_le_left
      (le_normalizer_iff_commutator_le_left.mp hAN)
      ((commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le)

include E in
/-- Thompson generation identifies the actual L-displacement of the core omega center. -/
theorem core_omega_commutator_eq_chosen
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (hgen : L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆) :
    ⁅omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2),L⁆ = V := by
  let H := L ⊔ (T : Subgroup G)
  let U := omegaCenterIn (H.pCoreIn 2)
  let C := commutatorPreimage H U V
  have hHV : H ≤ normalizer (V : Set G) :=
    sup_le S.chosen.normalizes (((structural G T L S.hypothesis).2.2 V S.chosen).1)
  have hHC : H ≤ normalizer (C : Set G) :=
    commutatorPreimage_normalized H U V H hHV H.le_normalizer
      (core_omega_normalized (T := T) (L := L)) hHV
  have hJC : elementaryAbelianMaxJ (T : Subgroup G) ≤ C := by
    apply sSup_le
    intro A hA
    exact le_commutatorPreimage (hA.1.trans le_sup_right)
      (E.core_omega_maxElementary_commutator_le structural A hA)
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
/-- The original central-quotient kernel centralizes the core omega center; no central cover is discarded. -/
theorem projection_kernel_centralizes_core_omega
    (hcomm : ⁅omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2),L⁆ ≤ V) :
    S.projection.ker.map L.subtype ≤
      centralizer (omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let U := omegaCenterIn Q
  let K := S.projection.ker.map L.subtype
  have hKL : K ≤ L := map_subtype_le _
  have hKV : K ≤ centralizer (V : Set G) := by
    rintro _ ⟨k,hk,rfl⟩ v hv
    have he := E.equivariant k ⟨v,hv⟩
    rw [show S.projection k = 1 from hk] at he
    have he' : V.normalizerMonoidHom ⟨k,S.chosen.normalizes k.property⟩ ⟨v,hv⟩ = ⟨v,hv⟩ := by
      apply E.coordinates.injective
      apply Multiplicative.toAdd.injective
      simpa using he
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he')).symm
  have hLK : ⁅L,K⁆ ≤ Q := by
    apply le_trans ?_ (pCoreIn_mono_of_normalizes (p := 2) le_sup_left
      (sup_le L.le_normalizer S.chosen.sylow_normalizes_component))
    apply commutator_le.mpr
    rintro l hl _ ⟨k,hk,rfl⟩
    have hk' : QuotientGroup.mk' (pCore 2 L) k ∈ center (L ⧸ pCore 2 L) := by
      change k ∈ (center (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L))
      apply (QuotientGroup.eq_one_iff k).mp
      exact S.quotient.injective ((show S.quotient (QuotientGroup.mk' _ k) = 1 from hk).trans (map_one S.quotient).symm)
    have he : ⁅(⟨l,hl⟩ : L),k⁆ ∈ pCore 2 L := by
      apply (QuotientGroup.eq_one_iff _).mp
      change (QuotientGroup.mk' (pCore 2 L)) ⁅(⟨l,hl⟩ : L),k⁆ = 1
      rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
      exact mem_center_iff.mp hk' _
    exact mem_map_of_mem L.subtype he
  have h1 : ⁅⁅K,L⁆,U⁆ = ⊥ := by
    rw [commutator_comm K L, commutator_eq_bot_iff_le_centralizer]
    exact hLK.trans (le_centralizer_iff.mp
      (fun u hu => ((mem_omegaCenterIn_iff _ _).mp hu).2.1))
  have h2 : ⁅⁅L,U⁆,K⁆ = ⊥ := by
    rw [commutator_comm L U,commutator_eq_bot_iff_le_centralizer]
    exact hcomm.trans (le_centralizer_iff.mp hKV)
  have hc : ⁅U,K⁆ ≤ centralizer (L : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (commutator_commutator_eq_bot_of_rotate h1 h2)
  have hv : ⁅U,K⁆ ≤ V := (commutator_mono le_rfl hKL).trans hcomm
  apply le_centralizer_iff.mp
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  intro x hx
  exact mem_bot.mpr (congrArg (fun v : V => (v : G))
    (SylowNormalizer.Points.natural_fixed_eq_one (E := E) (v := ⟨x,hv hx⟩) (hc hx)))

include E in
/-- Vanishing natural A₇ cohomology supplies the literal L-fixed supplement. -/
theorem core_omega_eq_sup_component_fixed
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
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
  have hc := E.core_omega_commutator_eq_chosen structural hgen
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
/-- Even permutations in the original Sylow action lift through the component and the two-core. -/
theorem sylow_even_le_component_sup_core
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (t : G) (ht : t ∈ T)
    (heven : (E.sourceNormalizerModel structural).permutation
      ⟨t, ((structural G T L S.hypothesis).2.2 V S.chosen).1 ht⟩ ∈
        alternatingGroup (Fin 7)) :
    t ∈ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let H := L ⊔ (T : Subgroup G)
  let D := E.sourceNormalizerModel structural
  have hHV : H ≤ normalizer (V : Set G) :=
    sup_le S.chosen.normalizes (((structural G T L S.hypothesis).2.2 V S.chosen).1)
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
      have hp := E.sourceNormalizerModel_component structural ⟨l,hl⟩
      change q l = _ at hp
      rw [hp]
      exact (S.projection ⟨l,hl⟩).property
    · intro a ha
      obtain ⟨l,hl⟩ := S.projection_surjective ⟨a,ha⟩
      refine ⟨⟨l,(show L ≤ H from le_sup_left) l.property⟩,l.property,?_⟩
      exact (E.sourceNormalizerModel_component structural l).trans (congrArg Subtype.val hl)
  let t' : H := ⟨t,mem_sup_right ht⟩
  have hm : q t' ∈ ((R : Subgroup H) ⊓ B).map q := by
    rw [hmap,hBq]
    exact ⟨mem_map_of_mem q (show t' ∈ R from ht),heven⟩
  obtain ⟨l,hl,he⟩ := hm
  have hc : t * (l : G)⁻¹ ∈ H.pCoreIn 2 := by
    rw [← RecognitionSource.chosen_sylow_centralizer_eq_core S.hypothesis S.chosen structural]
    refine ⟨(T : Subgroup G).mul_mem ht ((T : Subgroup G).inv_mem hl.1),?_⟩
    have hz : q (t' * l⁻¹) = 1 := by rw [map_mul,map_inv,he,mul_inv_cancel]
    have hk : inclusion hHV (t' * l⁻¹) ∈ D.permutation.ker := hz
    rw [normalizerModel_kernel] at hk
    intro v hv
    exact congrArg Subtype.val (hk ⟨v,V.le_normalizer hv⟩ hv)
  have hm := (L ⊔ H.pCoreIn 2).mul_mem (mem_sup_right hc) (mem_sup_left hl.2)
  simpa only [Subgroup.subtype_apply,inv_mul_cancel_right] using hm

include E in
/-- A moving maximum elementary subgroup and the two-core supplement L in LT. -/
theorem join_eq_component_maxElementary_core
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G))
    (hne : (A.subgroupOf (normalizer (V : Set G))).map
      (E.sourceNormalizerModel structural).permutation ≠ ⊥) :
    L ⊔ (T : Subgroup G) = L ⊔ A ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let D := E.sourceNormalizerModel structural
  have hTV := ((structural G T L S.hypothesis).2.2 V S.chosen).1
  obtain ⟨a,ha,hodd⟩ := SetLike.not_le_iff_exists.mp
    (natural_bestOffender_not_le_alternating _
      (E.maxElementary_image_bestOffender structural A hA hne))
  obtain ⟨b,hb,rfl⟩ := ha
  have hbT := hA.1 hb
  have hsup : L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      L ⊔ A ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  apply le_antisymm (sup_le (le_sup_left.trans le_sup_left) ?_)
    (sup_le (sup_le le_sup_left (hA.1.trans le_sup_right)) (pCoreIn_le 2 _))
  intro t ht
  by_cases he : D.permutation ⟨t,hTV ht⟩ ∈ alternatingGroup (Fin 7)
  · exact hsup (E.sylow_even_le_component_sup_core structural t ht he)
  · have hbt : D.permutation (b * ⟨t,hTV ht⟩) ∈ alternatingGroup (Fin 7) := by
      rw [map_mul, Subgroup.mul_mem_iff_of_index_two alternatingGroup.index_eq_two]
      exact iff_of_false hodd he
    have hm := hsup (E.sylow_even_le_component_sup_core structural ((b : G)*t)
      ((T : Subgroup G).mul_mem hbT ht) hbt)
    have hr := (L ⊔ A ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2).mul_mem
      (mem_sup_left (mem_sup_right (A.inv_mem hb))) hm
    simpa only [Subgroup.subtype_apply,inv_mul_cancel_left] using hr

include E in
/-- The L-fixed factor of the core omega center is the literal Sylow-central fixed factor. -/
theorem core_omega_component_fixed_eq_sylow_fixed
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G))
    (hne : (A.subgroupOf (normalizer (V : Set G))).map
      (E.sourceNormalizerModel structural).permutation ≠ ⊥) :
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
    have hxV : x ∈ V := E.core_omega_maxElementary_commutator_le structural A hA
      ((commutator_mono le_rfl inf_le_left) hx)
    have hxC : x ∈ C :=
      (le_normalizer_iff_commutator_le_right.mp (hA.1.trans hTC)) hx
    exact mem_bot.mpr (congrArg (fun v : V => (v : G))
      (SylowNormalizer.Points.natural_fixed_eq_one (E := E) (v := ⟨x,hxV⟩) hxC.2))
  have hQC : Q ≤ centralizer (C : Set G) :=
    le_centralizer_iff.mp (fun c hc => ((mem_omegaCenterIn_iff _ _).mp hc.1).2.1)
  have hHC : H ≤ centralizer (C : Set G) := by
    dsimp only [H]
    rw [E.join_eq_component_maxElementary_core structural A hA hne]
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


/-- The literal omega-center decomposition in source 12.3.7(1), with the
weight-six point-centralizer input retained for the source assembly. -/
theorem core_omega_decomposition_of_weight_six
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
      V ⊔ (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
    Disjoint V (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  have hg := E.thompson_generation_of_weight_six structural escape hsix
  obtain ⟨A,hA,hne,_⟩ := E.core_omega_maxElementary_splitting_of_weight_six structural escape hsix
  exact ⟨(E.core_omega_eq_sup_component_fixed structural hg).trans
    (congrArg (fun C => V ⊔ C)
      (E.core_omega_component_fixed_eq_sylow_fixed structural A hA hne)),
    E.core_omega_factors_disjoint⟩

/-- All three consequences of original 12.3.7(1), using the original
component, Thompson group, permutation map and embedded omega center.
The allowed weight-six premise is discharged by the six-component branch
and the final owner `qt-d-1236-1238-point-centralizers`. -/
theorem source_1237_one_of_weight_six
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T)
    (hsix : ∀ z : V, (z : G) ∈ centralizer (T : Set G) →
      weight (E.coordinates z).toAdd.val = 6 →
      centralizer ({(z : G)} : Set G) ≤ normalizer (L : Set G)) :
    L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
    Function.Surjective (E.sourceNormalizerModel structural).permutation ∧
    omegaCenterIn ((L ⊔ (T : Subgroup G)).pCoreIn 2) =
      V ⊔ (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
    Disjoint V (omegaCenterIn (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  obtain ⟨hg,hs⟩ := E.thompson_and_symmetric_of_weight_six structural escape hsix
  exact ⟨hg,hs,E.core_omega_decomposition_of_weight_six structural escape hsix⟩

end Setup.NaturalCoordinates
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
