module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.DeletedResidualAction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.ResidualComponent
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Tensor.DeletedSource
public import Theory.GroupTheory.AbelianConjugateSpan
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceNormality
/-!
# The residual-component obstruction in the deleted tensor branch

The genuine deleted four-dimensional constituent has no alternating-five
fixed vectors. Thus the literal H∞ moves the flag plane. If I₂ normalized
H∞, the parabolic factorization P = O₂(P)I₂ and the original conjugator
would propagate point centralization to that plane, a contradiction.
The corrected residual product I₂ = O²(P)U then excludes normal or
index-two component orbits, using only U ≤ H.

If G₀ = ⟨I₂,H∞⟩ has nontrivial two-core, adjoining the original Sylow T
preserves that fact. The local-component containment theorem constructs
a strictly larger normal component in G₀T. No containment T ≤ G₀ or
identification U = O₂(H) is assumed.

Source: Aschbacher--Smith, 14.4.10(3), printed p.1011; 12.8.9(1),
1.2.1(3), and 1.2.4. Quotients and inclusions retain the original markings.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.Tensor
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : Subgroup Five} {hAD : AltFive ≤ D}
  {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

omit [Finite G] in
private theorem component_normalized (H : Subgroup G) :
    H ≤ normalizer (component H : Set G) :=
  H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (solvableResidual H))

/-- The marked deleted action forces H∞ to move the actual flag plane. -/
theorem source_tensor_deleted_component_not_centralizes (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) :
    ¬ component F.H ≤ centralizer (F.Vi 2 : Set G) := by
  intro hc
  have hr := source_tensor_point_rank d earlier hq chosen F hne c
  rw [TensorDeleted.image_eq_bot_of_component_centralizes c hdel hc, finrank_bot] at hr
  omega

/-- The original parabolic and conjugator rule out normalization by I₂. -/
theorem source_tensor_deleted_not_normalizes_component (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent) :
    ¬ F.I₂ L ≤ normalizer (component F.H : Set G) := by
  let := chosen.elementary
  intro hn
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
  obtain ⟨_, _, _, _, _, _, _, _, hfactor, hPH, _⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT structural) hcomm hsquare
      (source_seed_geometry d earlier hq chosen F).2.1 hne g hgP hgH
  have hPN : F.P L ≤ normalizer (component F.H : Set G) := by
    rw [hfactor]
    exact sup_le (hPH.trans (component_normalized F.H)) hn
  have hHZ : F.H ≤ centralizer (F.Vi 1 : Set G) :=
    normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  have hKZ : component F.H ≤ centralizer (F.Vi 1 : Set G) :=
    (map_subtype_le _).trans hHZ
  have hspan := le_centralizer_conjugateSpanBy_of_normalizes
    (component F.H) (F.Vi 1) (F.P L) hPN hKZ
  have hplane : F.Vi 2 ≤ conjugateSpanBy (F.Vi 1) (F.P L) := by
    rw [← F.binary_plane_point_span (by decide) L chosen.normalizes g hgP hgH]
    refine sup_le (le_conjugateSpanBy _ _) ?_
    rintro _ ⟨z, hz, rfl⟩
    exact Subgroup.subset_closure ⟨g⁻¹, (F.P L).inv_mem hgP, z, hz, by simp⟩
  exact source_tensor_deleted_component_not_centralizes d earlier hq chosen F hne c hdel
    (hspan.trans (centralizer_le hplane))

/-- The actual two-residual excludes component orbits of size one or two. -/
theorem source_tensor_deleted_no_small_component_orbit (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent)
    {J : Subgroup G} (hIJ : F.I₂ L ≤ J) (hKJ : component F.H ≤ J) :
    ¬ ((component F.H).subgroupOf J).Normal ∧
      (normalizer ((component F.H).subgroupOf J : Set J)).index ≠ 2 := by
  let := chosen.elementary
  have exclude (ho : ((component F.H).subgroupOf J).Normal ∨
      (normalizer ((component F.H).subgroupOf J : Set J)).index = 2) : False := by
    let h := higherRankHypothesis d earlier hq chosen
    obtain ⟨hcomm, hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
    obtain ⟨_, hres, _⟩ :=
      F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
        (h.centralizer_LT structural) hcomm hsquare
        (source_seed_geometry d earlier hq chosen F).2.1 hne g hgP hgH
    have hRJ : twoResidual (F.P L) ≤ J := le_sup_left.trans (hres.ge.trans hIJ)
    have hr := A5.residual_normalizes_of_small_orbit hKJ hRJ ho
    rw [twoResidual_idempotent] at hr
    apply source_tensor_deleted_not_normalizes_component d earlier hq chosen structural
      alternatives F hne g hgP hgH c hdel
    rw [hres]
    exact sup_le hr (F.U_le_H.trans (component_normalized F.H))
  exact ⟨fun hn => exclude (.inl hn), fun hi => exclude (.inr hi)⟩

/-- The literal H∞ cannot itself be a component of a local overgroup of I₂. -/
theorem source_tensor_deleted_not_component_in_local_overgroup (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent)
    {J : Subgroup G} (hIJ : F.I₂ L ≤ J) (hKJ : component F.H ≤ J)
    (hcore : J.pCoreIn 2 ≠ ⊥) :
    ¬ ((component F.H).subgroupOf J).IsCComponent := by
  intro hK
  have ho := Chapter1.Section02.proposition_1_2_1_three_orbit_source
    (Chapter1.Section02.uniqueness_local_quotient_sqtk d.qtke hcore) hK
  have hn := source_tensor_deleted_no_small_component_orbit d earlier hq chosen structural
    alternatives F hne g hgP hgH c hdel hIJ hKJ
  exact ho.elim hn.1 hn.2
/-- The genuine tensor component belongs to the original Sylow local family. -/
theorem source_tensor_component_local (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) (c : CaseFiveCoordinates hAD (V := W) F.H F.U) :
    component F.H ∈ Chapter1.L G (T : Subgroup G) := by
  let K := component F.H
  let J := K ⊔ (T : Subgroup G)
  have hKH : K ≤ F.H := map_subtype_le _
  have hJH : J ≤ F.H := sup_le hKH (F.invariant 1)
  have hKT : (K.subgroupOf J).IsCComponent :=
    (TensorDeleted.component_isCComponent (starComponentEquiv hAD c.actor)).subgroupOf_of_le
      (show K ≤ J from le_sup_left) hJH
  have hp : IsPGroup 2 (F.Vi 1) :=
    IsPGroup.of_card (n := 1) (by simpa using F.card 1 (by decide))
  have hZJ : F.Vi 1 ≤ J := ((F.le_seed 1).trans chosen.le_sylow).trans le_sup_right
  have hZQ := le_pCoreIn_of_normalizes hp hZJ hJH
  have hcore : J.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hz := bot_unique (he ▸ hZQ)
    have hc := F.card 1 (by decide)
    rw [hz, card_bot] at hc
    norm_num at hc
  exact ⟨hKT, ⟨T.subtype le_sup_right, map_subgroupOf_eq_of_le le_sup_right⟩, hcore⟩

/-- The actual generated group is normalized by the original Sylow subgroup. -/
theorem source_tensor_generated_normalized (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    (T : Subgroup G) ≤ normalizer (A5.generated F.H (F.I₂ L) : Set G) := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  obtain ⟨hcomm, hsquare⟩ := source_commutator_squares d earlier hq chosen structural alternatives F
  obtain ⟨_, _, _, _, hIG, hIN, _⟩ :=
    F.binary_generation (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
      (h.centralizer_LT structural) hcomm hsquare
      (source_seed_geometry d earlier hq chosen F).2.1 hne g hgP hgH
  exact (le_inf ((F.invariant 2).trans ((normal_subgroupOf_iff_le_normalizer hIG).mp hIN))
    ((F.invariant 1).trans (component_normalized F.H))).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- A nonzero core of G₀ remains nonzero after adjoining T; containment of T
in G₀ is not imposed. -/
theorem source_tensor_generated_core_extension (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (hcore : (A5.generated F.H (F.I₂ L)).pCoreIn 2 ≠ ⊥) :
    (A5.generated F.H (F.I₂ L) ⊔ (T : Subgroup G)).pCoreIn 2 ≠ ⊥ := by
  let J := A5.generated F.H (F.I₂ L)
  have hn : J ⊔ (T : Subgroup G) ≤ normalizer (J : Set G) :=
    sup_le J.le_normalizer
      (source_tensor_generated_normalized d earlier hq chosen structural alternatives F hne g hgP hgH)
  have hQ := le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 J)
    ((pCoreIn_le 2 J).trans (show J ≤ J ⊔ (T : Subgroup G) from le_sup_left))
    (hn.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  exact fun he => hcore (bot_unique (he ▸ hQ))

/-- In the nontrivial-core branch the literal H∞ has a strictly larger
normal C-component in G₀T. The containing component is constructed. -/
theorem source_tensor_deleted_strict_component (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (c : CaseFiveCoordinates hAD (V := W) F.H F.U)
    (hdel : IsDeletedFour hAD c.constituent)
    (hcore : (A5.generated F.H (F.I₂ L)).pCoreIn 2 ≠ ⊥) :
    ∃ C : Subgroup G,
      component F.H < C ∧ C ≤ A5.generated F.H (F.I₂ L) ⊔ (T : Subgroup G) ∧
      (C.subgroupOf (A5.generated F.H (F.I₂ L) ⊔ (T : Subgroup G))).IsCComponent ∧
      (C.subgroupOf (A5.generated F.H (F.I₂ L) ⊔ (T : Subgroup G))).Normal ∧
      C ∈ Chapter1.L G (T : Subgroup G) := by
  let J := A5.generated F.H (F.I₂ L) ⊔ (T : Subgroup G)
  have hKJ : component F.H ≤ J := le_sup_right.trans le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hIJ : F.I₂ L ≤ J := le_sup_left.trans le_sup_left
  have hJcore := source_tensor_generated_core_extension d earlier hq chosen structural
    alternatives F hne g hgP hgH hcore
  have hlocal := source_tensor_component_local chosen F c
  have hlocalJ : (component F.H).subgroupOf J ∈ Chapter1.L J (T.subgroupOf J) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTJ hKJ).mp ⟨hKJ, hlocal⟩
  have hnorm : ((T.subtype hTJ : Sylow 2 J) : Subgroup J) ≤
      normalizer ((component F.H).subgroupOf J : Set J) := by
    rw [← subgroupOf_normalizer_eq hKJ]
    exact subgroupOf_mono J ((F.invariant 1).trans (component_normalized F.H))
  obtain ⟨C, ⟨hC, hKC, hnC⟩, _⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_source
      (Chapter1.Section02.uniqueness_local_quotient_sqtk d.qtke hJcore)
      (T.subtype hTJ) hlocalJ hnorm
  let C' := C.map J.subtype
  have hC'J : C' ≤ J := map_subtype_le _
  have hmap : C'.subgroupOf J = C := comap_map_eq_self_of_injective J.subtype_injective C
  have hK : component F.H ≤ C' := by
    simpa only [map_subgroupOf_eq_of_le hKJ] using map_mono (f := J.subtype) hKC
  have hne' : component F.H ≠ C' := by
    intro he
    have hh : ((component F.H).subgroupOf J).IsCComponent := by rw [he, hmap]; exact hC
    exact source_tensor_deleted_not_component_in_local_overgroup d earlier hq chosen structural
      alternatives F hne g hgP hgH c hdel hIJ hKJ hJcore hh
  have hc : (C'.subgroupOf J).IsCComponent := hmap.symm ▸ hC
  exact ⟨C', lt_of_le_of_ne hK hne', hC'J, hc, hmap.symm ▸ hnC,
    Chapter1.mem_L_of_cComponent hJcore
      ⟨T.subtype hTJ, map_subgroupOf_eq_of_le hTJ⟩ hC'J hc⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
