module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionComplete
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At

/-!
# Fusion at the original ambient group and Sylow subgroup: Basic

These are ambient-local versions of the existing source fusion proofs. Only
the structural premise changes: each use is at the original G,T,L,V. The
literal module actions, quotient maps, point Sylow subgroups and conjugators
are preserved. The universal APIs remain available in their original modules.

Source: Aschbacher–Smith, 12.2.16, printed pp.799–800; the reducible
normalizer argument uses 3.3.1 and B.5.1 as in the original proofs.
-/

/- Adapted from GlobalTI. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08

variable {G : Type*} [Group G] [Finite G]

variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

public theorem point_centralizer_le_chosen_normalizer_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    centralizer ({v} : Set G) ≤ normalizer (V : Set G) := by
  have hTI := ((structural L h).2.2 V D).2.2.1
  exact (le_inf (hnone v hv hv1) le_rfl).trans
    (inf_elementCentralizer_le_normalizer_of_trivial_intersections hTI hv hv1)

public theorem globalTI_of_fusion_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (hfusion : ∀ x y : G, x ∈ V → y ∈ V → x ≠ 1 → y ≠ 1 →
      (∃ g : G, g * x * g⁻¹ = y) →
      ∃ m ∈ normalizer (L : Set G), m * x * m⁻¹ = y) :
    IsTISubgroup V := by
  apply (isTISubgroup_iff V).mpr
  intro g hg x hx hgx
  by_contra hx1
  have hy1 : g * x * g⁻¹ ≠ 1 := fun he =>
    hx1 ((MulAut.conj g).map_eq_one_iff.mp he)
  have hgM := conjugator_mem_of_centralizer_le (hnone x hx hx1)
    (hfusion x (g * x * g⁻¹) hx hgx hx1 hy1 ⟨g, rfl⟩)
  rcases ((structural L h).2.2 V D).2.2.1 g hgM with hd | he
  · have hy : g * x * g⁻¹ ∈ V ⊓ V.map (MulAut.conj g).toMonoidHom :=
      ⟨hgx, mem_map_of_mem _ hx⟩
    exact hy1 (mem_bot.mp (hd ▸ hy))
  · exact hg (mem_normalizer_iff_map_conj_eq.mpr he)

public theorem globalTI_of_natural_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V) {d : ℕ}
    (hnatural : Chapter6.Source.IsConjugationModel L V
      (Representation.specialLinearNatural (k := ZMod 2) d)) :
    IsTISubgroup V := by
  apply globalTI_of_fusion_at h D structural hnone
  intro x y hx hy hx1 hy1 _
  obtain ⟨l, hl, he⟩ := natural_vector_transitive hnatural hx hy hx1 hy1
  exact ⟨l, L.le_normalizer hl, he⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionTransitive. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08

variable {G : Type*} [Group G] [Finite G]

variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

public theorem globalTI_of_chosenAction_transitive_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (ht : ∀ v w : D.space, v ≠ 0 → w ≠ 0 → ∃ l : L, D.chosenAction l v = w) :
    IsTISubgroup V := by
  apply globalTI_of_fusion_at h D structural hnone
  intro x y hx hy hx1 hy1 _
  obtain ⟨l,hl,he⟩ := chosen_vector_transitive D ht hx hy hx1 hy1
  exact ⟨l,L.le_normalizer hl,he⟩

public theorem globalTI_of_four_dimensional_image_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (hd : Module.finrank (ZMod 2) D.space = 4)
    (hc : 45 ∣ Nat.card (actionImage D.chosenAction)) : IsTISubgroup V := by
  apply globalTI_of_chosenAction_transitive_at h D structural hnone
  intro v w hv hw
  exact BinaryFourOrbit.representation_transitive D.chosenAction hd hc hv hw

omit [Finite G] in

private theorem chosen_action_group_ker_at (D : ChosenModule T L V) :
    D.chosenAction.asGroupHom.ker = (centralizer (V : Set G)).subgroupOf L := by
  ext l
  constructor
  · intro hl
    have hl' : D.chosenAction l = 1 := congrArg Units.val hl
    apply mem_centralizer_iff.mpr
    intro v hv
    obtain ⟨w,hw⟩ := D.spaceEquiv.surjective ⟨v,hv⟩
    have he := congrArg (fun z : D.space => (z.val.toMul.val : G))
      (LinearMap.congr_fun hl' w.toAdd)
    have hw' : (w.toAdd.val.toMul.val : G) = v :=
      (D.spaceEquiv_apply w.toAdd).symm.trans (congrArg Subtype.val hw)
    change (l : G) * (w.toAdd.val.toMul.val : G) * (l : G)⁻¹ =
      (w.toAdd.val.toMul.val : G) at he
    rw [hw'] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hl
    apply Units.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (l : G) * (v.val.toMul.val : G) * (l : G)⁻¹ = (v.val.toMul.val : G)
    have hv : (v.val.toMul.val : G) ∈ V :=
      D.image_eq.le (mem_map_of_mem _ (mem_map_of_mem _ v.property))
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hl) _ hv).symm

public theorem globalTI_of_alternating_seven_four_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    [((centralizer (V : Set G)).subgroupOf L).Normal]
    (e : (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) D.space = 4) : IsTISubgroup V := by
  apply globalTI_of_four_dimensional_image_at h D structural hnone hd
  have hc : Nat.card (actionImage D.chosenAction) =
      Nat.card (L ⧸ (centralizer (V : Set G)).subgroupOf L) := by
    rw [actionImage, ← Nat.card_congr
      (QuotientGroup.quotientKerEquivRange D.chosenAction.asGroupHom).toEquiv]
    rw [chosen_action_group_ker_at D]
  rw [hc, Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionFixedLine. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08

variable {G : Type*} [Group G] [Finite G]

variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

public theorem normalizer_centralizes_fixed_line_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) {z : G}
    (hz : z ∈ V) (hz1 : z ≠ 1) (hzL : z ∈ centralizer (L : Set G))
    (hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z) :
    normalizer (L : Set G) ≤ centralizer ({z} : Set G) := by
  have hMV : normalizer (L : Set G) ≤ normalizer (V : Set G) := by
    rcases ((structural L h).2.2 V D).2.2.2 with hN | he
    · exact hN
    · exact (hz1 (mem_bot.mp (he ▸ (show z ∈ V ⊓ centralizer (L : Set G) from ⟨hz,hzL⟩)))).elim
  intro m hm
  have hmzV : m * z * m⁻¹ ∈ V := (mem_normalizer_iff.mp (hMV hm) z).mp hz
  have hmzL : m * z * m⁻¹ ∈ centralizer (L : Set G) :=
    (mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer L hm) z).mp hzL
  have he : m * z * m⁻¹ = z := (hfixed _ hmzV hmzL).resolve_left
    (fun he => hz1 ((MulAut.conj m).map_eq_one_iff.mp he))
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)

public theorem fixed_line_weakly_closed_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V) {z : G}
    (hz : z ∈ V) (hz1 : z ≠ 1) (hzL : z ∈ centralizer (L : Set G))
    (hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z)
    {w : G} (hw : w ∈ V) (hzw : IsConj z w) : w = z := by
  have hCz : centralizer ({z} : Set G) = normalizer (L : Set G) :=
    le_antisymm (hnone z hz hz1)
      (normalizer_centralizes_fixed_line_at h D structural hz hz1 hzL hfixed)
  obtain ⟨g,hg⟩ := isConj_iff.mp hzw
  have hw1 : w ≠ 1 := fun he => hz1
    ((MulAut.conj g).map_eq_one_iff.mp (hg.trans he))
  have hc : Nat.card (centralizer ({w} : Set G)) =
      Nat.card (normalizer (L : Set G)) := by
    rw [← hCz]
    have he := Nat.card_congr
      (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) z).toEquiv
    simpa only [MulAut.conj_apply,hg] using he.symm
  have hCw : centralizer ({w} : Set G) = normalizer (L : Set G) :=
    eq_of_le_of_card_ge (hnone w hw hw1) hc.ge
  have hwL : w ∈ centralizer (L : Set G) := by
    intro l hl
    have hh : l ∈ centralizer ({w} : Set G) := hCw ▸ L.le_normalizer hl
    exact mem_centralizer_singleton_iff.mp hh
  exact (hfixed w hw hwL).resolve_left hw1

public theorem conjugator_mem_of_fixed_line_image_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V) {z : G}
    (hz : z ∈ V) (hz1 : z ≠ 1) (hzL : z ∈ centralizer (L : Set G))
    (hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z)
    {g : G} (hgz : g * z * g⁻¹ ∈ V) : g ∈ normalizer (L : Set G) := by
  have he := fixed_line_weakly_closed_at h D structural hnone hz hz1 hzL hfixed hgz
    (isConj_iff.mpr ⟨g,rfl⟩)
  exact hnone z hz hz1 (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he))

public theorem normalizer_le_of_fixed_line_in_omega_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V) {z : G}
    (hz : z ∈ V) (hz1 : z ≠ 1) (hzL : z ∈ centralizer (L : Set G))
    (hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z)
    (R : Subgroup G) (hzR : z ∈ omegaCenterIn R) (hRV : omegaCenterIn R ≤ V) :
    normalizer (R : Set G) ≤ normalizer (L : Set G) := by
  intro g hg
  apply conjugator_mem_of_fixed_line_image_at h D structural hnone hz hz1 hzL hfixed
  exact hRV ((mem_normalizer_iff.mp (normalizer_le_normalizer_omegaCenterIn R hg) z).mp hzR)

public theorem globalTI_of_transitive_off_fixed_line_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V) {z : G}
    (hz : z ∈ V) (hz1 : z ≠ 1) (hzL : z ∈ centralizer (L : Set G))
    (hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = z)
    (ht : ∀ x y : G, x ∈ V → y ∈ V → x ≠ 1 → y ≠ 1 → x ≠ z → y ≠ z →
      ∃ l ∈ L, l * x * l⁻¹ = y) : IsTISubgroup V := by
  apply globalTI_of_fusion_at h D structural hnone
  intro x y hx hy hx1 hy1 hxy
  have hc : IsConj x y := isConj_iff.mpr hxy
  by_cases hxz : x = z
  · subst x
    have hyz := fixed_line_weakly_closed_at h D structural hnone hz hz1 hzL hfixed hy hc
    exact ⟨1,one_mem _,by simp [hyz]⟩
  have hyz : y ≠ z := by
    intro he
    subst y
    exact hxz (fixed_line_weakly_closed_at h D structural hnone hz hz1 hzL hfixed hx hc.symm)
  obtain ⟨l,hl,he⟩ := ht x y hx hy hx1 hy1 hxz hyz
  exact ⟨l,L.le_normalizer hl,he⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionSLThree. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08 Section04.SmallFusion

variable {G : Type*} [Group G] [Finite G]

variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

public theorem globalTI_of_slThree_extension_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (E : SLThreeExtension D) (hne : fixedSubgroup L V ≠ ⊥) : IsTISubgroup V := by
  obtain ⟨z,hz1,hall⟩ := (Nat.card_eq_two_iff' (1 : fixedSubgroup L V)).mp
    (E.fixed_card_eq_two hne)
  have hz1' : (z : G) ≠ 1 := fun he => hz1 (Subtype.ext he)
  have hfixed : ∀ w ∈ V, w ∈ centralizer (L : Set G) → w = 1 ∨ w = (z : G) := by
    intro w hw hL
    by_cases hw1 : w = 1
    · exact Or.inl hw1
    · exact Or.inr (congrArg Subtype.val (hall ⟨w,hw,hL⟩
        (fun he => hw1 (congrArg Subtype.val he))))
  apply globalTI_of_transitive_off_fixed_line_at h D structural hnone
    z.property.1 hz1' z.property.2 hfixed
  intro x y hx hy hx1 hy1 hxz hyz
  exact E.transitive_nonfixed hne x y hx hy
    (fun hc => hxz ((hfixed x hx hc.2).resolve_left hx1))
    (fun hc => hyz ((hfixed y hy hc.2).resolve_left hy1))

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionAlternatingEight. -/
section
open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

variable {G : Type*} [Group G] [Finite G]

variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

namespace AlternatingEightFusion

variable (C : AlternatingEightFusion T L V)

public theorem fixed_mem_pointSylow_omega_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) : (C.z : G) ∈ omegaCenterIn C.pointSylow := by
  let := D.elementary
  have hMC := normalizer_centralizes_fixed_line_at h D structural
    C.z.property C.z_ne C.z_fixed C.fixed_line
  apply (mem_omegaCenterIn_iff C.pointSylow (C.z : G)).mpr
  refine ⟨⟨D.le_sylow C.z.property,?_⟩,?_,
    elemPow_eq_one_of_isElementaryAbelian _ C.z.property⟩
  · apply mem_centralizer_singleton_iff.mpr
    exact congrArg (fun w : V => (w : G)) (mul_comm C.z C.v)
  · intro r hr
    exact mem_centralizer_singleton_iff.mp (hMC ((structural L h).1 hr.1))

public theorem false_of_omega_le_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (homega : omegaCenterIn C.pointSylow ≤ V) : False := by
  exact C.outside (normalizer_le_of_fixed_line_in_omega_at h D structural hnone
    C.z.property C.z_ne C.z_fixed C.fixed_line C.pointSylow
    (C.fixed_mem_pointSylow_omega_at h D structural) homega C.normalizes)

end AlternatingEightFusion

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end

/- Adapted from FusionAssembly. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08 Section04.SmallFusion

variable {G : Type*} [Group G] [Finite G]

variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

public theorem globalTI_of_row_reductions_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (fixedFree : V ⊓ centralizer (L : Set G) = ⊥ → IsTISubgroup V)
    (reducible : V ⊓ centralizer (L : Set G) ≠ ⊥ →
      IsTISubgroup V ∨ Nonempty (AlternatingEightFusion T L V))
    (eight : ∀ C : AlternatingEightFusion T L V, omegaCenterIn C.pointSylow ≤ V) :
    IsTISubgroup V := by
  classical
  by_cases hc : V ⊓ centralizer (L : Set G) = ⊥
  · exact fixedFree hc
  · rcases reducible hc with ht | hC
    · exact ht
    · let C : AlternatingEightFusion T L V := Classical.choice hC
      exact (C.false_of_omega_le_at h D structural hnone (eight C)).elim

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from LocalConfigurationPrefix. -/
section
public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08 ChapterE

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

public theorem chosen_sylow_centralizer_eq_core_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    (T : Subgroup G) ⊓ centralizer (V : Set G) =
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have he := (D.fundamentalSetup h.toHypothesis1221).sylow_centralizer_module hu
  have ho : componentOrbit V (T : Subgroup G) = V :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer V T V le_rfl
      (((structural L h).2.2 V D).1)) (le_componentOrbit V T)
  rw [D.fundamentalSetup_module, ho] at he
  simpa only [Chapter3.Section02.localJoin, D.localOrbit_eq] using he

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionFixedFreeRows. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08 ChapterB.QuasisimpleSource

variable {G : Type*} [Group G] [Finite G]

variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

public theorem globalTI_of_alternating_six_fixedFree_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (a : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulCentralAction (alternatingNatural 6)) :
    IsTISubgroup V := by
  let := D.actionCentralizer_normal
  let e := (fixedFreeQuotientEquiv D hc).trans a.linearEquiv
  apply globalTI_of_chosenAction_transitive_at h D structural hnone
  intro v w hv hw
  obtain ⟨s,hs⟩ := BinaryPermutation.alternatingSix_natural_nonzero_transitive
    (e v) (e w) (by simpa using hv) (by simpa using hw)
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective
    ((centralizer (V : Set G)).subgroupOf L) (a.groupEquiv.symm s)
  refine ⟨l,e.injective ?_⟩
  change a.linearEquiv (fixedFreeQuotientEquiv D hc (D.chosenAction l v)) = e w
  rw [fixedFreeQuotientEquiv_action]
  change a.linearEquiv (D.faithfulCentralAction
    (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l)
    (fixedFreeQuotientEquiv D hc v)) = e w
  rw [a.intertwines,hl,a.groupEquiv.apply_symm_apply]
  exact hs

public theorem globalTI_of_g2_fixedFree_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (a : ActionEquiv D.centralQuotientAction
      ((g2Natural (ZMod 2)).comp (commutator (Atlas.G2.Model (ZMod 2))).subtype)) :
    IsTISubgroup V := by
  let e := (fixedFreeQuotientEquiv D hc).trans a.linearEquiv
  apply globalTI_of_chosenAction_transitive_at h D structural hnone
  intro v w hv hw
  obtain ⟨s,hs⟩ := Atlas.G2.Natural.derivedAction_transitive
    (ZMod 2) (e v) (e w) (by simpa using hv) (by simpa using hw)
  obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (a.groupEquiv.symm s)
  refine ⟨l,e.injective ?_⟩
  change a.linearEquiv (fixedFreeQuotientEquiv D hc (D.chosenAction l v)) = e w
  rw [fixedFreeQuotientEquiv_action]
  change a.linearEquiv (D.centralQuotientAction (QuotientGroup.mk' (pCore 2 L) l)
    (fixedFreeQuotientEquiv D hc v)) = e w
  rw [a.intertwines,hl,a.groupEquiv.apply_symm_apply]
  exact hs

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionFixedFreeOrbits. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08 ChapterB.QuasisimpleSource

variable {G : Type*} [Group G] [Finite G] {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

public theorem globalTI_of_conjugacyOrbit_separation_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (hsep : ∀ x y : G, x ∈ V → y ∈ V → x ≠ 1 → y ≠ 1 →
      (conjugacyOrbit L x).ncard = (conjugacyOrbit L y).ncard →
      ∃ l ∈ L, l * x * l⁻¹ = y) : IsTISubgroup V := by
  let N := normalizer (L : Set G) ⊓ normalizer (V : Set G)
  have hLN : L ≤ N := le_inf L.le_normalizer D.normalizes
  have hCN (x : G) (hx : x ∈ V) (hx1 : x ≠ 1) :
      centralizer ({x} : Set G) ≤ N :=
    le_inf (hnone x hx hx1)
      (point_centralizer_le_chosen_normalizer_at h D structural hnone hx hx1)
  have ho (x : G) (hx : x ∈ V) (hx1 : x ≠ 1) :
      conjugacyOrbit N x = conjugacyOrbit L x := by
    ext y
    constructor
    · rintro ⟨m,rfl⟩
      have hy : (m : G) * x * (m : G)⁻¹ ∈ V := (m.property.2 x).mp hx
      have hy1 : (m : G) * x * (m : G)⁻¹ ≠ 1 :=
        fun he => hx1 ((MulAut.conj (m : G)).map_eq_one_iff.mp he)
      obtain ⟨l,hl,he⟩ := hsep x _ hx hy hx1 hy1
        (conjugacyOrbit_normalizer L x m m.property.1).symm
      exact ⟨⟨l,hl⟩,he⟩
    · rintro ⟨l,rfl⟩
      exact ⟨⟨l,hLN l.property⟩,rfl⟩
  apply globalTI_of_fusion_at h D structural hnone
  intro x y hx hy hx1 hy1 hxy
  obtain ⟨g,rfl⟩ := hxy
  have hc : Nat.card (centralizer ({x} : Set G)) =
      Nat.card (centralizer ({g * x * g⁻¹} : Set G)) :=
    Nat.card_congr (CentralizerSmallKernelTransport.centralizerEquiv
      (MulAut.conj g) x).toEquiv
  have hox := conjugacyOrbit_mul_centralizer N x (hCN x hx hx1)
  have hoy := conjugacyOrbit_mul_centralizer N (g*x*g⁻¹) (hCN _ hy hy1)
  rw [ho x hx hx1] at hox
  rw [ho _ hy hy1,← hc] at hoy
  have he := Nat.eq_of_mul_eq_mul_right
    (Nat.card_pos (α := centralizer ({x} : Set G))) (hox.trans hoy.symm)
  obtain ⟨l,hl,he⟩ := hsep x _ hx hy hx1 hy1 he
  exact ⟨l,L.le_normalizer hl,he⟩

public theorem globalTI_of_chosen_orbit_separation_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (hsep : OrbitCardSeparates D.chosenAction) : IsTISubgroup V := by
  apply globalTI_of_conjugacyOrbit_separation_at h D structural hnone
  intro x y hx hy hx1 hy1 hcard
  let v := (D.spaceEquiv.symm ⟨x,hx⟩).toAdd
  let w := (D.spaceEquiv.symm ⟨y,hy⟩).toAdd
  let f : D.space → G := fun v => D.spaceEquiv (Multiplicative.ofAdd v)
  have hf : Function.Injective f := Subtype.val_injective.comp
    (D.spaceEquiv.injective.comp Multiplicative.ofAdd.injective)
  have hfv : f v = x := congrArg Subtype.val (D.spaceEquiv.apply_symm_apply ⟨x,hx⟩)
  have hfw : f w = y := congrArg Subtype.val (D.spaceEquiv.apply_symm_apply ⟨y,hy⟩)
  have hf0 : f 0 = 1 := congrArg Subtype.val D.spaceEquiv.map_one
  have he (l : L) (v : D.space) :
      f (D.chosenAction l v) = (l : G) * f v * (l : G)⁻¹ := by
    dsimp only [f]
    rw [D.spaceEquiv_apply,D.spaceEquiv_apply]
    rfl
  have himage (v : D.space) :
      f '' (Set.range fun l : L => D.chosenAction l v) = conjugacyOrbit L (f v) := by
    ext z
    constructor
    · rintro ⟨_,⟨l,rfl⟩,rfl⟩
      exact ⟨l,(he l v).symm⟩
    · rintro ⟨l,rfl⟩
      exact ⟨D.chosenAction l v,⟨l,rfl⟩,he l v⟩
  have hc : (Set.range fun l : L => D.chosenAction l v).ncard =
      (Set.range fun l : L => D.chosenAction l w).ncard := by
    rw [← Set.ncard_image_of_injective _ hf,← Set.ncard_image_of_injective _ hf,
      himage,himage,hfv,hfw]
    exact hcard
  have hv : v ≠ 0 := fun hz => hx1 (hfv.symm.trans ((congrArg f hz).trans hf0))
  have hw : w ≠ 0 := fun hz => hy1 (hfw.symm.trans ((congrArg f hz).trans hf0))
  obtain ⟨l,hl⟩ := hsep v w hv hw hc
  refine ⟨l,l.property,?_⟩
  have hh := congrArg f hl
  rwa [he,hfv,hfw] at hh

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end

/- Adapted from FusionFixedFree. -/
section
public noncomputable section

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

open ChapterI.Section06To08 ChapterB.QuasisimpleSource

variable {G : Type*} [Group G] [Finite G]

variable {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}

public theorem globalTI_of_quotient_orbit_separation_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (hsep : OrbitCardSeparates D.quotientAction) : IsTISubgroup V := by
  apply globalTI_of_chosen_orbit_separation_at h D structural hnone
  exact hsep.of_intertwining (QuotientGroup.mk' (pCore 2 L))
    (QuotientGroup.mk'_surjective _) (LinearEquiv.refl _ _) (fun _ _ => rfl)

public theorem globalTI_of_fixedFree_alternating_orbits_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) {n : ℕ}
    (a : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulCentralAction (alternatingNatural n))
    (hsep : OrbitCardSeparates (alternatingNatural n)) : IsTISubgroup V := by
  let := D.actionCentralizer_normal
  apply globalTI_of_chosen_orbit_separation_at h D structural hnone
  let f := a.groupEquiv.toMonoidHom.comp
    (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L))
  exact hsep.of_intertwining f
    (a.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
    ((fixedFreeQuotientEquiv D hc).trans a.linearEquiv) (by
      intro l v
      change a.linearEquiv (fixedFreeQuotientEquiv D hc (D.chosenAction l v)) = _
      rw [fixedFreeQuotientEquiv_action]
      exact a.intertwines (QuotientGroup.mk' _ l) _)

public theorem globalTI_of_fixedFree_module_alternatives_at
    (h : Hypothesis1223 K T L) (D : ChosenModule T L V)
    (structural : Structural1222At K T) (hnone : NoEscape L V)
    (rows : ModuleAlternatives1222 D)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) :
    IsTISubgroup V := by
  cases rows with
  | linear n _ a =>
      exact globalTI_of_natural_at h D structural hnone (D.conjugationModel_of_quotientAction a)
  | linearThreeExtension e hd _ =>
      exact (not_linear_three_four_fixedFree D hc e hd).elim
  | linearFiveExterior e hd hi =>
      let := hi
      exact globalTI_of_quotient_orbit_separation_at h D structural hnone
        (SL5ExteriorSquare.marked_irreducible_ten_orbitCardSeparates D.quotientAction e hd)
  | alternating n hn hu a =>
      by_cases he : n = 6
      · subst n
        exact globalTI_of_alternating_six_fixedFree_at h D structural hnone hc a
      · have hn : n = 5 ∨ n = 7 ∨ n = 8 := by omega
        apply globalTI_of_fixedFree_alternating_orbits_at h D structural hnone hc a
        rcases hn with rfl | rfl | rfl
        · exact BinaryPermutation.five_natural_orbitCardSeparates
        · exact BinaryPermutation.seven_natural_orbitCardSeparates
        · exact BinaryPermutation.eight_natural_orbitCardSeparates
  | alternatingSevenFour e hd =>
      let := D.actionCentralizer_normal
      exact globalTI_of_alternating_seven_four_at h D structural hnone e hd
  | g2 a => exact globalTI_of_g2_fixedFree_at h D structural hnone hc a
  | tripleSix e hd hf hi =>
      exact globalTI_of_quotient_orbit_separation_at h D structural hnone
        (Hexacode.marked_irreducible_six_orbitCardSeparates D.quotientAction e hf hi hd)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource

end
end
