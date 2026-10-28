module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Normalizers
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Selection
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.SylowKernelCore
public import CFSG.Quasithin.Chapter13.Section05.LocalGeometry.NonabelianClosure

/-!
# The selected component and the original conjugation quotients

The selected K retains exactly the output of the paragraph after 13.5.20.
The index-two seed and nonabelianness imply that V* has order two; its
normality in T* gives centrality. Evenness of the component's simple central
quotient then gives normalization and K* = [K*,V*]. The evenness input is
still explicit and must be discharged by the source configuration owner.

Both normalizer conclusions of 13.5.19 force Y* to move K*: otherwise K*
would lie in an overgroup whose two-core contains V*, contradicting the
component's commutation with that core. If L₁* normalizes K*, this gives
K* = [K*,Y*] = [K*,L₁*]. The ordinary-branch application discharges the
normalizer-image premise using the existing normalizer theorem.

We construct T_X = N_T(K), X = KL₁T_X as a join and the literal quotient
X/C_X(K*), proving the kernel of its faithful conjugation action. Normality
is only relative to X here. The Sylow property of T_X, F*(X̂), conditions
(i)–(iv), all model alternatives and the remaining clauses of 13.5.21
are separate obligations, not fields in the selection record.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.19 and the first paragraphs of 13.5.21, printed pp.922–923
(PDF pp.939–940).
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition
open Section08.Source
variable {G : Type*} [Group G] [Finite G]

/-- Exactly the selection output after 13.5.20. -/
structure Selected (D : ChapterF.Section09.Setup G) (K : Subgroup G) : Prop where
  le_H : K ≤ D.H
  ccomponent : (K.subgroupOf D.H).IsCComponent
  quasisimple : IsQuasisimple (starImage D.H K)
  quotient : Nonempty ((K ⧸ pCore 2 K) ≃* starImage D.H K)
  moved : ⁅starImage D.H K, starImage D.H D.V⁆ ≠ ⊥

theorem exists_selected (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hu : ¬ IsMulCommutative D.UH)
    (hf : starImage D.H D.V ≤
      centralizer (fittingSubgroup (Hstar D.H) : Set (Hstar D.H))) :
    ∃ K, Selected D K := by
  obtain ⟨K, hKH, hK, hq, he, hm⟩ := exists_component_of_fitting_centralized D h hu hf
  exact ⟨K, hKH, hK, hq, he, hm⟩

variable {D : ChapterF.Section09.Setup G} {K : Subgroup G}

theorem Selected.star_component (s : Selected D K) :
    IsComponent (Hstar D.H) (starImage D.H K) :=
  ⟨(Section08.Components.starImage_isCComponent D.H K s.ccomponent).subnormal,
    s.quasisimple⟩

/-- The exact image of the originally chosen Sylow subgroup. -/
noncomputable def starSylow (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) :
    Sylow 2 (Hstar D.H) :=
  (D.T.subtype h.T_le_H).mapSurjective (f := QuotientGroup.mk' (pCore 2 D.H))
    (QuotientGroup.mk'_surjective _)

theorem starSylow_coe (D : ChapterF.Section09.Setup G) (h : D.Hypothesis) :
    (starSylow D h : Subgroup (Hstar D.H)) = starImage D.H D.T := rfl

/-- Normality of the order-two image gives the source Sylow centrality. -/
theorem star_actor_centralizes_sylow (D : ChapterF.Section09.Setup G)
    (h : D.Hypothesis) (hcard : Nat.card (starImage D.H D.V) = 2) :
    starImage D.H D.V ≤ centralizer (starSylow D h : Set (Hstar D.H)) := by
  let A := starImage D.H D.V
  let S := starImage D.H D.T
  have hAS : A ≤ S := map_mono (comap_mono h.V_le_T)
  have hn : S ≤ normalizer (A : Set (Hstar D.H)) := by
    have hn' : (D.T : Subgroup G).subgroupOf D.H ≤
        normalizer (D.V.subgroupOf D.H : Set D.H) := by
      rw [← subgroupOf_normalizer_eq h.V_le_H]
      exact comap_mono h.T_normalizes_V
    exact (map_mono hn').trans (le_normalizer_map _)
  let : (A.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer hn
  have hc : Nat.card (A.subgroupOf S) = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv).trans hcard
  have hz := central_of_normal_card_two (A.subgroupOf S) hc
  intro a ha x hx
  exact congrArg Subtype.val (mem_center_iff.mp (hz
    (show (⟨a, hAS ha⟩ : S) ∈ A.subgroupOf S from ha)) ⟨x, hx⟩)

/-- Opening step of 13.5.21. The simple-section evenness premise remains
explicit until its earlier-source producer is applied. -/
theorem Selected.normalizes_and_commutator (s : Selected D K)
    (h : D.Hypothesis) (hcard : Nat.card (starImage D.H D.V) = 2)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K))) :
    starImage D.H D.V ≤ normalizer (starImage D.H K : Set (Hstar D.H)) ∧
      ⁅starImage D.H K, starImage D.H D.V⁆ = starImage D.H K := by
  have hn := s.star_component.centralizes_sylow_normalizes (starSylow D h)
    heven (star_actor_centralizes_sylow D h hcard)
  exact ⟨hn, s.star_component.commutator_eq_self_of_normalizes hn s.moved⟩

/-- In the nonabelian branch the source index-two seed supplies |V*|=2. -/
theorem Selected.normalizes_and_commutator_of_nonabelian (s : Selected D K)
    (h : D.Hypothesis) (hindex : D.Vplus.relIndex D.V = 2)
    (hU : ¬ IsMulCommutative D.UH)
    (heven : 2 ∣ Nat.card (starImage D.H K ⧸ center (starImage D.H K))) :
    starImage D.H D.V ≤ normalizer (starImage D.H K : Set (Hstar D.H)) ∧
      ⁅starImage D.H K, starImage D.H D.V⁆ = starImage D.H K :=
  s.normalizes_and_commutator h (LocalGeometry.star_V_card_two h hindex hU) heven

/-- Normalizing the literal image lifts to normalizing K, by the
C-component correspondence through the solvable two-core. -/
theorem Selected.normalizes_of_star (s : Selected D K) (A : Subgroup G)
    (hAH : A ≤ D.H)
    (hn : starImage D.H A ≤ normalizer (starImage D.H K : Set (Hstar D.H))) :
    A ≤ normalizer (K : Set G) := by
  let : Group.IsNilpotent (pCore 2 D.H) := pCore_isNilpotent
  have hn' : A.subgroupOf D.H ≤ normalizer (K.subgroupOf D.H : Set D.H) := by
    rw [← normalizer_cComponent_quotient s.ccomponent (pCore 2 D.H)]
    exact map_le_iff_le_comap.mp hn
  rw [← subgroupOf_normalizer_eq s.le_H] at hn'
  intro a ha
  exact hn' (show (⟨a, hAH ha⟩ : D.H) ∈ A.subgroupOf D.H from ha)

/-- Embedded two-cores commute with the exact star-image construction. -/
theorem starImage_twoCore (H J : Subgroup G) (hJH : J ≤ H) :
    starImage H (J.pCoreIn 2) = (starImage H J).pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have he : (J.pCoreIn 2).subgroupOf H = (J.subgroupOf H).pCoreIn 2 := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le ((pCoreIn_le 2 J).trans hJH),
      map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
      map_subgroupOf_eq_of_le hJH]
  change ((J.pCoreIn 2).subgroupOf H).map q = _
  rw [he, map_pCoreIn_of_ker_isPGroup q hk]
  rfl

private theorem component_centralizes_twoCore {X : Type*} [Group X] [Finite X]
    {C : Subgroup X} (hC : IsComponent X C) :
    ⁅C, pCore 2 X⁆ = ⊥ := by
  rcases hC.normal_dichotomy (pCore 2 X) with hle | hc
  · let := hC.2
    let : IsSimpleGroup (C ⧸ center C) := IsQuasisimple.simple
    let : Nontrivial C := (QuotientGroup.mk'_surjective (center C)).nontrivial
    let : Group.IsNilpotent C := (pCore_isPGroup.to_le hle).isNilpotent
    exact (Group.IsPerfect.not_isSolvable C inferInstance).elim
  · exact hc

private theorem component_centralizes_relative_twoCore {X : Type*} [Group X] [Finite X]
    {C : Subgroup X} (hC : IsComponent X C) (J : Subgroup X) (hCJ : C ≤ J) :
    ⁅C, J.pCoreIn 2⁆ = ⊥ := by
  have hc := congrArg (map J.subtype) (component_centralizes_twoCore (hC.subgroupOf hCJ))
  simpa only [map_commutator, map_subgroupOf_eq_of_le hCJ, Subgroup.map_bot,
    pCoreIn] using hc

/-- A component moved by V* cannot lie in an overgroup whose two-core contains V*. -/
theorem Selected.not_le_star_of_actor_core (s : Selected D K) (J : Subgroup G)
    (hJH : J ≤ D.H) (hVJ : D.V ≤ J.pCoreIn 2) :
    ¬ starImage D.H K ≤ starImage D.H J := by
  intro hKJ
  have hV : starImage D.H D.V ≤ (starImage D.H J).pCoreIn 2 := by
    rw [← starImage_twoCore D.H J hJH]
    exact map_mono (comap_mono hVJ)
  exact s.moved (bot_unique ((commutator_mono le_rfl hV).trans_eq
    (component_centralizes_relative_twoCore s.star_component _ hKJ)))

/-- Both clauses of 13.5.19 force Y* to act nontrivially on the selected K*. -/
theorem Selected.moved_by_Y (s : Selected D K) (Y : Subgroup G)
    (himage : starImage D.H (D.H ⊓ normalizer (Y : Set G)) =
      normalizer (starImage D.H Y : Set (Hstar D.H)))
    (hcore : D.V ≤ (D.H ⊓ normalizer (Y : Set G)).pCoreIn 2) :
    ⁅starImage D.H K, starImage D.H Y⁆ ≠ ⊥ := by
  intro hc
  apply s.not_le_star_of_actor_core _ inf_le_left hcore
  rw [himage]
  exact (commutator_eq_bot_iff_le_centralizer.mp hc).trans
    (Subgroup.centralizer_le_normalizer _)

/-- The second paragraph of 13.5.21, on the original normalizer and star maps. -/
theorem Selected.full_local_commutator (s : Selected D K) (Y : Subgroup G)
    (hYL : Y ≤ D.L₁)
    (himage : starImage D.H (D.H ⊓ normalizer (Y : Set G)) =
      normalizer (starImage D.H Y : Set (Hstar D.H)))
    (hcore : D.V ≤ (D.H ⊓ normalizer (Y : Set G)).pCoreIn 2)
    (hn : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H))) :
    ⁅starImage D.H K, starImage D.H Y⁆ = starImage D.H K ∧
      ⁅starImage D.H K, starImage D.H D.L₁⁆ = starImage D.H K := by
  have hYL' : starImage D.H Y ≤ starImage D.H D.L₁ := map_mono (comap_mono hYL)
  have hY := s.star_component.commutator_eq_self_of_normalizes
    (hYL'.trans hn) (s.moved_by_Y Y himage hcore)
  refine ⟨hY, s.star_component.commutator_eq_self_of_normalizes hn ?_⟩
  intro hb
  exact s.moved_by_Y Y himage hcore (bot_unique
    ((commutator_mono le_rfl hYL').trans_eq hb))

/-- In the ordinary branch Y=L₁, the proved normalizer-image theorem
discharges 13.5.19(1) in the preceding deduction. -/
theorem Selected.ordinary_local_commutator (s : Selected D K) (h : D.Hypothesis)
    (hcore : D.V ≤ (D.H ⊓ normalizer (D.L₁ : Set G)).pCoreIn 2)
    (hn : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H))) :
    ⁅starImage D.H K, starImage D.H D.L₁⁆ = starImage D.H K :=
  (s.full_local_commutator D.L₁ le_rfl (local_normalizer_image D h) hcore hn).2

/-- Actual application to the nonabelian F.9 setup. The remaining evenness
input is universal over its component sections, not a selected family label. -/
theorem exists_selected_full_commutator (D : ChapterF.Section09.Setup G)
    (h : D.Hypothesis) (hindex : D.Vplus.relIndex D.V = 2)
    (hU : ¬ IsMulCommutative D.UH)
    (hf : starImage D.H D.V ≤
      centralizer (fittingSubgroup (Hstar D.H) : Set (Hstar D.H)))
    (heven : ∀ C : Subgroup (Hstar D.H), IsComponent (Hstar D.H) C →
      2 ∣ Nat.card (C ⧸ center C)) :
    ∃ K, Selected D K ∧ D.V ≤ normalizer (K : Set G) ∧
      ⁅starImage D.H K, starImage D.H D.V⁆ = starImage D.H K := by
  obtain ⟨K, s⟩ := exists_selected D h hU hf
  obtain ⟨hn, hc⟩ := s.normalizes_and_commutator_of_nonabelian h hindex hU
    (heven _ s.star_component)
  exact ⟨K, s, s.normalizes_of_star D.V h.V_le_H hn, hc⟩

/-- T_X and X are the original subgroups, before any quotient is taken. -/
def TX (D : ChapterF.Section09.Setup G) (K : Subgroup G) : Subgroup G :=
  (D.T : Subgroup G) ⊓ normalizer (K : Set G)

def X (D : ChapterF.Section09.Setup G) (K : Subgroup G) : Subgroup G :=
  K ⊔ (D.L₁ ⊔ TX D K)

theorem Selected.X_le_H (s : Selected D K) (h : D.Hypothesis) : X D K ≤ D.H :=
  sup_le s.le_H (sup_le (le_sup_left.trans h.local_le) (inf_le_left.trans h.T_le_H))

/-- Normality in X follows from the proved normalization of its generators;
it does not assert the later normality in all of H. -/
theorem Selected.normal_in_X (s : Selected D K) (h : D.Hypothesis)
    (hn : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H))) :
    (K.subgroupOf (X D K)).Normal :=
  normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer
    (sup_le (s.normalizes_of_star _ (le_sup_left.trans h.local_le) hn) inf_le_right))

open scoped Pointwise in
/-- The generated subgroup denoting X is exactly the source setwise product. -/
theorem Selected.X_product (s : Selected D K) (h : D.Hypothesis)
    (hn : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H))) :
    (X D K : Set G) = (K : Set G) * (D.L₁ : Set G) * (TX D K : Set G) := by
  rw [X, coe_mul_of_right_le_normalizer_left K (D.L₁ ⊔ TX D K)
    (sup_le (s.normalizes_of_star _ (le_sup_left.trans h.local_le) hn) inf_le_right),
    coe_mul_of_right_le_normalizer_left D.L₁ (TX D K)
      (inf_le_left.trans (local_residual_normalized D h)), mul_assoc]

/-- Restrict the original map H → H/O₂(H) to the source subgroup X. -/
def starHom (s : Selected D K) (h : D.Hypothesis) : X D K →* Hstar D.H :=
  (QuotientGroup.mk' (pCore 2 D.H)).comp (inclusion (s.X_le_H h))

/-- This is C_X(K*), a preimage under the original star map, not C_X(K). -/
def componentCentralizer (s : Selected D K) (h : D.Hypothesis) : Subgroup (X D K) :=
  (centralizer (starImage D.H K : Set (Hstar D.H))).comap (starHom s h)

/-- The source quotient carrier X/C_X(K*). -/
abbrev Xhat (s : Selected D K) (h : D.Hypothesis) :=
  X D K ⧸ componentCentralizer s h

private theorem star_X_normalizes (s : Selected D K) (h : D.Hypothesis)
    (hn : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H))) :
    starImage D.H (X D K) ≤ normalizer (starImage D.H K : Set (Hstar D.H)) := by
  have hX : X D K ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (show K ≤ X D K from le_sup_left)).mp
      (s.normal_in_X h hn)
  have hi : (X D K).subgroupOf D.H ≤ normalizer (K.subgroupOf D.H : Set D.H) := by
    rw [← subgroupOf_normalizer_eq s.le_H]
    exact comap_mono hX
  exact (map_mono hi).trans (le_normalizer_map _)

def componentConjugation (s : Selected D K) (h : D.Hypothesis)
    (hn : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H))) :
    X D K →* MulAut (starImage D.H K) :=
  (starImage D.H K).normalizerMonoidHom.comp
    ((starHom s h).codRestrict (normalizer (starImage D.H K : Set (Hstar D.H)))
      (fun x => by exact star_X_normalizes s h hn (mem_map_of_mem _ x.property)))

theorem componentConjugation_ker (s : Selected D K) (h : D.Hypothesis)
    (hn : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H))) :
    (componentConjugation s h hn).ker = componentCentralizer s h := by
  rw [componentConjugation, ← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  rfl

theorem componentCentralizer_normal (s : Selected D K) (h : D.Hypothesis)
    (hn : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H))) :
    (componentCentralizer s h).Normal := by
  rw [← componentConjugation_ker s h hn]
  infer_instance

/-- The source quotient has a faithful conjugation action on the same K*. -/
theorem exists_faithful_Xhat_action (s : Selected D K) (h : D.Hypothesis)
    (hn : starImage D.H D.L₁ ≤ normalizer (starImage D.H K : Set (Hstar D.H))) :
    letI := componentCentralizer_normal s h hn
    ∃ f : Xhat s h →* MulAut (starImage D.H K), Function.Injective f ∧
      ∀ x : X D K, f (QuotientGroup.mk' (componentCentralizer s h) x) =
        componentConjugation s h hn x := by
  let := componentCentralizer_normal s h hn
  let f := QuotientGroup.lift (componentCentralizer s h) (componentConjugation s h hn)
    (componentConjugation_ker s h hn).ge
  exact ⟨f, (QuotientGroup.injective_lift_iff _ _ _).mpr
    (componentConjugation_ker s h hn).symm, fun x => QuotientGroup.lift_mk _ _ x⟩

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition
end
