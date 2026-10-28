module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.OrbitMatching.Diagonal
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.CommonPure

/-!
# Critical-pair matching from the literal commutator images

The original central points are distinct because their equality would put
an endpoint conjugator in Mc and contradict noncommutation. In the symmetric
cases, the two orthogonal-product commutator images supply a common pure
vector through the actual natural/dual orbits. Translating the endpoint then
constructs a crossing for the same suitable u, preserving every label.

In the asymmetric case, movement on a denominator/support intersection
puts a nontrivial commutator in both a pure support and the opposite central
point, contrary to suitability. The denominator is literally U intersect
O₂(Mc)^g; its commutator bound is proved from the original F.9 two-core bound.

These are conditional source consumers. Selection of the endpoint and the
rank-one/rank-two image profiles (including asymmetric movement) remain
separate geometric obligations. No fusion-control, outside-centralizer or
crossing premise is used.
Source: Aschbacher--Smith, 14.6.24(4), printed p.1041.
-/

public section
open Subgroup Theory.GroupTheory Representation
open BinaryNaturalDual BinaryNaturalDual.ModelOrbits
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.OrbitMatching
variable {G : Type*} [Group G] [Finite G]
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (W W' : Subgroup G)
    (f : (Mc ⊓ normalizer (W : Set G) : Subgroup G) →*
      BinaryLinear.GL (Fin 3 → ZMod 2)) (hf : Function.Surjective f)
    (c : BinaryConjugationSection (Mc ⊓ normalizer (W : Set G)) W (centralInvolutions T)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp f))
    (s : G) (hs : s ∈ Mc) (hsW : W.map (MulAut.conj s).toMonoidHom = W')
    (u : G) (huW : u ∈ W)
    (hu : ComponentSupports.Suitable
      (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) Mc u)


include hG hempty hM hunique hmany hcard e hab in
/-- Any actual critical endpoint has a different central point. -/
theorem source_critical_points_disjoint
    (i : (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab).CriticalEndpoint) :
    centralInvolutions T ⊓ i.conjugate (centralInvolutions T) = ⊥ := by
  let Z := centralInvolutions T
  let U := conjugateSpanBy (localModule T M) Mc
  have hZ : Nat.card Z = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hMc : Mc = centralizer (Z : Set G) :=
    (plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard hZ).2.2.1
  have hZg : Nat.card (i.conjugate Z) = 2 :=
    (Nat.card_congr ((MulAut.conj i.representative).subgroupMap Z).toEquiv).symm.trans hZ
  apply inf_eq_bot_of_card_two_of_ne Z (i.conjugate Z) hZ hZg
  intro he
  have hn : i.representative ∈ normalizer (Z : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr he.symm
  have hg : i.representative ∈ Mc := hMc.ge (normalizer_le_centralizer_of_card_two Z hZ hn)
  have hUg : i.conjugate U = U := mem_normalizer_iff_map_conj_eq.mp
    (le_normalizer_conjugateSpanBy (localModule T M) Mc hg)
  have hc := critical_spans_do_not_commute
    (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) rfl i
  change ¬ U ≤ centralizer (i.conjugate U : Set G) at hc
  rw [hUg] at hc
  exact hc (le_centralizer_iff_isMulCommutative.mpr hab)

section Symmetric
variable
    (K B : Subgroup G) (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hBU : B ≤ conjugateSpanBy (localModule T M) Mc)
    (φ : K →* BinaryLinear.GL (Fin 3 → ZMod 2)) (hφ : Function.Surjective φ)
    (d : BinaryConjugationSection K B (centralInvolutions T) (naturalDualRepresentation.comp φ))
    (hW : ∀ v : B, (v : G) ∈ W ↔ (d.coordinates v).toAdd.2 = 0)
    (hW' : ∀ v : B, (v : G) ∈ W' ↔ (d.coordinates v).toAdd.1 = 0)
    (i : (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab).CriticalEndpoint)

local notation "U" => conjugateSpanBy (localModule T M) Mc
local notation "Z" => centralInvolutions T
local notation "R" => ⁅U,i.conjugate U⁆

include hf c hs hsW huW hu hK hBU hφ d hW hW' in
/-- The actual pure and singular-diagonal orbits turn two singular commutator
images into a crossing for the original u. Noncommutation and separation of
the central points are derived from the actual endpoint. -/
theorem source_crossing_of_symmetric_commutator_images
    (hRB : R ≤ B) (hRBg : R ≤ i.conjugate B)
    (hZR : i.conjugate Z ≤ R)
    (hsingular : ∀ v ∈ d.imageSpace R, quadratic v = 0)
    (hsingular' : ∀ v ∈ d.imageSpace ((R).map (MulAut.conj i.representative⁻¹).toMonoidHom),
      quadratic v = 0)
    (hpure : ∃ v ∈ d.imageSpace R, IsPure v) :
    ∃ x ∈ Mc, ∃ k : G,
      k = x⁻¹ * i.representative ∧
      (∀ A : Subgroup G, A.map (MulAut.conj k).toMonoidHom =
        (i.conjugate A).map (MulAut.conj x⁻¹).toMonoidHom) ∧
      ∃ q : SourceCrossingGeometry (localModule T M) Mc Mc u,
        q.A = U ∧ q.g = k ∧ ¬ centralizer ({u} : Set G) ≤ Mc := by
  have hZZ := source_critical_points_disjoint hG T hempty hM hunique hmany hcard e hab i
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  obtain ⟨z,hz1,hzall⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp h.point_card
  have hzc : (z : G) ≠ 1 := fun he => hz1 (Subtype.ext he)
  have hZ : ∀ w ∈ Z, w = 1 ∨ w = (z : G) := by
    intro w hw
    by_cases he : w = 1
    · exact Or.inl he
    · exact Or.inr (congrArg Subtype.val (hzall ⟨w,hw⟩ (fun hh => he (congrArg Subtype.val hh))))
  have hpoint : (MulAut.conj i.representative) (z : G) ∈ R :=
    hZR (mem_map_of_mem _ z.property)
  have hpointZ : (MulAut.conj i.representative) (z : G) ∉ Z := by
    intro hz
    have he : (MulAut.conj i.representative) (z : G) = 1 :=
      (show (MulAut.conj i.representative) (z : G) ∈ (⊥ : Subgroup G) from
        hZZ.le ⟨hz,mem_map_of_mem _ z.property⟩)
    exact hzc ((MulAut.conj i.representative).injective (he.trans (map_one _).symm))
  have hmarks := pure_iff_mem_marked_supports d hW hW'
  have havoid (v : B) (hv : IsPure (d.coordinates v).toAdd) : ¬ IsConj (v : G) (z : G) := by
    obtain ⟨hvm,hvz⟩ := (hmarks v).mp hv
    exact source_pure_not_isConj_point hG T hempty hM hunique hmany hcard e hab
      W W' f hf c s hs hsW u huW hu v hvm hvz z z.property
  have hdiag (v w : B) (hv : IsSingularDiagonal (d.coordinates v).toAdd)
      (hw : IsSingularDiagonal (d.coordinates w).toAdd) : IsConj (v : G) (w : G) := by
    obtain ⟨x,_,he⟩ := source_diagonal_match hG T hempty hM hunique hmany hcard e hab
      K B hK hBU φ hφ d v w hv hw
    exact isConj_iff.mpr ⟨x,he⟩
  obtain ⟨a,b,ha,hb,haz,hbz,he⟩ := common_pure_of_singular_images d hmarks
    i.representative z hZ hpoint hpointZ hRB hRBg hsingular hsingular' hpure havoid hdiag
  exact source_crossing_of_common_pure hG T hempty hM hunique hmany hcard e hab
    W W' f hf c s hs hsW u huW hu i a b ha hb haz hbz he

include hf c hs hsW huW hu hK hBU hφ d hW hW' in
/-- Common consumer of the rank-one (line times line) and rank-two (plane
times annihilator line, or its dual) symmetric profiles. No common pure
vector or specified matching pair is assumed. -/
theorem source_crossing_of_orthogonal_commutator_profiles
    (hRB : R ≤ B) (hRBg : R ≤ i.conjugate B)
    (hZR : i.conjugate Z ≤ R)
    (P P' : Submodule (ZMod 2) (Fin 3 → ZMod 2))
    (Q Q' : Submodule (ZMod 2) (Module.Dual (ZMod 2) (Fin 3 → ZMod 2)))
    (he : d.imageSpace R = P.prod Q)
    (he' : d.imageSpace ((R).map (MulAut.conj i.representative⁻¹).toMonoidHom) = P'.prod Q')
    (horth : ∀ x ∈ P, ∀ f ∈ Q, f x = 0)
    (horth' : ∀ x ∈ P', ∀ f ∈ Q', f x = 0)
    (hne : P ≠ ⊥ ∨ Q ≠ ⊥) :
    ∃ x ∈ Mc, ∃ k : G,
      k = x⁻¹ * i.representative ∧
      (∀ A : Subgroup G, A.map (MulAut.conj k).toMonoidHom =
        (i.conjugate A).map (MulAut.conj x⁻¹).toMonoidHom) ∧
      ∃ q : SourceCrossingGeometry (localModule T M) Mc Mc u,
        q.A = U ∧ q.g = k ∧ ¬ centralizer ({u} : Set G) ≤ Mc := by
  obtain ⟨hsing,hp⟩ := orthogonal_product_profile d P Q he horth hne
  have hs' : ∀ v ∈ d.imageSpace ((R).map (MulAut.conj i.representative⁻¹).toMonoidHom),
      quadratic v = 0 := by
    intro v hv
    rw [he'] at hv
    exact horth' v.1 hv.1 v.2 hv.2
  exact source_crossing_of_symmetric_commutator_images hG T hempty hM hunique hmany hcard e hab
    W W' f hf c s hs hsW u huW hu K B hK hBU φ hφ d hW hW' i hRB hRBg hZR hsing hs' hp

end Symmetric
include hf c hs hsW huW hu in
/-- The asymmetric denominator/support movement contradicts the actual pure
orbit. The rank-two calculation must supply this movement on one of the two
supports; neither a pure point-class element nor the contradiction is an input. -/
theorem source_false_of_moving_denominator_support
    (i : (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab).CriticalEndpoint)
    (S : Subgroup G) (hS : S = W ∨ S = W')
    (hn : i.conjugate (conjugateSpanBy (localModule T M) Mc) ≤ normalizer (S : Set G))
    (hm : ¬ i.conjugate (conjugateSpanBy (localModule T M) Mc) ≤ centralizer
      (((conjugateSpanBy (localModule T M) Mc ⊓ i.conjugate (Mc.pCoreIn 2)) ⊓ S) : Set G)) :
    False := by
  have hZZ := source_critical_points_disjoint hG T hempty hM hunique hmany hcard e hab i
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let U := conjugateSpanBy (localModule T M) Mc
  let D := U ⊓ i.conjugate (Mc.pCoreIn 2)
  let R := ⁅i.conjugate U,D ⊓ S⁆
  have hR : R ≠ ⊥ := fun he => hm (commutator_eq_bot_iff_le_centralizer.mp he)
  have hpoint : R ≤ i.conjugate (centralInvolutions T) := by
    have hc := map_mono (f := (MulAut.conj i.representative).toMonoidHom)
      h.commutator_UH_QH_le_point
    rw [map_commutator] at hc
    exact (commutator_mono le_rfl (inf_le_left.trans inf_le_right)).trans hc
  have hsupport : R ≤ S :=
    (commutator_mono le_rfl inf_le_right).trans (le_normalizer_iff_commutator_le_right.mp hn)
  obtain ⟨v,hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hR
  have hvz : (v : G) ∉ centralInvolutions T := by
    intro hz
    apply hv1
    exact Subtype.ext (show (v : G) ∈ (⊥ : Subgroup G) from hZZ.le ⟨hz,hpoint v.property⟩)
  have hvpure : (v : G) ∈ W ∨ (v : G) ∈ W' := by
    rcases hS with rfl | rfl
    · exact Or.inl (hsupport v.property)
    · exact Or.inr (hsupport v.property)
  obtain ⟨z,hz,he⟩ := hpoint v.property
  have hvconj : IsConj (v : G) z := (isConj_iff.mpr ⟨i.representative,he⟩ :
    IsConj z (v : G)).symm
  exact source_pure_not_isConj_point hG T hempty hM hunique hmany hcard e hab
    W W' f hf c s hs hsW u huW hu v hvpure hvz z hz hvconj

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.OrbitMatching
