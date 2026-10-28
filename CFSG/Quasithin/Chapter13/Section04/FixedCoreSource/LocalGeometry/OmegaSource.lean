module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationAction
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Weights
public import Theory.Representation.BinaryPermutation.SixCoreOrbits
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import CFSG.Quasithin.Chapter3.Section02.SourceComponentThompson

/-!
# Escaping omega points and Thompson generation in the original core

The full normalizer permutes the six coordinates. Thus the Sylow two-group
preserves each fifteen-element nonconstant weight class and fixes a point
in it. Transport through the actual augmentation marking puts this point
in V intersect Ω₁Z(T). Equal-weight L-conjugacy preserves full-centralizer
escape, supplying the exact point required by the source argument.

Its escaping involution centralizer gives an outside maximal two-local.
The original fixed line puts C_G(Ω₁Z(T)) inside N_G(L), so the genuine
Chapter 3 Thompson theorem proves [L,J(T)]=L. No escaping omega point or
Thompson-movement premise is assumed. The preceding 12.2.13 source input
and universal structural theorem remain explicit.
Source: Aschbacher--Smith 13.3.5(3) and 13.4.3(1), printed pp.886,897.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
/-- Each nonconstant weight class has a representative in the actual Sylow omega-center. -/
theorem omega_representative_of_nonfixed
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hn : normalizer (L : Set G) ≤ normalizer (V : Set G))
    (v : V) (hv : v.val ∉ centralizer (L : Set G)) :
    ∃ z : V, z.val ∈ omegaOneCenterAmbient (T : Subgroup G) ∧
      z.val ∉ centralizer (L : Set G) ∧ m.weight z = m.weight v := by
  obtain ⟨q,hq,_,_⟩ := Nonsolvable.exists_core_normalizer_permutation D m hn
  let f := q.comp (inclusion D.sylow_normalizes_component)
  let : MulAction T (core (Fin 6)) := {
    smul := fun t w => coreRepresentation (Fin 6) (f t) w
    one_smul := fun w => by
      change coreRepresentation (Fin 6) (f 1) w = w
      rw [map_one,map_one]; rfl
    mul_smul := fun a b w => by
      change coreRepresentation (Fin 6) (f (a*b)) w =
        coreRepresentation (Fin 6) (f a) (coreRepresentation (Fin 6) (f b) w)
      rw [map_mul,map_mul]; rfl }
  let X : SubMulAction T (core (Fin 6)) := {
    carrier := {w | wordWeight w.val = m.weight v}
    smul_mem' := by
      intro t w hw
      exact (wordWeight_permute (f t) w.val).trans hw }
  have hvne := not_or.mp ((not_congr (m.fixed_iff v)).mp hv)
  have hc : Nat.card X = 15 := by
    change {w : core (Fin 6) | wordWeight w.val = m.weight v}.ncard = 15
    change {w : core (Fin 6) | wordWeight w.val = wordWeight (m.coordinate v).toAdd.val}.ncard = 15
    rw [←even_core_orbit_eq_weight (by decide : 3 ≤ Fintype.card (Fin 6))]
    apply sixCore_orbit_card
    · intro he
      exact hvne.1 (m.coordinate.injective (he.trans m.coordinate.map_one.symm))
    · intro he
      exact hvne.2 (m.coordinate.injective (he.trans m.constant_coordinate.symm))
  obtain ⟨w,hw⟩ := T.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card X
    (by rw [hc]; decide)
  let z : V := m.coordinate.symm (Multiplicative.ofAdd w.val)
  have hzcoord : (m.coordinate z).toAdd = w.val := m.coordinate.apply_symm_apply _
  have hweight : m.weight z = m.weight v := by
    change wordWeight (m.coordinate z).toAdd.val = _
    rw [hzcoord]
    exact w.property
  refine ⟨z,(CoreMarking.mem_omega_iff (D := D) z).mpr ?_,?_,hweight⟩
  · apply mem_centralizer_iff.mpr
    intro t ht
    have hfix := congrArg Subtype.val (hw ⟨t,ht⟩)
    have he := hq ⟨t,D.sylow_normalizes_component ht⟩ z
    rw [hzcoord] at he
    have he' : (m.coordinate (V.normalizerMonoidHom
        (inclusion hn ⟨t,D.sylow_normalizes_component ht⟩) z)).toAdd =
        (m.coordinate z).toAdd := he.trans (hfix.trans hzcoord.symm)
    have he'' := congrArg Subtype.val (m.coordinate.injective
      (Multiplicative.toAdd.injective he'))
    exact mul_inv_eq_iff_eq_mul.mp he''
  · intro hz
    have hnon := m.nonfixed_weight v hv
    rcases (m.fixed_iff z).mp hz with hz | hz
    · rw [hz,m.weight_one] at hweight
      omega
    · rw [hz,m.weight_constant] at hweight
      omega

/-- Construct the nonfixed escaping omega point from the preceding centralizer-escape theorem. -/
theorem exists_nonfixed_omega_escape
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u}) :
    ∃ z : V, z ≠ 1 ∧ z.val ∈ omegaOneCenterAmbient (T : Subgroup G) ∧
      z.val ∉ centralizer (L : Set G) ∧
      ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨v,hv,_,hvL,hout⟩ := exists_nonfixed_escape h structural D m h₀ earlier
  obtain ⟨z,hzT,hzL,hweight⟩ := omega_representative_of_nonfixed D m
    (normalizer_component_le_module h structural D m) ⟨v,hv⟩ hvL
  refine ⟨z,?_,hzT,hzL,?_⟩
  · intro he
    exact hzL ((m.fixed_iff z).mpr (Or.inl he))
  · intro hc
    exact hout ((m.centralizer_le_iff_of_weight_eq z ⟨v,hv⟩ hweight).mp hc)

/-- Original 13.4.3(1), with its outside-local and centralizer-control premises discharged. -/
theorem original_core_thompson_generation
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u}) :
    ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ = L := by
  obtain ⟨z,hz1,hzT,_,hout⟩ := exists_nonfixed_omega_escape h₀ h structural D m earlier
  have hz1' : z.val ≠ 1 := fun he => hz1 (Subtype.ext he)
  have htwo := isTwoLocal_involution_centralizer
    (orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.1 hz1')
  obtain ⟨H,hCH,hH⟩ := Finite.exists_le_maximal htwo
  have hTH : (T : Subgroup G) ≤ H := by
    apply le_trans ?_ hCH
    intro t ht
    exact mem_centralizer_singleton_iff.mpr
      (((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.2 t ht)
  have hmax : Chapter3.HasMaximalOutside T (normalizer (L : Set G)) :=
    Chapter3.hasMaximalOutside_of_two_distinct
      (h.source_normalizer_maximal_unique structural
        (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).1
      hH D.sylow_normalizes_component hTH (fun he => hout (hCH.trans_eq he))
  have hf : V ⊓ centralizer (L : Set G) ≤ omegaOneCenterAmbient (T : Subgroup G) := by
    intro a ha
    apply (CoreMarking.mem_omega_iff (D := D) ⟨a,ha.1⟩).mpr
    apply mem_centralizer_iff.mpr
    intro t ht
    exact (mem_centralizer_iff.mp
      (normalizer_component_le_fixed_centralizer h structural D m
        (D.sylow_normalizes_component ht)) a ha).symm
  exact Chapter3.Section02.source_component_thompson_generation h.simpleQTKE T L
    h.maximal_faithful.1 h.maximal_faithful.2 h.quasisimple D.sylow_normalizes_component
    hmax ((centralizer_le hf).trans (fixed_centralizer_eq_normalizer h structural D m).le)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
