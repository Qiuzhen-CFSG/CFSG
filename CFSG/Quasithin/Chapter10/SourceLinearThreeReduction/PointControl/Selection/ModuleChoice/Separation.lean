module
public import CFSG.Quasithin.Chapter10.SourceNonnormalPairAction
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
public import CFSG.Quasithin.Chapter10.SourceA5OriginalIrreducibility.Minimality

/-!
# Separated support in the original minimal full module

The maximal local group permutes the two original components. A seed fixed
by either component therefore generates a full module which is the sum of
the two component-fixed subgroups. The commutator with one component lies
in the subgroup fixed by the other, and the original exchanger gives the
literal crossed-centralization conclusion.

For a minimal full module, it suffices that one component-fixed subgroup
be moved by the other component. The sum of the two fixed subgroups is
M-invariant, and source reselection minimality makes it the entire module.
Conversely, crossed centralization supplies this nonzero commutator. Thus
the remaining source classification can prove a nonzero support statement
without first proving full/local equality or choosing quotient coordinates.

These are deductions from separated support, not a proof of its existence
or of the tensor exclusions. Source: Aschbacher--Smith, 3.2.6 and 10.1.1,
printed pp.581 and741, with the D.3.21 reselection argument, pp.204--207.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- A separated original seed gives the two fixed supports on its entire M-orbit. -/
theorem fullModule_eq_fixed_pair
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    D.fullModule = (D.fullModule ⊓ centralizer (L : Set G)) ⊔
      (D.fullModule ⊓ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G)) := by
  let B := L.map (MulAut.conj t).toMonoidHom
  let U := (D.fullModule ⊓ centralizer (L : Set G)) ⊔
    (D.fullModule ⊓ centralizer (B : Set G))
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  have hSV : D.seed ≤ D.fullModule :=
    (le_componentOrbit D.seed T).trans (le_componentOrbit _ D.maximalLocal)
  have hpair := source_nonnormal_maximal_pair D hn ht htn
  have hconj (m : D.maximalLocal) : D.seed.map (MulAut.conj (m : G)).toMonoidHom ≤ U := by
    have hV : D.seed.map (MulAut.conj (m : G)).toMonoidHom ≤ D.fullModule := by
      have hh := map_mono (f := (MulAut.conj (m : G)).toMonoidHom) hSV
      exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp
        (D.maximalLocal_normalizes_fullModule m.property))
    have hc : D.seed.map (MulAut.conj (m : G)).toMonoidHom ≤ centralizer (L : Set G) ∨
        D.seed.map (MulAut.conj (m : G)).toMonoidHom ≤ centralizer (B : Set G) := by
      rcases hsep with hs | hs
      · have hh := map_mono (f := (MulAut.conj (m : G)).toMonoidHom) hs
        rw [Theory.GroupTheory.map_centralizer_equiv] at hh
        change D.seed.map (MulAut.conj (m : G)).toMonoidHom ≤
          centralizer (((L.map (MulAut.conj t).toMonoidHom).map
            (MulAut.conj (m : G)).toMonoidHom) : Set G) at hh
        have he : (L.map (MulAut.conj t).toMonoidHom).map
            (MulAut.conj (m : G)).toMonoidHom =
            L.map (MulAut.conj ((m : G) * t)).toMonoidHom := by
          rw [map_map]
          congr 1
          ext x
          simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply]
          group
        rw [he] at hh
        rcases hpair ((m : G)*t) (D.maximalLocal.mul_mem m.property (hTM ht)) with he | he
        · rw [he] at hh
          exact Or.inl hh
        · rw [he] at hh
          exact Or.inr hh
      · have hh := map_mono (f := (MulAut.conj (m : G)).toMonoidHom) hs
        rw [Theory.GroupTheory.map_centralizer_equiv] at hh
        change D.seed.map (MulAut.conj (m : G)).toMonoidHom ≤
          centralizer ((L.map (MulAut.conj (m : G)).toMonoidHom) : Set G) at hh
        rcases hpair m m.property with he | he
        · rw [he] at hh
          exact Or.inl hh
        · rw [he] at hh
          exact Or.inr hh
    exact hc.elim (fun hc => (le_inf hV hc).trans le_sup_left)
      (fun hc => (le_inf hV hc).trans le_sup_right)
  apply le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  exact D.fullModule_eq_seed_orbit.le.trans (iSup_le hconj)

/-- The full fixed-support decomposition separates the original moved factor. -/
theorem moved_centralizes_partner_of_fixed_pair
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hpair : D.fullModule = (D.fullModule ⊓ centralizer (L : Set G)) ⊔
      (D.fullModule ⊓ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G))) :
    ⁅D.fullModule,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) := by
  let B := L.map (MulAut.conj t).toMonoidHom
  let X := D.fullModule ⊓ centralizer (B : Set G)
  let C := D.fullModule ⊓ centralizer (L : Set G)
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hgen : C ⊔ X = D.fullModule := hpair.symm
  have hXL : X ≤ normalizer (L : Set G) :=
    inf_le_left.trans (D.fullModule_le_orbit.trans (source_nonnormal_orbit_le_normalizer D hn))
  have hLX : L ≤ normalizer (X : Set G) := by
    apply le_trans (le_inf ?_ ?_) inf_normalizer_le_normalizer_inf
    · exact ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule
    · have hLB : L ≤ normalizer (B : Set G) := by
        have hh := map_mono (f := (MulAut.conj t).toMonoidHom)
          (source_nonnormal_orbit_le_normalizer D hn)
        have hO : (localOrbit T L).map (MulAut.conj t).toMonoidHom = localOrbit T L :=
          mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T ht)
        rw [hO,map_equiv_normalizer_eq] at hh
        exact (le_componentOrbit L T).trans hh
      exact hLB.trans (normalizer_le_normalizer_centralizer B)
  have he := commutator_eq_of_centralizing_sup hgen (show C ≤ centralizer (L : Set G) from inf_le_right) hXL
  rw [commutator_comm,←he,commutator_comm]
  exact (le_normalizer_iff_commutator_le_left.mp hLX).trans inf_le_right

/-- Seed separation already separates the full moved factor, without full/local equality. -/
theorem moved_centralizes_partner_of_separated_seed
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    ⁅D.fullModule,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) :=
  moved_centralizes_partner_of_fixed_pair D ht htn
    (fullModule_eq_fixed_pair D ht htn hsep)

/-- Minimality promotes one nonzero moved fixed support to the full decomposition. -/
theorem fullModule_eq_fixed_pair_of_minimal
    (hmin : D.IsMinimalFullModule)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hmove : ⁅D.fullModule ⊓ centralizer
      (L.map (MulAut.conj t).toMonoidHom : Set G), L⁆ ≠ ⊥) :
    D.fullModule = (D.fullModule ⊓ centralizer (L : Set G)) ⊔
      (D.fullModule ⊓ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G)) := by
  let B := L.map (MulAut.conj t).toMonoidHom
  let U := (D.fullModule ⊓ centralizer (L : Set G)) ⊔
    (D.fullModule ⊓ centralizer (B : Set G))
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) := fun h => htn (h ht)
  have hTM : (T : Subgroup G) ≤ D.maximalLocal := le_normalizer_componentOrbit L T
  have hpair := source_nonnormal_maximal_pair D hn ht htn
  have hUN : D.maximalLocal ≤ normalizer (U : Set G) := by
    intro m hm
    apply mem_normalizer_iff.mpr
    have hmap (s : G) (hs : s ∈ D.maximalLocal) :
        U.map (MulAut.conj s).toMonoidHom ≤ U := by
      have hpart (A : Subgroup G)
          (hA : A.map (MulAut.conj s).toMonoidHom = L ∨
            A.map (MulAut.conj s).toMonoidHom = B) :
          (D.fullModule ⊓ centralizer (A : Set G)).map
            (MulAut.conj s).toMonoidHom ≤ U := by
        rw [map_inf _ _ _ (MulAut.conj s).injective]
        have hV : D.fullModule.map (MulAut.conj s).toMonoidHom = D.fullModule :=
          mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hs)
        rw [hV,Theory.GroupTheory.map_centralizer_equiv]
        change D.fullModule ⊓ centralizer ((A.map (MulAut.conj s).toMonoidHom) : Set G) ≤ U
        rcases hA with he | he
        · rw [he]
          exact le_sup_left
        · rw [he]
          exact le_sup_right
      change (D.fullModule ⊓ centralizer (L : Set G) ⊔
        (D.fullModule ⊓ centralizer (B : Set G))).map (MulAut.conj s).toMonoidHom ≤ U
      rw [Subgroup.map_sup]
      refine sup_le (hpart L (hpair s hs)) (hpart B ?_)
      have he : B.map (MulAut.conj s).toMonoidHom =
          L.map (MulAut.conj (s*t)).toMonoidHom := by
        change (L.map (MulAut.conj t).toMonoidHom).map _ = _
        rw [map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply,mul_assoc]
      rw [he]
      exact hpair (s*t) (D.maximalLocal.mul_mem hs (hTM ht))
    intro x
    constructor
    · intro hx
      exact hmap m hm (mem_map_of_mem (MulAut.conj m).toMonoidHom hx)
    · intro hx
      have hh := hmap m⁻¹ (D.maximalLocal.inv_mem hm)
        (mem_map_of_mem (MulAut.conj m⁻¹).toMonoidHom hx)
      simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,
        mul_assoc,inv_mul_cancel_left,mul_inv_cancel,inv_mul_cancel,mul_one] using hh
  apply (source_minimal_fullModule_eq_of_normal_moved D hmin U hUN
    (sup_le inf_le_left inf_le_left) ?_).symm
  intro he
  exact hmove (bot_unique ((commutator_mono (show D.fullModule ⊓
    centralizer (B : Set G) ≤ U from le_sup_right) le_rfl).trans_eq he))

/-- The original exchanger transports opposite centralization to the required crossed form. -/
theorem crossed_of_opposite_centralization
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ⁅D.fullModule,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
  have hh := map_mono (f := (MulAut.conj t).toMonoidHom)
    hsep
  rw [Theory.GroupTheory.map_centralizer_equiv] at hh
  change (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤
    centralizer (((L.map (MulAut.conj t).toMonoidHom).map
      (MulAut.conj t).toMonoidHom) : Set G) at hh
  rw [conjugate_twice_eq_of_index_two L (T : Subgroup G) (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1
      (fun hn => htn (hn ht))) inf_le_right ht] at hh
  exact hh

/-- A separated seed supplies literal crossed centralization on the full module. -/
theorem crossed_of_separated_seed
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  crossed_of_opposite_centralization D ht htn
    (moved_centralizes_partner_of_separated_seed D ht htn hsep)

/-- The minimal selected module needs only a nonzero moved fixed support. -/
theorem crossed_of_minimal_fixed_support
    (hmin : D.IsMinimalFullModule)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hmove : ⁅D.fullModule ⊓ centralizer
      (L.map (MulAut.conj t).toMonoidHom : Set G), L⁆ ≠ ⊥) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) :=
  crossed_of_opposite_centralization D ht htn
    (moved_centralizes_partner_of_fixed_pair D ht htn
      (fullModule_eq_fixed_pair_of_minimal D hmin ht htn hmove))

/-- Crossed centralization gives a nonzero fixed-support commutator on the same module. -/
theorem fixed_support_moved_of_crossed
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    ⁅D.fullModule ⊓ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G),L⁆ ≠ ⊥ := by
  have hS : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤
      normalizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅D.fullModule,L⁆).map (MulAut.conj s).toMonoidHom = ⁅D.fullModule,L⁆
    have hV : D.fullModule.map (MulAut.conj s).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule
        (le_normalizer_componentOrbit L T hs.1))
    have hL : L.map (MulAut.conj s).toMonoidHom = L :=
      mem_normalizer_iff_map_conj_eq.mp hs.2
    rw [map_commutator,hV,hL]
  have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hcross
  rw [conjugate_twice_eq_of_index_two ⁅D.fullModule,L⁆ (T : Subgroup G)
    (normalizer (L : Set G))
    (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1
      (fun hn => htn (hn ht))) hS ht,Theory.GroupTheory.map_centralizer_equiv] at hh
  have hWV : ⁅D.fullModule,L⁆ ≤ D.fullModule :=
    le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
  intro he
  have hz := (commutator_mono (le_inf hWV hh) (le_refl L)).trans_eq he
  rw [source_full_moved_eq_commutator D] at hz
  exact source_full_moved_ne_bot D (bot_unique hz)

/-- For the selected minimal module, crossed centralization is equivalent to nonzero support. -/
theorem crossed_iff_fixed_support_moved
    (hmin : D.IsMinimalFullModule)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) ↔
      ⁅D.fullModule ⊓ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G),L⁆ ≠ ⊥ :=
  ⟨fixed_support_moved_of_crossed D ht htn, crossed_of_minimal_fixed_support D hmin ht htn⟩

/-- One original vector fixed by the opposite component and moved by L suffices. -/
theorem crossed_of_minimal_fixed_vector
    (hmin : D.IsMinimalFullModule)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    {v : G} (hv : v ∈ D.fullModule)
    (hvB : v ∈ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G))
    (hvL : v ∉ centralizer (L : Set G)) :
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G) := by
  apply crossed_of_minimal_fixed_support D hmin ht htn
  intro he
  exact hvL (commutator_eq_bot_iff_le_centralizer.mp he ⟨hv,hvB⟩)

end CFSG.Quasithin.Chapter10.PointControl.Selection.ModuleChoice
