module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.Omega
public import Theory.GroupTheory.ConjugacyFamilySpan

/-!
# The conjugate-family span in the small linear argument

Let U = Ω₁(R). Assume every conjugate of U lying in T acts inner on L,
expressed by containment in C_G(L)L. Centerlessness then places each such
conjugate in V. Their span contains U_C and U, and is invariant under X.
Faithfulness gives a nonzero displacement of U under X. Regularity of X
on [V,X] then puts all of [V,X] in the span, proving V = ⟨U^G ∩ T⟩.
The general conjugate-family theorem now gives weak closure.

The universal inner-placement premise is an intermediate obligation, not
an asserted consequence of LocalAction. In the PSL₂(4) application it must
be derived from source 16.4.6 for all applicable conjugate configurations.
The assertion for involutions of the one fixed R does not suffice.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed p.1194; the earlier exclusion is 16.4.6, pp.1184–1186.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure
open Subgroup
open scoped commutatorElement
variable {G : Type*} [Group G]

/-- All ambient conjugates of the specified subgroup. -/
def conjugateFamily (U : Subgroup G) : Set (Subgroup G) :=
  Set.range (fun a : G => U.conjBy a)

/-- Left conjugation composes the conjugating elements. -/
theorem conjugateFamily_invariant (U : Subgroup G) :
    SubgroupFamily.ConjugationInvariant (conjugateFamily U) := by
  rintro A ⟨a, rfl⟩ b
  exact ⟨b * a, (conjBy_conjBy U a b).symm⟩

/-- U and U_C have the same family when they are conjugate. -/
theorem conjugateFamily_conjBy (U : Subgroup G) (g : G) :
    conjugateFamily (U.conjBy g) = conjugateFamily U := by
  ext A
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a * g, (conjBy_conjBy U g a).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨a * g⁻¹, ?_⟩
    change (U.conjBy g).conjBy (a * g⁻¹) = U.conjBy a
    rw [conjBy_conjBy, inv_mul_cancel_right]

variable [Finite G] {T : Sylow 2 G} {z g : G} {L R : Subgroup G} {n : ℕ}

/-- Construct the span identity from universal inner placement and the local torus. -/
theorem space_eq_conjugate_span_of_inner_placement
    (h : StandardSetup T z L) (hZ : center L = ⊥)
    (d : LocalAction T L R n)
    (hconj : R = (commutingSylow T L).conjBy g)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hplace : ∀ a : G, (omegaOneAmbient R).conjBy a ≤ (T : Subgroup G) →
      (omegaOneAmbient R).conjBy a ≤ centralizer (L : Set G) ⊔ L) :
    benderSpace T L = SubgroupFamily.span (conjugateFamily (omegaOneAmbient R)) T := by
  classical
  let U := omegaOneAmbient R
  let W := omegaOneAmbient (commutingSylow T L)
  let F := conjugateFamily U
  let S := SubgroupFamily.span F (T : Subgroup G)
  let := d.commuting_elementary
  let := d.component_elementary
  let := space_elementary_of_factors (T := T) (L := L)
  have hUg : U = W.conjBy g := omega_conjugate hconj
  have hUe : IsElementaryAbelian 2 U := by
    rw [hUg]
    exact IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  let := hUe
  have hSV : S ≤ benderSpace T L := by
    apply sSup_le
    rintro A ⟨⟨a, rfl⟩, ha⟩ v hv
    have hea : IsElementaryAbelian 2 (U.conjBy a) :=
      IsElementaryAbelian.map (MulAut.conj a).toMonoidHom
    let := hea
    exact TorusConstruction.involution_mem_space h
      (TorusConstruction.involutionLifting_of_center_eq_bot hZ) (ha hv)
      (elemPow_eq_one_of_isElementaryAbelian v hv) (hplace a ha hv)
  have hUS : U ≤ S := SubgroupFamily.le_span
    (show U ∈ F from ⟨1, conjBy_one U⟩) (d.omega_le.trans (benderSpace_le_sylow T L))
  have hWS : W ≤ S := by
    apply SubgroupFamily.le_span
    · refine ⟨g⁻¹, ?_⟩
      change U.conjBy g⁻¹ = W
      rw [hUg, conjBy_inv]
    · exact (omegaOneAmbient_le _).trans inf_le_left
  have hXS : d.actor ≤ normalizer (S : Set G) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply SubgroupFamily.span_weakly_closed (conjugateFamily_invariant U)
    have hVx : (benderSpace T L).conjBy x = benderSpace T L :=
      mem_normalizer_iff_map_conj_eq.mp (actor_normalizes_space d.actor_le hx)
    exact ((map_mono hSV).trans hVx.le).trans (benderSpace_le_sylow T L)
  have hUne : U ≠ ⊥ := by
    intro hbot
    have he := congrArg (fun A : Subgroup G => A.conjBy g⁻¹) hUg
    rw [hbot, conjBy_inv] at he
    exact commuting_omega_nontrivial h (by simpa [Subgroup.conjBy] using he.symm)
  obtain ⟨u, hu, hu1⟩ := (Subgroup.nontrivial_iff_exists_ne_one U).mp
    ((Subgroup.nontrivial_iff_ne_bot U).mpr hUne)
  obtain ⟨x, hx, hux⟩ : ∃ x ∈ d.actor, ¬ Commute u x := by
    by_contra! hc
    have huW : u ∈ W := by
      change u ∈ omegaOneAmbient (commutingSylow T L)
      rw [← d.fixed_eq]
      exact ⟨d.omega_le hu, fun x hx => (hc x hx).eq.symm⟩
    exact hu1 (disjoint_def.mp hfaith (omegaOneAmbient_le R hu)
      ((omegaOneAmbient_le _ huW).2))
  have hcM : ⁅u, x⁆ ∈ ⁅benderSpace T L, d.actor⁆ :=
    commutator_mem_commutator (d.omega_le hu) hx
  have hc1 : ⁅u, x⁆ ≠ 1 := fun he => hux (commutatorElement_eq_one_iff_commute.mp he)
  have hcS : ⁅u, x⁆ ∈ S := by
    have hh := (mem_normalizer_iff.mp (hXS hx) u⁻¹).mp (S.inv_mem (hUS hu))
    convert S.mul_mem (hUS hu) hh using 1
    simp only [commutatorElement_def, mul_assoc]
  have hMS : ⁅benderSpace T L, d.actor⁆ ≤ S := by
    intro v hv
    by_cases hv1 : v = 1
    · exact hv1 ▸ S.one_mem
    obtain ⟨y, hy, _⟩ := d.regular _ hcM hc1 v hv hv1
    rw [← hy]
    exact (mem_normalizer_iff.mp (hXS y.property) _).mp hcS
  apply le_antisymm _ hSV
  rw [← d.span]
  exact sup_le hWS hMS

/-- The constructed span is weakly closed by conjugation invariance and equal orders. -/
theorem space_weakly_closed_of_inner_placement
    (h : StandardSetup T z L) (hZ : center L = ⊥)
    (d : LocalAction T L R n)
    (hconj : R = (commutingSylow T L).conjBy g)
    (hfaith : Disjoint R (centralizer (L : Set G)))
    (hplace : ∀ a : G, (omegaOneAmbient R).conjBy a ≤ (T : Subgroup G) →
      (omegaOneAmbient R).conjBy a ≤ centralizer (L : Set G) ⊔ L)
    (a : G) (ha : (benderSpace T L).conjBy a ≤ (T : Subgroup G)) :
    (benderSpace T L).conjBy a = benderSpace T L := by
  have he : benderSpace T L =
      SubgroupFamily.span (conjugateFamily (omegaOneAmbient R)) (T : Subgroup G) :=
    space_eq_conjugate_span_of_inner_placement h hZ d hconj hfaith hplace
  calc
    (benderSpace T L).conjBy a =
        (SubgroupFamily.span (conjugateFamily (omegaOneAmbient R)) (T : Subgroup G)).conjBy a :=
      congrArg (fun A : Subgroup G => A.conjBy a) he
    _ = SubgroupFamily.span (conjugateFamily (omegaOneAmbient R)) (T : Subgroup G) :=
      SubgroupFamily.span_weakly_closed (conjugateFamily_invariant (omegaOneAmbient R))
        (T : Subgroup G) a (by
          change (SubgroupFamily.span (conjugateFamily (omegaOneAmbient R))
            (T : Subgroup G)).conjBy a ≤ (T : Subgroup G)
          rw [← he]
          exact ha)
    _ = benderSpace T L := he.symm

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure
