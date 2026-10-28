module

public import Theory.GroupTheory.CComponent.PrimeGroupOvergroup
public import Theory.GroupTheory.CComponent.CommutatorDichotomy

/-!
# Normal generation by an invariant seed in a component orbit

A nontrivial perfect subgroup, invariant under an actor and normal in a single
C-component orbit, is the whole orbit. The C-component commutator dichotomy
shows that either a component lies in the subgroup, hence so do all its actor
conjugates, or the subgroup has abelian image modulo the solvable radical.
Perfectness excludes the latter case. Applying this to the seed's relative
normal closure proves normal generation without any projection to covering
factors and allows components with common centers.

The subnormal-chain comparison is GLS II, Lemma 5.20. The invariant-seed
application is the normal-closure step in Proposition 5.22(ii).
-/

public section
open Subgroup Theory.GroupTheory

namespace Subgroup
variable {G : Type*} [Group G]

theorem normalizer_inf_le_normalizer_componentOrbit (I X : Subgroup G) :
    normalizer (I : Set G) ⊓ normalizer (X : Set G) ≤
      normalizer (componentOrbit I X : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha z hz
  have hm : (componentOrbit I X).map (MulAut.conj a).toMonoidHom ≤ componentOrbit I X := by
    change (⨆ x : X, I.map (MulAut.conj (x : G)).toMonoidHom).map _ ≤ _
    rw [map_iSup]
    refine iSup_le fun x => ?_
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    apply (le_iSup (fun x : X => I.map (MulAut.conj (x : G)).toMonoidHom)
      ⟨a * x * a⁻¹, (mem_normalizer_iff.mp ha.2 _).mp x.property⟩)
    refine ⟨a * i * a⁻¹, (mem_normalizer_iff.mp ha.1 _).mp hi, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact hm (mem_map_of_mem _ hz)

/-- GLS 5.20's comparison, without finiteness. -/
theorem le_subnormal_of_self_normalClosure {I X H : Subgroup G}
    (hgen : componentOrbit I X = X) (hH : H.IsSubnormal) (hIH : I ≤ H) : X ≤ H := by
  induction hH with
  | top => exact le_top
  | step H K hHK hK hn ih =>
    have hXK : X ≤ K := ih (hIH.trans hHK)
    have hKH : K ≤ normalizer (H : Set G) :=
      (normal_subgroupOf_iff_le_normalizer hHK).mp hn
    rw [← hgen]
    exact iSup_conjugates_le_of_le_normalizer I X H hIH (hXK.trans hKH)

theorem IsCComponent.orbit_eq_of_normalized_perfect [Finite G]
    {K A D : Subgroup G} (hK : K.IsCComponent)
    [Group.IsPerfect D] (hne : D ≠ ⊥) (hD : D ≤ componentOrbit K A)
    (hAD : A ≤ normalizer (D : Set G))
    (hXD : componentOrbit K A ≤ normalizer (D : Set G)) : D = componentOrbit K A := by
  by_cases hKD : K ≤ D
  · exact le_antisymm hD (iSup_conjugates_le_of_le_normalizer K A D hKD hAD)
  let q := QuotientGroup.mk' (solvableRadical G)
  have hc (a : A) : ⁅K.map (MulAut.conj (a : G)).toMonoidHom, D⁆ ≤ solvableRadical G := by
    rcases (hK.map_equiv (MulAut.conj (a : G))).commutator_le_radical_or_eq_iSup_conjugates D
      with hc | he
    · exact hc
    · have hKa : K.map (MulAut.conj (a : G)).toMonoidHom ≤ D :=
        (le_iSup_conjugates _ D).trans (he.symm.le.trans
          (le_normalizer_iff_commutator_le_right.mp
            ((le_iSup (fun a : A => K.map (MulAut.conj (a : G)).toMonoidHom) a).trans hXD)))
      exact (hKD (by
        intro k hk
        exact (mem_normalizer_iff.mp (hAD a.property) k).mpr
          (hKa (mem_map_of_mem _ hk)))).elim
  have hcent : (componentOrbit K A).map q ≤ centralizer (D.map q : Set (G ⧸ solvableRadical G)) := by
    change (⨆ a : A, K.map (MulAut.conj (a : G)).toMonoidHom).map q ≤ _
    rw [map_iSup]
    refine iSup_le fun a => commutator_eq_bot_iff_le_centralizer.mp ?_
    rw [← map_commutator, map_eq_bot_iff]
    simpa only [q, QuotientGroup.ker_mk'] using hc a
  have hDD : ⁅D.map q, D.map q⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr ((map_mono hD).trans hcent)
  let : Group.IsPerfect (D.map q) := Group.IsPerfect.map q
  rw [commutator_eq_self, map_eq_bot_iff] at hDD
  rw [show q.ker = solvableRadical G from QuotientGroup.ker_mk' _] at hDD
  let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective hDD)
  let : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hne
  exact (Group.IsPerfect.not_isSolvable D inferInstance).elim

theorem IsCComponent.invariant_seed_normalClosure [Finite G]
    {K A I : Subgroup G} (hK : K.IsCComponent) [Group.IsPerfect I]
    (hne : I ≠ ⊥) (hI : I ≤ componentOrbit K A)
    (hAI : A ≤ normalizer (I : Set G)) :
    componentOrbit I (componentOrbit K A) = componentOrbit K A := by
  let X := componentOrbit K A
  let D := componentOrbit I X
  let : Group.IsPerfect D := isPerfect_iSup_conjugates I X
  have hDX : D ≤ X := iSup_conjugates_le_of_le_normalizer I X X hI X.le_normalizer
  have hneD : D ≠ ⊥ := fun he => hne (le_bot_iff.mp ((le_componentOrbit I X).trans he.le))
  have hAD : A ≤ normalizer (D : Set G) :=
    (le_inf hAI (le_normalizer_componentOrbit K A)).trans
      (normalizer_inf_le_normalizer_componentOrbit I X)
  exact hK.orbit_eq_of_normalized_perfect hneD hDX hAD (le_normalizer_componentOrbit I X)

end Subgroup
