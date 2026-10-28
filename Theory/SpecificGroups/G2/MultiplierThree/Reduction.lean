module

public import Theory.SpecificGroups.G2.FiniteUniversalCover
public import Theory.GroupTheory.CoveringKernelCard

/-!
# Lower-bound tests for the exceptional G₂(3) multiplier

The base throughout is the actual split-octonion automorphism group over
`ZMod 3`, and the multiplier carrier is the literal kernel of its constructed
finite universal cover. Restricting a central extension to its derived
subgroup produces a perfect central cover. The universal lift is surjective,
so the new kernel order divides the canonical universal-kernel order.

This gives two concrete ways to prove the lower bound of three: an element
of order three in the intersection of the kernel and the derived subgroup,
or a nonsplit extension with kernel of order three. Neither criterion assumes
finite-group universality of the proposed extension. No witness extension
or upper bound is constructed here.

Source: Aschbacher–Smith I.1.4(2), printed p.408 (PDF p.419), and GLS3,
Section 6.1, Tables 6.1.2–6.1.3. The commutator-lift criterion also matches
the orthogonal-root commutators in the G₂(3) case of GLS3 Section 6.3;
that discussion assumes a triple cover and does not establish its existence.
-/

namespace Atlas.G2.FiniteCover.MultiplierThree
open Theory.GroupTheory PerfectCentralCovering
open scoped commutatorElement

/-- The field of three elements lies in the proved simple/perfect range. -/
public instance threeField_large : Fact (2 < Nat.card (ZMod 3)) := ⟨by simp⟩

universe u
variable {E : Type u} [Group E]

/-- Every perfect central cover gives a divisor of the canonical kernel order. -/
public theorem kernel_card_dvd_of_perfectCentralCover (f : Cover E (Model (ZMod 3))) :
    Nat.card f.toMonoidHom.ker ∣ Nat.card (Kernel (ZMod 3)) := by
  let := f.isPerfect
  obtain ⟨h, hh, _⟩ := universalProjection_existsUnique_lift
    f.toMonoidHom f.surjective f.ker_le_center
  have hs : Function.Surjective h :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect f.toMonoidHom h
      (hh ▸ universalProjection_surjective (Model (ZMod 3))) f.ker_le_center
  exact kernel_card_dvd_of_surjective_factor (universalProjection (Model (ZMod 3)))
    f.toMonoidHom h hs hh

/-- Restrict the literal extension projection to the perfect derived subgroup. -/
@[expose] public noncomputable def derivedCover (π : E →* Model (ZMod 3))
    (hπ : Function.Surjective π) (hc : π.ker ≤ Subgroup.center E) :
    Cover (commutator E) (Model (ZMod 3)) where
  toMonoidHom := π.comp (commutator E).subtype
  surjective := by
    have hmap : (commutator E).map π = ⊤ := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hπ]
      exact Group.IsPerfect.commutator_eq_top
    intro b
    have hb : b ∈ (commutator E).map π := by rw [hmap]; trivial
    obtain ⟨d, hd, hdb⟩ := hb
    exact ⟨⟨d, hd⟩, hdb⟩
  isPerfect := commutator_isPerfect_of_surjective_of_ker_le_center π hπ hc
  ker_le_center := by
    intro d hd
    apply Subgroup.mem_center_iff.mpr
    intro x
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hc hd) x)

/-- A central derived element of order three supplies the lower bound, without
requiring the entire extension kernel to have order three. -/
public theorem three_dvd_kernel_card_of_central_extension
    (π : E →* Model (ZMod 3)) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center E) (z : E)
    (hz : z ∈ π.ker) (hd : z ∈ commutator E) (ho : orderOf z = 3) :
    3 ∣ Nat.card (Kernel (ZMod 3)) := by
  let f := derivedCover π hπ hc
  have hzk : (⟨z, hd⟩ : commutator E) ∈ f.toMonoidHom.ker := hz
  have hdiv : 3 ∣ Nat.card f.toMonoidHom.ker := by
    simpa only [Subgroup.orderOf_mk, ho] using f.toMonoidHom.ker.orderOf_dvd_natCard hzk
  exact hdiv.trans (kernel_card_dvd_of_perfectCentralCover f)

/-- Noncommuting lifts of commuting base elements detect the cubic multiplier
when their commutator has order three. -/
public theorem three_dvd_kernel_card_of_commutator_lifts
    (π : E →* Model (ZMod 3)) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center E) (x y : E)
    (hcomm : Commute (π x) (π y)) (ho : orderOf ⁅x, y⁆ = 3) :
    3 ∣ Nat.card (Kernel (ZMod 3)) := by
  apply three_dvd_kernel_card_of_central_extension π hπ hc ⁅x, y⁆ ?_ ?_ ho
  · rw [MonoidHom.mem_ker, map_commutatorElement]
    exact hcomm.commutator_eq
  · rw [commutator_eq_closure]
    exact Subgroup.subset_closure (commutator_mem_commutatorSet x y)

/-- A nonsplit central extension of degree three retains its whole kernel
upon restriction to the derived subgroup. -/
public theorem derivedCover_kernel_card_of_nonsplit
    (π : E →* Model (ZMod 3)) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center E) (hk : Nat.card π.ker = 3)
    (hns : ¬ ∃ s : Model (ZMod 3) →* E, π.comp s = MonoidHom.id _) :
    Nat.card (derivedCover π hπ hc).toMonoidHom.ker = 3 := by
  let g := (derivedCover π hπ hc).toMonoidHom
  let k : g.ker →* π.ker :=
    ((commutator E).subtype.comp g.ker.subtype).codRestrict π.ker (fun x => x.property)
  have hki : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : π.ker => (z : E)) h
  have hdvd : Nat.card g.ker ∣ 3 := by
    exact (Subgroup.card_dvd_of_injective k hki).trans (dvd_of_eq hk)
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdvd with htriv | hthree
  · have hbij : Function.Bijective g :=
      ⟨g.ker_eq_bot_iff.mp (Subgroup.card_eq_one.mp htriv),
        (derivedCover π hπ hc).surjective⟩
    let e := MulEquiv.ofBijective g hbij
    exact False.elim (hns ⟨(commutator E).subtype.comp e.symm.toMonoidHom, by
      apply MonoidHom.ext
      intro b
      exact e.apply_symm_apply b⟩)
  · exact hthree

/-- A nonsplit central triple extension forces three to divide the universal
kernel order; perfectness of the given extension is not an input. -/
public theorem three_dvd_kernel_card_of_nonsplit_extension
    (π : E →* Model (ZMod 3)) (hπ : Function.Surjective π)
    (hc : π.ker ≤ Subgroup.center E) (hk : Nat.card π.ker = 3)
    (hns : ¬ ∃ s : Model (ZMod 3) →* E, π.comp s = MonoidHom.id _) :
    3 ∣ Nat.card (Kernel (ZMod 3)) := by
  have h := kernel_card_dvd_of_perfectCentralCover (derivedCover π hπ hc)
  rwa [derivedCover_kernel_card_of_nonsplit π hπ hc hk hns] at h

end Atlas.G2.FiniteCover.MultiplierThree
