module
public import Theory.GroupTheory.ElementaryThompsonSmallImage

/-!
# Maximum replacements and Baumann displacement from small images

A maximum elementary subgroup with action image of order at most two has
an equally large centralizing replacement. Their intersection contains
alpha(C_S(V)), so [alpha(C_S(V)),J(S)] lies in V. A maximum replacement also
places alpha(S)V in alpha(C_S(V)), making the enlarged module elementary.

Only actual maximum elementary images are bounded. This is the hypothesis
available in the plane branch of Aschbacher--Smith 13.2.2(10), p.878;
the displacement argument is the step in B.2.18, pp.80--81, used by C.1.37.
The original plane application is in FixedCoreSource.Amalgam.PlaneAlpha.
-/

public noncomputable section
open Subgroup
namespace Stellmacher
open scoped IsMulCommutative
variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- A maximum elementary image of order at most two has a maximum
centralizing replacement. -/
theorem maxElementary_replacement_of_small_image
    (S V A : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (q : G →* H) (hk : q.ker = centralizer (V : Set G))
    (hc : Nat.card (A.map q) ≤ 2) :
    V ⊔ (A ⊓ centralizer (V : Set G)) ∈ elementaryAbelianMaxSubgroups S := by
  let := hA.2.1
  by_cases ha : A ≤ centralizer (V : Set G)
  · have hVA : V ≤ A := maxElementary_contains_elementary_centralizer S A V hA hVS
      (le_centralizer_iff.mp ha)
    simpa only [inf_eq_left.mpr ha,sup_eq_right.mpr hVA] using hA
  have hn : ¬ V ≤ centralizer (A : Set G) := fun hh => ha (le_centralizer_iff.mp hh)
  let F := V ⊓ centralizer (A : Set G)
  have hprod : Nat.card F * F.relIndex V = Nat.card V := by
    simpa only [relIndex_bot_left] using
      relIndex_mul_relIndex (⊥ : Subgroup G) F V bot_le inf_le_left
  have hi : 2 ≤ F.relIndex V := by
    have hpos : 0 < F.relIndex V := by
      have hv : 0 < Nat.card V := Nat.card_pos
      nlinarith
    have hne : F.relIndex V ≠ 1 := fun hh => hn ((relIndex_eq_one.mp hh).trans inf_le_right)
    omega
  have hb := maxElementary_card_bound_and_eq S V A hVS hA.1 0
    (by simpa using (maxOrder_eq_card_of_mem S A hA).symm) q hk
  apply hb.2
  have hlow : Nat.card F * 2 ≤ Nat.card V := by nlinarith
  have hu := hb.1
  change Nat.card V ≤ Nat.card F * Nat.card (A.map q) * 2^0 at hu
  change Nat.card V = Nat.card F * Nat.card (A.map q) * 2^0
  simp only [pow_zero,mul_one] at hu ⊢
  nlinarith

/-- Maximum replacements give the displacement bound needed in Baumann's
argument, without a hypothesis about all subgroups of the action quotient. -/
theorem omegaCenter_centralizer_commutator_maxJ_of_replacements
    (S V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hrep : ∀ A ∈ elementaryAbelianMaxSubgroups S,
      V ⊔ (A ⊓ centralizer (V : Set G)) ∈ elementaryAbelianMaxSubgroups S) :
    ⁅omegaOneCenterAmbient (elementaryAbelianMaxJ (S ⊓ centralizer (V : Set G))),
      elementaryAbelianMaxJ S⁆ ≤ V := by
  let F := omegaOneCenterAmbient (elementaryAbelianMaxJ (S ⊓ centralizer (V : Set G)))
  let f := QuotientGroup.mk' V
  have hc : F.map f ≤ centralizer ((elementaryAbelianMaxJ S).map f : Set (G ⧸ V)) := by
    apply le_centralizer_iff.mpr
    rw [map_le_iff_le_comap]
    apply sSup_le
    intro A hA
    have hB := hrep A hA
    have hBQ : V ⊔ (A ⊓ centralizer (V : Set G)) ≤ S ⊓ centralizer (V : Set G) :=
      le_inf hB.1 (sup_le V.le_centralizer inf_le_right)
    have hmax : V ⊔ (A ⊓ centralizer (V : Set G)) ∈
        elementaryAbelianMaxSubgroups (S ⊓ centralizer (V : Set G)) :=
      ⟨hBQ,hB.2.1,fun B hB' he => hB.2.2 B (hB'.trans inf_le_left) he⟩
    have hFB : F ≤ V ⊔ (A ⊓ centralizer (V : Set G)) := by
      let := omegaOneCenterAmbient_elementaryAbelian
        (elementaryAbelianMaxJ (S ⊓ centralizer (V : Set G)))
      apply maxElementary_contains_elementary_centralizer _ _ F hmax
      · intro x hx
        have hJ : elementaryAbelianMaxJ (S ⊓ centralizer (V : Set G)) ≤
            S ⊓ centralizer (V : Set G) := sSup_le fun _ hE => hE.1
        exact hJ ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
      · intro x hx
        exact mem_centralizer_iff.mpr fun y hy =>
          ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2 y (le_sSup hmax hy)
    have hFA : F.map f ≤ A.map f := by
      apply (map_mono hFB).trans
      rw [Subgroup.map_sup,show V.map f = ⊥ from (Subgroup.map_eq_bot_iff _).mpr (by simp [f]),bot_sup_eq]
      exact map_mono inf_le_left
    let := hA.2.1
    let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
    apply map_le_iff_le_comap.mp
    exact (A.map f).le_centralizer.trans (centralizer_le hFA)
  rw [←commutator_eq_bot_iff_le_centralizer,←map_commutator,Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk'] at hc
  exact hc

/-- The source enlarged elementary module and its displacement on every
maximum generator, from the small actual maximum images. -/
theorem omegaCenter_replacement_control_of_small_images
    (S V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (q : G →* H) (hk : q.ker = centralizer (V : Set G))
    (hc : ∀ A ∈ elementaryAbelianMaxSubgroups S, Nat.card (A.map q) ≤ 2) :
    let Q := S ⊓ centralizer (V : Set G)
    (omegaOneCenterAmbient (elementaryAbelianMaxJ S) ⊔ V ≤
      omegaOneCenterAmbient (elementaryAbelianMaxJ Q)) ∧
    IsElementaryAbelian 2 (omegaOneCenterAmbient (elementaryAbelianMaxJ S) ⊔ V : Subgroup G) ∧
    ⁅omegaOneCenterAmbient (elementaryAbelianMaxJ Q),elementaryAbelianMaxJ S⁆ ≤ V := by
  have hr := fun A hA => maxElementary_replacement_of_small_image S V A hVS hA q hk (hc A hA)
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty S
  have hb := hr A hA
  have hBQ : V ⊔ (A ⊓ centralizer (V : Set G)) ≤ S ⊓ centralizer (V : Set G) :=
    le_inf hb.1 (sup_le V.le_centralizer inf_le_right)
  have hh := maxElementary_centralizer_maxOrder_and_omegaCenter S V _ hVS hb hBQ
  have hle := sup_le hh.2.2.2 hh.2.2.1
  refine ⟨hle,?_,omegaCenter_centralizer_commutator_maxJ_of_replacements S V hr⟩
  let := omegaOneCenterAmbient_elementaryAbelian (elementaryAbelianMaxJ (S ⊓ centralizer (V : Set G)))
  exact IsElementaryAbelian.of_le hle

end Stellmacher
