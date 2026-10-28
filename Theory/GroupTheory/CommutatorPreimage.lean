module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The greatest subgroup centralizing an actor modulo a normal layer

The construction is an ambient subgroup, independent of a chief series.
Its defining commutator bound is valid when the containing subgroup
normalizes the layer. Simultaneous normalizers preserve the construction.
-/

namespace Subgroup
open scoped commutatorElement

public def commutatorPreimage {G : Type*} [Group G]
    (Q E Z : Subgroup G) : Subgroup G :=
  sSup {D : Subgroup G | D ≤ Q ∧ ⁅D, E⁆ ≤ Z}

public theorem commutatorPreimage_le {G : Type*} [Group G]
    (Q E Z : Subgroup G) : commutatorPreimage Q E Z ≤ Q :=
  sSup_le fun _ hD => hD.1

public theorem le_commutatorPreimage {G : Type*} [Group G]
    {Q E Z D : Subgroup G} (hDQ : D ≤ Q) (hcomm : ⁅D, E⁆ ≤ Z) :
    D ≤ commutatorPreimage Q E Z :=
  le_sSup ⟨hDQ, hcomm⟩

public theorem commutator_commutatorPreimage_le {G : Type*} [Group G]
    (Q E Z : Subgroup G) (hQZ : Q ≤ normalizer Z) :
    ⁅commutatorPreimage Q E Z, E⁆ ≤ Z := by
  let K : Subgroup G :=
    { carrier := {element | element ∈ Q ∧ ∀ other ∈ E, ⁅element, other⁆ ∈ Z}
      one_mem' := ⟨Q.one_mem, by simp⟩
      mul_mem' := by
        rintro first second ⟨hfirst, hfirstcomm⟩ ⟨hsecond, hsecondcomm⟩
        refine ⟨Q.mul_mem hfirst hsecond, ?_⟩
        intro other hother
        rw [commutatorElement_mul_left_eq_conj_mul]
        exact Z.mul_mem
          (le_normalizer_iff.mp hQZ first hfirst _ (hsecondcomm other hother))
          (hfirstcomm other hother)
      inv_mem' := by
        rintro element ⟨helement, hcomm⟩
        refine ⟨Q.inv_mem helement, ?_⟩
        intro other hother
        rw [commutatorElement_inv_left]
        have hinv : ⁅other, element⁆ ∈ Z := by
          rw [← commutatorElement_inv]
          exact Z.inv_mem (hcomm other hother)
        simpa only [inv_inv] using
          le_normalizer_iff.mp hQZ element⁻¹ (Q.inv_mem helement) _ hinv }
  have hCK : commutatorPreimage Q E Z ≤ K := by
    apply sSup_le
    intro D hD element helement
    exact ⟨hD.1 helement, commutator_le.mp hD.2 element helement⟩
  exact commutator_le.mpr fun element helement => (hCK helement).2

public theorem le_commutatorPreimage_iff {G : Type*} [Group G]
    (Q E Z D : Subgroup G) (hQZ : Q ≤ normalizer Z) :
    D ≤ commutatorPreimage Q E Z ↔ D ≤ Q ∧ ⁅D, E⁆ ≤ Z := by
  constructor
  · intro hD
    exact ⟨hD.trans (commutatorPreimage_le Q E Z),
      (commutator_mono hD le_rfl).trans (commutator_commutatorPreimage_le Q E Z hQZ)⟩
  · rintro ⟨hDQ, hcomm⟩
    exact le_commutatorPreimage hDQ hcomm

public theorem commutatorPreimage_normalized {G : Type*} [Group G]
    (Q E Z P : Subgroup G) (hQZ : Q ≤ normalizer Z)
    (hPQ : P ≤ normalizer Q) (hPE : P ≤ normalizer E)
    (hPZ : P ≤ normalizer Z) : P ≤ normalizer (commutatorPreimage Q E Z) := by
  apply le_normalizer_iff.mpr
  intro actor hactor element helement
  let conjugation := (MulAut.conj actor).toMonoidHom
  have hQ : Q.map conjugation = Q := mem_normalizer_iff_map_conj_eq.mp (hPQ hactor)
  have hE : E.map conjugation = E := mem_normalizer_iff_map_conj_eq.mp (hPE hactor)
  have hZ : Z.map conjugation = Z := mem_normalizer_iff_map_conj_eq.mp (hPZ hactor)
  have hmap : (commutatorPreimage Q E Z).map conjugation ≤ commutatorPreimage Q E Z := by
    apply le_commutatorPreimage
    · exact (map_mono (commutatorPreimage_le Q E Z)).trans_eq hQ
    · have hbound := map_mono (f := conjugation)
        (commutator_commutatorPreimage_le Q E Z hQZ)
      rw [map_commutator, hE, hZ] at hbound
      exact hbound
  exact hmap (mem_map_of_mem conjugation helement)

public theorem commutator_commutatorPreimage_eq {G : Type*} [Group G]
    (Q E Z : Subgroup G) (hQZ : Q ≤ normalizer Z)
    (hZQ : Z ≤ Q) (hZE : ⁅Z, E⁆ = Z) :
    ⁅commutatorPreimage Q E Z, E⁆ = Z := by
  apply le_antisymm (commutator_commutatorPreimage_le Q E Z hQZ)
  exact hZE.symm.le.trans (commutator_mono (le_commutatorPreimage hZQ hZE.le) le_rfl)

public theorem commutatorPreimage_eq_inf_comap_centralizer
    {G : Type*} [Group G] (Q E Z : Subgroup G) [Z.Normal] :
    commutatorPreimage Q E Z =
      Q ⊓ (centralizer (E.map (QuotientGroup.mk' Z) : Set (G ⧸ Z))).comap
        (QuotientGroup.mk' Z) := by
  let projection := QuotientGroup.mk' Z
  apply le_antisymm
  · refine le_inf (commutatorPreimage_le Q E Z) ?_
    apply (map_le_iff_le_comap).mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    rw [← map_commutator]
    apply (map_eq_bot_iff (f := projection) _).mpr
    simpa only [projection, QuotientGroup.ker_mk'] using
      commutator_commutatorPreimage_le Q E Z le_normalizer_of_normal
  · apply le_commutatorPreimage inf_le_left
    have hmap :
        (Q ⊓ (centralizer (E.map projection : Set (G ⧸ Z))).comap projection).map
          projection ≤ centralizer (E.map projection : Set (G ⧸ Z)) :=
      (map_le_iff_le_comap).mpr inf_le_right
    have hcomm := commutator_eq_bot_iff_le_centralizer.mpr hmap
    rw [← map_commutator] at hcomm
    simpa only [projection, QuotientGroup.ker_mk'] using
      (map_eq_bot_iff (f := projection) _).mp hcomm

end Subgroup
