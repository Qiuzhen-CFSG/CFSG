module
public import Theory.SpecificGroups.SymplecticFour.TwoConjugate.Borel
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableRootOrbit
public import Theory.GroupTheory.SolvableSylowControl.Marked

/-!
# Solvable supplements to proper symplectic Sylow overgroups

A proper subgroup containing a full Sylow two-subgroup of Sp₄ lies in
one of the two parabolics over that Sylow. Both contain its normalizer.
For fields of order at least four, every solvable Sylow overgroup lies
in that normalizer, so adjoining it cannot generate the full group.
The last theorem lifts this obstruction through an actual two-group
kernel, whose containment in the supplied Sylow preserves properness.

Source: Aschbacher--Smith 14.2.15, printed pp.985--986, the Borel and
parabolic contradiction in the quasisimple symplectic branch.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Adjoining the normalizer of a full Sylow to a proper Sylow overgroup
still gives a proper subgroup. -/
theorem proper_sylow_overgroup_sup_normalizer_ne_top
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (Q : Sylow 2 (Sp F)) (D : Subgroup (Sp F))
    (hQD : (Q : Subgroup (Sp F)) ≤ D) (hD : D ≠ ⊤) :
    D ⊔ normalizer (Q : Set (Sp F)) ≠ ⊤ := by
  obtain ⟨g,e,_,he⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
    (MulEquiv.refl (Sp F)) Q (unipotentSylow hF hn)
  have hQ : (Q : Subgroup (Sp F)).map e.toMonoidHom = unipotent := he
  have hproper : D.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hD
    apply top_unique
    intro x _
    apply (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
    rw [htop]
    trivial
  have hU : unipotent ≤ D.map e.toMonoidHom := hQ ▸ map_mono hQD
  have hB : (normalizer (Q : Set (Sp F))).map e.toMonoidHom = borel := by
    change (normalizer ((Q : Subgroup (Sp F)) : Set (Sp F))).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq,hQ,borel_eq_normalizer_unipotent]
  have hsup : (D ⊔ normalizer (Q : Set (Sp F))).map e.toMonoidHom =
      D.map e.toMonoidHom ⊔ borel := by rw [Subgroup.map_sup,hB]
  intro htop
  have htop' : D.map e.toMonoidHom ⊔ borel = ⊤ := by
    rw [←hsup,htop,←MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr e.surjective
  rcases TwoConjugate.proper_unipotent_overgroup_le_parabolic hF hn
      (D.map e.toMonoidHom) hU hproper with hp | hp
  · exact pointParabolic_ne_top (top_unique (htop' ▸ sup_le hp inf_le_left))
  · exact planeParabolic_ne_top (top_unique (htop' ▸ sup_le hp inf_le_right))

/-- A solvable subgroup containing the same full Sylow cannot supplement a
proper Sylow overgroup of nonbinary Sp₄ to the whole group. -/
theorem proper_sylow_overgroup_sup_solvable_ne_top
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (Q : Sylow 2 (Sp F)) (D A : Subgroup (Sp F))
    (hQD : (Q : Subgroup (Sp F)) ≤ D) (hD : D ≠ ⊤)
    (hQA : (Q : Subgroup (Sp F)) ≤ A) (hsol : Group.IsSolvable A) :
    D ⊔ A ≠ ⊤ := by
  have hfour : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide) hn)
  have hAN : A ≤ normalizer (Q : Set (Sp F)) :=
    solvable_overgroups_of_orthogonal_root_orbits hF (by omega)
      (fun B hs hu => solvable_unipotent_point_orbit_orthogonal hfour B hs hu)
      Q A hsol hQA
  intro htop
  exact proper_sylow_overgroup_sup_normalizer_ne_top hF (by omega) Q D hQD hD
    (top_unique (htop ▸ sup_le_sup_left hAN D))

/-- The same obstruction lifts through the literal two-group kernel. -/
theorem proper_sylow_overgroup_sup_solvable_ne_top_of_twoGroup_kernel
    {H : Type*} [Group H] [Finite H]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (f : H →* Sp F) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (Q : Sylow 2 H) (D A : Subgroup H)
    (hQD : (Q : Subgroup H) ≤ D) (hD : D ≠ ⊤)
    (hQA : (Q : Subgroup H) ≤ A) (hsol : Group.IsSolvable A) :
    D ⊔ A ≠ ⊤ := by
  have hkD : f.ker ≤ D := (hk.le_sylow_of_normal Q).trans hQD
  have hDm : D.map f ≠ ⊤ := by
    intro he
    apply hD
    rw [←comap_map_eq_self hkD,he,comap_top]
  let _ := hsol
  have hsm : Group.IsSolvable (A.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective A)
  have hne := proper_sylow_overgroup_sup_solvable_ne_top hF hn
    (Q.mapSurjective hf) (D.map f) (A.map f) (map_mono hQD) hDm (map_mono hQA) hsm
  intro he
  apply hne
  rw [←Subgroup.map_sup,he,←MonoidHom.range_eq_map]
  exact MonoidHom.range_eq_top.mpr hf

end Theory.SpecificGroups.SymplecticFour
