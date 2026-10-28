module
public import Theory.AtlasPort.LinearGroups.G2.ProperSylowOvergroups
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.SylowAlignment

/-!
# Solvable supplements to proper G₂ Sylow overgroups

Conjugate the prescribed full Sylow two-subgroup to the positive-root
subgroup in the actual split-octonion model. A proper overgroup lies in
one of the two standard root parabolics, while a solvable overgroup lies
in their common Borel when the field has more than two elements. Their
join therefore remains proper. The normalizer version includes F₂.

The final theorem lifts this obstruction through the given surjection
with a two-group kernel. Its normal kernel lies in the supplied Sylow,
so the proper overgroup has proper image. All Bruhat, root-capture,
parabolic-properness and Sylow markings come from the concrete model.

Source: Aschbacher--Smith 14.2.15, printed pp.985--986; GLS III,
Theorems 2.3.5 and 2.6.5--2.6.7. The octonion constructions retain the
licensed ATLAS port attribution (LICENSES/ATLAS.txt).
-/

public section
open Subgroup
namespace Atlas.G2
open LieParabolicSetup EvenLocal.NormalizerCover
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Adjoining the full Sylow normalizer preserves a proper Sylow overgroup. -/
theorem proper_sylow_overgroup_sup_normalizer_ne_top
    (Q : Sylow 2 (Model F)) (D : Subgroup (Model F))
    (hQD : (Q : Subgroup (Model F)) ≤ D) (hD : D ≠ ⊤) :
    D ⊔ normalizer (Q : Set (Model F)) ≠ ⊤ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model F) Q (sylow (F := F))
  let e := MulAut.conj g
  have hQ : (Q : Subgroup (Model F)).map e.toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hg
  have hproper : D.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hD
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective _ e.surjective]
    exact htop
  have hB : (normalizer (Q : Set (Model F))).map e.toMonoidHom = borel := by
    change (normalizer ((Q : Subgroup (Model F)) : Set (Model F))).map e.toMonoidHom = _
    rw [map_normalizer_eq_of_bijective _ e.bijective, hQ,
      SylowNormalizer.normalizer_unipotent]
  intro htop
  have ht : D.map e.toMonoidHom ⊔ borel = ⊤ := by
    rw [←hB, ←Subgroup.map_sup, htop, map_top_of_surjective _ e.surjective]
  rcases ProperSylowOvergroups.le_parabolic (D.map e.toMonoidHom)
      (hQ ▸ map_mono hQD) (lt_top_iff_ne_top.mpr hproper) with hp | hp
  · exact short_parabolic_ne_top (top_unique (ht ▸ sup_le hp borel_le_parabolic₁))
  · exact long_parabolic_ne_top (top_unique (ht ▸ sup_le hp borel_le_parabolic₂))

/-- A solvable overgroup of the same full Sylow cannot supplement a proper overgroup. -/
theorem proper_sylow_overgroup_sup_solvable_ne_top
    (hF : 2 < Nat.card F) (Q : Sylow 2 (Model F)) (D A : Subgroup (Model F))
    (hQD : (Q : Subgroup (Model F)) ≤ D) (hD : D ≠ ⊤)
    (hQA : (Q : Subgroup (Model F)) ≤ A) (hsol : Group.IsSolvable A) :
    D ⊔ A ≠ ⊤ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Model F) Q (sylow (F := F))
  let e := MulAut.conj g
  have hQ : (Q : Subgroup (Model F)).map e.toMonoidHom = unipotent :=
    congrArg Sylow.toSubgroup hg
  let _ := hsol
  have hA : A.map e.toMonoidHom ≤ borel := SolvableSylowPlacement.le_borel hF _
    (hQ ▸ map_mono hQA)
    (Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective A))
  have hAN : A ≤ normalizer (Q : Set (Model F)) := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    change A.map e.toMonoidHom ≤
      (normalizer ((Q : Subgroup (Model F)) : Set (Model F))).map e.toMonoidHom
    rw [map_normalizer_eq_of_bijective _ e.bijective, hQ,
      SylowNormalizer.normalizer_unipotent]
    exact hA
  intro htop
  exact proper_sylow_overgroup_sup_normalizer_ne_top Q D hQD hD
    (top_unique (htop ▸ sup_le_sup_left hAN D))

/-- The literal two-group-kernel quotient preserves the proper-supplement obstruction. -/
theorem proper_sylow_overgroup_sup_solvable_ne_top_of_twoGroup_kernel
    {H : Type*} [Group H] [Finite H] (hF : 2 < Nat.card F)
    (f : H →* Model F) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (Q : Sylow 2 H) (D A : Subgroup H)
    (hQD : (Q : Subgroup H) ≤ D) (hD : D ≠ ⊤)
    (hQA : (Q : Subgroup H) ≤ A) (hsol : Group.IsSolvable A) :
    D ⊔ A ≠ ⊤ := by
  have hkD : f.ker ≤ D := (hk.le_sylow_of_normal Q).trans hQD
  have hDm : D.map f ≠ ⊤ := by
    intro he
    apply hD
    rw [←comap_map_eq_self hkD, he, comap_top]
  let _ := hsol
  have hsm : Group.IsSolvable (A.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective A)
  have hne := proper_sylow_overgroup_sup_solvable_ne_top hF
    (Q.mapSurjective hf) (D.map f) (A.map f) (map_mono hQD) hDm (map_mono hQA) hsm
  intro he
  apply hne
  rw [←Subgroup.map_sup, he, map_top_of_surjective _ hf]

end Atlas.G2
