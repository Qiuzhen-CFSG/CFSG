module
public import Mathlib.GroupTheory.Sylow

/-!
# Lifting a normal prime subgroup to a surjective local normalizer

Let a finite group map onto a group with a nontrivial normal p-subgroup R.
A Sylow p-subgroup of the full preimage of R maps onto R. Frattini's
argument then makes its normalizer surject onto the whole target. The
kernel is unrestricted, and the lifted p-subgroup is nontrivial.

This is the local form of Frattini's argument used to lift section order
obstructions. The Mathieu--Ree application is in
`Theory.Mathieu.M22.ReeExclusion`.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory

theorem exists_pSubgroup_normalizer_surjective_of_normal_pSubgroup
    {E H : Type*} [Group E] [Finite E] [Group H]
    {p : ℕ} [Fact p.Prime] (f : E →* H) (hf : Function.Surjective f)
    (R : Subgroup H) [R.Normal] (hR : IsPGroup p R) (hne : R ≠ ⊥) :
    ∃ U : Subgroup E, U ≠ ⊥ ∧ IsPGroup p U ∧
      Function.Surjective (f.comp (normalizer (U : Set E)).subtype) := by
  let N := R.comap f
  let q : N →* R := f.subgroupComap R
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective R hf
  let P : Sylow p N := Sylow.nonempty.some
  have hPmap : (P : Subgroup N).map q = ⊤ :=
    ((P.mapSurjective hq).is_maximal' (hR.to_subgroup ⊤) le_top).symm
  let U : Subgroup E := (P : Subgroup N).map N.subtype
  have hUR : U.map f = R := by
    change ((P : Subgroup N).map N.subtype).map f = R
    rw [map_map]
    change (P : Subgroup N).map (R.subtype.comp q) = R
    rw [←map_map,hPmap,←MonoidHom.range_eq_map,range_subtype]
  have hNmap : N.map f = R := by
    rw [map_comap_eq, MonoidHom.range_eq_top.mpr hf, top_inf_eq]
  have hnmap : (normalizer (U : Set E)).map f = ⊤ := by
    have hh := congrArg (Subgroup.map f) P.normalizer_sup_eq_top
    change ((normalizer (U : Set E)) ⊔ N).map f = (⊤ : Subgroup E).map f at hh
    rw [Subgroup.map_sup,hNmap,map_top_of_surjective _ hf] at hh
    have hle : R ≤ (normalizer (U : Set E)).map f :=
      hUR ▸ map_mono (le_normalizer : U ≤ normalizer (U : Set E))
    rwa [sup_eq_left.mpr hle] at hh
  refine ⟨U,?_,P.isPGroup'.map _,?_⟩
  · intro he
    rw [he,Subgroup.map_bot] at hUR
    exact hne hUR.symm
  · exact MonoidHom.range_eq_top.mp (by rw [MonoidHom.range_comp,range_subtype,hnmap])
end Theory.GroupTheory

