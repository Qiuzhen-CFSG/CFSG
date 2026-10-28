module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection.Choice
public import Theory.GroupTheory.CComponent.NonsolvableNormalIntersection

/-!
# Escape of the proper first-flag component

A proper component containing the first flag residual cannot normalize L.
Otherwise its nonsolvable intersection with the normal subgroup L forces the
component into L; its perfectness then puts it back in the first residual.
The triangle generation identity transfers this escape to its third vertex.

Source: Aschbacher--Smith, proof of 11.1.2, printed pp.761--762.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : Chapter12.Section02.ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)

/-- The strict component inclusion in the source forces escape from N_G(L). -/
theorem proper_flag_component_escapes (K : Subgroup G)
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hlocal : f.Li 0 ∈ Chapter1.L G T) (hlt : f.Li 0 < K) :
    ¬ K ≤ normalizer (L : Set G) := by
  intro hKL
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using hK.2.subgroupOf_of_le le_rfl hK.1
  let : (L.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hKL
  have hnot : ¬ Group.IsSolvable ((f.Li 0).subgroupOf K) := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable hlocal
      (Group.isSolvable_of_surjective (f := (subgroupOfEquivOfLe hlt.le).toMonoidHom)
        (subgroupOfEquivOfLe hlt.le).surjective)
  have hKle : K ≤ L := by
    have hb : (f.Li 0).subgroupOf K ≤ L.subgroupOf K :=
      comap_mono ((LocalGeometry.localResidual_le _).trans inf_le_left)
    have he := htop.le_normal_of_nonsolvable_subgroup hnot le_top hb
    exact subgroupOf_eq_top.mp (top_unique he)
  let : Group.IsPerfect (K.subgroupOf (normalizer (f.Vi 0 : Set G))) := hK.2.perfect
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hK.1).toMonoidHom) (subgroupOfEquivOfLe hK.1).surjective
  exact (not_le_of_gt hlt) (le_map_solvableResidual_of_isPerfect K
    (L ⊓ normalizer (f.Vi 0 : Set G)) (le_inf hKle hK.1))

/-- The actual third triangle vertex escapes once the first component is proper. -/
theorem third_vertex_escapes_of_proper_flag_component (K K₀ : Subgroup G)
    (hK : Source.ComponentIn (normalizer (f.Vi 0 : Set G)) K)
    (hlocal : f.Li 0 ∈ Chapter1.L G T) (hlt : f.Li 0 < K)
    (hgen : K = f.Li 0 ⊔ K₀) :
    ¬ K₀ ⊔ f.Li 1 ≤ normalizer (L : Set G) :=
  third_vertex_escapes D S f K K₀ hgen
    (proper_flag_component_escapes D S f K hK hlocal hlt)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Reselection
