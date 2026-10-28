module
public import CFSG.Quasithin.ChapterB.Section06To07.Elementary
public import Theory.SpecificGroups.SL2.FrattiniParabolic
/-!
# Minimal parabolicity of a normalized natural block

The actual block quotient is SL₂. Its Sylow subgroup has a unique maximal
overgroup; the two-core kernel and the normal two-group extension preserve
this property and the Sylow subgroup remains nonnormal. This supplies the
minimality hypothesis used in the original C.5.4 natural-module argument.

Source: Aschbacher–Smith C.5.4(2), printed p.155, using B.6.10.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
theorem minimal_of_natural_quotient (K T : Subgroup G) (hn : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (e : (K ⧸ pCore 2 K) ≃* SL(2,F)) : ChapterB.IsMinimalParabolicOver P ⊤ := by
  let A := K ⊔ T
  let L := K.subgroupOf A
  let : L.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le K.le_normalizer hn)
  let eL : L ≃* K := subgroupOfEquivOfLe le_sup_left
  let eQ := QuotientGroup.congr (pCore 2 L) (pCore 2 K) eL (pCore_map_iso 2 eL)
  let f : L →* SL(2,F) := e.toMonoidHom.comp (eQ.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  have hf : Function.Surjective f := e.surjective.comp (eQ.surjective.comp (QuotientGroup.mk'_surjective _))
  have hk : f.ker ≤ (frattini (L ⧸ pCore 2 L)).comap (QuotientGroup.mk' (pCore 2 L)) := by
    intro x hx
    have hx' : QuotientGroup.mk' (pCore 2 L) x = 1 := eQ.map_eq_one_iff.mp (e.map_eq_one_iff.mp hx)
    change QuotientGroup.mk' (pCore 2 L) x ∈ frattini (L ⧸ pCore 2 L)
    rw [hx']
    exact one_mem _
  apply minimal_over_normal_rankOne_frattini F L P ?_ f hf hk
  apply map_injective A.subtype_injective
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le le_sup_left,hP,← subgroupOf_self A,map_subgroupOf_eq_of_le le_rfl]
end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
