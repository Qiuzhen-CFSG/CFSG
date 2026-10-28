module
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter
public import Theory.GroupTheory.PGroup.CharacteristicKernel

/-!
# Centralizers in centerless quasisimple two-extensions

The centralizer of a centerless normal subgroup embeds in the quotient.
When that quotient is a two-group and the subgroup is quasisimple, its
centralizer is exactly the two-core: components centralize solvable normal
subgroups. These statements concern normality in the displayed ambient group.

Source application: Aschbacher--Smith D.3.4 and the homogeneous orbit
section in 5.1.23, printed pp.194 and 645--646, `refs/quasithin.pdf`.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

theorem centralizer_isPGroup_of_centerless_quotient
    {p : ℕ} (K : Subgroup G) [K.Normal] (hz : center K = ⊥)
    (hq : IsPGroup p (G ⧸ K)) : IsPGroup p (centralizer (K : Set G)) := by
  let C := centralizer (K : Set G)
  let f : C →* G ⧸ K := (QuotientGroup.mk' K).comp C.subtype
  apply hq.of_injective f
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro x hx
  have hxK : (x : G) ∈ K := (QuotientGroup.eq_one_iff _).mp hx
  have hxZ : (⟨x,hxK⟩ : K) ∈ center K := mem_center_iff.mpr (fun k =>
    Subtype.ext (mem_centralizer_iff.mp x.property k k.property))
  rw [hz,mem_bot] at hxZ
  exact Subtype.ext (congrArg (fun k : K => (k : G)) hxZ)


variable [Finite G]

theorem centralizer_eq_twoCore_of_centerless_quasisimple_quotient
    (K : Subgroup G) [K.Normal] [IsQuasisimple K] (hz : center K = ⊥)
    (hq : IsPGroup 2 (G ⧸ K)) : centralizer (K : Set G) = pCore 2 G := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance,centralizer_isPGroup_of_centerless_quotient K hz hq⟩
  · let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
    have hc : IsComponent G K := ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩
    exact le_centralizer_iff.mp (hc.le_centralizer_of_solvable_normal (pCore 2 G))


end Theory.GroupTheory
