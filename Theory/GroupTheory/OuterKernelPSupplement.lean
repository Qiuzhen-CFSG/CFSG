module
public import Theory.GroupTheory.NormalizerActionCore
public import Theory.GroupTheory.SolvableOuterQuotient
/-!
# Outer kernels of centerless normal subgroups with prime-group supplements

If B is centerless, normal and supplemented by a p-group, its centralizer
embeds into the p-group quotient by B. A trivial ambient p-core therefore
kills that centralizer. The literal map to Out(B) consequently has kernel B.

Source application: Aschbacher--Smith 12.6.31, printed p.836,
refs/quasithin.pdf, excluding the normal Sp₄ and G₂ rows.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {J : Type*} [Group J]
/-- A centerless normal subgroup with a p-group supplement is self-centralizing
when the ambient p-core vanishes. -/
theorem centralizer_eq_bot_of_centerless_p_supplement {p : ℕ}
    (B T : Subgroup J) [B.Normal] (hT : IsPGroup p T)
    (hgen : B ⊔ T = ⊤) (hz : center B = ⊥) (hzero : pCore p J = ⊥) :
    centralizer (B : Set J) = ⊥ := by
  let C := centralizer (B : Set J)
  have hquot : IsPGroup p (J ⧸ B) := isPGroup_quotient_of_sup_eq_top B T hT hgen
  let f : C →* J ⧸ B := (QuotientGroup.mk' B).comp C.subtype
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply bot_unique
    intro c hc
    have hb : (c : J) ∈ B := (QuotientGroup.eq_one_iff _).mp hc
    have hm : (⟨c,hb⟩ : B) ∈ center B :=
      mem_center_iff.mpr (fun b => Subtype.ext (c.property b b.property))
    have he : (⟨c,hb⟩ : B) = 1 := mem_bot.mp (hz ▸ hm)
    exact mem_bot.mpr (Subtype.ext (congrArg (fun b : B => b.val) he))
  exact bot_unique ((show C ≤ pCore p J from
    le_sSup ⟨inferInstance,hquot.of_injective f hf⟩).trans hzero.le)

/-- The actual outer action has precisely the original normal subgroup as kernel. -/
theorem outer_action_kernel_of_centerless_p_supplement {p : ℕ}
    (B T : Subgroup J) [B.Normal] (hT : IsPGroup p T)
    (hgen : B ⊔ T = ⊤) (hz : center B = ⊥) (hzero : pCore p J = ⊥) :
    ((QuotientGroup.mk' (MulAut.innerSubgroup B)).comp
      (MulAut.conjNormal : J →* MulAut B)).ker = B := by
  rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk',MulAut.conjNormal_comap_innerSubgroup,
    centralizer_eq_bot_of_centerless_p_supplement B T hT hgen hz hzero,sup_bot_eq]
end Theory.GroupTheory
