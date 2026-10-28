module
public import Theory.GroupTheory.WreathTwoThreeCore
public import Theory.GroupTheory.WreathTwoSylowModel
public import Theory.GroupTheory.TwoThreeCoreQuotient

/-!
# The dihedral quotient above the literal overlap two-three core

The three-core of S₃ wr C₂ has order nine and two-group quotient. Its
intersection with a Sylow two-subgroup is trivial, so the quotient is the
actual dihedral Sylow model of order eight. Transport through a given
two-core quotient identifies the quotient by O₂,₃ in the source order:
first O₂, then O₃ in the quotient.
Source: Aschbacher--Smith 10.2.3(3), printed p.745.
-/

open Subgroup Theory.GroupTheory
public noncomputable section
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
local notation "W" => WreathTwoResidual.Actor

theorem wreath_threeCore_quotient :
    Nonempty ((W ⧸ pCore 3 W) ≃* DihedralGroup 4) := by
  let P : Sylow 2 W := Classical.choice inferInstance
  let q := QuotientGroup.mk' (pCore 3 W)
  let f := q.comp (P : Subgroup W).subtype
  have hf : Function.Surjective f := by
    let Q := P.mapSurjective (QuotientGroup.mk'_surjective (pCore 3 W))
    have hQ : (Q : Subgroup (W ⧸ pCore 3 W)) = ⊤ :=
      top_unique ((WreathTwoResidual.threeCore_quotient_two.to_subgroup ⊤).le_sylow_of_normal Q)
    intro x
    have hx : x ∈ (P : Subgroup W).map q := by
      change x ∈ (Q : Subgroup (W ⧸ pCore 3 W))
      rw [hQ]
      trivial
    obtain ⟨y,hy,he⟩ := hx
    exact ⟨⟨y,hy⟩,he⟩
  have hd : Disjoint (P : Subgroup W) (pCore 3 W) :=
    P.isPGroup'.disjoint_of_coprime pCore_isPGroup (by decide)
  have hi : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    exact disjoint_def.mp hd x.property ((QuotientGroup.eq_one_iff _).mp hx)
  obtain ⟨e⟩ := wreath_two_sylow_mulEquiv_dihedral_four P
  exact ⟨(MulEquiv.ofBijective f ⟨hi,hf⟩).symm.trans e⟩

theorem twoThreeCoreQuotient_of_wreath {X : Type*} [Group X] [Finite X]
    (e : (X ⧸ pCore 2 X) ≃* W) :
    Nonempty ((X ⧸ (pCore 3 (X ⧸ pCore 2 X)).comap (QuotientGroup.mk' (pCore 2 X))) ≃*
      DihedralGroup 4) := by
  obtain ⟨d⟩ := wreath_threeCore_quotient
  exact ⟨(twoThreeCoreQuotientEquiv X).trans
    ((QuotientGroup.congr _ _ e (pCore_map_iso 3 e)).trans d)⟩
end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.QuotientGeometry
