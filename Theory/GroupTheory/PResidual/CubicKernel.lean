module

public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PCoreLocalSetup
/-!
# Iterated residuals in a normal subgroup with a cubic supplement

If X/O₂(X) has order three, then O³(X) is a two-group. Consequently,
when a normal subgroup C is supplemented by X, O²(O³(G)) lies in C.
The proof passes to G/C, transports the three-residual along X's
surjection, and kills the resulting two-group image with O².

Source application: the sufficient two-kernel replacement calculation for
Aschbacher–Smith 13.8.20, printed p.954/PDF p.971.
-/

public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- A cubic two-core quotient leaves a two-group three-residual. -/
theorem threeResidual_isPGroup_of_cubicCoreQuotient
    (hc : Nat.card (G ⧸ pCore 2 G) = 3) : IsPGroup 2 (pResidual 3 G) := by
  have h3 : IsPGroup 3 (G ⧸ pCore 2 G) := IsPGroup.of_card (n := 1) (by simpa using hc)
  have hle : pResidual 3 G ≤ pCore 2 G := sInf_le ⟨inferInstance, h3⟩
  exact pCore_isPGroup.to_le hle

variable [Finite G]
/-- A cubic supplement forces the iterated residual into the normal kernel. -/
theorem two_threeResidual_le_normal_of_cubic_supplement
    (C X : Subgroup G) [C.Normal] (hgen : C ⊔ X = ⊤)
    (hc : Nat.card (X ⧸ pCore 2 X) = 3) :
    (pResidual 2 (pResidual 3 G)).map (pResidual 3 G).subtype ≤ C := by
  let q := QuotientGroup.mk' C
  let f := q.comp X.subtype
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    have hm := congrArg (fun A : Subgroup G => A.map q) hgen
    simpa only [map_sup, q, QuotientGroup.map_mk'_self, bot_sup_eq,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective C),
      f, MonoidHom.range_comp, range_subtype] using hm
  have htwo : IsPGroup 2 (pResidual 3 (G ⧸ C)) := by
    rw [← map_pResidual_of_surjective 3 f hf]
    exact (threeResidual_isPGroup_of_cubicCoreQuotient hc).map f
  let r : pResidual 3 G →* pResidual 3 (G ⧸ C) :=
    (q.comp (pResidual 3 G).subtype).codRestrict _
      (fun x => map_pResidual_le 3 q (mem_map_of_mem q x.property))
  have hz : pResidual 2 (pResidual 3 (G ⧸ C)) = ⊥ :=
    bot_unique (sInf_le ⟨inferInstance, htwo.to_quotient ⊥⟩)
  rintro _ ⟨x, hx, rfl⟩
  have hh := map_pResidual_le 2 r (mem_map_of_mem r hx)
  rw [hz] at hh
  exact (QuotientGroup.eq_one_iff x.val).mp (congrArg Subtype.val hh)
end Subgroup
