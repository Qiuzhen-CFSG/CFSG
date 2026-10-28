module
public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Assembly.Source
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicCentralizer

/-!
# Cubic fixed points in the original G.2.4 layers

A cubic subgroup of the residual embeds in the actual A₅ star quotient.
Its centralizer has odd order, so a fixed element of the residual two-core
lies in the kernel S. The original natural SL₂(4) upper layer has no cubic
fixed points, placing that element in S₂. This is the precise fixed-space
input used to exclude the G₂ natural central quotient in13.5.25.
Source: Aschbacher–Smith13.5.25 and G.2.4(6), printed pp.925,334.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section02.AlternatingFive
open Setup
variable {G : Type*} [Group G] [Finite G] {S : Setup G} {g : G}

/-- The literal residual two-core fixed by a cubic subgroup lies in S₂. -/
theorem Hypothesis.cubic_fixed_le_second (b : Hypothesis S g)
    (A : Subgroup G) (hAL : A ≤ S.L₁) (hA : Nat.card A = 3) :
    S.L₁.pCoreIn 2 ⊓ centralizer (A : Set G) ≤ AlternatingFive.S₂ S g := by
  have hLL : S.L₁ ≤ S.L := (map_subtype_le _).trans inf_le_left
  let f : S.L₁ →* S.star S.L := (starProjection S).comp (inclusion hLL)
  have hk : f.ker = (terminalLocalStarProjection S).ker := by
    ext x
    change f x = 1 ↔ terminalLocalStarProjection S x = 1
    rw [Subtype.ext_iff,Subtype.ext_iff]
    rfl
  have hp : IsPGroup 2 f.ker := hk ▸ terminalLocalStarProjection_ker_isPGroup S
  let a : A →* S.star S.L := f.comp (inclusion hAL)
  have hpa : IsPGroup 2 a.ker := by
    change IsPGroup 2 (f.comp (inclusion hAL)).ker
    rw [←MonoidHom.comap_ker]
    exact hp.comap_of_injective (inclusion hAL) (inclusion_injective hAL)
  have hthree : IsPGroup 3 A := IsPGroup.of_card (n := 1) hA
  have ha : Function.Injective a := (MonoidHom.ker_eq_bot_iff a).mp (by
    simpa only [inf_idem] using
      (IsPGroup.disjoint_of_coprime hpa (hthree.to_subgroup a.ker)
        (by decide : Nat.Coprime 2 3)).eq_bot)
  have hc : Nat.card a.range = 3 :=
    (Nat.card_congr (MonoidHom.ofInjective ha).toEquiv).symm.trans hA
  have hC : IsPGroup 3 (centralizer (a.range : Set (S.star S.L))) :=
    IsPGroup.of_card (n := 1)
      (alternatingGroup.FiveLocalGeometry.cubic_centralizer_card b.model a.range hc)
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := A) 3 (by rw [hA])
  let tL : S.L := ⟨t,(hAL.trans hLL) t.property⟩
  have htstar : orderOf (starProjection S tL) = 3 :=
    (orderOf_injective a ha t).trans ht
  let := b.second_normal_in_core b.L_le_I
  obtain ⟨n,c,_,_,_,_,_⟩ := b.source_natural_layer
    Section01.SL2FourRecognition.recognitionInput
  rintro j ⟨⟨x,hx,rfl⟩,hj⟩
  have hfx : f x = 1 := by
    have hmem : f x ∈ (pCore 2 S.L₁).map f ⊓ centralizer (a.range : Set (S.star S.L)) := by
      refine ⟨mem_map_of_mem f hx,?_⟩
      rintro _ ⟨z,rfl⟩
      change f (inclusion hAL z) * f x = f x * f (inclusion hAL z)
      rw [←map_mul,←map_mul]
      congr 1
      apply Subtype.ext
      exact mem_centralizer_iff.mp hj z.val z.property
    have hd := IsPGroup.disjoint_of_coprime (pCore_isPGroup.map f) hC
      (by decide : Nat.Coprime 2 3)
    simpa only [hd.eq_bot,mem_bot] using hmem
  have hxS : x.val ∈ S.S g := by
    have he := congrArg Subtype.val hfx
    let xLT : S.LT := ⟨x,(hLL.trans le_sup_left) x.property⟩
    have hq : QuotientGroup.mk' (pCore 2 S.LT) xLT = 1 := he
    rw [b.S_eq_star_kernel]
    exact ⟨(hLL.trans b.L_le_I) x.property,
      mem_map_of_mem S.LT.subtype ((QuotientGroup.eq_one_iff xLT).mp hq)⟩
  let u : S.S g := ⟨x,hxS⟩
  let q := QuotientGroup.mk' ((AlternatingFive.S₂ S g).subgroupOf (S.S g))
  have hfix : c.action ⟨tL,b.L_le_I tL.property⟩ (q u) = q u := by
    rw [c.action_mk]
    congr 1
    apply Subtype.ext
    change t.val * x.val * t.val⁻¹ = x.val
    have hcomm : t.val * x.val = x.val * t.val := mem_centralizer_iff.mp hj t.val t.property
    rw [hcomm,mul_inv_cancel_right]
  exact (QuotientGroup.eq_one_iff u).mp ((c.cubic_fixedPointFree tL htstar) (q u) hfix)

end CFSG.Quasithin.ChapterG.Section02.AlternatingFive
