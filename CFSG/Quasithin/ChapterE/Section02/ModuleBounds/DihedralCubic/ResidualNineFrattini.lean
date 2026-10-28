module

public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.ResidualNine
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.PGroupCore
public import Theory.ElementaryAbelian.Injective

/-!
# Descending the source inversion to the orthogonal residual

An order-nine image in the quaternion orthogonal group is elementary. A normal
two-subgroup therefore maps trivially by coprime disjointness, and the induced
map on the quotient kills its Frattini subgroup. Consequently inversion on the
source quotient modulo Frattini descends to inversion of the actual orthogonal
image, where the residual-nine obstruction applies.

The source consumer uses the literal two-residual K = O²(H) and the normal
two-subgroup K ∩ O₂(H), represented inside K by subgroupOf. It retains the
original normal quaternion subgroup and the marked Sylow-normal elementary
subgroup. No residual image faithfulness is assumed.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, E.2.17,
printed pp.229--230, the inversion of Kbar/Phi(Kbar) and its order-nine image.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.DihedralCubic

/-- The actual action kills the Frattini preimage above any normal two-kernel
when its orthogonal image has order nine. -/
theorem frattini_preimage_le_orthogonal_kernel
    {K : Type*} [Group K] [Finite K] (f : K→*BinaryFourPlus.Wreath)
    (h9 : Nat.card f.range=9) (N : Subgroup K) [N.Normal] (hN : IsPGroup 2 N) :
    (frattini (K⧸N)).comap (QuotientGroup.mk' N)≤f.ker := by
  let := orthogonal_subgroup_nine_elementary f.range h9
  have hp3 : IsPGroup 3 f.range := IsElementaryAbelian.isPGroup 3 _
  have hd : Disjoint (N.map f) f.range :=
    IsPGroup.disjoint_of_coprime (hN.map f) hp3 (by decide)
  have hz : N.map f=⊥ := disjoint_self.mp (hd.mono_right (map_le_range f N))
  have hNk : N≤f.ker := (Subgroup.map_eq_bot_iff _).mp hz
  let g := QuotientGroup.lift N f hNk
  have hr : g.range≤f.range := by
    rintro x ⟨y,rfl⟩
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective N y
    exact ⟨k,rfl⟩
  let : IsElementaryAbelian 3 g.range :=
    IsElementaryAbelian.of_injective (inclusion hr) (inclusion_injective hr)
  let : Fact (IsPGroup 3 g.range) := ⟨IsElementaryAbelian.isPGroup 3 _⟩
  have h := frattini_le_comap_frattini_of_surjective g.rangeRestrict_surjective
  rw [frattini_eq_bot_of_isElementaryAbelian (R:=g.range) (p:=3)] at h
  intro x hx
  have hh := mem_bot.mp (h hx)
  exact congrArg Subtype.val hh

/-- The residual-nine exclusion with the source inversion modulo Frattini,
rather than a separate inversion assumption on the orthogonal image. -/
theorem source_residual_image_ne_nine_of_frattini_inversion
    {H : Type*} [Group H] [Finite H] (S : Sylow 2 H) (U V : Subgroup H)
    [U.Normal] [IsElementaryAbelian 2 V] (d : QuaternionCentralProductData U)
    (hVS : V≤(S : Subgroup H)) (hn : (V.subgroupOf (S : Subgroup H)).Normal)
    (v : H) (hv : v∈V)
    (hi : ∀ k : pResidual 2 H, (MulAut.conjNormal v : MulAut (pResidual 2 H)) k*k ∈
      (frattini (pResidual 2 H⧸(pCore 2 H).subgroupOf (pResidual 2 H))).comap
        (QuotientGroup.mk' ((pCore 2 H).subgroupOf (pResidual 2 H)))) :
    Nat.card ((pResidual 2 H).map (d.quotientWreathAction.comp MulAut.conjNormal))≠9 := by
  intro h9
  let f := (d.quotientWreathAction.comp MulAut.conjNormal).comp (pResidual 2 H).subtype
  have hf9 : Nat.card f.range=9 := by
    simpa only [f,MonoidHom.range_comp,Subgroup.range_subtype] using h9
  have hN : IsPGroup 2 ((pCore 2 H).subgroupOf (pResidual 2 H)) :=
    pCore_isPGroup.comap_subtype
  have hk := frattini_preimage_le_orthogonal_kernel f hf9
    ((pCore 2 H).subgroupOf (pResidual 2 H)) hN
  apply source_residual_image_ne_nine S U V d hVS hn v hv ?_ h9
  intro k hmem
  have hh := hk (hi ⟨k,hmem⟩)
  change f ((MulAut.conjNormal v : MulAut (pResidual 2 H)) ⟨k,hmem⟩*⟨k,hmem⟩)=1 at hh
  simpa only [f,MonoidHom.comp_apply,Subgroup.subtype_apply,
    Subgroup.coe_mul,MulAut.conjNormal_apply] using hh

end CFSG.Quasithin.ChapterE.DihedralCubic
