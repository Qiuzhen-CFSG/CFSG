module
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Detecting a reduced action on a normal submodule

Suppose a normal subgroup K is supplemented by a two-group. If its action
kernel on a normal submodule already centralizes the full reduced module,
then the two modules have the same ambient centralizer. Indeed the image
of the smaller module's centralizer embeds in the two-group quotient by
K, so reducedness kills this normal image.

Source: the reduced-module kernel comparison used in Aschbacher--Smith
10.2.9, printed pp.751--752; see also B.2.11--14, printed pp.77--78.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A reduced action is detected on a normal submodule once its kernel
on a normal subgroup with a two-group supplement is detected there. -/
theorem IsPReduced.centralizer_eq_of_normal_intersection
    {U V : Subgroup G} (hU : IsPReduced 2 U) [V.Normal] (hVU : V ≤ U)
    (K P : Subgroup G) [K.Normal] (hP : IsPGroup 2 P) (hgen : K ⊔ P = ⊤)
    (hK : K ⊓ centralizer (V : Set G) ≤ centralizer (U : Set G)) :
    centralizer (V : Set G) = centralizer (U : Set G) := by
  let := hU.normal
  let q := QuotientGroup.mk' (centralizer (U : Set G))
  let A := K.map q
  let C := centralizer (V : Set G)
  let N := C.map q
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : A.Normal := Normal.map inferInstance q hq
  let : N.Normal := Normal.map inferInstance q hq
  have hCA : N ⊓ A = ⊥ := by
    apply bot_unique
    rintro x ⟨⟨z,hz,hzx⟩,k,hk,hkx⟩
    have he : z⁻¹*k ∈ centralizer (U : Set G) := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (z⁻¹*k) = 1
      rw [map_mul,map_inv,hzx,hkx,inv_mul_cancel]
    have hkc : k ∈ C := by
      have hh := C.mul_mem hz ((centralizer_le hVU) he)
      simpa only [mul_inv_cancel_left] using hh
    have hzq : q k = 1 := (QuotientGroup.eq_one_iff _).mpr (hK ⟨hk,hkc⟩)
    exact mem_bot.mpr (hkx.symm.trans hzq)
  have hgen' : A ⊔ P.map q = ⊤ := by
    change K.map q ⊔ P.map q = ⊤
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective q hq]
  have hquot : IsPGroup 2 ((G ⧸ centralizer (U : Set G)) ⧸ A) :=
    isPGroup_quotient_of_sup_eq_top A (P.map q) (hP.map q) hgen'
  let f : N →* ((G ⧸ centralizer (U : Set G)) ⧸ A) :=
    (QuotientGroup.mk' A).comp N.subtype
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply bot_unique
    intro x hx
    have hxA : (x : G ⧸ centralizer (U : Set G)) ∈ A := (QuotientGroup.eq_one_iff _).mp hx
    exact Subtype.ext (mem_bot.mp (hCA ▸ (show (x : G ⧸ centralizer (U : Set G)) ∈
      N ⊓ A from ⟨x.property,hxA⟩)))
  have hpN : IsPGroup 2 N := hquot.of_injective f hf
  have hNle : N ≤ pCore 2 (G ⧸ centralizer (U : Set G)) := le_sSup ⟨inferInstance,hpN⟩
  have hN : N = ⊥ := bot_unique (hNle.trans_eq hU.quotient_pCore_eq_bot)
  apply le_antisymm ?_ (centralizer_le hVU)
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  exact mem_bot.mp (hN ▸ mem_map_of_mem q hx)

end Theory.GroupTheory

