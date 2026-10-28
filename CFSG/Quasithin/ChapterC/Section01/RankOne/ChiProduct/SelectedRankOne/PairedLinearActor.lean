module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearAxis
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLocalModule
public import Theory.Representation.NormalElementaryQuotient.MovedCoordinates
/-!
# The original first coordinate is the selected local action quotient

Restrict the same marked product coordinates to the genuine component and
its original Baumann join. The first coordinate is surjective, and its
kernel is exactly the centralizer of the literal local module. The proof
retains the original central kernel and uses perfectness to kill the
opposite factor action on the first support.

Source: Aschbacher–Smith C.1.26 and B.6.10, printed pp.132 and117.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.QuasisimpleSource ChapterB.RankOneBaumann.PairedFactorOrbit
variable {G H D : Type*} [Group G] [Group H] [Group D]
@[expose] noncomputable def pairedFirstActor
    (q : G →* H) (Y : Subgroup H) (e : Y ≃* D × D)
    (N : Subgroup G) (hN : N.map q ≤ Y) : N →* D :=
  (MonoidHom.fst D D).comp (e.toMonoidHom.comp
    ((q.comp N.subtype).codRestrict Y (fun n => hN (mem_map_of_mem q n.property))))

variable (F : BinaryField)
local notation "A" => Matrix.SpecialLinearGroup (Fin 2) F.Carrier
local notation "W" => Fin 2 → F.Carrier

theorem paired_first_actor_kernel
    (T U L : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (Y : Subgroup H) (e : Y ≃* A × A) (hA : IsPPerfect 2 A)
    (hNY : (L ⊔ baumann T).map q ≤ Y)
    (hL : L.map q = (⊤ : Subgroup A).map (Y.subtype.comp (e.symm.toMonoidHom.comp (MonoidHom.inl A A))))
    (f : Additive U →ₗ[ZMod 2] (W × W)) (hf : Function.Surjective f)
    (hfk : f.ker ≤ fixedSpace (NormalElementaryQuotient.representation U q hq hk)
      (Y.subtype.comp e.symm.toMonoidHom).range)
    (he : ∀ g v, f (NormalElementaryQuotient.representation U q hq hk
      ((Y.subtype.comp e.symm.toMonoidHom) g) v) =
      (linearNatural F 2 g.1 (f v).1,linearNatural F 2 g.2 (f v).2))
    (hv : (GlaubermanNiles.localV (inclusion (show baumann T ≤ L ⊔ baumann T from le_sup_right))).map
      (L ⊔ baumann T).subtype = ⁅U,L⁆ ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G))) :
    Function.Surjective (pairedFirstActor q Y e (L ⊔ baumann T) hNY) ∧
      (pairedFirstActor q Y e (L ⊔ baumann T) hNY).ker =
        GlaubermanNiles.localKernel (inclusion (show baumann T ≤ L ⊔ baumann T from le_sup_right)) := by
  let N := L ⊔ baumann T
  let α := NormalElementaryQuotient.representation U q hq hk
  let j := Y.subtype.comp e.symm.toMonoidHom
  let j₁ := j.comp (MonoidHom.inl A A)
  let r := pairedFirstActor q Y e N hNY
  let M := NormalElementaryQuotient.commutatorSpace U L
  have hres : pResidual 2 A = ⊤ := (pResidual_eq_top_iff 2 A).mpr hA
  have hm : M.map f = (⊤ : Submodule (ZMod 2) W).prod ⊥ := by
    change (NormalElementaryQuotient.commutatorSpace U L).map f = _
    rw [NormalElementaryQuotient.commutatorSpace_eq U q hq hk,hL,←hres]
    apply first_axis_moved_map F α j₁ f hf
    intro a v
    have hh := he (a,1) v
    simpa only [j₁,j,MonoidHom.comp_apply,MonoidHom.inl_apply,map_one,Module.End.one_apply] using hh
  have hvalue (n : N) : j (e ⟨q n,hNY (mem_map_of_mem q n.property)⟩) = q n := by
    exact congrArg Subtype.val (e.symm_apply_apply _)
  have hs : Function.Surjective r := by
    intro a
    have hh : j₁ a ∈ L.map q := hL.symm ▸ mem_map_of_mem j₁ (mem_top a)
    obtain ⟨l,hl,hql⟩ := hh
    let n : N := ⟨l,(show L ≤ N from le_sup_left) hl⟩
    refine ⟨n,?_⟩
    have heq : (⟨q n,hNY (mem_map_of_mem q n.property)⟩ : Y) = e.symm (a,1) := Subtype.ext hql
    change (e ⟨q n,hNY (mem_map_of_mem q n.property)⟩).1 = a
    rw [heq,e.apply_symm_apply]
  refine ⟨hs,?_⟩
  rw [localKernel_factor_baumann T U L hv]
  ext n
  have hc : (n:G) ∈ centralizer ((⁅U,L⁆ : Subgroup G) : Set G) ↔
      ∀ v ∈ M, α (q n) v = v := by
    constructor
    · intro hn v hv'
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [NormalElementaryQuotient.representation_apply,←hn v.toMul hv',mul_inv_cancel_right]
    · intro hn w hw
      let v : Additive U := Additive.ofMul ⟨w,(commutator_le_left U L) hw⟩
      have hh := congrArg (fun v : Additive U => (v.toMul:G)) (hn v hw)
      rw [NormalElementaryQuotient.representation_apply] at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  change r n = 1 ↔ (n:G) ∈ centralizer ((⁅U,L⁆ : Subgroup G) : Set G)
  rw [hc,←hvalue n]
  exact (first_axis_action_kernel F α j hA f hfk he M hm
    (e ⟨q n,hNY (mem_map_of_mem q n.property)⟩)).symm
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
