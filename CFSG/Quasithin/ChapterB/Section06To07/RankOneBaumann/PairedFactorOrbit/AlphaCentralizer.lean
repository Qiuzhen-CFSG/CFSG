module
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.Source
public import Stellmacher.ElementaryAbelianMaxJFixedIntersection
/-!
# A selected paired component has nonzero fixed points in alpha

The second Sylow fixed line in the actual paired natural quotient lifts to
alpha(T). The first component fixes that line. Its two-perfectness removes
the retained central kernel from the action, so it fixes the lift itself.
This supplies the positive fixed-subgroup premise used to identify the
actual selected Cartan axis in Aschbacher--Smith 10.2.3(4), pp.746--747.
-/
public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
open QuasisimpleSource SourceInduction CFSG.Quasithin.ChapterB
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
set_option backward.isDefEq.respectTransparency false in
theorem paired_source_alpha_centralizer_nontrivial
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first)
    (K : Subgroup G) (hK : IsPPerfect 2 K)
    (hKi : K.map q ≤ d.first.map
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype) :
    thompsonAlpha (T : Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥ := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  let A := Matrix.SpecialLinearGroup (Fin 2) F.Carrier
  let V := Fin 2 → F.Carrier
  let N := linearNatural F 2
  obtain ⟨ρ,_,hnat,_,⟨hJq,_⟩,hfix⟩ := source_images_and_fixedSpace T hP U hU hJ q hq hker d F c hexchange
  obtain ⟨P₀,hP₀⟩ := (T.mapSurjective hq).exists_sylow_map_eq_inf_of_normal Y
  have hPJ : (P₀ : Subgroup Y).map Y.subtype = (elementaryAbelianMaxJ (T : Subgroup G)).map q :=
    hP₀.trans hJq.symm
  obtain ⟨P,Q,hPQ⟩ := layer_fixedSpace_product F Y c.action.groupEquiv ρ hnat _ P₀ hPJ
  have hne : fixedSpace N (Q : Subgroup A) ≠ ⊥ := by
    intro hz
    obtain ⟨g,_,hg⟩ := exists_residual_fixed_line_span F Q
    rw [hz,Submodule.map_bot,bot_sup_eq] at hg
    exact bot_ne_top hg
  obtain ⟨y,hy,hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨v,hv⟩ := c.quotientMap_surjective (0,y)
  have hvJ : v ∈ fixedSpace α ((elementaryAbelianMaxJ (T : Subgroup G)).map q) := by
    rw [hfix,hPQ]
    change c.quotientMap v ∈ (fixedSpace N (P : Subgroup A)).prod (fixedSpace N (Q : Subgroup A))
    rw [hv]
    exact ⟨Submodule.zero_mem _,hy⟩
  have hvα : (v.toMul:G) ∈ thompsonAlpha (T : Subgroup G) := by
    have hUT := hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)
    have hh := omegaCenter_maxJ_inf_elementary_eq_fixed (T : Subgroup G) U hUT
    exact (hh.ge ⟨v.toMul.property,
      (NormalElementaryQuotient.mem_fixedSpace_image U q hq hker _ v).mp hvJ⟩).1
  have hKfix : v ∈ fixedSpace (α.comp q) K := by
    apply fixed_of_pPerfect_central_kernel (α.comp q) K hK c.quotientMap
    · intro w hw a
      have hwY : w ∈ Representation.invariants (α.comp Y.subtype) := by
        rw [←c.quotientMap_ker]
        exact hw
      have haY : q a ∈ Y := (map_subtype_le d.first) (hKi (mem_map_of_mem q a.property))
      exact hwY ⟨q a,haY⟩
    · intro k
      obtain ⟨a,ha,hqa⟩ := hKi (mem_map_of_mem q k.property)
      have ha' : a ∈ ((⊤ : Subgroup A).prod ⊥).map c.action.groupEquiv.symm.toMonoidHom :=
        c.first_eq.symm ▸ ha
      obtain ⟨x,hx,hxa⟩ := ha'
      have hcoords : c.action.groupEquiv a=x := by
        rw [←hxa]
        exact c.action.groupEquiv.apply_symm_apply x
      have hh := c.quotientMap_action a v
      change c.quotientMap (α (a:H) v) = _ at hh
      change (a:H)=q (k:G) at hqa
      rw [hqa,hcoords,hv] at hh
      change c.quotientMap (α (q k) v) = (N x.1 0,N x.2 y) at hh
      rw [show x.2=1 from hx.2,map_zero,map_one,Module.End.one_apply] at hh
      exact hh.trans hv.symm
  have hvK : (v.toMul:G) ∈ centralizer (K : Set G) := by
    intro k hk
    have hh := congrArg (fun x : Additive U => (x.toMul:G)) (hKfix ⟨k,hk⟩)
    change ((α (q k) v).toMul:G)=(v.toMul:G) at hh
    rw [NormalElementaryQuotient.representation_apply] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  intro hz
  have he : (v.toMul:G)=1 := mem_bot.mp (hz ▸ (show (v.toMul:G) ∈
    thompsonAlpha (T : Subgroup G) ⊓ centralizer (K : Set G) from ⟨hvα,hvK⟩))
  have hv0 : v=0 := Additive.toMul.injective (Subtype.ext he)
  have hh := congrArg Prod.snd hv
  rw [hv0,map_zero] at hh
  exact hy0 hh.symm
end CFSG.Quasithin.ChapterB.RankOneBaumann.PairedFactorOrbit
