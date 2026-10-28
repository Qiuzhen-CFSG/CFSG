module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedFive.ActionCore
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedFive.LocalStructure
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedFive.Module
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender
public import Theory.GroupTheory.ElementaryThompsonFrattini
/-!
# The actual paired-five local S5 action

Restrict the original first moved module to L N_T(L). Its A5 cover extends
to an S5 action with exact centralizer kernel. The first transposition in
the proved original Thompson–Baumann image makes this action surjective.
The same element belongs to the local Thompson subgroup, so local movement
is proved on the same module and prescribed Sylow subgroup.

Source: Aschbacher–Smith C.1.23 and C.1.26, printed pp.129–132.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne.PairedFive
open ChapterB ChapterB.SourceInduction
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

-- The first axis yields the full local conjugation action.
theorem first_local_action
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (c : d.MarkedProduct (naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hk)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first)
    (L : Subgroup G)
    (hi : L.map q = (alternatingGroup (Fin 5)).map
      (SymmetricFive.Paired.leftFactorMap (offenderSubgroup
        (NormalElementaryQuotient.representation U q hq hk)) c.action.groupEquiv))
    (hUL : U ≤ normalizer (L : Set G))
    (hBL : baumann (T : Subgroup G) ≤ normalizer (L : Set G))
    (R : Sylow 2 (localJoin (T : Subgroup G) L))
    (hR : (R : Subgroup (localJoin (T : Subgroup G) L)).map (localJoin (T : Subgroup G) L).subtype =
      (T : Subgroup G) ⊓ normalizer (L : Set G)) :
    let N := localJoin (T : Subgroup G) L
    let V := localMoved (T : Subgroup G) U L
    ∃ (p : N →* Equiv.Perm (Fin 5)) (hp : Function.Surjective p)
      (hk : p.ker = centralizer (V : Set N)),
      ∃ E : Additive V ≃ₗ[ZMod 2] core (Fin 5),
        (L.subgroupOf N).map p = alternatingGroup (Fin 5) ∧
        (∀ g v, E (NormalElementaryQuotient.representation V p hp hk g v) =
          coreRepresentation (Fin 5) g (E v)) ∧
        ¬ elementaryAbelianMaxJ (R : Subgroup N) ≤ centralizer (V : Set N) := by
  let N := localJoin (T : Subgroup G) L
  let V := localMoved (T : Subgroup G) U L
  let W := (⁅U,L⁆ : Subgroup G)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left U L)
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let e := c.action.groupEquiv
  let j := SymmetricFive.Paired.leftFactorMap Y e
  obtain ⟨f,_,hf⟩ := first_five_moved_coordinates U q hq hk d c L hi
  let E := (movedEquiv (T : Subgroup G) U L hUL).trans f
  have he (g : N) (hg : q (g:G) ∈ Y) (v : Additive V) :
      E (conjugationAction V g v) = coreRepresentation (Fin 5) (e ⟨q (g:G),hg⟩).1 (E v) := by
    have hgv : (g:G) * (((movedEquiv (T : Subgroup G) U L hUL) v).toMul:G) * (g:G)⁻¹ ∈ W := by
      exact (conjugationAction V g v).toMul.property
    have hh := hf (g:G) hg ((movedEquiv (T : Subgroup G) U L hUL) v) hgv
    apply Eq.trans ?_ hh
    apply congrArg f
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl
  let L₀ := L.subgroupOf N
  let eL : L₀ ≃* L := subgroupOfEquivOfLe (show L ≤ N from le_sup_left)
  let eA := (alternatingGroup (Fin 5)).equivMapOfInjective j
    (SymmetricFive.Paired.leftFactorMap_injective Y e)
  let a : L₀ →* alternatingGroup (Fin 5) := eA.symm.toMonoidHom.comp
    ((MulEquiv.subgroupCongr hi).toMonoidHom.comp ((q.subgroupMap L).comp eL.toMonoidHom))
  have ha : Function.Surjective a := eA.symm.surjective.comp
    ((MulEquiv.subgroupCongr hi).surjective.comp ((q.subgroupMap_surjective L).comp eL.surjective))
  have hqa (l : L₀) : j (a l) = q ((l:N):G) := by
    exact congrArg Subtype.val (eA.apply_symm_apply ((MulEquiv.subgroupCongr hi) (q.subgroupMap L (eL l))))
  have hla (l : L₀) : q ((l:N):G) ∈ Y := by
    rw [←hqa]
    exact (e.symm ((a l:Equiv.Perm (Fin 5)),1)).property
  have hcoord (l : L₀) : (e ⟨q ((l:N):G),hla l⟩).1 = (a l:Equiv.Perm (Fin 5)) := by
    have hz : (⟨q ((l:N):G),hla l⟩:Y) = e.symm ((a l:Equiv.Perm (Fin 5)),1) := Subtype.ext (hqa l).symm
    rw [hz,e.apply_symm_apply]
  obtain ⟨p,hpk,hpL,hpe⟩ := ambient_five_action V L₀ a ha E (by
    intro l v
    exact (he l (hla l) v).trans (congrArg (fun g => coreRepresentation (Fin 5) g (E v)) (hcoord l)))
  have hpcoord (g : N) (hg : q (g:G) ∈ Y) : p g = (e ⟨q (g:G),hg⟩).1 := by
    apply coreRepresentation_injective
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := E.surjective v
    exact (hpe g w).symm.trans (he g hg w)
  obtain ⟨hJB,a₀,b₀,hB⟩ := SymmetricFive.Paired.thompson_baumann_of_source_model
    T hP U hU hJ q hq hk d c hexchange
  let s := (MulAut.conj a₀) (Equiv.swap (0:Fin 5) 1)
  have hsD : s ∈ (Offenders.D 5).map (MulAut.conj a₀).toMonoidHom :=
    mem_map_of_mem _ (Offenders.pairSwap_mem 0 (by decide))
  have hgim : Y.subtype (e.symm (s,1)) ∈ (elementaryAbelianMaxJ (T : Subgroup G)).map q := by
    rw [hJB,hB]
    exact ⟨(s,1),⟨hsD,one_mem _⟩,rfl⟩
  obtain ⟨g,hgJ,hqg⟩ := hgim
  have hgB := elementaryAbelianMaxJ_le_baumann (T : Subgroup G) hgJ
  have hgR : g ∈ (T : Subgroup G) ⊓ normalizer (L : Set G) := ⟨hgB.1,hBL hgB⟩
  let gn : N := ⟨g,(show (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ N from le_sup_right) hgR⟩
  have hgY : q g ∈ Y := hqg.symm ▸ (e.symm (s,1)).property
  have hpg : p gn = s := by
    have hh := hpcoord gn hgY
    have hz : (⟨q g,hgY⟩:Y) = e.symm (s,1) := Subtype.ext hqg
    change p gn = (e ⟨q g,hgY⟩).1 at hh
    rw [hz,e.apply_symm_apply] at hh
    exact hh
  have hsodd : s ∉ alternatingGroup (Fin 5) := by
    simp [s,Equiv.Perm.mem_alternatingGroup,MulAut.conj_apply]
  have hp : Function.Surjective p := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    intro z _
    have haRange : alternatingGroup (Fin 5) ≤ p.range := hpL.symm ▸ map_le_range p L₀
    by_cases hz : z ∈ alternatingGroup (Fin 5)
    · exact haRange hz
    · have hzi : s⁻¹ ∉ alternatingGroup (Fin 5) := fun h => hsodd (inv_mem_iff.mp h)
      have hzs : z*s⁻¹ ∈ alternatingGroup (Fin 5) :=
        (mul_mem_iff_of_index_two alternatingGroup.index_eq_two).mpr ⟨fun h => (hz h).elim,fun h => (hzi h).elim⟩
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using p.range.mul_mem (haRange hzs) (show s ∈ p.range from ⟨gn,hpg⟩)
  refine ⟨p,hp,hpk,E,hpL,?_,?_⟩
  · intro z v
    obtain ⟨g,rfl⟩ := hp z
    rw [quotient_action_apply]
    exact hpe g v
  · have hBR : baumann (T : Subgroup G) ≤ (T : Subgroup G) ⊓ normalizer (L : Set G) := le_inf inf_le_left hBL
    have hJR : (elementaryAbelianMaxJ (R : Subgroup N)).map N.subtype = elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [←elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective,hR]
      exact elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G) _
        ((elementaryAbelianMaxJ_le_baumann _).trans hBR) inf_le_left
    have hgnJ : gn ∈ elementaryAbelianMaxJ (R : Subgroup N) := by
      obtain ⟨n,hn,heq⟩ := hJR.symm ▸ hgJ
      exact (Subtype.ext heq : n=gn) ▸ hn
    intro hc
    have hpone : p gn = 1 := by
      change gn ∈ p.ker
      rw [hpk]
      exact hc hgnJ
    exact hsodd ((hpg.symm.trans hpone).symm ▸ one_mem _)
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne.PairedFive
