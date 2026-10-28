module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Solvable.Star
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Solvable.Geometry
public import Theory.GroupTheory.TwoConjugateSylowImage.Preimage
public import Theory.GroupTheory.NormalCoreTwoClosedTransport
public import Theory.GroupTheory.SylowQuotientPreimage
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# The solvable E.2.9 witness in the original group

Lift the genuine star-quotient witness through the original normal core.
Minimal-pair rechoice makes its conjugator internal without changing its
star image. The pair is subnormal in that image’s full preimage, so the
prescribed Sylow intersection remains Sylow. Normal-core pullback preserves
the exact dihedral quotient. Finally, centralization of the original normal
core modulo the two-core makes the lifted normal core two-closed.

No classification or desired-witness premise is used. The source SQTK
hypothesis is unnecessary in this solvable branch.
Source: Aschbacher–Smith, E.2.7–9, printed pp.220–222.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Witnesses.Solvable
variable {H : Type*} [Group H] [Finite H]

structure Witness (T : Sylow 2 H) (M V : Subgroup H) where
  subgroup : Subgroup H
  le : V ≤ subgroup
  conjugator : subgroup
  generate : V.subgroupOf subgroup ⊔
    (V.subgroupOf subgroup).map (MulAut.conj conjugator).toMonoidHom = ⊤
  sylow : Sylow 2 subgroup
  sylow_eq : (sylow : Subgroup subgroup).map subgroup.subtype = (T : Subgroup H) ⊓ subgroup
  core_two_closed : ∃S : Sylow 2 (M.subgroupOf subgroup).normalCore,
    (S : Subgroup (M.subgroupOf subgroup).normalCore).Normal
  dihedral : ∃p a:ℕ,p.Prime ∧ p≠2 ∧ 0<a ∧
    Nonempty ((subgroup ⧸ (M.subgroupOf subgroup).normalCore) ≃* DihedralGroup (p^a))

omit [Finite H] in
private theorem pair_map {G : Type*} [Group G] (f : H →* G) (V : Subgroup H) (g:H) :
    (V ⊔ V.map (MulAut.conj g).toMonoidHom).map f =
      V.map f ⊔ (V.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_sup,map_map,map_map]
  congr 2
  ext x
  simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,map_mul,map_inv]

private theorem lift_witness (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (V : Subgroup H)
    [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (w : CoreFreeWitness
      ((ChapterB.minimalParabolicMax T hP).map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP)))
      (V.map (QuotientGroup.mk' (ChapterB.minimalParabolicCore T hP))) p) :
    Nonempty (Witness T (ChapterB.minimalParabolicMax T hP) V) := by
  let M := ChapterB.minimalParabolicMax T hP
  let J := ChapterB.minimalParabolicCore T hP
  let Q := pCore 2 H
  let q := QuotientGroup.mk' J
  have hq := QuotientGroup.mk'_surjective J
  let W := V.map q
  let B := M.map q
  have hJM : J ≤ M := normalCore_le M
  have hQJ : Q ≤ J := ChapterB.minimalParabolicTwoCore_le_core T hP
  have hMpre : B.comap q = M := by
    rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hJM]
  have hgenstar : W ⊔ W.map (MulAut.conj (w.conjugator : H ⧸ J)).toMonoidHom = w.subgroup := by
    have hh := congrArg (fun A : Subgroup w.subgroup => A.map w.subgroup.subtype) w.generate
    rw [pair_map,map_subgroupOf_eq_of_le w.le,← MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hex : ∃g:H,q g ∈ w.subgroup ∧
      (V ⊔ V.map (MulAut.conj g).toMonoidHom).map q = w.subgroup := by
    obtain ⟨g,hg⟩ := hq (w.conjugator : H ⧸ J)
    refine ⟨g,hg.symm ▸ w.conjugator.property,?_⟩
    rw [pair_map,hg]
    exact hgenstar
  obtain ⟨g,hg,hmap⟩ := exists_internal_conjugator_in_preimage q V
    (IsElementaryAbelian.isPGroup 2 V) w.subgroup w.sylow w.sylow_eq hex
  let I := V ⊔ V.map (MulAut.conj g).toMonoidHom
  have hVI : V ≤ I := le_sup_left
  let gg : I := ⟨g,hg⟩
  have hgen : V.subgroupOf I ⊔ (V.subgroupOf I).map (MulAut.conj gg).toMonoidHom = ⊤ := by
    apply map_injective I.subtype_injective
    rw [pair_map,map_subgroupOf_eq_of_le hVI,← MonoidHom.range_eq_map,range_subtype]
    rfl
  have hIL : I ≤ w.subgroup.comap q := map_le_iff_le_comap.mp hmap.le
  let L := w.subgroup.comap q
  have hL : L = I ⊔ J := by
    change w.subgroup.comap q = I ⊔ J
    rw [← hmap,comap_map_eq,QuotientGroup.ker_mk']
  have hSylowStar : (w.sylow : Subgroup w.subgroup) =
      ((T : Subgroup H).map q).subgroupOf w.subgroup := by
    apply Eq.symm
    apply w.sylow.is_maximal' (T.isPGroup'.map q).comap_subtype
    apply map_le_iff_le_comap.mp
    rw [w.sylow_eq]
    exact map_mono hVT
  obtain ⟨S0,hS0⟩ := T.exists_subgroupOf_eq_comap q w.subgroup w.sylow hSylowStar
  have hsn : (I.subgroupOf L).IsSubnormal := by
    rw [hL]
    exact pair_subnormal_in_core_join T hP V
      ((normal_subgroupOf_iff_le_normalizer hVT).mp hn) hVcore g
  obtain ⟨R,hR⟩ := S0.exists_subgroupOf_eq_of_subnormal (I.subgroupOf L) hsn
  let e := subgroupOfEquivOfLe hIL
  let S := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS : (S : Subgroup I) = (T : Subgroup H).subgroupOf I := by
    change (R : Subgroup _).map e.toMonoidHom = _
    rw [hR,hS0]
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨⟨x,hIL x.property⟩,x.property⟩,hx,rfl⟩
  let f : I →* w.subgroup := (q.comp I.subtype).codRestrict w.subgroup (fun x => hIL x.property)
  have hf : Function.Surjective f := by
    intro y
    have hy : (y : H ⧸ J) ∈ I.map q := hmap.ge y.property
    obtain ⟨x,hx,he⟩ := hy
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  let A := M.subgroupOf I
  let Astar := B.subgroupOf w.subgroup
  have hA : Astar.comap f = A := by
    ext x
    change q x ∈ B ↔ (x:H) ∈ M
    exact SetLike.ext_iff.mp hMpre (x : H)
  have hcore : A.normalCore = Astar.normalCore.comap f := by
    rw [← hA,normalCore_comap_of_surjective f hf]
  let C := A.normalCore
  let Cstar := Astar.normalCore
  let r : C →* Cstar := (f.comp C.subtype).codRestrict Cstar (fun x => hcore.le x.property)
  have hr : Function.Surjective r := by
    intro y
    obtain ⟨x,hx⟩ := hf y
    have hxC : x ∈ C := hcore.ge (show f x ∈ Cstar from hx.symm ▸ y.property)
    exact ⟨⟨x,hxC⟩,Subtype.ext hx⟩
  have hCstar : IsPGroup 2 Cstar := by
    have hAE : IsElementaryAbelian 2 Astar := by
      change IsElementaryAbelian 2 (B.subgroupOf w.subgroup)
      rw [show B.subgroupOf w.subgroup = W.subgroupOf w.subgroup from w.maximal_eq]
      let : IsElementaryAbelian 2 W := IsElementaryAbelian.map q
      exact IsElementaryAbelian.subgroupOf w.le
    let := hAE
    exact (IsElementaryAbelian.isPGroup 2 Astar).to_le Astar.normalCore_le
  let N := (Q.subgroupOf I).subgroupOf C
  have hN : IsPGroup 2 N := pCore_isPGroup.comap_subtype.comap_subtype
  have hNker : N ≤ r.ker := by
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff ((x : I) : H)).mpr (hQJ hx)
  have hcomm : ⁅r.ker,⊤⁆ ≤ N := by
    apply commutator_le.mpr
    intro x hx y _
    have hxJ : ((x : I) : H) ∈ J := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg (fun z : Cstar => ((z : w.subgroup) : H ⧸ J)) hx
    let qQ := QuotientGroup.mk' Q
    have hc := pair_centralizes_core_modulo_twoCore T hP V hVcore g
      (mem_map_of_mem qQ (y : I).property)
    have he := hc (qQ ((x:I):H)) (mem_map_of_mem qQ hxJ)
    change (((x:I):H)*((y:I):H)*((x:I):H)⁻¹*((y:I):H)⁻¹) ∈ Q
    apply (QuotientGroup.eq_one_iff _).mp
    change qQ _ = 1
    rw [map_mul,map_mul,map_mul,map_inv,map_inv]
    exact commutatorElement_eq_one_iff_mul_comm.mpr he
  have hclosed : ∃P:Sylow 2 C,(P:Subgroup C).Normal :=
    normalSylowTwo_of_odd_pCore_index (odd_pCore_index_of_central_kernel_mod_two r hr hCstar N hN hNker hcomm)
  have hquot : Nonempty ((I ⧸ A.normalCore) ≃* DihedralGroup (p^w.exponent)) := by
    obtain ⟨d⟩ := w.dihedral
    exact ⟨(QuotientGroup.equivOfSurjectiveComap f hf A.normalCore Astar.normalCore hcore.symm).trans d⟩
  refine ⟨⟨I,hVI,gg,hgen,S,?_,hclosed,p,w.exponent,hp,hp2,w.positive,hquot⟩⟩
  rw [hS,subgroupOf_map_subtype]

/-- The solvable E.2.9 member, with the original Sylow and maximal subgroup. -/
theorem solvable_witness (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : Group.IsSolvable H)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hn : (V.subgroupOf (T : Subgroup H)).Normal)
    (hVcore : V ≤ (ChapterB.minimalParabolicMax T hP).pCoreIn 2)
    (hout : ¬ V ≤ ChapterB.minimalParabolicCore T hP) :
    Nonempty (Witness T (ChapterB.minimalParabolicMax T hP) V) := by
  obtain ⟨p,hp,hp2,⟨w⟩⟩ := solvable_star_witness T hP hs V hVT hn hout
  exact lift_witness T hP V hVT hn hVcore hp hp2 w
end CFSG.Quasithin.ChapterE.Witnesses.Solvable
end
