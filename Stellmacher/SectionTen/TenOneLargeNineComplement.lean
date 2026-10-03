module
public import Stellmacher.SectionTen.TenOneLargeTerminalStructure
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# An actual complement for the terminal nine alternative

If the literal image of the terminal residual in P/O₂(P) has model
C₃ × C₃, the residual contains an actual odd complement with that model.
Its join with the residual two-core is the whole residual and their
intersection is trivial. No source-(18) module data are assumed.

Restrict the original P/O₂(P) projection to E. The residual-core
intersection identity identifies its kernel with O₂(E). The first
isomorphism theorem therefore gives the same quotient model for E/O₂(E).
Schur–Zassenhaus supplies a complement to this normal two-core. Its
quotient equivalence gives the model, and mapping through E's subtype
retains the actual subgroup of the ambient group.

Source: Stellmacher (10.1), printed p.64, the complement chosen between
(18) and (19). This module only produces that complement; the exclusion
of the nine alternative uses the later fixed-factor argument.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u

public theorem ten_one_large_nine_complement
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (hmodel : Nonempty
      ((((EAt ctx.Γ ctx.criticalPath.a').subgroupOf (GAt ctx.Γ ctx.criticalPath.a')).map
        (QuotientGroup.mk' (pCore 2 (GAt ctx.Γ ctx.criticalPath.a')))) ≃* (C3 × C3))) :
    ∃ D : Subgroup G, D ≤ EAt ctx.Γ ctx.criticalPath.a' ∧
      EAt ctx.Γ ctx.criticalPath.a' = twoCoreIn (EAt ctx.Γ ctx.criticalPath.a') ⊔ D ∧
      Disjoint (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')) D ∧
      Nonempty (D ≃* (C3 × C3)) := by
  classical
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  let U := twoCoreIn E
  have hE : E=twoResidualIn P := ctx.Γ.twoResidualAt_def _
  have hEP : E≤P := hE ▸ twoResidualIn_le P
  let q := QuotientGroup.mk' (pCore 2 P)
  let f : E →* P ⧸ pCore 2 P := q.comp (Subgroup.inclusion hEP)
  let Ebar := (E.subgroupOf P).map q
  have hrange : f.range=Ebar := by
    ext x
    constructor
    · rintro ⟨e,rfl⟩
      exact ⟨Subgroup.inclusion hEP e,e.property,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      exact ⟨⟨p,hp⟩,rfl⟩
  have hU : U=E⊓twoCoreIn P := by
    change twoCoreIn E=E⊓twoCoreIn P
    rw [hE,residual_core_eq_inter_core]
  have hker : f.ker=pCore 2 E := by
    ext e
    constructor
    · intro he
      have heQ : (e:G)∈twoCoreIn P := by
        refine ⟨Subgroup.inclusion hEP e,?_,rfl⟩
        exact (QuotientGroup.eq_one_iff _).mp he
      have heU : (e:G)∈U := hU.symm ▸ ⟨e.property,heQ⟩
      obtain ⟨u,hu,heu⟩ := heU
      exact (show u=e from Subtype.ext heu) ▸ hu
    · intro he
      have heU : (e:G)∈U := Subgroup.mem_map_of_mem E.subtype he
      have heQ : (e:G)∈twoCoreIn P := (hU ▸ heU).2
      obtain ⟨p,hp,hpe⟩ := heQ
      have hp' : p=Subgroup.inclusion hEP e := Subtype.ext hpe
      exact (QuotientGroup.eq_one_iff _).mpr (hp' ▸ hp)
  let ebar : (E ⧸ pCore 2 E) ≃* Ebar :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))
  let model : (E ⧸ pCore 2 E) ≃* (C3×C3) := ebar.trans hmodel.some
  have hthree : Nat.card C3=3 :=
    (Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 3) ≃ ZMod 3)).trans (by norm_num)
  have hquot : Nat.card (E ⧸ pCore 2 E)=9 := by
    rw [Nat.card_congr model.toEquiv,Nat.card_prod,hthree]
  have hindex : (pCore 2 E).index=9 := (Subgroup.index_eq_card _).trans hquot
  have hcop : Nat.Coprime (Nat.card (pCore 2 E)) (pCore 2 E).index := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p:=2) (G:=E)).exists_card_eq
    rw [hn,hindex]
    exact (show Nat.Coprime 2 9 by decide).pow_left n
  obtain ⟨K,hcomp⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  let D := K.map E.subtype
  let eD : D ≃* (C3×C3) :=
    (K.equivMapOfInjective E.subtype E.subtype_injective).symm.trans
      (hcomp.symm.QuotientMulEquiv.symm.trans model)
  refine ⟨D,Subgroup.map_subtype_le K,?_,?_,⟨eD⟩⟩
  · have hh := congrArg (Subgroup.map E.subtype) hcomp.sup_eq_top
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,Subgroup.range_subtype] at hh
    exact hh.symm
  · rw [Subgroup.disjoint_def]
    intro x hxU hxD
    obtain ⟨u,hu,rfl⟩ := hxU
    obtain ⟨d,hd,hdu⟩ := hxD
    have hdu' : d=u := Subtype.ext hdu
    have hu1 : u=1 := Subgroup.disjoint_def.mp hcomp.disjoint hu (hdu' ▸ hd)
    exact congrArg Subtype.val hu1

end Stellmacher.SectionTen
