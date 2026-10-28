module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.SL2NaturalOffenders.Ratios

/-!
# Sylow-fixed subgroups in an even rank-one block

Project an actual subgroup of U(L) through U(L)/C_U(L). Disjointness from the
center makes the projection injective, and centralization of a Sylow two-group
places its image in the natural Sylow fixed line. Thus its order is at most
the field order. The proof uses the defining literal quotient and module maps.

Source: Aschbacher–Smith, C.1.12 and the L₂(4) contradiction in Lemma13.3.12,
printed pp.124 and890. No chief-factor count is assumed.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC

private theorem sylow_fixed_card {F : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F]
    (P : Sylow 2 (SL2NaturalOffenders.NoStrong.Actor F)) :
    Nat.card (fixedSpace (SL2NaturalOffenders.NoStrong.natural (F:=F)) (P:Subgroup _))=Nat.card F := by
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) F).injective 2
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SL2NaturalOffenders.NoStrong.Actor F)
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2) P
  have he : (P:Subgroup _)=(Matrix.SpecialLinearGroup.upperUnipotent F).map (MulAut.conj g).toMonoidHom := by
    rw [←hg]
    rfl
  rw [he,← Nat.card_congr (fixedSpaceConjEquiv (SL2NaturalOffenders.NoStrong.natural (F:=F))
    (Matrix.SpecialLinearGroup.upperUnipotent F) g).toEquiv]
  have hc := Module.natCard_eq_pow_finrank (K:=ZMod 2)
    (V:=fixedSpace (SL2NaturalOffenders.NoStrong.natural (F:=F))
      (Matrix.SpecialLinearGroup.upperUnipotent F))
  rw [SL2NaturalOffenders.Ratios.upper_fixed_finrank] at hc
  exact hc.trans (Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=F)).symm

theorem IsL2EvenBlock.card_le_of_sylow_fixed_disjoint_center
    {L : Type*} [Group L] [Finite L] {n : ℕ} (hL : IsL2EvenBlock L n)
    (P : Sylow 2 L) (E : Subgroup L) (hE : E≤blockU L)
    (hEP : E≤centralizer (P:Set L)) (hEZ : Disjoint E (center L)) : Nat.card E≤2^n := by
  obtain ⟨hn,_,F,_,_,hF,_,rho,⟨model⟩,hmodel⟩ := hL
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p:=2) (f:=n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let q : L→*SL2NaturalOffenders.NoStrong.Actor F :=
    model.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := model.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  let R : Sylow 2 (SL2NaturalOffenders.NoStrong.Actor F) := P.mapSurjective hq
  let f : E→*Multiplicative (Fin 2→F) := model.moduleIso.toMonoidHom.comp
    ((QuotientGroup.mk' (blockFixed L)).comp (Subgroup.inclusion hE))
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_antisymm _ bot_le
    intro e he
    change f e=1 at he
    have hh : QuotientGroup.mk' (blockFixed L) (Subgroup.inclusion hE e)=1 :=
      model.moduleIso.injective (by change f e=model.moduleIso 1;simpa only [map_one] using he)
    have hm : Subgroup.inclusion hE e∈blockFixed L := (QuotientGroup.eq_one_iff _).mp hh
    have hz : (e:L)∈center L := hm
    have hb : (e:L)∈E⊓center L := ⟨e.property,hz⟩
    rw [hEZ.eq_bot] at hb
    exact Subtype.ext (mem_bot.mp hb)
  let j : E→fixedSpace (SL2NaturalOffenders.NoStrong.natural (F:=F)) (R:Subgroup _) :=
    fun e => ⟨(f e).toAdd,by
      intro a
      obtain ⟨l,hl,he⟩ := a.property
      change q l=(a:SL2NaturalOffenders.NoStrong.Actor F) at he
      change SL2NaturalOffenders.NoStrong.natural (a : SL2NaturalOffenders.NoStrong.Actor F) (f e).toAdd=(f e).toAdd
      rw [←he]
      have hc : blockConjugate L l (Subgroup.inclusion hE e)=Subgroup.inclusion hE e := by
        apply Subtype.ext
        change l*(e:L)*l⁻¹=(e:L)
        rw [(mem_centralizer_iff.mp (hEP e.property)) l hl,mul_inv_cancel_right]
      have hh := model.intertwining l (Subgroup.inclusion hE e)
      rw [hc] at hh
      have heq := congrArg Multiplicative.toAdd hh
      rw [hmodel] at heq
      exact heq.symm⟩
  have hj : Function.Injective j := by
    intro e d hed
    apply hf
    exact Multiplicative.toAdd.injective (congrArg Subtype.val hed)
  calc
    Nat.card E≤Nat.card (fixedSpace (SL2NaturalOffenders.NoStrong.natural (F:=F)) (R:Subgroup _)) :=
      Nat.card_le_card_of_injective j hj
    _=Nat.card F := sylow_fixed_card R
    _=2^n := hF

end CFSG.Quasithin.ChapterC
