module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.OmegaBound
public import Theory.GroupTheory.ElementaryThompsonFixedIndex
public import Theory.SpecificGroups.SL2.ResidualSylowGeneration

/-!
# Two moving maximum elementary subgroups generate the original group

Maximal elementary order gives the upper fixed-index bound on Ω₁(Z(O₂(H))).
The actual natural moved quotient gives the matching lower bound and forces
the whole Sylow image in SL₂. Over F₂, the proved fixed-index bound and
nontrivial image of order two give the same result. An original residual
conjugator supplies the opposite image. Campbell's genuine Frattini kernel
then upgrades generation in the quotient to O₂(H)AA^g = H.

Source: Campbell, *Pushing up in Finite Groups* (1979), II.4.1, printed p.25,
applied to the original Aschbacher–Smith C.1.17 marking.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H J : Type*} [Group B] [Finite B] [Group H] [Finite H] [Group J]
  {e : B →* H} {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite B] in
theorem maxElementary_image_and_index_of_natural_projection (h : InLocalClass e)
    (d : Campbell.Embedding J H)
    (q : H →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = localKernel e)
    (f : moved e →* Multiplicative (Fin 2 → F)) (hf : Function.Surjective f)
    (he : ∀ g w, (f (movedConjugate e g w)).toAdd = Matrix.mulVec (q g).val (f w).toAdd)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H))
    (hAQ : ¬ A ≤ pCore 2 H) :
    A.map q = (d.sylow : Subgroup H).map q ∧
      (centralizer (A : Set H)).relIndex (omegaOneCenterAmbient (pCore 2 H)) = Nat.card F := by
  let D := A.map q
  let P := d.sylow.mapSurjective hq
  have hcore : pCore 2 H ≤ q.ker := by rw [hk]; exact h.core_le_localKernel
  have hpartial : Campbell.NoPartialComplement (q.ker.map (QuotientGroup.mk' (pCore 2 H))) := by
    rw [hk]; exact h.kernel_noPartialComplement
  have hSK : (d.sylow : Subgroup H) ⊓ q.ker = pCore 2 H := d.sylow_inf_eq_core _ hcore hpartial
  have hAK : q.ker.subgroupOf A = (pCore 2 H).subgroupOf A := by
    ext a
    exact ⟨fun ha => hSK ▸ (show (a : H) ∈ (d.sylow : Subgroup H) ⊓ q.ker from
      ⟨hA.1 a.property,ha⟩),fun ha => hcore ha⟩
  have hcard : (pCore 2 H).relIndex A = Nat.card D := by
    rw [← relIndex_ker A q]
    change ((pCore 2 H).subgroupOf A).index = (q.ker.subgroupOf A).index
    rw [hAK]
  have hD : D ≠ ⊥ := by
    intro hb
    have hAK' : A ≤ q.ker := (map_eq_bot_iff A).mp hb
    exact hAQ ((le_inf hA.1 hAK').trans hSK.le)
  have hpre : (centralizer (A : Set H)).subgroupOf (moved e) ≤
      (Theory.SpecificGroups.SL2.NaturalFixedIndex.fixed D).comap f := by
    intro w hw b hb
    obtain ⟨a,ha,rfl⟩ := hb
    have hc : movedConjugate e a w = w := by
      apply Subtype.ext
      change a * (w : H) * a⁻¹ = w
      have hm : a * (w : H) = (w : H) * a := hw a ha
      rw [hm,mul_inv_cancel_right]
    change Matrix.mulVec (q a).val (f w).toAdd = (f w).toAdd
    simpa only [hc] using (he a w).symm
  have hi : (Theory.SpecificGroups.SL2.NaturalFixedIndex.fixed D).index ≤
      (centralizer (A : Set H)).relIndex (moved e) := by
    rw [← (Theory.SpecificGroups.SL2.NaturalFixedIndex.fixed D).index_comap_of_surjective hf]
    exact index_antitone hpre
  have hlo : Nat.card F ≤ (centralizer (A : Set H)).relIndex
      (omegaOneCenterAmbient (pCore 2 H)) :=
    (Theory.SpecificGroups.SL2.NaturalFixedIndex.field_card_le_fixed_index hD).trans
      (hi.trans (relIndex_le_of_le_right h.moved_le_coreOmegaCenter index_ne_zero_of_finite))
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (pCore 2 H)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  have hu := maxElementary_fixedIndex_le_relIndex (d.sylow : Subgroup H) (pCore 2 H) A
    (omegaOneCenterAmbient (pCore 2 H)) (pCore_isPGroup.le_sylow_of_normal d.sylow)
    (fun x hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)
    (fun x hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2) hA
  have hupper : (centralizer (A : Set H)).relIndex (omegaOneCenterAmbient (pCore 2 H)) ≤ Nat.card D :=
    (hu.1.trans hu.2).trans_eq hcard
  have hPcard : Nat.card P = Nat.card F := Nat.card_congr
    (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 P).toEquiv.symm
  have hDle : D ≤ (P : Subgroup SL(2,F)) := map_mono hA.1
  have hc : Nat.card D ≤ Nat.card F := (card_le_of_le hDle).trans_eq hPcard
  refine ⟨eq_of_le_of_card_ge hDle ?_,le_antisymm (hupper.trans hc) hlo⟩
  change Nat.card P ≤ Nat.card D
  rw [hPcard]
  exact hlo.trans hupper
end CFSG.Quasithin.ChapterC.GlaubermanNiles
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open Subgroup
variable {B H : Type*} [Group B] [Group H] [Finite H] {e : B →* H}

theorem InLocalClass.supplement_eq_top_of_core_le (h : InLocalClass e) (U : Subgroup H)
    (hQU : pCore 2 H ≤ U) (hs : U ⊔ localKernel e = ⊤) : U = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hq := QuotientGroup.mk'_surjective (pCore 2 H)
  have hs' : (localKernel e).map q ⊔ U.map q = ⊤ := by
    rw [← Subgroup.map_sup,sup_comm,hs,Subgroup.map_top_of_surjective q hq]
  have hu := h.kernel_noPartialComplement (U.map q) hs'
  have hu' := congrArg (Subgroup.comap q) hu
  rw [comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hQU,comap_top] at hu'
  exact hu'

end CFSG.Quasithin.ChapterC.GlaubermanNiles

namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups IsMulCommutative
variable {B H J : Type*} [Group B] [Finite B] [Group H] [Finite H] [Group J]
  {e : B →* H} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem InLocalClass.exists_two_maxElementary_generators_large (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F) (hF : 2 < Nat.card F)
    (d : Campbell.Embedding J H) (hS : (d.sylow : Subgroup H) = e.range) :
    ∃ (A : Subgroup H) (g : H),
      A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H) ∧
      g ∈ pResidual 2 H ∧
      pCore 2 H ⊔ A ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤ ∧
      (centralizer (A : Set H)).relIndex (omegaOneCenterAmbient (pCore 2 H)) = Nat.card F := by
  obtain ⟨q,f,hq,hk,hf,he⟩ := h.exists_large_campbell_projection hB m hF
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H), ¬ A ≤ pCore 2 H := by
    by_contra! hn
    have hJQ : elementaryAbelianMaxJ (d.sylow : Subgroup H) ≤ pCore 2 H := sSup_le hn
    apply h.thompson_moves_moved hB d.sylow hS.symm
    exact hJQ.trans (Subgroup.le_centralizer_iff.mp
      (h.moved_le_coreOmegaCenter.trans (fun x hx =>
        ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2)))
  obtain ⟨A,hA,hAQ⟩ := hex
  obtain ⟨hmap,hidx⟩ := maxElementary_image_and_index_of_natural_projection h d q hq hk f hf he A hA hAQ
  obtain ⟨g,hg,hgen⟩ := Matrix.SpecialLinearGroup.exists_residual_conjugate_sylow_image_sup_eq_top d.sylow q hq
  let c := (MulAut.conj g).toMonoidHom
  have hconj (U : Subgroup H) : (U.map c).map q = (U.map q).map (MulAut.conj (q g)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change q (g*x*g⁻¹) = q g*q x*(q g)⁻¹
    simp only [map_mul,map_inv]
  have hAg : (A.map c).map q = ((d.sylow : Subgroup H).map c).map q := by rw [hconj,hmap,hconj]
  let U := pCore 2 H ⊔ A ⊔ A.map c
  have hmapU : U.map q = ⊤ := by
    apply top_unique
    rw [← hgen,← hmap,← hAg]
    have hAU : A ≤ U := (show A ≤ pCore 2 H ⊔ A from le_sup_right).trans le_sup_left
    have hAgU : A.map c ≤ U := le_sup_right
    exact sup_le (map_mono hAU) (map_mono hAgU)
  have hU : U = ⊤ := by
    apply InLocalClass.supplement_eq_top_of_core_le h U ((show pCore 2 H ≤ pCore 2 H ⊔ A from le_sup_left).trans le_sup_left)
    have hu := congrArg (Subgroup.comap q) hmapU
    simpa only [comap_map_eq,hk,comap_top] using hu
  exact ⟨A,g,hA,hg,hU,hidx⟩

end CFSG.Quasithin.ChapterC.GlaubermanNiles

namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups IsMulCommutative
variable {B H J : Type*} [Group B] [Finite B] [Group H] [Finite H] [Group J]
  {e : B →* H} {F : Type} [Field F] [Finite F] [CharP F 2]

theorem maxElementary_image_and_index_small (h : InLocalClass e) (hB : IsBaumannFixed B)
    (hF : Nat.card F = 2) (d : Campbell.Embedding J H)
    (q : H →* SL(2,F)) (hq : Function.Surjective q) (hk : q.ker = localKernel e)
    (A : Subgroup H) (hA : A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H))
    (hAQ : ¬ A ≤ pCore 2 H) :
    A.map q = (d.sylow : Subgroup H).map q ∧
      (centralizer (A : Set H)).relIndex (omegaOneCenterAmbient (pCore 2 H)) = Nat.card F := by
  let D := A.map q
  let P := d.sylow.mapSurjective hq
  have hcore : pCore 2 H ≤ q.ker := by rw [hk]; exact h.core_le_localKernel
  have hpartial : Campbell.NoPartialComplement (q.ker.map (QuotientGroup.mk' (pCore 2 H))) := by
    rw [hk]; exact h.kernel_noPartialComplement
  have hSK : (d.sylow : Subgroup H) ⊓ q.ker = pCore 2 H := d.sylow_inf_eq_core _ hcore hpartial
  have hAK : q.ker.subgroupOf A = (pCore 2 H).subgroupOf A := by
    ext a
    exact ⟨fun ha => hSK ▸ (show (a : H) ∈ (d.sylow : Subgroup H) ⊓ q.ker from
      ⟨hA.1 a.property,ha⟩),fun ha => hcore ha⟩
  have hcard : (pCore 2 H).relIndex A = Nat.card D := by
    rw [← relIndex_ker A q]
    change ((pCore 2 H).subgroupOf A).index = (q.ker.subgroupOf A).index
    rw [hAK]
  have hD : D ≠ ⊥ := by
    intro hb
    have hAK' : A ≤ q.ker := (map_eq_bot_iff A).mp hb
    exact hAQ ((le_inf hA.1 hAK').trans hSK.le)
  have hPcard : Nat.card P = Nat.card F := Nat.card_congr
    (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 P).toEquiv.symm
  have hDle : D ≤ (P : Subgroup SL(2,F)) := map_mono hA.1
  have hc : Nat.card D = 2 := le_antisymm
    ((card_le_of_le hDle).trans_eq (hPcard.trans hF)) ((one_lt_card_iff_ne_bot D).mpr hD)
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (pCore 2 H)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  have hu := maxElementary_fixedIndex_le_relIndex (d.sylow : Subgroup H) (pCore 2 H) A
    (omegaOneCenterAmbient (pCore 2 H)) (pCore_isPGroup.le_sylow_of_normal d.sylow)
    (fun x hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1)
    (fun x hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2) hA
  have hb := h.omegaFixedIndexBound hB d A hA hAQ
  refine ⟨eq_of_le_of_card_ge hDle ?_,?_⟩
  · change Nat.card P ≤ Nat.card D
    rw [hPcard,hF,hc]
  · exact (le_antisymm (hu.1.trans hu.2) hb).trans (hcard.trans (hc.trans hF.symm))

theorem InLocalClass.exists_two_maxElementary_generators (h : InLocalClass e) (hB : IsBaumannFixed B)
    (m : NaturalModel e F)
    (d : Campbell.Embedding J H) (hS : (d.sylow : Subgroup H) = e.range) :
    ∃ (A : Subgroup H) (g : H),
      A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H) ∧
      g ∈ pResidual 2 H ∧
      pCore 2 H ⊔ A ⊔ A.map (MulAut.conj g).toMonoidHom = ⊤ ∧
      (centralizer (A : Set H)).relIndex (omegaOneCenterAmbient (pCore 2 H)) = Nat.card F := by
  have ht : 2 ≤ Nat.card F := Finite.one_lt_card
  rcases ht.eq_or_lt with hF | hF
  swap
  · exact InLocalClass.exists_two_maxElementary_generators_large h hB m hF d hS
  obtain ⟨a⟩ := h.localStar_equiv_psl hB m
  let E := a.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm
  let q := E.toMonoidHom.comp (QuotientGroup.mk' (localKernel e))
  have hq : Function.Surjective q := E.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = localKernel e := by
    ext g
    change E (QuotientGroup.mk' (localKernel e) g) = 1 ↔ _
    rw [E.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff g
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups (d.sylow : Subgroup H), ¬ A ≤ pCore 2 H := by
    by_contra! hn
    have hJQ : elementaryAbelianMaxJ (d.sylow : Subgroup H) ≤ pCore 2 H := sSup_le hn
    apply h.thompson_moves_moved hB d.sylow hS.symm
    exact hJQ.trans (Subgroup.le_centralizer_iff.mp
      (h.moved_le_coreOmegaCenter.trans (fun x hx =>
        ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2)))
  obtain ⟨A,hA,hAQ⟩ := hex
  obtain ⟨hmap,hidx⟩ := maxElementary_image_and_index_small h hB hF.symm d q hq hk A hA hAQ
  obtain ⟨g,hg,hgen⟩ := Matrix.SpecialLinearGroup.exists_residual_conjugate_sylow_image_sup_eq_top d.sylow q hq
  let c := (MulAut.conj g).toMonoidHom
  have hconj (U : Subgroup H) : (U.map c).map q = (U.map q).map (MulAut.conj (q g)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change q (g*x*g⁻¹) = q g*q x*(q g)⁻¹
    simp only [map_mul,map_inv]
  have hAg : (A.map c).map q = ((d.sylow : Subgroup H).map c).map q := by rw [hconj,hmap,hconj]
  let U := pCore 2 H ⊔ A ⊔ A.map c
  have hmapU : U.map q = ⊤ := by
    apply top_unique
    rw [← hgen,← hmap,← hAg]
    have hAU : A ≤ U := (show A ≤ pCore 2 H ⊔ A from le_sup_right).trans le_sup_left
    have hAgU : A.map c ≤ U := le_sup_right
    exact sup_le (map_mono hAU) (map_mono hAgU)
  have hU : U = ⊤ := by
    apply InLocalClass.supplement_eq_top_of_core_le h U ((show pCore 2 H ≤ pCore 2 H ⊔ A from le_sup_left).trans le_sup_left)
    have hu := congrArg (Subgroup.comap q) hmapU
    simpa only [comap_map_eq,hk,comap_top] using hu
  exact ⟨A,g,hA,hg,hU,hidx⟩

end CFSG.Quasithin.ChapterC.GlaubermanNiles
