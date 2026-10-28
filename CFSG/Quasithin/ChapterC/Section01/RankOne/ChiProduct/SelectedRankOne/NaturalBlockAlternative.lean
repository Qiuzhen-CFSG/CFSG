module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedBlockSteps
/-!
# Retaining the natural type in a selected component block

Equivalences transport the full natural conjugation model, retaining its
field exponent. In the C.1.18 block alternative the only other type is the
alternating-three block, which is solvable. An actual C-component excludes
that case, so its literal residual equivalence recovers a natural block of
some exponent, rather than discarding the type after proving shortness.

Source: Aschbacher–Smith C.1.18 and10.2.3(4), pp.126–127 and746–747.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC
variable {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
theorem IsL2EvenBlock.of_equiv {n : ℕ} (e : A ≃* B) (h : IsL2EvenBlock A n) :
    IsL2EvenBlock B n := by
  obtain ⟨hn,hs,F,iF,iFin,hF,hq,ρ,⟨m⟩,hρ⟩ := h
  have hk : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
  have hp : IsPGroup 2 e.toMonoidHom.ker := by rw [hk]; exact IsPGroup.of_bot
  obtain ⟨m'⟩ := BlockModuleModel.exists_of_central_two_quotient
    e.toMonoidHom e.surjective hs.twoPerfect hp (hk ▸ bot_le) ρ m
  refine ⟨hn,RankOne.Solvable.isShort_of_equiv e hs,F,iF,iFin,hF,?_,ρ,⟨m'⟩,hρ⟩
  exact hq.of_mulEquiv
    (QuotientGroup.congr (pCore 2 A) (pCore 2 B) e (pCore_map_iso 2 e)).symm

namespace RankOne.ChiProduct.SelectedRankOne
open ChapterB GlaubermanNiles
variable {G : Type*} [Group G] [Finite G]
theorem selected_component_natural_of_blockAlternative
    (T : Sylow 2 G) (K : Subgroup G) (hK : K.IsCComponent) (hp : IsPPerfect 2 K)
    (hBK : baumann (T : Subgroup G) ≤ normalizer (K : Set G))
    (hb : BlockAlternative (K ⊔ baumann (T : Subgroup G) : Subgroup G)) :
    IsBlock K ∧ ∃ n, IsL2EvenBlock K n := by
  let N := K ⊔ baumann (T : Subgroup G)
  let e := ((pResidual 2 N).equivMapOfInjective N.subtype N.subtype_injective).trans
    (MulEquiv.subgroupCongr (selected_component_residual_map T K hp hBK))
  refine ⟨(selected_component_chi_of_blockAlternative T K hK hp hBK hb).1,?_⟩
  rcases hb.2 with ⟨n,hn⟩ | ha
  · exact ⟨n,hn.of_equiv e⟩
  · have haK : IsAlternatingBlock K 3 := RankOne.Solvable.isAlternatingBlock_of_equiv e ha
    obtain ⟨f⟩ := haK.2.2.quotient_iso
    let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
    let : Group.IsSolvable (K ⧸ pCore 2 K) := Group.isSolvable_of_surjective
      (f := f.symm.toMonoidHom) f.symm.surjective
    let : Group.IsNilpotent (pCore 2 K) := pCore_isPGroup.isNilpotent
    have hs : Group.IsSolvable K := (Group.isSolvable_iff_subgroup_quotient (pCore 2 K)).mpr
      ⟨inferInstance,inferInstance⟩
    exact (hK.not_isSolvable hs).elim
end RankOne.ChiProduct.SelectedRankOne
end CFSG.Quasithin.ChapterC
