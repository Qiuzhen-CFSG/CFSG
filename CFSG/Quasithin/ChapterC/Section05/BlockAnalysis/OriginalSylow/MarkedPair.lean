module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.RankOneSetup.Source

/-!
# The original rank-one pair retains its specified modules

Transport the selected natural or A₃ block along the actual conjugacy of the
C.5.3 orbit, retaining the natural field exponent and representation. The
source C.5.4 producer then constructs both markings used in the original
C.5.12 terminal, rather than assuming an independent second setup.

Source: Aschbacher–Smith C.5.3–4 and C.5.8–12, pp.154–155,160–163.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
variable {H M K R T : Subgroup G}

private theorem natural_equiv {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B]
    (e : A ≃* B) {n : ℕ} (h : IsL2EvenBlock A n) : IsL2EvenBlock B n := by
  obtain ⟨hn,hs,F,hF,hfin,hcard,hq,hm⟩ := h
  refine ⟨hn,ChapterC.RankOne.Solvable.isShort_of_equiv e hs,F,hF,hfin,hcard,?_,?_⟩
  · exact hq.of_mulEquiv
      (QuotientGroup.congr (pCore 2 A) (pCore 2 B) e (pCore_map_iso 2 e)).symm
  · obtain ⟨ρ,⟨m⟩,hρ⟩ := hm
    have hk : e.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e.injective
    have hp : IsPGroup 2 e.toMonoidHom.ker := by rw [hk]; exact IsPGroup.of_bot
    obtain ⟨m'⟩ := BlockModuleModel.exists_of_central_two_quotient e.toMonoidHom
      e.surjective hs.twoPerfect hp (hk ▸ bot_le) ρ m
    exact ⟨ρ,⟨m'⟩,hρ⟩

/-- Conjugacy of the original blocks preserves the exact natural/A₃
alternative, including the field exponent and the specified module. -/
theorem OriginalHypotheses.rankOne_type_conjugate
    (d : OriginalHypotheses H M K R T)
    (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (i j : Fin b.size)
    (hi : (∃ n, IsL2EvenBlock ((b.block i).map H.subtype) n) ∨
      IsAlternatingBlock ((b.block i).map H.subtype) 3) :
    (∃ n, IsL2EvenBlock ((b.block j).map H.subtype) n) ∨
      IsAlternatingBlock ((b.block j).map H.subtype) 3 := by
  obtain ⟨t,_,ht⟩ := b.transitive i j
  let e := (equivMapOfInjective (b.block i) H.subtype H.subtype_injective).symm.trans
    (((MulAut.conj t⁻¹).subgroupMap (b.block i)).trans
      ((MulEquiv.subgroupCongr ht.symm).trans
        (equivMapOfInjective (b.block j) H.subtype H.subtype_injective)))
  rcases hi with ⟨n,hn⟩ | ha
  · exact Or.inl ⟨n,natural_equiv e hn⟩
  · exact Or.inr (ChapterC.RankOne.Solvable.isAlternatingBlock_of_equiv e ha)

/-- Both source markings for an actual conjugate pair are constructed
from the original orbit, with no independent second marking assumption. -/
theorem OriginalHypotheses.rankOne_paired_setups
    (d : OriginalHypotheses H M K R T)
    (b : OrbitDecomposition (d.sylow : Subgroup H) (R.subgroupOf H) (pResidual 2 H))
    (i j : Fin b.size)
    (hi : (∃ n, IsL2EvenBlock ((b.block i).map H.subtype) n) ∨
      IsAlternatingBlock ((b.block i).map H.subtype) 3) :
    ∃ (F F' : Type) (_ : Field F) (_ : Field F'),
      Nonempty (Setup R ((b.block i).map H.subtype) F) ∧
      Nonempty (Setup R ((b.block j).map H.subtype) F') := by
  obtain ⟨F,hF,h⟩ := d.rankOne_setup b i hi
  obtain ⟨F',hF',h'⟩ := d.rankOne_setup b j (d.rankOne_type_conjugate b i j hi)
  exact ⟨F,F',hF,hF',h,h'⟩

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
end
