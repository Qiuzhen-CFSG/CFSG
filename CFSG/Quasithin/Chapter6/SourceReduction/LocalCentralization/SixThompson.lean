module
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.SixGeometry
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FourThompson
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.SevenThompsonImage

/-!
# The original six-space Thompson image

The literal action of KT on U has kernel O₂(KT). Its A₇ component and
Thompson movement force the full quotient to be S₇. The Thompson image
is the full group of three disjoint transpositions, of order eight.
The result retains the actual omega-module, kernel and permutation action.

Source: Aschbacher–Smith 5.1.13, p.637, using B.3.2(4), pp.83–84.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
namespace LocalA7Configuration
variable {T : Sylow 2 G} {L W H A Y X D K : Subgroup G} {n : ℕ}

/-- Both the full S₇ quotient and the order-eight Thompson image belong to
the original KT. No semidirect-product splitting is assumed. -/
theorem six_thompson_image (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : LocalCartanWitness T H A Y X D)
    (hc : Nat.card (localOmegaModule T K) = 64) :
    let M := K ⊔ (T : Subgroup G)
    let U := (localOmegaModule T K).subgroupOf M
    let J := (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf M
    ∃ f : M →* Equiv.Perm (Fin 7), Function.Surjective f ∧
      f.ker = centralizer (U : Set M) ∧ f.ker = pCore 2 M ∧
      (K.subgroupOf M).map f = alternatingGroup (Fin 7) ∧
      (∃ g : Equiv.Perm (Fin 7), J.map f =
        (ChapterB.Offenders.D 7).map (MulAut.conj g).toMonoidHom) ∧
      Nat.card (J.map f) = 8 := by
  let M := K ⊔ (T : Subgroup G)
  let U := (localOmegaModule T K).subgroupOf M
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  have hr : IsPReduced 2 U := LocalOmega.reduced_internal a.reduced
  let := hr.normal
  let := hr.elementary
  obtain ⟨f,hker,hcore,hK,l,hl⟩ := a.six_action h hH d hc
  have hUP : U ≤ P :=
    (show U ≤ pCore 2 M from le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 U⟩).trans
      (pCore_isPGroup.le_sylow_of_normal P)
  have hPmap : (P : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hJmap : (elementaryAbelianMaxJ (P : Subgroup M)).map M.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,hPmap]
  have hj : ¬ elementaryAbelianMaxJ (P : Subgroup M) ≤ f.ker := by
    rw [hker]
    intro hj
    apply a.right_thompson_moves
    rw [←hJmap]
    rintro _ ⟨x,hx,rfl⟩ u hu
    exact congrArg M.subtype (hj hx ⟨u,a.reduced.1 hu⟩ hu)
  have hJM : elementaryAbelianMaxJ (T : Subgroup G) ≤ M :=
    (show elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) from
      sSup_le fun _ hE => hE.1).trans le_sup_right
  have hJ : elementaryAbelianMaxJ (P : Subgroup M) =
      (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [hJmap,map_subgroupOf_eq_of_le hJM]
  obtain ⟨hf,g,hg⟩ := ChapterB.Offenders.seven_thompson_image U f hker
    (hK ▸ map_le_range f (K.subgroupOf M)) P hUP hj l hl
  rw [hJ] at hg
  refine ⟨f,hf,hker,hcore,hK,⟨g,hg⟩,?_⟩
  rw [hg,card_map_of_injective (MulAut.conj g).injective]
  exact ChapterB.Offenders.Odd.card_disjointTranspositions (Or.inr rfl) le_rfl

end LocalA7Configuration
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
