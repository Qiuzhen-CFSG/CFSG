module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.ComponentRecognition
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.Rank
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.LieType.Endpoints
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ChiZero
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.LinearThree.Blocks
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.SymplecticFour.Blocks
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.PerfectSubgroups
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.SymplecticFour.SplitTorusRank
public import Theory.SpecificGroups.SymplecticFour.Sylow.ThreeResidualPlacement.OvergroupGeometry

/-!
# Odd rank from the actual local block in a rank-two Lie component

A full-Sylow local C-component that is an intrinsic L₂(2ⁿ) block has a
proper join with the Sylow in a quasisimple group. In PSL₃ and Sp₄, the
proved Sylow-overgroup geometry places this join in a parabolic. Its
perfect local component lies in the parabolic's solvable residual, which
is the concrete natural L₂ block. Restricting the full Sylow to the
parabolic lets A.3.12 identify these two C-components. Their intrinsic
module cardinalities identify the source exponent with the field exponent.

The natural module's two-rank excludes both binary model endpoints. A
prime divisor of 2ⁿ−1 then gives an elementary abelian subgroup of rank two.
The split tori suffice in Sp₄ and away from three in PSL₃; the established
projective diagonal-and-cycle construction handles three in PSL₃. The final
wrappers transport this conclusion through the supplied model equivalence of the
literal quasisimple component; no separate component-recognition premise
or additional centralizer hypothesis is imposed.

Source: Aschbacher–Smith 2.4.7, printed p.541, with A.3.12 and the local
models in F.1.12(I)(1)–(2).
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.LinearShadows.Double
variable {G : Type*} [Group G] [Finite G]

private theorem local_map_equiv {A S : Subgroup G}
    (hA : A ∈ ChapterA.Section03.localCComponents S)
    {H : Type*} [Group H] (e : G ≃* H) :
    A.map e.toMonoidHom ∈ ChapterA.Section03.localCComponents (S.map e.toMonoidHom) := by
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  exact Chapter1.Section02.localCComponents_map_of_solvable_ker hA e.toMonoidHom

omit [Finite G] in
private theorem local_perfect {L S : Subgroup G}
    (hL : L ∈ ChapterA.Section03.localCComponents S) : Group.IsPerfect L := by
  let := hL.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show L ≤ L ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show L ≤ L ⊔ S from le_sup_left)).surjective

private theorem local_join_ne_top [IsQuasisimple G] {L S : Subgroup G} {n : ℕ}
    (hL : L ∈ ChapterA.Section03.localCComponents S)
    (hn : ChapterC.IsL2EvenBlock L n) : L ⊔ S ≠ ⊤ := by
  intro he
  change (L.subgroupOf (L ⊔ S)).IsCComponent at hL
  rw [he] at hL
  have hc : L.IsCComponent := by
    simpa only [map_subgroupOf_eq_of_le (show L ≤ ⊤ from le_top)] using
      hL.map_subtype (show (⊤ : Subgroup G).IsSubnormal from .top)
  have ht : (⊤ : Subgroup G).IsCComponent :=
    (show IsComponent G ⊤ from ⟨.top, IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  have hl := hc.eq_of_le ht le_top
  let : IsQuasisimple (⊤ : Subgroup G) := IsQuasisimple.of_mulEquiv topEquiv.symm
  exact natural_block_not_quasisimple hn
    (IsQuasisimple.of_mulEquiv (MulEquiv.subgroupCongr hl).symm)

private theorem natural_isCComponent {L : Subgroup G} {n : ℕ}
    (hL : L.IsSubnormal) (hn : ChapterC.IsL2EvenBlock L n) : L.IsCComponent := by
  rcases hn.2.1.quotient with hq | h3
  · let := hq
    exact isCComponent_of_isPPerfect_of_quasisimple_core_quotient hL hn.2.1.twoPerfect
  · let : IsCyclic (L ⧸ pCore 2 L) := isCyclic_of_prime_card h3
    let : CommGroup (L ⧸ pCore 2 L) := IsMulCommutative.instCommGroup
    let : Group.IsNilpotent (pCore 2 L) := pCore_isPGroup.isNilpotent
    let : Group.IsSolvable L := (Group.isSolvable_iff_subgroup_quotient (pCore 2 L)).mpr
      ⟨inferInstance, inferInstance⟩
    exact hn.not_solvable.elim

private theorem exponent_eq {L : Type*} [Group L] {n m : ℕ}
    (hn : ChapterC.IsL2EvenBlock L n) (hm : ChapterC.IsL2EvenBlock L m) : n = m := by
  have hp := hn.module_card.symm.trans hm.module_card
  have he := (Nat.pow_right_injective (by decide : 1 < (2 : ℕ))) hp
  omega

/-- Restrict the full Sylow to the actual parabolic. Minimality in the
containing χ₀ residual identifies the local block and its field exponent. -/
theorem natural_exponent_eq_of_parabolic_residual (P : Sylow 2 G)
    {L R : Subgroup G} {n m : ℕ}
    (hlocal : L ∈ ChapterA.Section03.localCComponents P)
    (hn : ChapterC.IsL2EvenBlock L n) (hPR : (P : Subgroup G) ≤ R) (hLR : L ≤ R)
    (hm : ChapterC.IsL2EvenBlock (solvableResidual R) m) : n = m := by
  have hc := ChapterA.Section03.SourceEmbeddings.local_restrict hlocal hLR
  have hperfect := local_perfect hc
  let := hperfect
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_chiZero_containing_component
    (P.subtype hPR) hc
    (natural_isCComponent (inferInstance : (solvableResidual R).Normal).isSubnormal hm)
    (le_solvableResidual_of_isPerfect (L.subgroupOf R)) (Or.inl ⟨m, hm⟩)
  have hn' := hn.of_mulEquiv (subgroupOfEquivOfLe hLR).symm
  rw [he] at hn'
  exact exponent_eq hn' hm

omit [Finite G] in
private theorem residual_model {R D : Subgroup G} {m : ℕ}
    (hD : (solvableResidual R).map R.subtype = D)
    (hm : ChapterC.IsL2EvenBlock D m) :
    ChapterC.IsL2EvenBlock (solvableResidual R) m := by
  let e := ((solvableResidual R).equivMapOfInjective R.subtype R.subtype_injective).trans
    (MulEquiv.subgroupCongr hD)
  exact hm.of_mulEquiv e.symm

private theorem exists_odd_prime {n : ℕ} (hn : 1 < n) :
    ∃ p, p.Prime ∧ Odd p ∧ p ∣ 2 ^ n - 1 := by
  have hbig : 4 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  refine ⟨p, hp, hp.odd_of_ne_two ?_, hd⟩
  intro he
  subst p
  have ht : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
  have hx := Nat.dvd_sub ht hd
  have he : 2 ^ n - (2 ^ n - 1) = 1 := by omega
  rw [he] at hx
  omega

end CFSG.Quasithin.Chapter2.LinearShadows.Double


namespace CFSG.Quasithin.Chapter2.LinearShadows.Double

private theorem psl_three_exponent (F : Type) [Field F] [Finite F]
    [IsQuasisimple PSL(3,F)] {m n : ℕ} (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ m)
    (P : Sylow 2 PSL(3,F)) (L : Subgroup PSL(3,F))
    (hlocal : L ∈ ChapterA.Section03.localCComponents P)
    (hn : ChapterC.IsL2EvenBlock L n) : n = m := by
  have hl := natural_block_image_two_rank hn L.subtype (by simp)
  rw [Matrix.PSL3Even.two_rank F (by omega) hF] at hl
  have hm' : 1 < m := by have := hn.1; omega
  have hcard : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hm'
  obtain ⟨g, hg⟩ :=
    Matrix.PSL3.LinearThree.UnipotentOvergroups.proper_sylow_overgroup_parabolic_cover
      F (n := m) (by omega) hF P (L ⊔ P) le_sup_right (local_join_ne_top hlocal hn)
  let a := MulAut.conj g
  let P' := P.mapSurjective (f := a.toMonoidHom) a.surjective
  have hc : L.map a.toMonoidHom ∈ ChapterA.Section03.localCComponents P' :=
    local_map_equiv hlocal a
  have hn' := hn.of_mulEquiv (L.equivMapOfInjective a.toMonoidHom a.injective)
  have aux (R : Subgroup PSL(3,F)) (hR : (L ⊔ P).map a.toMonoidHom ≤ R)
      (hr : ChapterC.IsL2EvenBlock (solvableResidual R) m) : n = m :=
    natural_exponent_eq_of_parabolic_residual P' hc hn'
      ((map_mono (show (P : Subgroup PSL(3,F)) ≤ L ⊔ P from le_sup_right)).trans hR)
      ((map_mono (show L ≤ L ⊔ P from le_sup_left)).trans hR) hr
  rcases hg with hg | hg
  · exact aux _ hg (residual_model
      (Matrix.PSL3.LinearThree.PerfectSubgroups.pointParabolic_residual F hcard)
      (ChapterF.GreenBook.LieModels.LinearThree.pointLocal_isL2EvenBlock F hF hm'))
  · exact aux _ hg (residual_model
      (Matrix.PSL3.LinearThree.PerfectSubgroups.lineParabolic_residual F hcard)
      (ChapterF.GreenBook.LieModels.LinearThree.lineLocal_isL2EvenBlock F hF hm'))

private theorem symplectic_four_exponent (F : Type) [Field F] [Finite F] [CharP F 2]
    [IsQuasisimple (Theory.SpecificGroups.SymplecticFour.Sp F)]
    {m n : ℕ} (hm : 1 < m) (hF : Nat.card F = 2 ^ m)
    (P : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F))
    (L : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
    (hlocal : L ∈ ChapterA.Section03.localCComponents P)
    (hn : ChapterC.IsL2EvenBlock L n) : n = m := by
  have hcard : 2 < Nat.card F := by
    rw [hF]
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hm
    change 4 ≤ 2 ^ m at hh
    omega
  obtain ⟨g, hg⟩ :=
    Theory.SpecificGroups.SymplecticFour.ThreeResidualPlacement.proper_sylow_overgroup_parabolic_cover
      hcard P (L ⊔ P) le_sup_right (local_join_ne_top hlocal hn)
  let a := MulAut.conj g
  let P' := P.mapSurjective (f := a.toMonoidHom) a.surjective
  have hc : L.map a.toMonoidHom ∈ ChapterA.Section03.localCComponents P' :=
    local_map_equiv hlocal a
  have hn' := hn.of_mulEquiv (L.equivMapOfInjective a.toMonoidHom a.injective)
  have aux (R : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F))
      (hR : (L ⊔ P).map a.toMonoidHom ≤ R)
      (hr : ChapterC.IsL2EvenBlock (solvableResidual R) m) : n = m :=
    natural_exponent_eq_of_parabolic_residual P' hc hn'
      ((map_mono (show (P : Subgroup _) ≤ L ⊔ P from le_sup_right)).trans hR)
      ((map_mono (show L ≤ L ⊔ P from le_sup_left)).trans hR) hr
  rcases hg with hg | hg
  · exact aux _ hg (residual_model
      (Theory.SpecificGroups.SymplecticFour.pointParabolic_solvableResidual_eq hF hm)
      (ChapterF.GreenBook.LieModels.SymplecticFour.pointLocal_isL2EvenBlock hF hm))
  · exact aux _ hg (residual_model
      (Theory.SpecificGroups.SymplecticFour.planeParabolic_solvableResidual_eq hF hm)
      (ChapterF.GreenBook.LieModels.SymplecticFour.planeLocal_isL2EvenBlock hF hm))

variable {K : Type*} [Group K] [Finite K] [IsQuasisimple K]

/-- The actual full-Sylow local block determines the coefficient field of a
PSL₃ component, giving the source's required odd rank through the established
projective rank theorem. -/
theorem odd_rank_of_psl_three {m n : ℕ} (hm : 1 ≤ m)
    (hmodel : ClassicalGroup.IsPSL K 3 (2 ^ m))
    (P : Sylow 2 K) (L : Subgroup K)
    (hlocal : L ∈ ChapterA.Section03.localCComponents P)
    (hn : ChapterC.IsL2EvenBlock L n) :
    ∃ p, p.Prime ∧ Odd p ∧ p ∣ 2 ^ n - 1 ∧ 2 ≤ primeRank p K := by
  obtain ⟨F, hField, hFinite, hF, ⟨e⟩⟩ := hmodel
  let : IsQuasisimple PSL(3,F) := IsQuasisimple.of_mulEquiv e
  have hn' := hn.of_mulEquiv (L.equivMapOfInjective e.toMonoidHom e.injective)
  have he := psl_three_exponent F hm hF (P.mapSurjective e.surjective)
    (L.map e.toMonoidHom) (local_map_equiv hlocal e) hn'
  obtain ⟨p, hp, ho, hd⟩ := exists_odd_prime hn.1
  refine ⟨p, hp, ho, hd, ?_⟩
  rw [primeRank_equiv p e]
  apply LinearDouble.psl_three_prime_rank hp
  simpa only [hF, ← he] using hd

/-- The derived symplectic family has the same rank-two split torus. Its
binary member is excluded by the natural block's elementary two-rank. -/
theorem odd_rank_of_derived_symplectic_four {n : ℕ}
    (hmodel : ComponentRefinement.LieType.IsDerivedSymplecticFour K)
    (P : Sylow 2 K) (L : Subgroup K)
    (hlocal : L ∈ ChapterA.Section03.localCComponents P)
    (hn : ChapterC.IsL2EvenBlock L n) :
    ∃ p, p.Prime ∧ Odd p ∧ p ∣ 2 ^ n - 1 ∧ 2 ≤ primeRank p K := by
  obtain ⟨m, hm, F, hField, hFinite, hF, ⟨e⟩⟩ := hmodel
  have hl := natural_block_image_two_rank hn
    (((commutator (Matrix.symplecticGroup (Fin 2) F)).subtype.comp e.toMonoidHom).comp
      L.subtype) (by
        rw [MonoidHom.ker_eq_bot]
        · exact bot_le
        · exact Subtype.val_injective.comp (e.injective.comp Subtype.val_injective))
  rw [Theory.SpecificGroups.SymplecticFour.EvenTwoRank.rank hF (by omega)] at hl
  have hm' : 1 < m := by have := hn.1; omega
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let e' := e.trans (Theory.SpecificGroups.SymplecticFour.EvenTwoRank.derivedEquiv hF hm')
  let : IsQuasisimple (Theory.SpecificGroups.SymplecticFour.Sp F) :=
    IsQuasisimple.of_mulEquiv e'
  have hn' := hn.of_mulEquiv (L.equivMapOfInjective e'.toMonoidHom e'.injective)
  have he := symplectic_four_exponent F hm' hF (P.mapSurjective e'.surjective)
    (L.map e'.toMonoidHom) (local_map_equiv hlocal e') hn'
  obtain ⟨p, hp, ho, hd⟩ := exists_odd_prime hn.1
  refine ⟨p, hp, ho, hd, ?_⟩
  rw [primeRank_equiv p e']
  apply Theory.SpecificGroups.SymplecticFour.split_torus_prime_rank hp
  simpa only [hF, ← he] using hd

end CFSG.Quasithin.Chapter2.LinearShadows.Double
