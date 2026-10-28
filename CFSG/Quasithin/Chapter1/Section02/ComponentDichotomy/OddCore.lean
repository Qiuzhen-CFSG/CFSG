module
public import CFSG.Quasithin.ChapterA.Section01.RankActions.SourceActions
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Odd-core centralization by the original normalizer residual

For an elementary abelian two-subgroup A, two-perfect commutator idempotence
makes [A,X] the exact input of A.1.26(1). It therefore centralizes the odd
core. Restricting to H proves the statement for the residual of the literal
relative normalizer H ∩ N_G(A), preserving its inclusion into G.

Source: Aschbacher–Smith 1.2.11, printed p.508. The proof there cites
A.1.26.2, while the elementary odd-core assertion is clause A.1.26(1).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1
variable {G : Type*} [Group G] [Finite G]

theorem elementary_residual_centralizes_oddCore
    (hsqt : IsStronglyQuasithin G) (A X : Subgroup G)
    [IsElementaryAbelian 2 A] (hp : IsPPerfect 2 X)
    (hn : X ≤ normalizer (A : Set G)) :
    ⁅A,X⁆ ≤ centralizer (pPrimeCore 2 G : Set G) := by
  have hC : ⁅A,X⁆ ≤ A := le_normalizer_iff_commutator_le_left.mp hn
  let : IsElementaryAbelian 2 (⁅A,X⁆ : Subgroup G) := IsElementaryAbelian.of_le hC
  exact commutator_eq_bot_iff_le_centralizer.mp
    (ChapterA.lemma_A_1_26_1_of_stronglyQuasithin hsqt X ⁅A,X⁆ hp
      (commutator_isPPerfect_idempotent X A hp
        (IsElementaryAbelian.isPGroup 2 A) hn))

theorem relative_residual_centralizes_oddCore
    (H A : Subgroup G) (hsqt : IsStronglyQuasithin H) (hAH : A ≤ H)
    [IsElementaryAbelian 2 A] :
    ⁅A, (pResidual 2 (H ⊓ normalizer (A : Set G) : Subgroup G)).map
      (H ⊓ normalizer (A : Set G)).subtype⁆ ≤
      centralizer ((pPrimeCore 2 H).map H.subtype : Set G) := by
  let X := (pResidual 2 (H ⊓ normalizer (A : Set G) : Subgroup G)).map
    (H ⊓ normalizer (A : Set G)).subtype
  have hXH : X ≤ H := (map_subtype_le _).trans inf_le_left
  have hn : X ≤ normalizer (A : Set G) := (map_subtype_le _).trans inf_le_right
  let A' := A.subgroupOf H
  let X' := X.subgroupOf H
  let : IsElementaryAbelian 2 A' := IsElementaryAbelian.subgroupOf hAH
  have hp : IsPPerfect 2 X' := by
    let e := subgroupOfEquivOfLe hXH
    exact (isPPerfect_embedded_pResidual 2 (H ⊓ normalizer (A : Set G))).of_surjective
      e.symm.toMonoidHom e.symm.surjective
  have hn' : X' ≤ normalizer (A' : Set H) := by
    apply le_normalizer_iff.mpr
    intro x hx a ha
    exact le_normalizer_iff.mp hn x hx a ha
  have hc := elementary_residual_centralizes_oddCore hsqt A' X' hp hn'
  have he : ⁅A',X'⁆.map H.subtype = ⁅A,X⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le hAH,map_subgroupOf_eq_of_le hXH]
  intro x hx y hy
  obtain ⟨x',hx',rfl⟩ := mem_map.mp (he.symm ▸ hx)
  obtain ⟨y',hy',rfl⟩ := mem_map.mp hy
  exact congrArg Subtype.val (hc hx' y' hy')
end CFSG.Quasithin.Chapter1
