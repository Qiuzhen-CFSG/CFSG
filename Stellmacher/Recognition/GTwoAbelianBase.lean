module

public import Stellmacher.Recognition.GTwoSylow
public import Stellmacher.SectionFiveToSeven.Result7_6.CoreFacts

/-!
# A normal abelian base in the actual G₂(2)' Sylow configuration

Every ambient Sylow two-subgroup of a finite group with Stellmacher's local
`G₂(2)'` type contains a normal subgroup isomorphic to `C₄ × C₄`, of index
two or four. This is a direct structural consequence of the supplied local
type, independent of simplicity and local solvability.

The subgroup is the actual two-core of the first vertex's two-residual.
The residual is normal in the vertex, and its two-core is characteristic,
so this subgroup is normal in the vertex. Its injective ambient image is
therefore a normal two-subgroup of the mapped vertex and lies in the given
ambient Sylow intersection. Restriction preserves normality, and Sylow
conjugacy transports it to the supplied Sylow. Its model gives order sixteen;
the proved ambient Sylow order bound gives the two possible indices.

Source: Stellmacher (8.6)(a1), printed p. 41, and the local-type definition
following (8.6), printed p. 45 (`refs/latex/stellmacher-n-group.tex`). The
proof uses the actual mapped local data and makes no assumption that the
local pair generates the ambient group. Full Sylow shape and global
recognition require further arguments.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven SevenSix

/-- The actual G₂ local type supplies a normal `C₄ × C₄` base in each ambient Sylow. -/
public theorem exists_normal_c4_prod_c4_of_gTwoTwoDerived_type
    {G : Type*} [Group G] [Finite G] (S0 : Sylow 2 G)
    (hType : IsOfGTwoTwoDerivedType G) :
    ∃ A : Subgroup S0, A.Normal ∧
      Nonempty (A ≃* Later.C4 × Later.C4) ∧ (A.index = 2 ∨ A.index = 4) := by
  obtain ⟨data⟩ := hType
  let := data.groupK
  let := data.finiteK
  let P := GAt data.Γ data.criticalPath.a
  let R := EAt data.Γ data.criticalPath.a
  let B := twoCoreIn R
  have hR : R = twoResidualIn P := data.Γ.twoResidualAt_def _
  have hRP : R ≤ P := by rw [hR]; exact twoResidualIn_le P
  have hRN : (R.subgroupOf P).Normal := by rw [hR]; exact twoResidualIn_normal P
  have hBP : B ≤ P := (twoCoreIn_le R).trans hRP
  have hBN : (B.subgroupOf P).Normal := twoCoreIn_normal_of_normal R P hRP hRN
  have hPN : P ≤ Subgroup.normalizer (B : Set data.K) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mp hBN
  let Pm := P.map data.embedding
  let Bm := B.map data.embedding
  have hBmPm : Bm ≤ Pm := Subgroup.map_mono hBP
  have hPmN : Pm ≤ Subgroup.normalizer (Bm : Set G) :=
    (Subgroup.map_mono hPN).trans (Subgroup.le_normalizer_map data.embedding)
  have hBmN : (Bm.subgroupOf Pm).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBmPm).mpr hPmN
  have hBmTwo : IsPGroup 2 Bm := ((pCore_isPGroup (p := 2) (G := R)).map R.subtype).map data.embedding
  have hST : (data.sylowIntersection : Subgroup G) ≤ Pm := by
    rw [← data.intersection_eq]
    exact inf_le_left
  let S := data.sylowIntersection
  have hBmS : Bm ≤ (S : Subgroup G) := by
    let := hBmN
    have htwo : IsPGroup 2 (Bm.subgroupOf Pm) :=
      hBmTwo.of_equiv (Subgroup.subgroupOfEquivOfLe hBmPm).symm
    have hle := htwo.le_sylow_of_normal (S.subtype hST)
    intro x hx
    exact hle (show (⟨x, hBmPm hx⟩ : Pm) ∈ Bm.subgroupOf Pm from hx)
  let A0 := Bm.subgroupOf (S : Subgroup G)
  have hA0N : A0.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBmS).mpr (hST.trans hPmN)
  obtain ⟨eB⟩ := data.caseA.twoCore_model
  let e0 : A0 ≃* C4 × C4 :=
    ((Subgroup.subgroupOfEquivOfLe hBmS).trans
      (B.equivMapOfInjective data.embedding data.embedding_injective).symm).trans eB
  let eS := S.equiv S0
  let A := A0.map eS.toMonoidHom
  have hAN : A.Normal := hA0N.map _ eS.surjective
  let eA : A ≃* C4 × C4 := (eS.subgroupMap A0).symm.trans e0
  refine ⟨A, hAN, ⟨eA⟩, ?_⟩
  have hcard : Nat.card A = 16 := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_prod]
    norm_num [C4]
  have hindex := A.card_mul_index
  rw [hcard] at hindex
  rcases sylow_card_of_gTwoTwoDerived_type S0 ⟨data⟩ with h32 | h64
  · left
    omega
  · right
    omega

end Stellmacher.Recognition
