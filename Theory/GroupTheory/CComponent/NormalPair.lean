module
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.ComponentPairRankDescent
public import Theory.GroupTheory.PCoreImage

/-!
# Normal pairs of C-components

A normal product of two distinct conjugate C-components has component
normalizers of index two. Pass to the solvable-radical quotient, apply the
ordinary component-pair theorem, and lift the normalizer through the same
quotient. The ambient two-core normalizes every C-component; consequently
an index-two component normalizer has the original ambient two-core.

Source: Aschbacher--Smith, A.3.3 and the second-normalizer construction in
14.6.15, printed pp.42--43 and1034. The source application retains relative
normality inside the chosen maximal two-local subgroup.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A normal exchanged pair of C-components has exactly two conjugates. -/
theorem IsCComponent.normalizer_index_two_of_normal_pair
    {B : Subgroup G} (hB : B.IsCComponent)
    (t : G) (hne : B ≠ B.conjBy t) [(B ⊔ B.conjBy t).Normal] :
    (normalizer (B : Set G)).index = 2 := by
  let R := solvableRadical G
  let q := QuotientGroup.mk' R
  let A := B.map q
  have hA : IsComponent (G ⧸ R) A := map_cComponent_isComponent_of_solvableRadical hB
  have he : (B.conjBy t).map q = A.conjBy (q t) := by
    change (B.map (MulAut.conj t).toMonoidHom).map q =
      (B.map q).map (MulAut.conj (q t)).toMonoidHom
    rw [map_map,map_map]
    congr 1
  have hn : A ≠ A.conjBy (q t) := by
    intro hh
    exact hne (hB.eq_of_map_quotient_eq (hB.map_equiv (MulAut.conj t)) R
      (hh.trans he.symm))
  have hp : (A ⊔ A.conjBy (q t)).Normal := by
    rw [←he,show A = B.map q from rfl,←map_sup]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective R)
  let := hp
  rw [←cComponent_normalizer_index_quotient hB R]
  exact ComponentPairRankDescent.component_normalizer_index_two_of_normal_pair A hA (q t) hn

/-- Every ambient prime core normalizes each C-component. -/
theorem IsCComponent.pCore_le_normalizer {B : Subgroup G} (hB : B.IsCComponent)
    (p : ℕ) [Fact p.Prime] : pCore p G ≤ normalizer (B : Set G) := by
  let : Group.IsNilpotent (pCore p G) := pCore_isPGroup.isNilpotent
  rw [←normalizer_cComponent_quotient hB (pCore p G)]
  intro x hx
  change QuotientGroup.mk' (pCore p G) x ∈
    normalizer (B.map (QuotientGroup.mk' (pCore p G)) : Set _)
  have he : QuotientGroup.mk' (pCore p G) x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hx
  rw [he]
  exact one_mem _

/-- A normal component normalizer has the same ambient prime core. -/
theorem IsCComponent.normalizer_pCoreIn {B : Subgroup G} (hB : B.IsCComponent)
    (p : ℕ) [Fact p.Prime] [(normalizer (B : Set G)).Normal] :
    (normalizer (B : Set G)).pCoreIn p = pCore p G := by
  apply le_antisymm
  · let N := normalizer (B : Set G)
    have hn : (N.pCoreIn p).Normal := by
      apply normalizer_eq_top_iff.mp
      apply top_unique
      exact (show (⊤ : Subgroup G) ≤ normalizer (N : Set G) by
        rw [normalizer_eq_top]).trans
          (normalizer_le_normalizer_characteristic_image N (pCore p N))
    exact le_sSup ⟨hn,isPGroup_pCoreIn p N⟩
  · apply le_pCoreIn_of_normalizes pCore_isPGroup (hB.pCore_le_normalizer p)
    exact le_normalizer_of_normal

end Subgroup
