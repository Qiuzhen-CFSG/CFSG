module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingGeometry.LocalMarking
public import Theory.GroupTheory.PResidual.NormalizedImageContainment
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.SpecificGroups.SymmetricSeven.PairResidual

/-!
# The original R-normalizer Levi subgroup

In the marked action, the two-residual of N_K(R) normalizes the transposition
and therefore fixes its two letters. Its image lies in the original A₅.
The action kernel is a two-group normalizing L, so two-perfectness lifts this
containment to L itself. Thus the actual Levi subgroup normalizes O₂(LT),
as required by C.6.4.

Source: Aschbacher–Smith, original 4.3.7, printed p.616.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The two-residual of the literal K-normalizer of R lies in the original L. -/
theorem BlockAlternatingCoordinates.levi_le_component {c : SourceConfiguration T L}
    (d : BlockAlternatingCoordinates c) :
    (pResidual 2 (c.K.map c.H.subtype ⊓ normalizer (c.I.pCoreIn 2 : Set G) : Subgroup G)).map
      (c.K.map c.H.subtype ⊓ normalizer (c.I.pCoreIn 2 : Set G)).subtype ≤ L := by
  let A := c.K.map c.H.subtype
  let J := A ⊔ ((T : Subgroup G) ⊓ c.H)
  let R := c.I.pCoreIn 2
  let N := A ⊓ normalizer (R : Set G)
  have hNJ : N ≤ J := inf_le_left.trans le_sup_left
  let i : N →* J := inclusion hNJ
  let P := (pResidual 2 N).map i
  let f := d.chart.actor
  have hP : IsPPerfect 2 P := (isPPerfect_pResidual (G := N) 2).of_surjective
    (i.subgroupMap _) (i.subgroupMap_surjective _)
  have hPf : IsPPerfect 2 (P.map f) := hP.of_surjective (f.subgroupMap P)
    (f.subgroupMap_surjective P)
  have hnorm : P.map f ≤ normalizer (zpowers (Equiv.swap (0 : Fin 7) 1) : Set _) := by
    rintro _ ⟨p,⟨n,hn,rfl⟩,rfl⟩
    have hn' : i n ∈ normalizer (R.subgroupOf J : Set J) := by
      intro r
      exact n.property.2 (r : G)
    have hh := (R.subgroupOf J).le_normalizer_map f (mem_map_of_mem f hn')
    rwa [d.transposition] at hh
  have hfix := Equiv.Perm.twoPerfect_normalizes_swap_fixes
    (0 : Fin 7) 1 (by decide) (P.map f) hPf hnorm
  have hPA : P ≤ A.subgroupOf J := by
    rintro _ ⟨n,hn,rfl⟩
    exact n.property.1
  have hPfA : P.map f ≤ alternatingGroup (Fin 7) :=
    d.chart.component_image ▸ map_mono hPA
  have himage : P.map f ≤ (L.subgroupOf J).map f := by
    rw [d.five_image]
    intro x hx
    refine ⟨⟨x,hPfA hx⟩,?_,rfl⟩
    intro a
    exact hfix x hx a a.property
  have hk : IsPGroup 2 f.ker := d.kernel ▸ pCore_isPGroup
  have hkn : f.ker ≤ normalizer (L.subgroupOf J : Set J) := by
    intro k hk' l
    have hR : (k : G) ∈ R := c.block_join_core_le (mem_map_of_mem J.subtype (d.kernel ▸ hk'))
    exact (c.c28.radical_le hR).2 (l : G)
  have hPL := isPPerfect_le_of_map_le_of_kernel_normalizes f P (L.subgroupOf J)
    hP hk hkn himage
  rintro _ ⟨n,hn,rfl⟩
  exact hPL (mem_map_of_mem i hn)

/-- The actual Levi residual therefore normalizes the original O₂(LT). -/
theorem BlockAlternatingCoordinates.levi_normalizes {c : SourceConfiguration T L}
    (d : BlockAlternatingCoordinates c) :
    (pResidual 2 (c.K.map c.H.subtype ⊓ normalizer (c.I.pCoreIn 2 : Set G) : Subgroup G)).map
      (c.K.map c.H.subtype ⊓ normalizer (c.I.pCoreIn 2 : Set G)).subtype ≤
        normalizer ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
  d.levi_le_component.trans ((le_sup_left : L ≤ L ⊔ (T : Subgroup G)).trans
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))))
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
