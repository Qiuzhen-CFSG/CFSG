module

public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.Collinearity
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The quotient-geometry endpoint of the G₂(2)′ exclusion

The source's last contradiction is a cycle in the point collinearity graph
of `Uβ/Zβ`. The four points are the images of `Zα`, `F₁`, `V₁`, and `F₂`.
The two noncontainments in Lemma 14.7.62(1) separate the first three kinds
of subgroup images; containment of `Zβ` in both four-groups preserves their
distinctness in the quotient. The line families (c) and (c′) then give the
four incidences. We build the resulting walk and prove it is a four-cycle,
contradicting the concrete octonion collinearity theorem.

`G` below represents `Uβ`, `N` represents `Zβ`, and `U,A` represent the
restrictions of the original `U,Uα` to `Uβ`. `QuotientGeometry` records an
actual incidence realization by subgroups of the literal quotient. It
contains no cycle prohibition. Its construction, the four point images,
and the line families remain explicit in the conditional endpoint.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Theorem 14.7.53, printed pp.1065–1069, especially
Lemma 14.7.62 and formulas (a)–(d), (a′), (c′) on pp.1068–1069. The complete
exclusion still requires Lemmas 14.7.54–62 and the construction of those
families from the original local setup; this module does not assert it.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion
open Subgroup
variable {G Q : Type*} [Group G] [Group Q]

/-- Separation from a subgroup survives a map whose kernel lies in that subgroup. -/
private theorem map_ne_of_not_le (π : G →* Q) {P R A : Subgroup G}
    (hPA : ¬ P ≤ A) (hRA : R ≤ A) (hker : π.ker ≤ A) :
    P.map π ≠ R.map π := by
  intro he
  have h := (Subgroup.map_le_map_iff).mp he.le
  exact hPA (h.trans (sup_le hRA hker))

/-- Distinct subgroups containing the kernel have distinct quotient images. -/
private theorem map_ne_of_ker_le (π : G →* Q) {R S : Subgroup G}
    (hR : π.ker ≤ R) (hS : π.ker ≤ S) (hne : R ≠ S) :
    R.map π ≠ S.map π := by
  intro he
  exact hne (map_injective_of_ker_le π hR hS he)

/-- The four source points remain distinct modulo `Zβ`.
Here `P=V₁`, `Z=Zα`, and `R,S` are two commutator four-groups.
The two containers are the restrictions of `U` and `Uα` to `Uβ`.
This uses both noncontainments of Lemma 14.7.62(1). -/
theorem source_quotient_points_distinct (N : Subgroup G) [N.Normal]
    (U A P Z R S : Subgroup G)
    (hPA : ¬ P ≤ A) (hZU : ¬ Z ≤ U) (hZA : Z ≤ A)
    (hRU : R ≤ U) (hRA : R ≤ A) (hSU : S ≤ U) (hSA : S ≤ A)
    (hNR : N ≤ R) (hNS : N ≤ S) (hRS : R ≠ S) :
    let π := QuotientGroup.mk' N
    P.map π ≠ Z.map π ∧ P.map π ≠ R.map π ∧ P.map π ≠ S.map π ∧
      Z.map π ≠ R.map π ∧ Z.map π ≠ S.map π ∧ R.map π ≠ S.map π := by
  dsimp only
  have hker : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N
  have hNA : (QuotientGroup.mk' N).ker ≤ A := by simpa only [hker] using hNR.trans hRA
  have hNU : (QuotientGroup.mk' N).ker ≤ U := by simpa only [hker] using hNR.trans hRU
  exact ⟨map_ne_of_not_le _ hPA hZA hNA,
    map_ne_of_not_le _ hPA hRA hNA, map_ne_of_not_le _ hPA hSA hNA,
    map_ne_of_not_le _ hZU hRU hNU, map_ne_of_not_le _ hZU hSU hNU,
    map_ne_of_ker_le _ (by simpa only [hker] using hNR) (by simpa only [hker] using hNS) hRS⟩

open Atlas.G2
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon

/-- A realization of the actual binary octonion geometry by subgroups.
This is incidence data, not a four-cycle obstruction. Construction on the
source module requires its natural/Weyl identification. -/
structure QuotientGeometry (Q : Type*) [Group Q] where
  point : SingularPoints (ZMod 2) ↪ Subgroup Q
  line : ZeroProductLine (ZMod 2) ↪ Subgroup Q
  point_card : ∀ p, Nat.card (point p) = 2
  line_card : ∀ L, Nat.card (line L) = 4
  incidence : ∀ p L, pointOnLine p L ↔ point p ≤ line L

/-- The terminal contradiction of 14.7.53, conditional on the two source
line families (c) and (c′), their module realization, and the previously
constructed subgroups. All six point inequalities are proved through the
literal quotient map. This is not the complete source exclusion theorem. -/
theorem false_of_source_quotient_line_families
    (N : Subgroup G) [N.Normal] (geom : QuotientGeometry (G ⧸ N))
    (U A P Z R S : Subgroup G)
    (hPA : ¬ P ≤ A) (hZU : ¬ Z ≤ U) (hZA : Z ≤ A)
    (hRU : R ≤ U) (hRA : R ≤ A) (hSU : S ≤ U) (hSA : S ≤ A)
    (hNR : N ≤ R) (hNS : N ≤ S) (hRS : R ≠ S)
    (p z r s : SingularPoints (ZMod 2))
    (hp : geom.point p = P.map (QuotientGroup.mk' N))
    (hz : geom.point z = Z.map (QuotientGroup.mk' N))
    (hr : geom.point r = R.map (QuotientGroup.mk' N))
    (hs : geom.point s = S.map (QuotientGroup.mk' N))
    (Lpr Lps Lzr Lzs : ZeroProductLine (ZMod 2))
    (hLpr : geom.line Lpr = (R ⊔ P).map (QuotientGroup.mk' N))
    (hLps : geom.line Lps = (S ⊔ P).map (QuotientGroup.mk' N))
    (hLzr : geom.line Lzr = (R ⊔ Z).map (QuotientGroup.mk' N))
    (hLzs : geom.line Lzs = (S ⊔ Z).map (QuotientGroup.mk' N)) : False := by
  obtain ⟨hpz, hpr, hps, hzr, hzs, hrs⟩ := source_quotient_points_distinct N
    U A P Z R S hPA hZU hZA hRU hRA hSU hSA hNR hNS hRS
  have hpz' : p ≠ z := fun h => hpz (by rw [← hp, ← hz, h])
  have hpr' : p ≠ r := fun h => hpr (by rw [← hp, ← hr, h])
  have hps' : p ≠ s := fun h => hps (by rw [← hp, ← hs, h])
  have hzr' : z ≠ r := fun h => hzr (by rw [← hz, ← hr, h])
  have hzs' : z ≠ s := fun h => hzs (by rw [← hz, ← hs, h])
  have hrs' : r ≠ s := fun h => hrs (by rw [← hr, ← hs, h])
  have on {t : SingularPoints (ZMod 2)} {D E : Subgroup G}
      {L : ZeroProductLine (ZMod 2)}
      (ht : geom.point t = D.map (QuotientGroup.mk' N))
      (hL : geom.line L = E.map (QuotientGroup.mk' N)) (hDE : D ≤ E) :
      pointOnLine t L := (geom.incidence t L).mpr (by rw [ht, hL]; exact map_mono hDE)
  have hprAdj : collinearityGraph.Adj p r :=
    ⟨hpr', Lpr, on hp hLpr le_sup_right, on hr hLpr le_sup_left⟩
  have hzrAdj : collinearityGraph.Adj z r :=
    ⟨hzr', Lzr, on hz hLzr le_sup_right, on hr hLzr le_sup_left⟩
  have hpsAdj : collinearityGraph.Adj p s :=
    ⟨hps', Lps, on hp hLps le_sup_right, on hs hLps le_sup_left⟩
  have hzsAdj : collinearityGraph.Adj z s :=
    ⟨hzs', Lzs, on hz hLzs le_sup_right, on hs hLzs le_sup_left⟩
  let w : collinearityGraph.Walk z z :=
    .cons hzrAdj (.cons hprAdj.symm (.cons hpsAdj (.cons hzsAdj.symm .nil)))
  have hw : w.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · apply SimpleGraph.Walk.IsPath.mk'
      change [r, p, s, z].Nodup
      simp [hpz', hpr'.symm, hps', hzr'.symm, hzs'.symm, hrs']
    · change (3 : ℕ) ≤ 4
      decide
  exact binary_collinearity_no_four_cycle z w hw rfl

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion
