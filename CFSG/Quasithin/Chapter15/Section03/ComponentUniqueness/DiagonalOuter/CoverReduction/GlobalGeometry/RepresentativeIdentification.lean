module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.A312Specialization
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.CoverEmbeddingRigidity
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.RepresentativeEnvelope


/-!
# Identification of the representative-centralizer component

Restrict the marked cover L to H=C_G(v) through the actual subgroup
inclusion. This transports its central two-core, center order, three-rank
and projective marking to the component envelope's smaller subgroup B.
The proved A.3.12 specialization gives equal quotient images or M₂₃;
the perfect-cover rigidity theorem, using the explicit trivial M₂₃
multiplier, proves B=K in both cases. Relative normality of K now gives
C_G(v)≤N_G(L)≤N_G(Z(L))=I.

The component envelope is an intermediate output constructed by
`representative_envelope_of_outside`, not a source hypothesis in the final
assembly. No outside-family condition is imposed on C_G(v).

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
proof of 15.3.38 on printed p.1136; A.3.12, pp.47--48; I.1.3, p.407.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
universe u
variable {G : Type u} [Group G]

private theorem map_center_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (center A).map e.toMonoidHom = center B := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (centerCongr e ⟨z, hz⟩).property
  · intro hx
    exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩

/-- Resolve the actual component embedding and bound the representative
centralizer. The only remaining multiplier input concerns the universal
projection of the concrete Mathieu group. -/
theorem representative_centralizer_le_of_envelope [Finite G] {κ : GroupClass.{u}}
    (hG : IsSimpleQTKE κ G) (I L V : Subgroup G) [IsKleinFour V]
    [IsQuasisimple L] (c : ProjectiveMarking L 4)
    (hI : I = normalizer (V : Set G))
    (hZ : (center L).map L.subtype = V) (hcore : center L = pCore 2 L)
    (hrank : primeRank 3 L = 2) (v : G) (hv2 : orderOf v = 2)
    (hm : (PerfectCentralCovering.universalProjection Sporadic.Mathieu.M23).ker = ⊥)
    (henv : let H := centralizer ({v} : Set G)
      ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧ L ≤ K.map H.subtype ∧
        Chapter1.Section02.A312Embedding
          ((L.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))
          (K.map (QuotientGroup.mk' (pCore 2 H)))) :
    centralizer ({v} : Set G) ≤ I := by
  let H := centralizer ({v} : Set G)
  obtain ⟨K, hK, hKn, hLK, hemb⟩ := henv
  have hLH : L ≤ H := hLK.trans (map_subtype_le _)
  let B := L.subgroupOf H
  let e : B ≃* L := subgroupOfEquivOfLe hLH
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv e.symm
  let : IsQuasisimple K := hK.2
  let : K.Normal := hKn
  have hBK : B ≤ K := by
    intro x hx
    obtain ⟨y, hy, he⟩ := mem_map.mp (hLK hx)
    exact (Subtype.ext he : y = x) ▸ hy
  have hBc : center B = pCore 2 B := by
    apply (map_injective (f := e.toMonoidHom) e.injective)
    rw [map_center_equiv, pCore_map_iso, hcore]
  have hLc : Nat.card (center L) = 4 := by
    rw [← card_map_of_injective L.subtype_injective, hZ, IsKleinFour.card_four]
  have hBc4 : Nat.card (center B) = 4 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans hLc
  let b : ProjectiveMarking B 4 := {
    F := c.F
    card := c.card
    equivalence := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans c.equivalence }
  have hBKeq : B = K := CoverEmbeddingRigidity.eq_of_equal_image_or_m23
    hBK hBc hBc4 b hm
    (A312Specialization.a312_eq_or_mathieu23 (hG.involution_centralizer_sqtk hv2)
      B K hBK hKn ((primeRank_congr 3 e).trans hrank) hBc hBc4 b hemb)
  have hBnormal : B.Normal := hBKeq ▸ hKn
  have hHL : H ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLH).mp hBnormal
  rw [hI, ← hZ]
  exact hHL.trans (normalizer_le_normalizer_characteristic_image L (center L))

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.GlobalGeometry
