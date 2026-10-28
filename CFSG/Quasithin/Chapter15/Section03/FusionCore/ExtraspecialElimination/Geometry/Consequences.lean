module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Sections
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.LocalAlgebra
/-!
# Quotient centralizers, proper kernels, and actual covers

The two cross-centralizations imply the quotient-centralizer equality in
15.3.49(f). F.9.13(5)'s noncentrality then makes D_gamma proper, as in (g).

For (n), equality of two star images is equivalent to a cover by the
smaller numerator and the exact section-centralizer kernel. Thus the
reversed star-image equality supplied by a successful F.9.17 symmetry
argument gives the required cover. This equivalence does not assert that
the original endpoint's three rank equalities imply the reversed equality;
that remains the geometric symmetry obligation.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.49(f), (g), (n), printed pp.1143–1144; F.9.17, printed p.324.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry
variable {G : Type*} [Group G]

/-- The remaining quotient-centralizer assertion of (f) and the strict kernel inclusion (g). -/
theorem centralizer_equality_and_proper_kernel
    (V ZS H Ug Vg Z Zg : Subgroup G) (hUV : Ug ≤ Vg)
    (hUgZ : Ug ≤ normalizer (Z : Set G))
    (hcrossH : sectionCentralizer (localSpan V H) Ug Zg ≤ centralizer (Vg : Set G))
    (hcrossG : sectionCentralizer Vg (localSpan ZS H) Z ≤ centralizer (localSpan V H : Set G))
    (hnoncentral : ¬ ⁅Ug, V⁆ ≤ Zg) :
    sectionCentralizer (localSpan V H) Ug Zg = localSpan V H ⊓ centralizer (Ug : Set G) ∧
      sectionCentralizer Ug (localSpan ZS H) Z < Ug := by
  refine ⟨commutatorPreimage_eq_relativeCentralizer _ _ _
    (hcrossH.trans (centralizer_le hUV)), ?_⟩
  have hDgEg : sectionCentralizer Ug (localSpan ZS H) Z ≤
      sectionCentralizer Vg (localSpan ZS H) Z := by
    exact le_commutatorPreimage ((commutatorPreimage_le Ug (localSpan ZS H) Z).trans hUV)
      (commutator_commutatorPreimage_le Ug (localSpan ZS H) Z hUgZ)
  have hc : sectionCentralizer Ug (localSpan ZS H) Z ≤ centralizer (V : Set G) :=
    (hDgEg.trans hcrossG).trans (centralizer_le (le_conjugateSpanBy V H))
  apply proper_of_crossCentralization _ Ug V (commutatorPreimage_le _ _ _) hc
  intro he
  exact hnoncentral (he ▸ bot_le)

/-- Star-image equality is precisely a cover by the smaller subgroup and the action kernel. -/
theorem starImage_eq_iff_centralizer_cover
    (K B Z X U : Subgroup G) [IsElementaryAbelian 2 B]
    (action : SectionAction K B Z) (hUX : U ≤ X) (hXK : X ≤ K) :
    starImage K U = starImage K X ↔ X = U ⊔ sectionCentralizer X B Z := by
  rw [sectionCentralizer_eq_core_intersection K B Z X action hXK]
  constructor
  · intro he
    apply le_antisymm
    · intro x hx
      have hxm : QuotientGroup.mk' (pCore 2 K) ⟨x, hXK hx⟩ ∈ starImage K U := by
        rw [he]
        exact mem_map_of_mem _ hx
      obtain ⟨u, hu, heq⟩ := hxm
      have hcore := QuotientGroup.eq.mp heq
      have hxu : (u : G)⁻¹ * x ∈ X ⊓ localTwoCore K := by
        refine ⟨X.mul_mem (X.inv_mem (hUX hu)) hx, ?_⟩
        exact mem_map_of_mem K.subtype hcore
      have hprod := (U ⊔ X ⊓ localTwoCore K).mul_mem ((show U ≤ U ⊔ (X ⊓ localTwoCore K) from le_sup_left) hu)
        ((show X ⊓ localTwoCore K ≤ U ⊔ (X ⊓ localTwoCore K) from le_sup_right) hxu)
      simpa using hprod
    · exact sup_le hUX inf_le_left
  · intro he
    apply le_antisymm
      (show starImage K U ≤ starImage K X from map_mono (fun _ hx => hUX hx))
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hpre : X ≤ ((starImage K U).comap (QuotientGroup.mk' (pCore 2 K))).map K.subtype := by
      rw [he]
      apply sup_le
      · intro u hu
        exact ⟨⟨u, hXK (hUX hu)⟩, mem_map_of_mem _ hu, rfl⟩
      · intro q hq
        obtain ⟨qK, hqK, hqEq⟩ := hq.2
        refine ⟨qK, ?_, hqEq⟩
        change QuotientGroup.mk' (pCore 2 K) qK ∈ starImage K U
        rw [show QuotientGroup.mk' (pCore 2 K) qK = 1 from (QuotientGroup.eq_one_iff _).mpr hqK]
        exact one_mem _
    obtain ⟨z, hz, heq⟩ := hpre hy
    have heq' : z = y := Subtype.ext heq
    exact heq' ▸ hz

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry
