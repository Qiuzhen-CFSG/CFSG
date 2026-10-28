module
public import CFSG.Quasithin.Chapter10.SourceA5ZeroBaumannProduct
public import CFSG.Quasithin.Chapter10.SourceA5ZeroElementaryGeometry
public import Theory.SpecificGroups.DihedralProduct.AmbientCentralEnlargements

/-!+# The actual central enlargements in the zero-center A₅ branch

The original Baumann product supplies four dihedral coordinates. Transporting
the canonical central enlargements back to the original group gives four
distinct subgroups, permuted by the original Sylow subgroup. The intersections
with the original module have order 32 and generate it, so their common
normalizer lies in the original maximal local subgroup.

Source: Aschbacher–Smith, 10.2.1, printed p.743.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher DihedralProductCanonical
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- All geometry needed by the normalizer argument, on the original ambient
subgroups and with no extra factor-marking premise. -/
theorem source_a5_zero_central_enlargements
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ eR : ChapterB.baumann (T : Subgroup G) ≃* (Fin 4 → DihedralGroup 4),
      let S := ChapterB.baumann (T : Subgroup G)
      let F := ambientGamma S eR
      Function.Injective F ∧
        (∀ i, F i ≤ S) ∧
        (∀ t ∈ (T : Subgroup G), ∀ i,
          ∃ j, (F i).map (MulAut.conj t).toMonoidHom = F j) ∧
        (∀ i, Nat.card (D.moduleSubgroup ⊓ F i : Subgroup G) = 32) ∧
        (⨆ i, D.moduleSubgroup ⊓ F i) = D.moduleSubgroup ∧
        (⨅ i, normalizer (F i : Set G)) ≤ D.maximalLocal := by
  obtain ⟨eP⟩ := source_a5_zero_original_baumann_dihedral_four_product D e hn hout hz
  let S := ChapterB.baumann (T : Subgroup G)
  let eR : S ≃* (Fin 4 → DihedralGroup 4) := eP.trans fourProductEquiv
  have hTS : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (T : Subgroup G).le_normalizer.trans (normalizer_le_normalizer_baumann _)
  have hTF : ∀ t ∈ (T : Subgroup G), ∀ i,
      ∃ j, (ambientGamma S eR i).map (MulAut.conj t).toMonoidHom =
        ambientGamma S eR j := by
    intro t ht i
    exact ⟨normalizerFactorAction S eR ⟨t,hTS ht⟩ i,
      map_ambientGamma S eR ⟨t,hTS ht⟩ i⟩
  obtain ⟨hc,hs⟩ := source_a5_zero_module_gamma_geometry D e hn hout hz eR
  exact ⟨eR,ambientGamma_injective S eR,ambientGamma_le S eR,hTF,hc,hs,
    source_a5_zero_canonical_gamma_kernel_le D e hn hout hz eR hTF⟩

end CFSG.Quasithin.Chapter10
