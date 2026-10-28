module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.Closure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Source

/-!
# Applying invariant-constituent reselection to the original Hall action

The seed reconstruction supplies the literal module geometry and moved
minimality consumed by the completed recognition theorem. The natural and
Suzuki Hall actions are excluded; the orthogonal row supplies an injective
map from the actual Hall action image to the two norm-one factors, giving
the exponent bound on the original Hall subgroup.

Seed separation and existence of the N_M(L)-invariant L-Irr⁺ constituent
remain with qt-d-10-nona5-central-hall-orders. These conditional applications
do not discharge SeedAnalysisAt or SourceNonnormalCentralHallAt.
Source: Aschbacher--Smith D.3.21(3), 3.2.6, and 10.2.3,
printed pp.204--207,581,745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
universe u
variable {G : Type u} [Group G] [Finite G] (T : Sylow 2 G)

/-- The original Hall consumer can use crossed movement and L-minimality
instead of constructing the three seed clauses separately. Their source proofs
remain with qt-d-10-nona5-central-hall-orders. -/
theorem hall_exponent_of_moved_minimal_and_crossed
    {L : Subgroup G} (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hmin : MovedMinimal D)
    (hcross : ⁅D.fullModule,L⁆ ≤
      centralizer (L.map (MulAut.conj t).toMonoidHom : Set G)) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1 := by
  have hs := (separatedSeed_iff_moved_minimal_and_crossed D c ht htn).mpr ⟨hmin,hcross⟩
  obtain ⟨geometry,_⟩ := geometry_and_minimality_of_separatedSeed D ht htn hs
  obtain ⟨hlocal,hfull⟩ := cubic_bounds D c
  have row := source_movedRecognitionAt L D H B c hnot (component_model D c.nonnormal)
    hlocal hfull geometry hmin
  have hall := HallGeometry.source_hallGeometryAt T L D H B c geometry
  cases row with
  | natural r hr e coordinates =>
    exact (hall.natural_excluded r hr e coordinates.some).elim
  | orthogonal n hn e coordinates =>
    obtain ⟨e',⟨p⟩⟩ := hall.orthogonal n hn e coordinates.some
    obtain ⟨f,hf⟩ := p.image_embedding c.faithful
    exact ⟨n,hn,exponent_dvd_of_image_embedding D B c.hall_le c.faithful n f hf⟩
  | suzuki m hm e coordinates =>
    exact (hall.suzuki_excluded m hm e coordinates.some).elim

/-- Apply a replacement constituent directly to the literal Hall exponent.
Existence of separation and this constituent remains with the central Hall
assembly owner qt-d-10-nona5-central-hall-orders. -/
theorem hall_exponent_of_stabilizer_invariant_constituent
    {L : Subgroup G} (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (I : Submodule (ZMod 2)
      (Additive (ReducedNormal.ModuleGroup (Chapter3.Section02.localJoin T L))))
    (hI : Representation.BinaryOffender.IsIrrPlus
      (ReducedNormal.representation (Chapter3.Section02.localJoin T L))
      (L.subgroupOf (Chapter3.Section02.localJoin T L)) I)
    (hIW : ReducedNormal.subspaceImage (Chapter3.Section02.localJoin T L) I ≤ ⁅D.fullModule,L⁆)
    (hstable : D.maximalLocal ⊓ normalizer (L : Set G) ≤
      normalizer (ReducedNormal.subspaceImage (Chapter3.Section02.localJoin T L) I : Set G)) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1 :=
  hall_exponent_of_moved_minimal_and_crossed T D c hnot ht htn
    (movedMinimal_of_stabilizer_invariant_constituent D c ht htn hsep I hI hIW hstable)
    (full_moved_centralizes_opposite_of_seed_separated D ht htn hsep)

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
