module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.RankReduction.NaturalRank
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound.OddMover
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
/-!
# Solvability and odd rank in the natural source configuration

The original residual is normal in C(V₂), hence subnormal in N(V₂).
Quasithinness and the K-group hypothesis provide the genuine SQTK two-core
quotient there. The actual odd mover and two-group intersection then
exclude every nonsolvable component. Together with NaturalRank this is
the whole conclusion of 13.3.14(b) in the natural A₆/3.A₆ branch.

The chosen-module TI and normalizer placement, local uniqueness, point
overgroup escape and original cubic plane image remain earlier-source
inputs. The independent Fitting and component reductions (d)–(g) are not
asserted here. Source: Aschbacher–Smith, printed p.891.
-/
@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V P E U M H : Subgroup G}
  (d : NaturalSetup T L V P E U M H)
include d
/-- Solvability on the actual plane normalizer, using its genuine SQTK quotient. -/
theorem natural_residual_solvable_of_intersection (g : G)
    (hgE : g ∈ normalizer (E : Set G)) (hodd : Odd (orderOf g))
    (hI : let Y := centralizingResidual (conjugateSpanBy U H)
      IsPGroup 2 (Y ⊓ Y.map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    Group.IsSolvable (centralizingResidual (conjugateSpanBy U H)) := by
  let Y := centralizingResidual (conjugateSpanBy U H)
  let C := centralizer (E : Set G)
  let N := normalizer (E : Set G)
  have hYC : Y ≤ C :=
    (centralizingResidual_le_seed_centralizer U H).trans (centralizer_le d.plane_le_seed)
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer _
  have hCEH : C ≤ H := by
    rw [d.first_normalizer]
    exact (centralizer_le d.line_le_plane).trans (Subgroup.centralizer_le_normalizer _)
  have hCY : C ≤ normalizer (Y : Set G) :=
    hCEH.trans (normalizes_centralizingResidual U H)
  let A := Y.subgroupOf N
  let B := C.subgroupOf N
  have hAB : A ≤ B := fun _ hx => hYC hx
  have hBN : B.Normal := inferInstance
  have hAN : (A.subgroupOf B).Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hAB).mpr
    apply le_normalizer_iff.mpr
    intro c hc a ha
    exact le_normalizer_iff.mp hCY c.val hc a.val ha
  have hAsub : A.IsSubnormal := .step A B hAB hBN.isSubnormal hAN
  let gn : N := ⟨g,hgE⟩
  have hgn : Odd (orderOf gn) := by
    rw [← orderOf_injective N.subtype N.subtype_injective]
    exact hodd
  have hIn : IsPGroup 2 (A ⊓ A.map (MulAut.conj gn).toMonoidHom : Subgroup N) := by
    apply hI.comap_subtype.to_le
    rintro x ⟨hx,⟨y,hy,hyx⟩⟩
    exact ⟨hx,⟨y.val,hy,congrArg Subtype.val hyx⟩⟩
  have hne : E ≠ ⊥ := by intro h; have hc := d.plane_card; simp [h] at hc
  have htwo : IsPGroup 2 E := IsPGroup.of_card (n := 2) d.plane_card
  have hQ := Chapter1.Section02.uniqueness_local_quotient_sqtk d.counterexample.qtke
    (Chapter1.mem_H_of_isTwoLocal (show IsTwoLocal N from ⟨E,hne,htwo,rfl⟩))
  let := ChapterA.Section03.ComponentOrbitBound.isSolvable_of_subnormal_odd_conjugate_intersection
    hQ A hAsub gn hgn hIn
  exact Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (hYC.trans hCN)).symm.toMonoidHom)
    (subgroupOfEquivOfLe (hYC.trans hCN)).symm.injective

/-- The natural A₆/3.A₆ branch of the source reduction 13.3.14(b). -/
theorem natural_residual_solvable_and_odd_rank [Group.IsPerfect L]
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨ V.map (MulAut.conj g).toMonoidHom = V)
    (hNVL : normalizer (V : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M)
    (hescape : ¬ H ≤ M)
    (X : Subgroup G) (hXL : X ≤ L)
    (hx : letI := Section05.AmbientSource.source_plane_isKleinFour d
      Nat.card ((X.subgroupOf (normalizer (E : Set G))).map
        (Section05.AmbientSource.planeAction E)) = 3) :
    let Y := centralizingResidual (conjugateSpanBy U H)
    Group.IsSolvable Y ∧ ∀ p : ℕ, p.Prime → Odd p → primeRank p Y ≤ 1 := by
  obtain ⟨g,hg,hodd,hgE,_,hjoin⟩ := natural_odd_plane_mover d X hXL hx
  refine ⟨natural_residual_solvable_of_intersection d g hgE hodd ?_,?_⟩
  · exact natural_residual_intersection_isTwoGroup d hTI hNVL hunique hescape
      ⟨g,hXL hg⟩ hgE hjoin
  · exact natural_residual_odd_rank d hTI hNVL hunique hescape X hXL hx
end CFSG.Quasithin.Chapter13.Section03.Noncentrality
