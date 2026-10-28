module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreReducedCatalogue
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreSymmetricExtensions
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalModuleComparison
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicOrbit

/-!
# Cartan normalization allowing original symmetric Lie extensions

The cubic source input may return the previously handled reduced catalogue,
or a full original symplectic, G₂ or Ree automorphism extension. The new
endpoint-solvability transport excludes these original extensions directly,
including binary parameters and either orientation. The regular inputs retain
their full overlap and both commuting squares. No pure-model isomorphism or
outer-index bound is assumed.

The same selected R then feeds SourceCartanPrimeExclusion, together with the
independent quintic opposite-solvability theorem. The proved small-generation
and prime-pair construction give the original hglobal implication. Exhaustive
DGS recognition and quintic solvability remain explicit and are owned by
qt-dgs85-source-assembly and qt-f112-quintic-solvable-parabolics; the authorized
5.1.13 premise is unchanged. This does not assert the final source theorem.
Source: Aschbacher–Smith F.1.12 and 5.2.2, pp.263–264,647–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterF.GreenBook ChapterF.Source.DGS85.OriginalExtension
open ChapterF.Source.SuzukiContainment
open ChapterF.SourceCompletion.UnitaryNonbinary
universe u
variable {G : Type u} [Group G] [Finite G]

variable
    (hDGS : ∀ (T : Sylow 2 G) (L W : Subgroup G) (n : ℕ),
      Input KnownSimple.IsKnownSimple T L W n →
      ∀ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        1 < ChapterE.generationParameter H →
        ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 →
        ∀ A B : Subgroup G, CartanPair T L H A B → CartanLocalControl A H →
        (n = 2 ∨ n = 4 ∨ n = 8) →
        ∀ D : Subgroup G, CartanPrimeActor A H 3 D →
        ∀ R : Subgroup G, LocalData T L H B D R → SelectedSourceModels H R →
        (generated L H D R).pCoreIn 2 = ⊥ →
        let α := reducedAmalgam ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)
        let P := ChapterF.Source.parabolic ![D ⊔ Global.sourceS L H,R]
          (reducedSylow ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) 1
        Global.ConcreteAmalgamComparison α ∨
        (∃ (q : ℕ) (_ : IsPrimePow q) (_ : Even q) (M : UnitaryFive.Model q),
          Nonempty (Iso α M.amalgam) ∨ Nonempty (Iso α M.amalgam.reverse)) ∨
        (ClassicalGroup.IsPSL (P ⧸ pCore 2 P) 2 2 ∨
          Nonempty ((P ⧸ pCore 2 P) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
          Nonempty ((P ⧸ pCore 2 P) ≃* DihedralGroup 5)) ∨
        (∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
            (m : ℕ) (_ : 0 < m) (_ : Nat.card F = 2^m)
            (E : SourceExtension
              (Theory.SpecificGroups.SymplecticFour.pointParabolic (F := F))
              (Theory.SpecificGroups.SymplecticFour.planeParabolic (F := F))),
          Nonempty (Iso (zeroCoreAmalgam L H B D R) E.amalgam) ∨
          Nonempty (Iso (zeroCoreAmalgam L H B D R) E.amalgam.reverse)) ∨
        (∃ (F : Type u) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
            (m : ℕ) (_ : 0 < m) (_ : Nat.card F = 2^m)
            (E : SourceExtension (Atlas.G2.LieParabolicSetup.parabolic₁ (F := F))
              (Atlas.G2.LieParabolicSetup.parabolic₂ (F := F))),
          Nonempty (Iso (zeroCoreAmalgam L H B D R) E.amalgam) ∨
          Nonempty (Iso (zeroCoreAmalgam L H B D R) E.amalgam.reverse)) ∨
        (∃ (m : ℕ) (E : SourceExtension (ReeF4.Parabolics.parabolic m .suzuki)
            (ReeF4.Parabolics.parabolic m .linear)),
          Nonempty (Iso (zeroCoreAmalgam L H B D R) E.amalgam) ∨
          Nonempty (Iso (zeroCoreAmalgam L H B D R) E.amalgam.reverse)))
    (hquintic : ∀ K R S : Subgroup G, ChapterF.Source.HypothesisF11 ![K,R] S →
      IsQuasithin (ChapterF.Source.generated ![K,R] S) → S ≤ K → S.relIndex K = 5 →
        Group.IsSolvable (ChapterF.Source.parabolic ![K,R] S 1))
include hDGS hquintic

/-- The original extension restrictions discharge three more broad source
rows on the selected pair, before applying the independently supplied quintic result. -/
theorem sourceCartanPrimeExclusion_of_extension_sources :
    SourceCartanPrimeExclusion KnownSimple.IsKnownSimple G := by
  intro _ T L W n h H hH hgen hthree A B c hcontrol hn p D hd
  obtain ⟨R,d,hselected,hz,hf⟩ := source_prime_pair_zero_core h hH hgen hthree c hd
  rcases hd.prime with hp | hp
  · subst p
    rcases hDGS T L W n h H hH hgen hthree A B c hcontrol hn D hd R d hselected hz with
      hc | ⟨q,hq,heven,M,he⟩ | ht | hsp | hg2 | hree
    · exact d.zeroCore_not_reduced_comparison h hH c hd hz hc
    · exact d.zeroCore_not_reduced_unitaryFive h hH c hd hz hq heven M he
    · exact d.zeroCore_not_reduced_small_type h hH c hd hz ht
    · obtain ⟨F,_,_,_,m,hm,hF,E,he⟩ := hsp
      have hn := d.zeroCore_not_symplectic_sourceExtension h hH c hd hz hm hF E
      exact he.elim (fun ⟨e⟩ => hn.1 ⟨e.toParabolicEquiv⟩)
        (fun ⟨e⟩ => hn.2 ⟨e.toParabolicEquiv⟩)
    · obtain ⟨F,_,_,_,m,hm,hF,E,he⟩ := hg2
      have hn := d.zeroCore_not_g2_sourceExtension h hH c hd hz hm hF E
      exact he.elim (fun ⟨e⟩ => hn.1 ⟨e.toParabolicEquiv⟩)
        (fun ⟨e⟩ => hn.2 ⟨e.toParabolicEquiv⟩)
    · obtain ⟨m,E,he⟩ := hree
      have hn := d.zeroCore_not_ree_sourceExtension h hH c hd hz m E
      exact he.elim (fun ⟨e⟩ => hn.1 ⟨e.toParabolicEquiv⟩)
        (fun ⟨e⟩ => hn.2 ⟨e.toParabolicEquiv⟩)
  · subst p
    exact d.right_parabolic_not_solvable hz
      (hquintic _ _ _ hf (h.qtke.quasithin.subgroup _) le_sup_right
        (Input.prime_left_index h hH c hd))

/-- The exact local-to-global normalization, with only the two independent
remaining source outputs and the authorized earlier 5.1.13 theorem explicit. -/
theorem cartan_normalizes_of_extension_sources
    (h513 : SourceLocalCartanEscape KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H) :
    A ≤ normalizer (residual H : Set G) :=
  cartan_normalizes_of_prime_sources sourceCartanSmallGeneration
    (sourceCartanPrimeExclusion_of_extension_sources hDGS hquintic) h513
    h hH hgen hthree c hcontrol

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
