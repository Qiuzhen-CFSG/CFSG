module

public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.Containers
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.Pairs
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalSieve.LinearExclusion

/-!
# Opening source reductions for the local Cartan sieve

Apply the E.2.2 seed construction and the source embedding and uniqueness
theorems to the original universal Input, H-star member, Cartan pair and Y.
The graph source excludes a PSL3(4) residual. A moved seed has a PSL2(4)
quotient and gives an actual exchanged pair generating the residual.
An unmoved seed equals the residual and lies properly in a normal relative
C-component of Y. The companion container theorem also retains the unique
embedding and its normal Sylow orbit before the unmoved/moved split.

These are proved reductions of the sieve. The remaining model exclusions,
the escaping inverted cubic, A7 exclusion and whole-module recognition
remain with the local Cartan classification owner. No LocalCartanSieve or
SourceLocalCartanEscape inhabitant is asserted here.

Source: Aschbacher--Smith, 5.1.10--13, pp.634--638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The source escape has a genuine seed. A moved seed has a PSL2(4) quotient; if the
seed is the entire residual, it has a proper normal containing C-component.
The exceptional linear residual is excluded by the proved graph source. -/
theorem localCartan_escape_seed_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (_c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    (¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) ∧
      ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
        IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
        K ∈ Chapter1.L G (T : Subgroup G) ∧
        componentOrbit K (T : Subgroup G) = residual H ∧
        ((K < residual H ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
          ∃ t ∈ (T : Subgroup G), K.map (MulAut.conj t).toMonoidHom ≠ K ∧
            residual H = K ⊔ K.map (MulAut.conj t).toMonoidHom ∧
            ((K.map (MulAut.conj t).toMonoidHom).subgroupOf H).IsCComponent ∧
            (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = K) ∨
          (K = residual H ∧ ∃ X : Subgroup G, X ≤ Y ∧
            (X.subgroupOf Y).IsCComponent ∧ (X.subgroupOf Y).Normal ∧
            residual H < X)) := by
  refine ⟨LocalSieve.not_linear_four_residual_of_escape h.qtke
    h.sylow_normalizes hH hY hescape, ?_⟩
  obtain ⟨K, hKH, hK, hq, hg, hl, ho, he | hm⟩ :=
    LocalSieve.exists_escape_seed h.qtke h.sylow_normalizes hH hgen hY hescape
  · refine ⟨K, hKH, hK, hq, hg, hl, ho, Or.inr ⟨he, ?_⟩⟩
    exact LocalSieve.exists_proper_normal_component h.qtke hH.1.1.2
      (he ▸ hl) hY hescape
  · exact ⟨K, hKH, hK, hq, hg, hl, ho, Or.inl ⟨hm.1, hm.2,
      LocalSieve.moved_seed_pair h.qtke hKH hH.1.1.2 hH.1.1.1 hK ho hm.1.ne⟩⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
