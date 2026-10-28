module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSieve

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The local seed sieve on the original Chapter 12 module

Use the whole reduced subgroup R2(LT) to instantiate the generic source
input. The actual escaping Cartan then produces the source seed and
containing component. The moved branch retains two explicitly exchanged
components and identifies the seed quotient as PSL2(4); the unmoved branch
has a proper normal containing component. The actual PSL3(4) residual is
excluded without a separate graph-action hypothesis.

This supplies the original chosen-module applications of the opening
sieve reductions. The A7/J2/M23 shortlist and escaping cubic, followed by
the A7 contradiction and full A5-module recognition, remain with the local
Cartan classification owner before the unchanged relocation assembly applies.

Source: Aschbacher--Smith, 5.1.10--13 and 12.2.2, pp.634--638,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The local source seed reduction at the original whole reduced subgroup.
The paired alternative identifies the seed quotient, not the whole residual. -/
theorem rankOne_local_cartan_escape_seed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
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
            residual H < X)) :=
  localCartan_escape_seed_reduction
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl)
    hH hgen c hY hescape

/-- The same chosen-module hypotheses construct the unique local container
and its actual normal orbit, without a seed-normalization assumption. -/
theorem rankOne_local_cartan_escape_embedding
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (_c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃! C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  exact LocalSieve.exists_escape_seed_embedding hi.qtke hi.sylow_normalizes
    hH hgen hY hescape

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
