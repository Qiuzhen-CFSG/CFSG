module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableAt.Recognition
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Terminal

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Recognition
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Centralizers
public import Theory.GroupTheory.ElementaryThompsonInvolutionFusion

/-!
# The terminal source argument from intrinsic involution geometry: structure at the original group

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
solvable-centralizer recognition on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907;
see the original `Solvable/Terminal` proof for the local step.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open SolvableCentralizerC3 Quasithin.I5
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Intrinsic local involution geometry suffices: neither ambient fusion nor
any full product-centralizer containment is a premise. -/
theorem isPSp_of_thompson_local_data_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : G) (H₀ : Subgroup G) (C : MarkedC3 T L z H₀)
    (hJ : IsMulCommutative (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)))
    (hn : normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤
      generated (normalizer (L : Set G)) z H₀)
    (hr : ∀ a ∈ generated (normalizer (L : Set G)) z H₀,
      BenderSuzuki.PFAppendixIII.IsInvolution a →
      ∃ c ∈ generated (normalizer (L : Set G)) z H₀,
        MulAut.conj c a ∈ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G))
    (hpair : ∀ d ∈ V ⊓ centralizer (L : Set G), d ≠ 1 →
      ∀ e ∈ generated (normalizer (L : Set G)) z H₀,
      (∃ c ∈ generated (normalizer (L : Set G)) z H₀, MulAut.conj c d = e) →
      Commute d e → e ≠ d →
      ∃ c ∈ generated (normalizer (L : Set G)) z H₀,
        (T : Subgroup G) ≤ centralizer ({MulAut.conj c (d * e)} : Set G)) :
    ClassicalGroup.IsPSp G 3 2 := by
  let E := generated (normalizer (L : Set G)) z H₀
  let := hJ
  have hf := Stellmacher.involution_fusion_of_abelian_maxJ T E hn hr
  have hME : normalizer (L : Set G) ≤ E := first_le_generated _ _ _
  have hTE : (T : Subgroup G) ≤ E := D.sylow_normalizes_component.trans hME
  apply isPSp_of_geometry_and_fusion_at h₀ h structural D m z H₀ C.system hf
  intro d hd hd1 e he hde hcomm hne
  have hd2 : d ^ 2 = 1 := by
    let := D.elementary
    exact elemPow_eq_one_of_isElementaryAbelian d hd.1
  have hdi : BenderSuzuki.PFAppendixIII.IsInvolution d := ⟨hd1, hd2⟩
  have hdT := D.le_sylow hd.1
  have hdE := hTE hdT
  have hdc := fixed_generator_centralizer_at h structural D m hd hd1
  have hdC : d ∈ centralizer (T : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mp (hdc.symm ▸ D.sylow_normalizes_component ht)
  have he2 : e ^ 2 = 1 := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hde
    rw [← hg]
    change (MulAut.conj g d) ^ 2 = 1
    rw [← map_pow, hd2, map_one]
  have hprod : (d * e) ^ 2 = 1 := by rw [hcomm.mul_pow, hd2, he2, one_mul]
  have hprod1 : d * e ≠ 1 := by
    intro heq
    apply hne
    exact (eq_inv_of_mul_eq_one_right heq).trans hdi.inv_eq_self
  apply centralizer_le_of_conjugate_sylow_central E T (h₀.qtke.evenCharacteristic T)
    hTE d hdT hdC (fun b hb hdb => hf d hdE b hb hdi hdb) (hdc.le.trans hME)
    (orderOf_eq_prime hprod hprod1)
  exact hpair d hd hd1 e he (hf d hdE e he hdi hde) hcomm hne

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
