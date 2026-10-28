module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Recognition
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Centralizers
public import Theory.GroupTheory.ElementaryThompsonInvolutionFusion

/-!
# The terminal source argument from intrinsic involution geometry

This application derives both ambient involution fusion and full
commuting-product centralizer containment. Burnside fusion uses the
abelian J(T) and representatives for the involution classes in it. The
characteristic-two argument applies to products that are conjugate inside
E to Sylow-central involutions. The literal fixed line supplies d and
C_G(d)=N_G(L), and the existing ZD recognition then gives PSp₆(2).

The local product, the marked C₃ system, its Thompson normalizer, and
the intrinsic symplectic involution calculations still have to be
constructed. This is their assembly interface, not an unconditional proof
of 13.4.8–9. Earlier Chapter12/13.3 premises remain with the original
fixed-core assembly. Source: Aschbacher–Smith 13.4.9, pp.906–907.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open SolvableCentralizerC3 Quasithin.I5
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original vertices and the original common Sylow subgroup are part
of the marking. Construction of this record is the local geometry obligation. -/
structure MarkedC3 (T : Sylow 2 G) (L : Subgroup G) (z : G) (H₀ : Subgroup G) where
  system : DSystem .C3 (generated (normalizer (L : Set G)) z H₀)
  first : system.family 0 = (normalizer (L : Set G)).subgroupOf
    (generated (normalizer (L : Set G)) z H₀)
  second : system.family 1 = (centralizer ({z} : Set G)).subgroupOf
    (generated (normalizer (L : Set G)) z H₀)
  third : system.family 2 = H₀.subgroupOf (generated (normalizer (L : Set G)) z H₀)
  chamber : system.T = (T : Subgroup G).subgroupOf
    (generated (normalizer (L : Set G)) z H₀)

/-- Intrinsic local involution geometry suffices: neither ambient fusion nor
any full product-centralizer containment is a premise. -/
theorem isPSp_of_thompson_local_data
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
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
  apply isPSp_of_geometry_and_fusion h₀ h structural D m z H₀ C.system hf
  intro d hd hd1 e he hde hcomm hne
  have hd2 : d ^ 2 = 1 := by
    let := D.elementary
    exact elemPow_eq_one_of_isElementaryAbelian d hd.1
  have hdi : BenderSuzuki.PFAppendixIII.IsInvolution d := ⟨hd1, hd2⟩
  have hdT := D.le_sylow hd.1
  have hdE := hTE hdT
  have hdc := fixed_generator_centralizer h structural D m hd hd1
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
