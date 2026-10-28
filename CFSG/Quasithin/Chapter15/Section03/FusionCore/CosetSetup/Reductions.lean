module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Actions
public import Stellmacher.TwoResidualIdentification
public import Theory.GroupTheory.TwoLocalCoreObstruction

/-!
# Elementary reductions in 15.3.48–49

The action of a subgroup of C_M(V)T on V has two-group image. Its actual
two-residual therefore centralizes V, giving 15.3.49(1). The factorization
is the conclusion of 15.3.7; no centralizer bound on the residual is assumed.

The uniqueness of the maximal two-local overgroup of YT kills the two-core
of ⟨YT,H⟩. Together with the normalizer and conjugate-centralization clauses
of 15.3.46 this proves the geometric clauses (c), (d), and (e) of F.9.1.
The preamble, irreducibility, and normal-core clause still need verification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1141–1142.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup

private theorem residual_le_kernel {G K : Type*} [Group G] [Group K] [Finite G]
    (X : Subgroup G) (f : X →* K) (hp : IsPGroup 2 f.range) :
    Stellmacher.twoResidualSubgroup X ≤ f.ker := by
  rw [Stellmacher.SectionThree.twoResidualSubgroup_eq_hktPResidual']
  exact BenderSuzuki.External.hktPResidual_le f.ker inferInstance
    (hp.of_equiv (QuotientGroup.quotientKerEquivRange f).symm)

/-- A two-group supplement accounts for the whole action, so the two-residual is in the centralizer. -/
theorem residual_centralizes_of_two_supplement
    {G : Type*} [Group G] [Finite G]
    (X V T : Subgroup G) (hX : X ≤ normalizer (V : Set G))
    (hT : T ≤ normalizer (V : Set G)) (hTp : IsPGroup 2 T)
    (hfactor : ∀ x ∈ X, ∃ c ∈ centralizer (V : Set G), ∃ t ∈ T, c * t = x) :
    Stellmacher.twoResidualAmbient X ≤ X ⊓ centralizer (V : Set G) := by
  let f : X →* MulAut V := V.normalizerMonoidHom.comp (inclusion hX)
  let g : T →* MulAut V := V.normalizerMonoidHom.comp (inclusion hT)
  have hrange : f.range ≤ g.range := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨c, hc, t, ht, he⟩ := hfactor x x.property
    refine ⟨⟨t, ht⟩, ?_⟩
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change t * (v : G) * t⁻¹ = (x : G) * v * (x : G)⁻¹
    rw [← he]
    have htv : t * (v : G) * t⁻¹ ∈ V := (hT ht v).mp v.property
    have hctv := hc _ htv
    calc
      t * (v : G) * t⁻¹ = c * (t * (v : G) * t⁻¹) * c⁻¹ := by
        rw [← hctv]; group
      _ = (c * t) * (v : G) * (c * t)⁻¹ := by group
  have hp : IsPGroup 2 f.range :=
    (hTp.of_surjective g.rangeRestrict g.rangeRestrict_surjective).to_le hrange
  rintro x ⟨r, hr, rfl⟩
  refine ⟨r.property, ?_⟩
  have hk := residual_le_kernel X f hp hr
  have hk' : inclusion hX r ∈ V.normalizerMonoidHom.ker := hk
  rw [normalizerMonoidHom_ker] at hk'
  exact hk'

/-- Source 15.3.49(1), from the product factorization in 15.3.7 and the local containment H ≤ M_c. -/
theorem lemma_15_3_49_1
    {G : Type*} [Group G] [Finite G]
    (M Mc H V : Subgroup G) (T : Sylow 2 G)
    (hM : M ≤ normalizer (V : Set G)) (hTM : (T : Subgroup G) ≤ M)
    (hH : H ≤ Mc)
    (hfactor : ∀ x ∈ M ⊓ Mc,
      ∃ c ∈ M ⊓ centralizer (V : Set G), ∃ t ∈ (T : Subgroup G), c * t = x) :
    Stellmacher.twoResidualAmbient (M ⊓ H) ≤ (M ⊓ H) ⊓ centralizer (V : Set G) :=
  residual_centralizes_of_two_supplement (M ⊓ H) V T (inf_le_left.trans hM)
    (hTM.trans hM) T.isPGroup' (fun x hx => by
      obtain ⟨c, hc, t, ht, he⟩ := hfactor x ⟨hx.1, hH hx.2⟩
      exact ⟨c, hc.2, t, ht, he⟩)

/-- F.9.1(c), (d), and (e) for the Chapter 15 setup. The earlier weak-closure conclusion proves (e) already from its first commutator premise. -/
theorem coset_geometric_clauses
    {G : Type*} [Group G] [Finite G]
    (M Y T H V ZS : Subgroup G)
    (hM : M = normalizer (V : Set G))
    (hZS : normalizer (ZS : Set G) ≤ M) (hZSV : ZS ≤ V)
    (hunique : Chapter4.UniqueMaximalOvergroup (Y ⊔ T) M) (hH : ¬ H ≤ M)
    (hweak : ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ M →
      V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
    H ⊓ normalizer (ZS : Set G) ≤ H ⊓ normalizer (V : Set G) ∧
      pCore 2 ((Y ⊔ T) ⊔ H : Subgroup G) = ⊥ ∧
      ∀ g : G, ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≤
          V ⊓ V.map (MulAut.conj g).toMonoidHom →
        ⁅ZS, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ ∧
          ⁅ZS.map (MulAut.conj g).toMonoidHom, V⁆ = ⊥ := by
  refine ⟨inf_le_inf_left H (hZS.trans_eq hM),
    Theory.GroupTheory.twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup
      (Y ⊔ T) H M hunique.2.2 hH, ?_⟩
  intro g hg
  have hn : V.map (MulAut.conj g).toMonoidHom ≤ M := by
    rw [hM]
    exact le_normalizer_iff_commutator_le_left.mpr (hg.trans inf_le_left)
  have hc := hweak g hn
  constructor
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    exact hZSV.trans (le_centralizer_iff.mp hc)
  · apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (Subgroup.map_mono hZSV).trans hc

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup

end
