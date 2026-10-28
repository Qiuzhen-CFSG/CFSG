module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PlanePairAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.OriginalProductCoreWeight
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.OriginalProductModule

/-!
# The component core's weight in the original product alternative: structure at the original group

The component's invariant-plane normalizer is the actual outside
parabolic P. Its residual fixes only the component's constant line, so
it cannot centralize the original fixed generator d once d belongs to
the component module. Finite minimal descent and the proved uniqueness
of the outside parabolic identify the two literal subgroups.

The product commutator bound and the reduced omega action give reverse
residual normalization. If d had weight two in the component core, the
marked tetrahedral orbit calculation would put the original L₂ inside
N_G(K)=C_G(z). But L₂ fixes only the original constant line, contradicting
the escaping choice of z. Thus d has weight four.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/OriginalProductCoreWeight` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V K U : Subgroup G}

/-- Once the original fixed generator lies in the component core, the
component plane normalizer is the unique actual outside parabolic. -/
theorem component_core_plane_parabolic_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hK12 : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (DK : ChosenModule T K U) (mK : CoreMarking DK)
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hd : m.constant.val ∈ U)
    (z : G) (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hH : centralizer ({z} : Set G) = K ⊔ (T : Subgroup G))
    (P : Subgroup G) (hPH : P ⋖ centralizer ({z} : Set G))
    (hunique : ∀ Q ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      Q ≤ centralizer ({z} : Set G) → Q = P) :
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (mK.naturalPreimage W : Set G) ∧
      P = (K ⊔ (T : Subgroup G)) ⊓ normalizer (mK.naturalPreimage W : Set G) := by
  classical
  obtain ⟨W,hW,hT⟩ := LocalGeometry.exists_original_invariant_plane_at hK12 structural DK mK
  let Q := (K ⊔ (T : Subgroup G)) ⊓ normalizer (mK.naturalPreimage W : Set G)
  have hTQ : (T : Subgroup G) ≤ Q := le_inf le_sup_right hT
  have hQH : Q ≤ centralizer ({z} : Set G) := hH.symm ▸ inf_le_left
  have hQM : ¬ Q ≤ normalizer (L : Set G) := by
    intro hQM
    have hdR : m.constant.val ∈ centralizer ((pResidual 2 Q).map Q.subtype : Set G) := by
      apply mem_centralizer_iff.mpr
      intro a ha
      have haC : a ∈ centralizer ({m.constant.val} : Set G) := by
        rw [fixed_generator_centralizer_at h structural D m
          ⟨m.constant.property,m.constant_fixed⟩
          (fun hh => m.constant_ne_one (Subtype.ext hh))]
        exact hQM (map_subtype_le _ ha)
      exact mem_centralizer_singleton_iff.mp haC
    have hdK : m.constant.val ∈ centralizer (K : Set G) :=
      ((Solvable.original_second_flag_fixed DK mK W hW hT).le ⟨hd,hdR⟩).2
    apply hKM
    rw [←fixed_generator_centralizer_at h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun hh => m.constant_ne_one (Subtype.ext hh))]
    intro a ha
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hdK a ha)
  have hlocal : Q ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T hTQ hQH (Solvable.centralizer_mem_HOver hzT hz1)
  let S : Set (Subgroup G) := {Y | Y ∈ Chapter1.HOver G (T : Set G) ∧
    ¬ Y ≤ normalizer (L : Set G) ∧ Y ≤ Q}
  obtain ⟨R,hR⟩ := (Set.toFinite S).exists_minimalFor id S ⟨Q,hlocal,hQM,le_rfl⟩
  have hstar : R ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) := by
    refine ⟨⟨hR.1.1,hR.1.2.1⟩,?_⟩
    intro Y hY hYR
    exact hR.2 ⟨hY.1,hY.2,hYR.trans hR.1.2.2⟩ hYR
  have hPQ : P ≤ Q := hunique R hstar (hR.1.2.2.trans hQH) ▸ hR.1.2.2
  have hne : Q ≠ centralizer ({z} : Set G) := by
    intro he
    have hc := (Solvable.original_second_flag_coatom DK mK W hW hT).1
    apply hc
    change Q.subgroupOf (K ⊔ (T : Subgroup G)) = ⊤
    rw [he,hH,subgroupOf_self]
  exact ⟨W,hW,hT,((hPH.eq_or_eq hPQ hQH).resolve_right hne).symm⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
