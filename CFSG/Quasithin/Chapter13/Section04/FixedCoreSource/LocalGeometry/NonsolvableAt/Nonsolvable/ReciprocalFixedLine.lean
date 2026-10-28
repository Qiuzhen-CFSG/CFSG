module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CentralFourAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentFixedAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentNaturalResidualAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSeedAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ReciprocalFixedLine
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.WeightFourResidual
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentContainment
public import Theory.GroupTheory.Commutator.QuotientCenterCard

/-!
# Fixed-line placement in the reciprocal augmentation A₆ residual: structure at the original group

For a nonfixed vector of an augmentation core, either it or its product
with the fixed generator has weight four. The weight-four double
commutator lies in the literal point residual. Consequently a point belongs
to that residual whenever the fixed generator does.

In the selected augmentation A₆ branch, the original weight-four calculation
puts z in J = O^{3′}(C_L(z)). The component marking identifies its fixed
line with ⟨z⟩, and the reciprocal residual is this same J. Applying the
point calculation to the original fixed generator d gives C_V(L) ≤ J.
Thus P C_V(L), where P=[V,J], is the actual sixteen-group in O₂(J), and
its image in the literal quotient O₂(J)/⟨z⟩ is central of order eight.
The final application derives the original weight-four condition from the
same mixed conjugator and both reciprocal radical containments.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/ReciprocalFixedLine` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V K : Subgroup G}

/-- In the actual selected augmentation A₆ branch, the original weight-four
point puts the entire original fixed line in the common reciprocal residual. -/
theorem original_weight_four_reciprocal_fixed_line_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G)) (hw : m.weight z = 4)
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    V ⊓ centralizer (L : Set G) ≤ Solvable.firstCentralizerResidual L z.val := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let J := Solvable.firstCentralizerResidual L z.val
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨DK,⟨mK⟩,hfix,_,_,_,_⟩ := component_core_marking_of_source_fixed_at
    h₀ h structural m h1332 fixed hindex z.property hzT hz1 hK.1 hHN hKM hfK hfixed
  have hzJ : z.val ∈ J := ((Subgroup.commutator_le_sup _ _).trans (sup_le (pCoreIn_le 2 J) (pCoreIn_le 2 J)))
    (original_weight_four_residual_sixteen D m eL z hzL hw).2.1
  have hsplit : conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K = U := by
    have hh := component_seed_split h₀ hzT hz1 hK.1 (h1332 K hfK).1
    rw [component_full_fixed_line_at h structural z.val hz1 hzT hindex K hK.1 hKM,
      sup_eq_left.mpr (show zpowers z.val ≤ U from hfix.symm ▸ inf_le_left)] at hh
    exact hh
  have hdU : m.constant.val ∈ U := hsplit ▸
    le_conjugateSpanBy _ _ (m.constant_mem_central_four_at h structural).2
  have hdK : m.constant.val ∉ centralizer (K : Set G) := by
    intro hd
    apply hKM
    rw [←fixed_generator_centralizer_at h structural D m
      ⟨m.constant.property,m.constant_fixed⟩
      (fun he => m.constant_ne_one (Subtype.ext he))]
    exact fun k hk => mem_centralizer_singleton_iff.mpr (hd k hk)
  have hrec := component_reciprocal_residual_of_ordinary_six_at h₀ h structural m hzT hz1
    hK hHN (component_quotient_quasisimple h1332 hfK) eK eL
  have hcJ : mK.constant.val ∈ J := (zpowers_le.mpr hzJ)
    (hfix.le ⟨mK.constant.property,mK.constant_fixed⟩)
  have hdJ : m.constant.val ∈ J := by
    have hc : mK.constant.val ∈ Solvable.firstCentralizerResidual K m.constant.val :=
      hrec.symm ▸ hcJ
    have hh := core_point_mem_residual_of_fixed_mem DK mK eK ⟨m.constant.val,hdU⟩ hdK hc
    rwa [hrec] at hh
  intro x hx
  rcases (m.fixed_iff ⟨x,hx.1⟩).mp hx.2 with he | he
  · have he' : x = 1 := congrArg Subtype.val he
    rw [he']
    exact one_mem J
  · have he' : x = m.constant.val := congrArg Subtype.val he
    rw [he']
    exact hdJ

open Section03.Noncentrality.SupercriticalSource
variable {A B : Subgroup G}

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
