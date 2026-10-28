module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure.KernelBound.Level6
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.LocalKernel

/-!
# The actual HS pair kernel has at most 64 elements

Every element of the pair kernel in `localGroup 0` lies in the existing
certified HS stabilizer chain. At each level, commutation with `e0` and
setwise preservation of its fixed-letter pairs force the necessary screen.
The six exhaustive transitions leave 64 permutations, and the last residual
group is trivial. Choosing the resulting representative embeds the kernel
in `Fin 64`, proving its cardinality bound without any centralizer-order or
quotient assumption.

Source: Aschbacher–Smith 16.1.5(10), printed p.1172; GLS3 Table 5.3m,
printed p.274. This proves full-kernel coverage needed by `KernelWitnesses`;
recognition of the quotient is a separate obligation.
-/

namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.OrderCertificate
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore (core mem_core_iff)
open Sporadic.LeechRelated.HS.EvenLocalCandidates.LargeElementaryCentralizers (decompose)
open KernelBound

private theorem pair_covered (g : Perm) (hg : g ∈ H0)
    (hc : (e0 : Perm) * g = g * (e0 : Perm)) (hp : PairCondition g) :
    ∃ i : Fin 64, g = prefix6 i := by
  have h0 : ∃ i, ∃ h ∈ H0, g = prefix0 i * h := ⟨0, g, hg, (one_mul g).symm⟩
  have h1 := advance H0 H1 prefix0 prefix1 rep0 color1 base1
    (fun _ hh => decompose gen0 inv0 inv0_spec gen1 inv1 inv1_spec
      rep0 act0 factor0 0 rep0_base step0 hh)
    (fun _ hh => residual1_spec hh)
    (fun i j ht => ⟨next1 i j, transition1 i j ht⟩) hc hp h0
  have h2 := advance H1 H2 prefix1 prefix2 rep1 color2 base2
    (fun _ hh => decompose gen1 inv1 inv1_spec gen2 inv2 inv2_spec
      rep1 act1 factor1 0 rep1_base step1 hh)
    (fun _ hh => residual2_spec hh)
    (fun i j ht => ⟨next2 i j, transition2 i j ht⟩) hc hp h1
  have h3 := advance H2 H3 prefix2 prefix3 rep2 color3 base3
    (fun _ hh => decompose gen2 inv2 inv2_spec gen3 inv3 inv3_spec
      rep2 act2 factor2 0 rep2_base step2 hh)
    (fun _ hh => residual3_spec hh)
    (fun i j ht => ⟨next3 i j, transition3 i j ht⟩) hc hp h2
  have h4 := advance H3 H4 prefix3 prefix4 rep3 color4 base4
    (fun _ hh => decompose gen3 inv3 inv3_spec gen4 inv4 inv4_spec
      rep3 act3 factor3 0 rep3_base step3 hh)
    (fun _ hh => residual4_spec hh)
    (fun i j ht => ⟨next4 i j, transition4 i j ht⟩) hc hp h3
  have h5 := advance H4 H5 prefix4 prefix5 rep4 color5 base5
    (fun _ hh => decompose gen4 inv4 inv4_spec gen5 inv5 inv5_spec
      rep4 act4 factor4 0 rep4_base step4 hh)
    (fun _ hh => residual5_spec hh)
    (fun i j ht => ⟨next5 i j, transition5 i j ht⟩) hc hp h4
  have h6 := advance H5 H6 prefix5 prefix6 rep5 color6 base6
    (fun _ hh => decompose gen5 inv5 inv5_spec gen6 inv6 inv6_spec
      rep5 act5 factor5 0 rep5_base step5 hh)
    (fun _ hh => residual6_spec hh)
    (fun i j ht => ⟨next6 i j, transition6 i j ht⟩) hc hp h5
  obtain ⟨i, h, hh, he⟩ := h6
  have hone : h = 1 := by
    change h ∈ wordSubgroup gen6 inv6 inv6_spec at hh
    rw [wordSubgroup_fin_zero_eq_bot, mem_bot] at hh
    exact hh
  rw [hone, mul_one] at he
  exact ⟨i, he⟩

private theorem core_covered (g : core) : ∃ i : Fin 64, g.val.val.val = prefix6 i := by
  apply pair_covered g.val.val.val (generated_le g.val.val.property)
  · have hle : localGroup 0 ≤ centralizer ({e0} : Set Carrier) :=
      le_of_eq localGroup_zero_eq_centralizer
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hle g.val.property)).symm
  · exact (mem_core_iff g.val).mp g.property

/-- The actual kernel of the action on the ten fixed-letter pairs has at most
64 elements, with no centralizer-order or quotient hypothesis. -/
public theorem core_card_le : Nat.card core ≤ 64 := by
  classical
  let f : core → Fin 64 := fun g => Classical.choose (core_covered g)
  have hf (g : core) : g.val.val.val = prefix6 (f g) := Classical.choose_spec (core_covered g)
  have hinj : Function.Injective f := by
    intro g h he
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact (hf g).trans ((congrArg prefix6 he).trans (hf h).symm)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hinj

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
