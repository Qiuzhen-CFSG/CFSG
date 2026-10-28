module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.FixedLineKernel
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationAction
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.OffenderIntersection

/-!
# The fixed-line action kernel on the original augmentation core: structure at the original group

A normalizer element whose displacement lies in C_V(L) acts trivially
on the natural quotient of the five-dimensional core. Faithfulness of
the six-letter permutation action on that quotient makes its permutation
trivial, so it fixes the whole original core. The action uses the original
normalizer marking and L/centralCore L projection throughout.

The terminal application combines this kernel calculation with the actual
intersection in a conjugate of V. It retains the earlier normalizer fusion
and the point-fusion conclusion of source 13.4.17 as explicit inputs.

Specialize the original proof to `Structural1222At` at the same G,T.
All action maps, full quotient kernels and source hypotheses are retained;
no universal Chapter12 record is inferred. Intrinsic model and group lemmas
are reused from the preserved source module. This family feeds guarded
nonsolvable-centralizer exclusion on the actual five-dimensional module.

Source: Aschbacher--Smith 13.4.10--17, printed pp.907--915;
see the original `Nonsolvable/FixedLineKernel` proof for the local step.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BinaryPermutation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original full normalizer cannot act nontrivially on the five-space
with all displacement in its distinguished fixed line. -/
theorem original_fixed_line_kernel_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (A : Subgroup G) (hA : A ≤ normalizer (V : Set G))
    (hc : ⁅V,A⁆ ≤ V ⊓ centralizer (L : Set G)) : ⁅V,A⁆ = ⊥ := by
  have hn := normalizer_component_le_module_at h structural D m
  have hAM : A ≤ normalizer (L : Set G) :=
    hA.trans (normalizer_component_eq_module_at h structural D m).symm.le
  obtain ⟨q,hq,_,hk⟩ := exists_core_normalizer_permutation D m hn
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  intro a ha
  have hqa : q ⟨a,hAM ha⟩ = 1 := by
    apply naturalRepresentation_injective (Fin 6) (by decide)
    apply LinearMap.ext
    intro w
    obtain ⟨u,rfl⟩ := coreToNatural_surjective w
    obtain ⟨v,hv⟩ := m.coordinate.surjective (Multiplicative.ofAdd u)
    have hv' : (m.coordinate v).toAdd = u := congrArg Multiplicative.toAdd hv
    rw [←hv']
    let c : V := V.normalizerMonoidHom ⟨a,hA ha⟩ v * v⁻¹
    have hcf : c.val ∈ V ⊓ centralizer (L : Set G) := by
      apply hc
      rw [commutator_comm]
      exact commutator_mem_commutator ha v.property
    have hp : coreToNatural (Fin 6) (m.coordinate c).toAdd = 0 := by
      apply Subtype.ext
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact (m.mem_fixed_iff c).mp hcf.2
    have he : (m.coordinate c).toAdd =
        coreRepresentation (Fin 6) (q ⟨a,hAM ha⟩) (m.coordinate v).toAdd -
          (m.coordinate v).toAdd := by
      change (m.coordinate (V.normalizerMonoidHom ⟨a,hA ha⟩ v * v⁻¹)).toAdd = _
      simp only [map_mul,map_inv,toAdd_mul,toAdd_inv,
        ←sub_eq_add_neg]
      exact congrArg (fun w : core (Fin 6) => w - (m.coordinate v).toAdd)
        (hq ⟨a,hAM ha⟩ v)
    rw [map_one,Module.End.one_apply]
    apply sub_eq_zero.mp
    rw [←coreToNatural_equivariant,←map_sub,←he]
    exact hp
  change (⟨a,hAM ha⟩ : normalizer (L : Set G)) ∈
    (centralizer (V : Set G)).subgroupOf (normalizer (L : Set G))
  rw [←hk]
  exact hqa

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
