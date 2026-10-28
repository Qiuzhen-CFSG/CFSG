module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Setup
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.ComponentCase.ThreeDimensional.InnerInvolution
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# The actual action in the Borel component branch

The displacement decomposition supplies a noncentral involution t in X ∩ U.
An element centralizing U fixes t, so it cannot move the component X to a
commuting distinct component. Thus the whole relative centralizer C_G(U)
normalizes X. Its actual conjugation action fixes t and contains the inner
image of a Sylow two-subgroup of X, obtained from the common source Sylow.

The intrinsic action-vanishing contract below is a new mathematical obligation.
It is not assumed as an earlier source result. Its model-specific proofs must
be supplied before the Borel interaction is complete.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8 and
E.6.23, printed pp.247–248 and 254–255; ordinary component calculus.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Borel
open ComponentBalance Components
universe u
variable {G : Type*} [Group G]

/-- Intrinsic model obligation for the mixed action. The image includes the
actual inner Sylow action, and the original A₃ group embeds subnormally in
the actor. No whole-group A₄ identification is taken as an input. -/
def FixedSylowActionTrivial (X : Type u) [Group X] : Prop :=
  ∀ (H D : Type u) [Group H] [Finite H] [Group D] [Finite D],
    ChapterC.IsAlternatingBlock D 3 →
    ∀ ι : D →* H, Function.Injective ι → ι.range.IsSubnormal →
      ∀ ρ : H →* MulAut X, ∀ S : Sylow 2 X,
        (∀ s ∈ (S : Subgroup X), MulAut.conj s ∈ ρ.range) →
        ∀ t : X, t ∉ center X → t ^ 2 = 1 →
          (∀ a : H, ρ a t = t) → ρ.comp ι = 1

private theorem normalizes_component_of_fixed_noncentral
    {H X D : Subgroup G} (hX : IsComponentIn X H) (hDH : D ≤ H)
    (t : X) (ht : t ∉ center X) (hDt : D ≤ centralizer ({(t : G)} : Set G)) :
    D ≤ normalizer (X : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  have hHg : H.map (MulAut.conj g).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer (hDH hg))
  have hXg : IsComponentIn (X.map (MulAut.conj g).toMonoidHom) H := by
    simpa only [hHg] using hX.map (MulAut.conj g)
  have hcomm := commutator_eq_bot_iff_le_centralizer.mp
    (hX.commutator_eq_bot_of_ne hXg (Ne.symm hne))
  have htg : (t : G) ∈ X.map (MulAut.conj g).toMonoidHom := by
    refine ⟨t, t.property, ?_⟩
    change g * (t : G) * g⁻¹ = t
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hDt hg))
  apply ht
  apply mem_center_iff.mpr
  intro x
  apply Subtype.ext
  exact ((hcomm x.property) t htg).symm

variable [Finite G] {M V : Subgroup G}

/-- Fixing the noncentral marked involution prevents the entire hyperplane
centralizer from moving X to a distinct component of C_G(A). -/
theorem centralizer_normalizes_component [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {U A X : Subgroup G} (hUh : IsHyperplane V U)
    (hA : A ∈ obstructionFamily M V) (hAU : A ≤ U)
    (hc : subgroupCorank V A = 2) (hX : CentralizerComponent A X)
    (hfixed : V ⊓ centralizer (X : Set G) = A) (b : BorelAlternative M V A X 2) :
    centralizer (U : Set G) ≤ normalizer (X : Set G) := by
  obtain ⟨t, htU, htZ, _⟩ :=
    ComponentCase.borel_hyperplane_inner_involution h hUh hA hAU hc hX hfixed b
  exact normalizes_component_of_fixed_noncentral hX (centralizer_le hAU) t htZ
    (centralizer_le (Set.singleton_subset_iff.mpr htU))

/-- Conjugation by the entire original hyperplane centralizer. -/
def centralizerAction {U X : Subgroup G}
    (hn : centralizer (U : Set G) ≤ normalizer (X : Set G)) :
    centralizer (U : Set G) →* MulAut X :=
  X.normalizerMonoidHom.comp (inclusion hn)

omit [Finite G] in
/-- A marked element in U is fixed by the full conjugation action. -/
theorem centralizerAction_fixed {U X : Subgroup G}
    (hn : centralizer (U : Set G) ≤ normalizer (X : Set G))
    (t : X) (ht : (t : G) ∈ U) (a : centralizer (U : Set G)) :
    centralizerAction hn a t = t := by
  apply Subtype.ext
  change (a : G) * (t : G) * (a : G)⁻¹ = t
  rw [← a.property t ht, mul_inv_cancel_right]

/-- The common Sylow gives the actual inner Sylow action inside the image;
the ambient actor need not normalize the chosen Sylow. -/
theorem centralizerAction_contains_sylow
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {U A X : Subgroup G} (hU : U ∈ obstructionFamily M V)
    (hA : A ∈ obstructionFamily M V) (hX : CentralizerComponent A X)
    (hn : centralizer (U : Set G) ≤ normalizer (X : Set G)) :
    ∃ S : Sylow 2 X, ∀ s ∈ (S : Subgroup X),
      MulAut.conj s ∈ (centralizerAction hn).range := by
  obtain ⟨_, S, hS, _⟩ := component_sylow_action h hA hX rfl
  have hQ := (Chapter1.isSylowIn_iff.mp (h.sylow_obstruction hU)).2.1
  refine ⟨S, ?_⟩
  intro s hs
  have hsQ := (show (s : G) ∈ X ⊓ sylowCentralizer (T : Subgroup G) V from
    hS ▸ mem_map_of_mem X.subtype hs).2
  refine ⟨⟨s, hQ hsQ⟩, ?_⟩
  ext x
  rfl

/-- Discharge the original component action once its intrinsic model theorem
has been proved. Relative subnormality and every action marking are supplied
here from the genuine block and common-Sylow hypotheses. -/
theorem commutes_of_fixedSylowActionTrivial [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {U A L X : Subgroup G} (hU : U ∈ obstructionFamily M V)
    (hUh : IsHyperplane V U) (hL : SmallBlock U L)
    (h3 : ChapterC.IsAlternatingBlock L 3)
    (hA : A ∈ obstructionFamily M V) (hAU : A ≤ U)
    (hc : subgroupCorank V A = 2) (hX : CentralizerComponent A X)
    (hfixed : V ⊓ centralizer (X : Set G) = A) (b : BorelAlternative M V A X 2)
    (ha : FixedSylowActionTrivial X) : ⁅L, X⁆ = ⊥ := by
  let hn := centralizer_normalizes_component h hUh hA hAU hc hX hfixed b
  let ρ := centralizerAction hn
  let ι : L →* centralizer (U : Set G) := inclusion hL.1
  have hr : ι.range = L.subgroupOf (centralizer (U : Set G)) := by
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact l.property
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hs : ι.range.IsSubnormal := hr ▸ hL.2.1.subnormal
  obtain ⟨S, hS⟩ := centralizerAction_contains_sylow h hU hA hX hn
  obtain ⟨t, htU, htZ, ht2⟩ :=
    ComponentCase.borel_hyperplane_inner_involution h hUh hA hAU hc hX hfixed b
  have he := ha (centralizer (U : Set G)) L h3 ι (inclusion_injective hL.1)
    hs ρ S hS t htZ ht2 (centralizerAction_fixed hn t htU)
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro l hl x hx
  have hh := congrArg (fun f : L →* MulAut X => (f ⟨l, hl⟩ ⟨x, hx⟩ : G)) he
  change l * x * l⁻¹ = x at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Lifting.Three.Placement.Borel
