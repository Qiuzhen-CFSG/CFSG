module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Quotients
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.CubicQuotientReduction

/-!
# Seed separation on each original local quotient

The proper invariant kernel in 14.7.50 belongs to U_I/V₁ for the selected
local I, which need not equal the full point normalizer. Pulling that kernel
back to U_I and using natural irreducibility on V/V₁ shows that its
intersection with V is exactly V₁. This proves 14.7.2(1) at the actual local
and retains the original quotient map, without a complement to the kernel.

Source: Aschbacher–Smith 14.7.2(1), p.1043, and 14.7.50, p.1064,
refs/quasithin.pdf.
-/

public noncomputable section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
open Subgroup Representation Chapter12.Section08 CriticalFusion.Source
universe u v w
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]

/-- Every proper invariant subspace meets the original seed in its point. -/
theorem local_seed_intersection
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    {ρ : Representation (ZMod 2) I W}
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (A : Submodule (ZMod 2) W)
    (hA : ∀ g w, w ∈ A → ρ g w ∈ A) (hproper : A ≠ ⊤) :
    ∀ v : (F.UH I), (v : G) ∈ V →
      ((c.coordinates v).toAdd ∈ A ↔ (v : G) ∈ F.Vi 1) := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  let J : Subgroup G :=
    (A.toAddSubgroup.toSubgroup.comap c.coordinates).map (F.UH I).subtype
  have memI (u : (F.UH I)) : (u : G) ∈ J ↔
      (c.coordinates u).toAdd ∈ A := by
    constructor
    · rintro ⟨v, hv, he⟩
      exact (Subtype.ext he : v = u) ▸ hv
    · intro hu
      exact ⟨u, hu, rfl⟩
  have hIU : J ≤ (F.UH I) := by rintro _ ⟨u, _, rfl⟩; exact u.property
  have hPI : F.Vi 1 ≤ J := by
    intro v hv
    apply (memI ⟨v, c.kernel_le hv⟩).mpr
    rw [(c.coordinates_eq_one_iff _).mpr hv]
    exact A.zero_mem
  have hclosed (h : I) {v : G} (hv : v ∈ J) : (h : G) * v * (h : G)⁻¹ ∈ J := by
    let u : (F.UH I) := ⟨v, hIU hv⟩
    apply (memI ⟨_, (mem_normalizer_iff.mp
      (c.normalized h.property) v).mp u.property⟩).mpr
    rw [c.equivariant h u]
    exact hA h _ ((memI u).mp hv)
  have hHI : I ≤ normalizer (J : Set G) := by
    intro h hh
    apply mem_normalizer_iff.mpr
    intro v
    constructor
    · exact hclosed ⟨h, hh⟩
    · intro hv
      simpa only [Subgroup.coe_inv, inv_inv, mul_assoc, inv_mul_cancel_left,
        mul_inv_cancel_right, inv_mul_cancel, mul_one] using
        hclosed (⟨h, hh⟩ : I)⁻¹ hv
  have hLVI : F.Li L 1 ≤ normalizer ((V ⊓ J : Subgroup G) : Set G) :=
    le_normalizer_inf ((F.Li_le L 1).trans (inf_le_left.trans h.chosen.normalizes))
      ((F.Li_one_le_of_mem_Hz hI).trans hHI)
  have split := F.invariant_subgroup_of_ambient_natural h.naturalMarking
    (by decide : 3 ≤ 3) (V ⊓ J) (le_inf (F.le_seed 1) hPI) inf_le_left hLVI
  have hinter : V ⊓ J = F.Vi 1 := by
    rcases split with he | he
    · exact he
    · exfalso
      apply hproper
      have hVI : V ≤ J := he.ge.trans inf_le_right
      have hUI : (F.UH I) ≤ J := conjugateSpanBy_le hVI hHI
      apply top_unique
      intro w _
      obtain ⟨u, hu⟩ := c.onto (Multiplicative.ofAdd w)
      have hw := (memI u).mp (hUI u.property)
      rw [hu] at hw
      exact hw
  intro v hv
  constructor
  · intro ha
    exact hinter ▸ (show (v : G) ∈ V ⊓ J from ⟨hv, (memI v).mpr ha⟩)
  · intro hp
    rw [(c.coordinates_eq_one_iff _).mpr hp]
    exact A.zero_mem

open Representation in
/-- Seed separation lifts fixation through an arbitrary proper invariant quotient
for an actor that normalizes the original seed. -/
theorem local_quotient_plane_fixed_of_seed_normalized
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    {W : Type v} {X : Type w} [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {ρ : Representation (ZMod 2) I W} {σ : Representation (ZMod 2) I X}
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap σ) (hp : p.toLinearMap.ker ≠ ⊤)
    (Y : Subgroup G) (hYI : Y ≤ I) (hYp : IsPPerfect 2 Y)
    (hYV : Y ≤ normalizer (V : Set G))
    (hfix : ∀ y (hy : y ∈ Y) (v : F.UH I), (v : G) ∈ F.Vi 2 →
      σ ⟨y,hYI hy⟩ (p (c.coordinates v).toAdd) = p (c.coordinates v).toAdd) :
    ⁅F.Vi 2,Y⁆ = ⊥ := by
  have hs := local_seed_intersection h I hI c p.toLinearMap.ker (by
    intro g w hw
    change p (ρ g w) = 0
    rw [p.isIntertwining, show p w = 0 from hw, map_zero]) hp
  apply moving_plane_centralized_of_normalized Y (hYI.trans hI.2.1) hYp
  apply le_normalizer_iff_commutator_le_right.mpr
  apply le_trans ?_ (F.monotone (by decide : 1 ≤ 2))
  apply commutator_le.mpr
  intro y hy v hv
  let u : F.UH I := ⟨v, le_conjugateSpanBy V I (F.le_seed 2 hv)⟩
  let yu : F.UH I := ⟨y*v*y⁻¹,(mem_normalizer_iff.mp (c.normalized (hYI hy)) v).mp u.property⟩
  have hyu : (yu : G) ∈ V := (mem_normalizer_iff.mp (hYV hy) v).mp (F.le_seed 2 hv)
  have hb : ((yu*u⁻¹ : F.UH I) : G) ∈ V := V.mul_mem hyu (V.inv_mem (F.le_seed 2 hv))
  apply (hs (yu*u⁻¹) hb).mp
  change p ((c.coordinates (yu*u⁻¹)).toAdd) = 0
  rw [map_mul,map_inv,toAdd_mul,toAdd_inv,←sub_eq_add_neg]
  rw [map_sub, show (c.coordinates yu).toAdd = ρ ⟨y,hYI hy⟩ (c.coordinates u).toAdd
    from c.equivariant ⟨y,hYI hy⟩ u, p.isIntertwining,hfix y hy u hv,sub_self]


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource
