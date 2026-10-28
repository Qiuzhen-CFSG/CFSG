module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Elementary
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Sections
public import Theory.Representation.FirstCohomologyDuality.SimpleCover

/-!
# The centralizer radical of the original commutator pairing

The centralizer of O₂(H) in U has a proper H-invariant image in U/V₁:
otherwise [U,O₂(H)]=V₁ would be trivial. The indecomposable natural
cover puts every proper invariant subspace in the kernel of the original
projection. Thus C_U(O₂(H)) lies in U₀. Restriction to the prepared
rank-three commutator has radical precisely V₁, and the opposite point
has nontrivial commutator with O₂(H).

The only earlier inputs here are the actual action descent from 14.5.15(4)
and [U,O₂(H)]=V₁ from 14.5.21(2). Their producer is qt-14-05; the
preparation producer supplies `Preliminary`. No pairing-surjectivity or
axis-action assertion is assumed.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.5.21 and the proof of 14.7.70, printed pp.1019 and 1074.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
open Subgroup Representation Chapter12.Section08
open Representation.OneCohomology Representation.SL2FourNatural
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

private theorem proper_invariant_le_kernel (s : d.ActionDescent)
    (A : Submodule (ZMod 2) W)
    (hA : ∀ h w, w ∈ A → d.action h w ∈ A) (hne : A ≠ ⊤) :
    A ≤ d.projection.toLinearMap.ker := by
  let p := restrictedProjection d.naturalQuotient s.projection
  have hp : IsCover p := SL2FourCentralCover.isCover_of_natural_indecomposable p
    d.projection_onto s.kernel_fixed s.indecomposable
  have hi : ∀ g w, w ∈ A → s.action (alternatingActor d.naturalQuotient g) w ∈ A := by
    intro g w hw
    obtain ⟨h, hh⟩ := d.qH_surjective (alternatingActor d.naturalQuotient g)
    rw [← hh, s.original]
    exact hA h w hw
  have him : ∀ g v, v ∈ A.map p.toLinearMap →
      naturalRepresentation g v ∈ A.map p.toLinearMap := by
    rintro g _ ⟨w, hw, rfl⟩
    exact ⟨_, hi g w hw, LinearMap.congr_fun (p.isIntertwining' g) w⟩
  have hbot : A.map p.toLinearMap = ⊥ := by
    by_contra hn
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
    have ht : A.map p.toLinearMap = ⊤ := by
      apply top_unique
      intro w _
      by_cases hw : w = 0
      · exact hw ▸ (A.map p.toLinearMap).zero_mem
      obtain ⟨g, hg⟩ := transitive_nonzero v w hv0 hw
      exact hg ▸ him g v hv
    exact hne (invariant_eq_top_of_cover_image_eq_top p hp A hi ht)
  intro w hw
  have : p w ∈ A.map p.toLinearMap := ⟨w, hw, rfl⟩
  rw [hbot] at this
  exact this

include d in
/-- H centralizes the original point, so it also centralizes it on restriction
to its actual two-core. -/
theorem point_le_core_centralizer :
    F.Vi 1 ≤ F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G) := by
  refine le_inf d.conjugationSection.kernel_le ?_
  exact le_centralizer_iff.mpr
    ((pCoreIn_le 2 F.H).trans_eq (point_centralizer d).symm)

/-- The radical bound follows from the genuine indecomposable natural cover
and the earlier nontrivial commutator, before invoking F.9.7. -/
theorem core_centralizer_le_U₀ (s : d.ActionDescent)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G) ≤ d.U₀ := by
  let C := F.U ⊓ centralizer (F.H.pCoreIn 2 : Set G)
  have hnormQ : F.H ≤ normalizer (F.H.pCoreIn 2 : Set G) :=
    F.H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))
  have hnorm : F.H ≤ normalizer (C : Set G) :=
    (le_inf d.conjugationSection.normalized
      (hnormQ.trans (normalizer_le_normalizer_centralizer _))).trans
        inf_normalizer_le_normalizer_inf
  have hi : ∀ h w, w ∈ tilde d C → d.action h w ∈ tilde d C := by
    intro h w hw
    obtain ⟨a, ha, rfl⟩ := (d.conjugationSection.mem_imageSpace_iff _ _).mp hw
    let b : F.U := ⟨(h : G) * a * (h : G)⁻¹,
      (mem_normalizer_iff.mp (d.conjugationSection.normalized h.property) a).mp a.property⟩
    exact (d.conjugationSection.mem_imageSpace_iff _ _).mpr
      ⟨b, (mem_normalizer_iff.mp (hnorm h.property) a).mp ha,
        d.conjugationSection.equivariant h a⟩
  have hne : tilde d C ≠ ⊤ := by
    intro ht
    have hUC : F.U ≤ C := (tilde_le_iff d le_rfl inf_le_left
      (point_le_core_centralizer d)).mp (ht ▸ le_top)
    have hb : F.Vi 1 = ⊥ := h21.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr (hUC.trans inf_le_right))
    have hh : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
    rw [hb, card_bot] at hh
    omega
  apply (tilde_le_iff d inf_le_left d.U₀_le_U d.point_le_U₀).mp
  rw [tilde_U₀ d]
  exact proper_invariant_le_kernel d s _ hi hne

namespace Preliminary
variable {d} {c : CriticalPath (L := L) F} (h : Preliminary d c)
include h

/-- The restricted pairing on F/V₁ has zero left radical. -/
theorem commutator_inf_core_centralizer (s : d.ActionDescent)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    Fcomm c ⊓ centralizer (F.H.pCoreIn 2 : Set G) = F.Vi 1 := by
  apply le_antisymm
  · calc
      Fcomm c ⊓ centralizer (F.H.pCoreIn 2 : Set G) ≤ Fcomm c ⊓ d.U₀ :=
        le_inf inf_le_left ((inf_le_inf_right _ (h.commutator_le.trans inf_le_left)).trans
          (core_centralizer_le_U₀ d s h21))
      _ = F.Vi 1 := h.commutator_inf
  · exact le_inf h.point_le ((point_le_core_centralizer d).trans inf_le_right)

/-- The source's first cross-commutator is nontrivial because Zα is outside
the radical U₀. Its value is the literal original point. -/
theorem opposite_commutator (s : d.ActionDescent)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1) :
    ⁅c.Zα, F.H.pCoreIn 2⁆ = F.Vi 1 := by
  have hle : ⁅c.Zα, F.H.pCoreIn 2⁆ ≤ F.Vi 1 :=
    (commutator_mono (h.opposite_le.trans (h.commutator_le.trans inf_le_left)) le_rfl).trans_eq h21
  have hn : ⁅c.Zα, F.H.pCoreIn 2⁆ ≠ ⊥ := by
    intro hb
    exact h.opposite_not_le ((le_inf
      (h.opposite_le.trans (h.commutator_le.trans inf_le_left))
      (commutator_eq_bot_iff_le_centralizer.mp hb)).trans (core_centralizer_le_U₀ d s h21))
  apply eq_of_le_of_card_ge hle
  have hh := (one_lt_card_iff_ne_bot _).mpr hn
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  omega

end Preliminary
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
