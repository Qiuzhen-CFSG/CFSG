module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Quasisimple.Basic
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special
public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.Reduction
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.ElementaryEightParabolicRecognition

/-!
# Full max4 preimages in the recognized Rudvalis cover

The literal recognition map restricts to the full preimage of max4. Central
transfer at its odd index proves this preimage perfect. Its two-core quotient
is identified by the actual projection and the checked action on the model
E8. The checked special core and full eight action make max4 centerless, so
the center of its preimage is exactly the original covering kernel of order two.

These are intrinsic preimage facts. Identifying this subgroup with the original
V-normalizer still requires the source marked-eight and complement arguments.
No normalizer coverage, center calculation, or splitting is assumed here.

Source: Aschbacher–Smith 14.7.68(2), printed p.1071 (PDF p.1088), and
I.1.3(1), p.407; the actual max4 structure is in GLS3 Table 5.3r.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Theory.GroupTheory
open Rudvalis.SylowOvergroups Rudvalis.CoreQuotients Rudvalis.CoveringIncidence
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover
open Rudvalis.Multiplier.TwoPrimary PerfectCentralCovering

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

private theorem max4_center_trivial : center max4 = ⊥ := by
  classical
  apply le_antisymm ?_ bot_le
  intro z hz
  have hc : (z : Rudvalis.Model) ∈ centralizer (elementary 2 : Set Rudvalis.Model) := by
    apply mem_centralizer_iff.mpr
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x, marked_eight_le_max4 hx⟩)
  have hp : z ∈ pCore 2 max4 := by
    rw [← max4_centralizer_eq_pCore]
    exact hc
  let p : max4Core := ⟨z, mem_map_of_mem max4.subtype hp⟩
  have hpc : p ∈ center max4Core := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact congrArg (fun t : max4 => (t : Rudvalis.Model))
      (mem_center_iff.mp hz ⟨y, max4Core_le_max4 y.property⟩)
  have he : (z : Rudvalis.Model) ∈ elementary 2 := by
    rw [← max4CoreCenter_eq_marked]
    exact mem_map_of_mem max4Core.subtype hpc
  let a : elementary 2 := ⟨z, he⟩
  have hfix (b : MulAut (elementary 2)) : b a = a := by
    obtain ⟨g, rfl⟩ := max4EightAction_surjective b
    apply Subtype.ext
    rw [max4EightAction_apply]
    have hcomm := congrArg Subtype.val (mem_center_iff.mp hz g)
    change (g : Rudvalis.Model) * (z : Rudvalis.Model) = (z : Rudvalis.Model) * g at hcomm
    rw [hcomm, mul_inv_cancel_right]
  have ha : a = 1 := by
    let := RankOneEightCharacteristic.elementary_two_elementary
    by_contra hne
    have hall (b : elementary 2) : b = 1 ∨ b = a := by
      by_cases hb : b = 1
      · exact Or.inl hb
      · obtain ⟨f, hf⟩ := ElementaryEightParabolic.automorphism_transitive a b hne hb
        exact Or.inr (hf.symm.trans (hfix f))
    let f : Bool → elementary 2 := fun b => if b then a else 1
    have hf : Function.Surjective f := by
      intro b
      rcases hall b with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
    have hcard := Nat.card_le_card_of_surjective f hf
    rw [RankOneEightCharacteristic.elementary_two_card,
      show Nat.card Bool = 2 by simp] at hcard
    omega
  change z = 1
  calc
    z = inclusion marked_eight_le_max4 a := rfl
    _ = inclusion marked_eight_le_max4 1 := congrArg (inclusion marked_eight_le_max4) ha
    _ = 1 := map_one _

namespace Data
variable {d : Data T L V F W} {u : F.U} {Lu : Subgroup G}
namespace FixedRudvalisCover
variable (r : d.FixedRudvalisCover u Lu)

/-- Change the coordinates on the recognized model by an actual inner automorphism. -/
def align (g : Rudvalis.Model) : d.FixedRudvalisCover u Lu where
  projection := (MulAut.conj g).toMonoidHom.comp r.projection
  onto := (MulAut.conj g).surjective.comp r.onto
  kernel := by
    have hk : ((MulAut.conj g).toMonoidHom.comp r.projection).ker = r.projection.ker := by
      ext x
      change MulAut.conj g (r.projection x) = 1 ↔ r.projection x = 1
      exact (MulAut.conj g).map_eq_one_iff
    rw [hk, r.kernel]

/-- The full preimage of the literal max4 subgroup under the recognition map. -/
def max4Preimage : Subgroup Lu := max4.comap r.projection

/-- Restriction of the same recognition map, without choosing a lift. -/
def max4Restriction : r.max4Preimage →* max4 := r.projection.subgroupComap max4

theorem max4Restriction_onto : Function.Surjective r.max4Restriction :=
  r.projection.subgroupComap_surjective_of_surjective max4 r.onto

def max4KernelEquiv : r.max4Restriction.ker ≃* r.projection.ker :=
  subgroupComapKernelEquiv r.projection max4

theorem max4Restriction_kernel_card (hne : (u : G) ≠ 1) :
    Nat.card r.max4Restriction.ker = 2 :=
  (Nat.card_congr r.max4KernelEquiv.toEquiv).trans (r.kernel_card_two d hne)

theorem max4Restriction_kernel_central (hLu : Lu ≤ d.fixedCentralizer u) :
    r.max4Restriction.ker ≤ center r.max4Preimage := by
  intro x hx
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  have hk : (x : Lu) ∈ r.projection.ker := congrArg Subtype.val hx
  exact mem_center_iff.mp (r.kernel_le_center d hLu hk) y

theorem max4Preimage_perfect (hne : (u : G) ≠ 1)
    (hLu : Lu ≤ d.fixedCentralizer u) (hq : IsQuasisimple Lu) :
    Group.IsPerfect r.max4Preimage := by
  let := hq
  let := max4_isPerfect
  have hk : IsPGroup 2 r.projection.ker := IsPGroup.of_card (n := 1)
    (by simpa using r.kernel_card_two d hne)
  exact perfect_preimage_of_central_pGroup_kernel r.projection r.onto
    (r.kernel_le_center d hLu) hk max4 max4_index_odd

theorem max4Preimage_twoPerfect (hne : (u : G) ≠ 1)
    (hLu : Lu ≤ d.fixedCentralizer u) (hq : IsQuasisimple Lu) :
    IsPPerfect 2 r.max4Preimage := by
  let := r.max4Preimage_perfect hne hLu hq
  intro N hN hp
  let := hN
  by_contra hneN
  let : Nontrivial (r.max4Preimage ⧸ N) := QuotientGroup.nontrivial_iff.mpr hneN
  let : Group.IsPerfect (r.max4Preimage ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  exact Group.IsPerfect.not_isNilpotent (r.max4Preimage ⧸ N) hp.isNilpotent

/-- The quotient map is induced by the original covering projection. -/
def max4PreimageQuotientEquiv (hne : (u : G) ≠ 1) :
    (r.max4Preimage ⧸ pCore 2 r.max4Preimage) ≃* MulAut (elementary 2) :=
  (r.max4Restriction.pCoreQuotientEquiv r.max4Restriction_onto
    (IsPGroup.of_card (n := 1) (by simpa using r.max4Restriction_kernel_card hne))).trans
    (max4QuotientEquiv.trans eightAutEquivPSL.symm)

@[simp] theorem max4PreimageQuotientEquiv_mk (hne : (u : G) ≠ 1)
    (x : r.max4Preimage) :
    r.max4PreimageQuotientEquiv hne (QuotientGroup.mk' (pCore 2 r.max4Preimage) x) =
      max4EightAction (r.max4Restriction x) := by
  change eightAutEquivPSL.symm
    (max4QuotientEquiv (QuotientGroup.mk' (pCore 2 max4) (r.max4Restriction x))) = _
  rw [max4QuotientEquiv_mk]
  exact eightAutEquivPSL.symm_apply_apply _

theorem max4Preimage_center_eq_kernel (hLu : Lu ≤ d.fixedCentralizer u) :
    center r.max4Preimage = r.max4Restriction.ker := by
  apply le_antisymm ?_ (r.max4Restriction_kernel_central hLu)
  intro z hz
  change r.max4Restriction z = 1
  apply mem_bot.mp
  rw [← max4_center_trivial]
  apply mem_center_iff.mpr
  intro y
  obtain ⟨x, rfl⟩ := r.max4Restriction_onto y
  simpa only [map_mul] using congrArg r.max4Restriction (mem_center_iff.mp hz x)

theorem max4Preimage_center_card (hne : (u : G) ≠ 1)
    (hLu : Lu ≤ d.fixedCentralizer u) : Nat.card (center r.max4Preimage) = 2 := by
  rw [r.max4Preimage_center_eq_kernel hLu]
  exact r.max4Restriction_kernel_card hne

end FixedRudvalisCover
end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

