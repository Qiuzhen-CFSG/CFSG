module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.InnerEstimate.Contracts
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.InnerEstimate.Involutions
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Adjacent.Proper.InnerEstimate.RepresentativeBounds
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.GeneratedSubgroupInvariants

/-!
# Proper adjacent support: the inner common-fixed-space estimate

The two explicit involution classes transfer the representative displacement
bounds to any nonidentity element of an elementary actor. Monotonicity of fixed
spaces then gives codimension at least nine for the actor's common fixed space,
which exceeds twice its rank when that rank is at most four.

The proved mixed-tensor comparison and its independent displacement witnesses
provide the two representative bounds on the original module. Combining them
with this reduction proves `proper_inner_estimate`, discharging the inner-estimate
input of `proper_adjacent_remaining_actors_of_separation_and_inner_estimate`.
The independent support-separation input remains with that consumer's assembly
owner. The estimate here is specific to proper adjacent support; no uniform
involution bound is assumed for the separate adjoint or full-support branches.

Source application: Aschbacher–Smith K.3.2, printed pp.454–455; Guralnick–Malle,
Classification of 2F-modules II, author manuscript, Proposition 4.7, pp.25–26.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
open Representation Representation.BinaryOffender
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Conjugacy of the two concrete involutions transfers their estimates to
any nonidentity involution in the original module. -/
theorem nine_le_fixedCodim_involution_of_bounds [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Group V)
    (h : ProperInvolutionBounds σ) {v : V} (hv : v ≠ 0)
    (hh : LocalHighestVector σ {0, 1} v)
    (t : Group) (ht : t ^ 2 = 1) (hne : t ≠ 1) :
    9 ≤ fixedCodim σ (Subgroup.zpowers t) := by
  obtain ⟨hfirst, hsecond⟩ := h v hv hh
  rcases InnerEstimate.involution_conjugacy t ht hne with hc | hc
  · obtain ⟨c, rfl⟩ := isConj_iff.mp hc
    rwa [fixedCodim_zpowers_conj]
  · obtain ⟨c, rfl⟩ := isConj_iff.mp hc
    rwa [fixedCodim_zpowers_conj]

/-- The common fixed space is contained in the fixed space of any member
of the actor. The two representative estimates therefore cover every actor
of rank at most four, with its literal common fixed space. -/
theorem proper_inner_estimate_of_involution_bounds [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Group V) (h : ProperInvolutionBounds σ) :
    ProperInnerEstimate σ := by
  intro v hv hh B hB _ hr _
  obtain ⟨t, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB.1
  have hne' : (t : Group) ≠ 1 := fun he => hne (Subtype.ext he)
  let : IsElementaryAbelian 2 B := hB.2
  have ht2 : (t : Group) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (A := B) (p := 2) (t : Group) t.property
  have hnine := nine_le_fixedCodim_involution_of_bounds σ h hv hh t ht2 hne'
  have hle : fixedSpace σ B ≤ fixedSpace σ (Subgroup.zpowers (t : Group)) :=
    σ.invariants_comp_subtype_antitone (Subgroup.zpowers_le.mpr t.property)
  have hfix := Submodule.finrank_mono hle
  have htfin := fixedCodim_add_finrank σ (Subgroup.zpowers t)
  have hBfin := fixedCodim_add_finrank σ B
  omega

/-- Faithful irreducible binary SL₄ modules with proper adjacent highest support
satisfy the strict common-fixed-space estimate for every remaining inner actor.
The two cyclic bounds are proved on this same module, with no degree or absolute
irreducibility assumption. -/
theorem proper_inner_estimate [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) Group V) (hf : Function.Injective σ)
    (hi : IsIrreducible σ) : ProperInnerEstimate σ :=
  proper_inner_estimate_of_involution_bounds σ (proper_involution_bounds σ hf hi)

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
