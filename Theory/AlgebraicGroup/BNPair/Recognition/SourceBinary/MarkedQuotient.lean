module
public import Theory.AlgebraicGroup.BNPair.StandardParabolicCore
public import Theory.GroupTheory.Amalgam.RankTwoQuotientTransport
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.CoreFaithfulness

/-!
# Marked finite quotients and local lifting

The input is one normal subgroup D and one Tits system on X/D, with
both original endpoint images identified with its two marked singleton
standard parabolics and the original whole overlap mapped to its Borel.
No global injectivity of X → X/D is assumed. The two endpoint-kernel
intersections are trivial.

Standard-parabolic classification proves that the two marked parabolics
meet in the Borel. The first isomorphism theorem, with the trivial
restricted kernels, constructs the three local equivalences using that
same quotient map; both amalgam squares follow on representatives.
Faithfulness of the original overlap then transfers to the Borel by the
existing faithful-completion core theorem.

This is the local lifting step in DGS, Groups and Graphs, Part II,
Theorem D, printed p.224, after (3.6)–(3.7), pp.77–80. Construction of
this marked finite quotient remains an earlier geometric input. Neither
splitness nor irreducibility nor a Lie-model comparison is claimed by
this input or by the transport theorems below.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary
variable {X : Type*} [Group X]

private theorem restricted_quotient_injective (D P : Subgroup X) [D.Normal]
    (h : Disjoint D P) : Function.Injective ((QuotientGroup.mk' D).comp P.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  exact subgroupOf_eq_bot.mpr h

private def restrictedQuotientEquiv (D P : Subgroup X) [D.Normal]
    (h : Disjoint D P) : P ≃* P.map (QuotientGroup.mk' D) :=
  (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq
      (show (⊥ : Subgroup P) = (QuotientGroup.mk' D).ker.subgroupOf P from by
        rw [QuotientGroup.ker_mk']
        exact (subgroupOf_eq_bot.mpr h).symm))).trans
    (RankTwoAmalgam.subgroupQuotientMapEquiv (QuotientGroup.mk' D) P)

/-- The literal quotient and both marked parabolics supplied by the regular
apartment branch. The original carrier need not be finite. -/
structure MarkedQuotient (P : Fin 2 → Subgroup X) where
  D : Subgroup X
  [normal : D.Normal]
  [finite : Finite (X ⧸ D)]
  disjoint : ∀ i, Disjoint D (P i)
  tits : TitsSystem (X := X ⧸ D)
  simple : Fin 2 → (tits.N ⧸ (tits.B ⊓ tits.N).subgroupOf tits.N)
  simple_injective : Function.Injective simple
  simple_range : Set.range simple = tits.S
  parabolic_image : ∀ i, (P i).map (QuotientGroup.mk' D) =
    tits.standardParabolic {simple i}
  borel_image : (P 0 ⊓ P 1).map (QuotientGroup.mk' D) = tits.B

attribute [instance] MarkedQuotient.normal MarkedQuotient.finite

namespace MarkedQuotient
variable {P : Fin 2 → Subgroup X} (d : MarkedQuotient P)

/-- Every image and every local equivalence uses this quotient map. -/
abbrev q : X →* X ⧸ d.D := QuotientGroup.mk' d.D

/-- Each specified reflection belongs to the distinguished set. -/
theorem simple_mem (i : Fin 2) : d.simple i ∈ d.tits.S :=
  d.simple_range ▸ Set.mem_range_self i

/-- Distinct singleton standard parabolics have exactly the whole Borel
in common; no dihedral-order assumption is used. -/
theorem standard_intersection :
    d.tits.standardParabolic {d.simple 0} ⊓
      d.tits.standardParabolic {d.simple 1} = d.tits.B := by
  let H := d.tits.standardParabolic {d.simple 0} ⊓
    d.tits.standardParabolic {d.simple 1}
  have hB : d.tits.B ≤ H := le_inf (d.tits.B_le_standardParabolic _)
    (d.tits.B_le_standardParabolic _)
  have hsi (i : Fin 2) : ({d.simple i} : Set _) ⊆ d.tits.S :=
    Set.singleton_subset_iff.mpr (d.simple_mem i)
  have hempty : d.tits.simpleIndices H = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro s hs
    obtain ⟨hsS, hsH⟩ := (d.tits.mem_simpleIndices_iff _ _).mp hs
    have hs0 : s ∈ d.tits.simpleIndices (d.tits.standardParabolic {d.simple 0}) :=
      (d.tits.mem_simpleIndices_iff _ _).mpr ⟨hsS, fun x hx => (hsH hx).1⟩
    have hs1 : s ∈ d.tits.simpleIndices (d.tits.standardParabolic {d.simple 1}) :=
      (d.tits.mem_simpleIndices_iff _ _).mpr ⟨hsS, fun x hx => (hsH hx).2⟩
    rw [d.tits.simpleIndices_standardParabolic (hsi 0)] at hs0
    rw [d.tits.simpleIndices_standardParabolic (hsi 1)] at hs1
    exact (by decide : (0 : Fin 2) ≠ 1)
      (d.simple_injective ((Set.mem_singleton_iff.mp hs0).symm.trans
        (Set.mem_singleton_iff.mp hs1)))
  change H = d.tits.B
  rw [d.tits.subgroup_eq_standardParabolic_simpleIndices H hB,
    hempty, d.tits.standardParabolic_empty]

/-- Both markings, rather than endpoint-kernel disjointness alone, preserve
the entire overlap under the same quotient map. -/
theorem image_intersection : (P 0).map d.q ⊓ (P 1).map d.q = (P 0 ⊓ P 1).map d.q := by
  rw [d.parabolic_image 0, d.parabolic_image 1, d.borel_image]
  exact d.standard_intersection

/-- The inclusion amalgam of the two marked standard parabolics. -/
def standardAmalgam : RankTwoAmalgam
    (d.tits.standardParabolic {d.simple 0}) d.tits.B
    (d.tits.standardParabolic {d.simple 1}) :=
  RankTwoAmalgam.ofSubgroups _ _ _ (d.tits.B_le_standardParabolic _)
    (d.tits.B_le_standardParabolic _)

/-- Restrict the original quotient map to either endpoint. -/
def endpointEquiv (i : Fin 2) : P i ≃* d.tits.standardParabolic {d.simple i} :=
  (restrictedQuotientEquiv d.D (P i) (d.disjoint i)).trans
    (MulEquiv.subgroupCongr (d.parabolic_image i))

/-- Restrict the same quotient map to the whole original intersection. -/
def borelEquiv : (P 0 ⊓ P 1 : Subgroup X) ≃* d.tits.B :=
  (restrictedQuotientEquiv d.D (P 0 ⊓ P 1) ((d.disjoint 0).mono_right inf_le_left)).trans
    (MulEquiv.subgroupCongr d.borel_image)

/-- The endpoint map retains its literal quotient marking. -/
@[simp] theorem endpointEquiv_apply (i : Fin 2) (x : P i) :
    (d.endpointEquiv i x : X ⧸ d.D) = d.q x := by rfl

/-- The middle map retains its literal quotient marking. -/
@[simp] theorem borelEquiv_apply (x : (P 0 ⊓ P 1 : Subgroup X)) :
    (d.borelEquiv x : X ⧸ d.D) = d.q x := by rfl

/-- The original inclusion amalgam is isomorphic to the marked quotient
amalgam, including both commuting squares. -/
def markedIso : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
    d.standardAmalgam where
  left := d.endpointEquiv 0
  middle := d.borelEquiv
  right := d.endpointEquiv 1
  left_commutes _ := Subtype.ext rfl
  right_commutes _ := Subtype.ext rfl

/-- The assembled left equivalence is the original quotient map. -/
@[simp] theorem markedIso_left_apply (x : P 0) :
    (d.markedIso.left x : X ⧸ d.D) = d.q x := by rfl

/-- The assembled middle equivalence is that same quotient map. -/
@[simp] theorem markedIso_middle_apply (x : (P 0 ⊓ P 1 : Subgroup X)) :
    (d.markedIso.middle x : X ⧸ d.D) = d.q x := by rfl

/-- The assembled right equivalence is the original quotient map. -/
@[simp] theorem markedIso_right_apply (x : P 1) :
    (d.markedIso.right x : X ⧸ d.D) = d.q x := by rfl

/-- The quotient is a faithful completion of the original amalgam. -/
def completion (hgen : P 0 ⊔ P 1 = ⊤) :
    RankTwoAmalgam.FaithfulCompletion
      (RankTwoAmalgam.ofSubgroups (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right)
      (G := X ⧸ d.D) where
  left := d.q.comp (P 0).subtype
  right := d.q.comp (P 1).subtype
  compatible := rfl
  left_injective := restricted_quotient_injective _ _ (d.disjoint 0)
  right_injective := restricted_quotient_injective _ _ (d.disjoint 1)
  middle_injective := restricted_quotient_injective _ _
    ((d.disjoint 0).mono_right inf_le_left)
  generated := by
    rw [MonoidHom.range_comp, MonoidHom.range_comp, range_subtype, range_subtype,
      ← Subgroup.map_sup, hgen, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

/-- The marked middle image is the actual Borel. -/
theorem completion_middle_range (hgen : P 0 ⊔ P 1 = ⊤) :
    (d.completion hgen).middle.range = d.tits.B := by
  change (d.q.comp (P 0 ⊓ P 1).subtype).range = _
  rw [MonoidHom.range_comp, range_subtype]
  exact d.borel_image

/-- A faithful original overlap gives a faithful Borel in the quotient. -/
theorem borel_core_eq_bot (hgen : P 0 ⊔ P 1 = ⊤)
    (hcore : (P 0 ⊓ P 1).normalCore = ⊥) : d.tits.B.normalCore = ⊥ := by
  let original := RankTwoAmalgam.FaithfulCompletion.ofSubgroups
    (P 0) (P 0 ⊓ P 1) (P 1) inf_le_left inf_le_right hgen
  have hc : original.middle.range.normalCore = ⊥ := by
    dsimp only [original]
    rw [RankTwoAmalgam.FaithfulCompletion.ofSubgroups_middle_range]
    exact hcore
  have h := (d.completion hgen).middle_normalCore_eq_bot_of_model original hc
  rwa [d.completion_middle_range] at h

end MarkedQuotient
end Theory.AlgebraicGroup.TitsSystem.SourceBinary
