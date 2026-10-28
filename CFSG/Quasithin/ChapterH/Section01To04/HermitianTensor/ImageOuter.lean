module

public import Theory.Representation.HermitianTensorThree.ImageOuter.OuterInvolutions.Sections

/-!
# The faithful Hermitian image and all outer involution sections

The descended kernel is the norm-one cubic scalars, also the kernel on the
full tensor. Thus the literal image is PSL₃(E) for odd n and SL₃(E) for even n.
The identifications below apply these results to the actual solvable residual
of a source overgroup M, with compatibility for the given binary action.

The full normalizer retains GL₃ congruences, including inner-diagonal maps,
and coefficient automorphisms. Its proved coverage discharges the inputs of
the outer involution and rank theorems. Every outer involution is F-linear
and has an F-linear normalizer conjugator to the marked field swap. This
transports the literal fixed and moved spaces and both quotient actions,
proving every clause of H.4.4(6). The source two-rank is exactly 4n.
All source applications retain the equation L = M∞ and the given faithful
binary action. The PGL₃(4) congruence extension for H.4.6(3) is re-exported.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.377 and 380–382.
-/


@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterH.Section01To04.HermitianTensor.ImageOuter
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter

variable (n : ℕ) [NeZero n]
variable (M : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hM : SourceOvergroup n M)

/-- The actual residual of the source group, identified with its literal image on V. -/
def residualEquivBinaryImage : Subgroup.solvableResidual M ≃* binaryImage n :=
  ((Subgroup.solvableResidual M).equivMapOfInjective M.subtype M.subtype_injective).trans
    (MulEquiv.subgroupCongr hM)

theorem residualEquivBinaryImage_apply (g : Subgroup.solvableResidual M) :
    (residualEquivBinaryImage n M hM g).val = g.val.val := rfl

def residualEquivImage : Subgroup.solvableResidual M ≃* Image n :=
  (residualEquivBinaryImage n M hM).trans (binaryImageEquiv n).symm

/-- The comparison retains the given action, rather than just the group isomorphism type. -/
theorem residualEquivImage_action (g : Subgroup.solvableResidual M) (X : Space n) :
    imageAction n (residualEquivImage n M hM g) X = overgroupAction n M g.val X := by
  rw [← binaryImageEquiv_apply]
  change ((binaryImageEquiv n) ((binaryImageEquiv n).symm
    (residualEquivBinaryImage n M hM g))).val X = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- H.4.4(7), odd n, for L = M∞ with its actual faithful tensor image. -/
def residualEquivPSL (hn : Odd n) :
    Subgroup.solvableResidual M ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (E n) :=
  (residualEquivImage n M hM).trans (imageEquivPSL n hn)

/-- H.4.4(7), even n, retaining the full special linear group. -/
def residualEquivSL (hn : Even n) : Subgroup.solvableResidual M ≃* Cover n :=
  (residualEquivImage n M hM).trans (imageEquivSL n hn)

include hM in
/-- The source overgroup meets the concrete input of the remaining normalizer theorem. -/
theorem source_mem_normalizer (g : M) : g.val ∈ binaryNormalizer n :=
  sourceOvergroup_le_normalizer n M hM g.property

open Subgroup

include hM in
/-- The source group acts by full semilinear congruences, with inner-diagonal factors. -/
theorem source_congruence (g : M) : HasCongruenceExpression n g.val :=
  sourceOvergroup_hasCongruenceExpression n M hM g.val g.property

include hM in
/-- The actual source overgroup has the two-rank stated in H.4.2. -/
theorem source_twoRank_eq : primeRank 2 M = 4 * n :=
  OuterRank.sourceOvergroup_twoRank_eq n (normalizerCoverage n)
    ⟨FieldSections.centralizerEquiv n⟩ M hM

include hM in
theorem source_twoRank_le : primeRank 2 M ≤ 4 * n := (source_twoRank_eq n M hM).le

include hM in
/-- Fusion takes place in the full normalizer; it transports M and its residual. -/
theorem source_outer_conjugacy (i : M) (hi2 : orderOf i = 2)
    (hiL : i.val ∉ binaryImage n) :
    ∃ c ∈ binaryNormalizer n,
      MulAut.conj c i.val = fieldSwapBinary n ∧
      SourceOvergroup n (M.map (MulAut.conj c).toMonoidHom) ∧
      fieldSwapBinary n ∈ M.map (MulAut.conj c).toMonoidHom :=
  OuterRank.source_outer_involution_transport_of_coverage n (normalizerCoverage n) M hM i hi2 hiL

include hM in
/-- The original outer involution preserves F, with an F-linear conjugator. -/
theorem source_outer_linear (i : M) (hi2 : orderOf i = 2)
    (hiL : i.val ∉ binaryImage n) :
    ∃ (j c : Space n ≃ₗ[F n] Space n), binaryEquiv n j = i.val ∧
      binaryEquiv n c ∈ binaryNormalizer n ∧
      MulAut.conj (binaryEquiv n c) (binaryEquiv n j) = fieldSwapBinary n :=
  OuterInvolutions.exists_linear_lift_and_conjugator n i.val (source_mem_normalizer n M hM i)
    ((orderOf_coe i).trans hi2) hiL

include hM in
/-- H.4.4(6): the fixed space of each outer involution has binary dimension 6n. -/
theorem source_outer_fixed_dimension (i : M) (hi2 : orderOf i = 2)
    (hiL : i.val ∉ binaryImage n) :
    Module.finrank (ZMod 2) (LinearMap.ker (i.val.toLinearMap - LinearMap.id)) = 6 * n := by
  obtain ⟨j, c, hj, hc, hci⟩ := source_outer_linear n M hM i hi2 hiL
  rw [← hj]
  exact OuterInvolutions.finrank_binaryFixed n j c hci

include hM in
/-- H.4.4(6): the pointwise centralizer in M is precisely the cyclic subgroup of i. -/
theorem source_outer_pointwise (i : M) (hi2 : orderOf i = 2)
    (hiL : i.val ∉ binaryImage n) (g : M) :
    (∀ X : Space n, i.val X = X → g.val X = X) ↔ g ∈ Subgroup.zpowers i := by
  obtain ⟨j, c, hj, hc, hci⟩ := source_outer_linear n M hM i hi2 hiL
  have hjM : binaryEquiv n j ∈ M := hj.symm ▸ i.property
  have hpoint := OuterInvolutions.source_relative_pointwiseFixed_eq n j c hc hci M hM hjM
  have hei : (⟨binaryEquiv n j, hjM⟩ : M) = i := Subtype.ext hj
  rw [hei] at hpoint
  have hmem := SetLike.ext_iff.mp hpoint g
  change (∀ X : OuterInvolutions.fixed n j, g.val X.val = X.val) ↔ g ∈ Subgroup.zpowers i at hmem
  rw [← hmem]
  constructor
  · intro h X
    apply h X.val
    rw [← hj]
    exact (OuterInvolutions.mem_fixed n j X.val).mp X.property
  · intro h X hX
    apply h ⟨X, ?_⟩
    apply (OuterInvolutions.mem_fixed n j X).mpr
    change binaryEquiv n j X = X
    rw [hj, hX]

include hM in
/-- H.4.4(6): the full centralizer in the actual residual image is SL₃(F). -/
theorem source_outer_centralizer (i : M) (hi2 : orderOf i = 2)
    (hiL : i.val ∉ binaryImage n) :
    Nonempty (↥(binaryImage n ⊓ Subgroup.centralizer ({i.val} : Set _)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (F n)) := by
  obtain ⟨j, c, hj, hc, hci⟩ := source_outer_linear n M hM i hi2 hiL
  rw [← hj]
  exact ⟨OuterInvolutions.centralizerEquiv n j c hc hci⟩

include hM in
/-- H.4.4(6): the three inherited actions are faithful and F-dimension three.
The witness j is the given involution, with scalars retained, so these are
literally [V,i], C_V(i)/[V,i], and V/C_V(i). -/
theorem source_outer_sections (i : M) (hi2 : orderOf i = 2)
    (hiL : i.val ∉ binaryImage n) :
    ∃ j : Space n ≃ₗ[F n] Space n,
      binaryEquiv n j = i.val ∧
      OuterInvolutions.moved n j ≤ OuterInvolutions.fixed n j ∧
      Module.finrank (F n) (OuterInvolutions.fixed n j) = 6 ∧
      Module.finrank (F n) (OuterInvolutions.moved n j) = 3 ∧
      Module.finrank (F n) ((OuterInvolutions.fixed n j) ⧸ OuterInvolutions.movedInFixed n j) = 3 ∧
      Module.finrank (F n) ((Space n) ⧸ OuterInvolutions.fixed n j) = 3 ∧
      Function.Injective (OuterInvolutions.movedAction n j) ∧
      Function.Injective (OuterInvolutions.middleAction n j) ∧
      Function.Injective (OuterInvolutions.topAction n j) := by
  obtain ⟨j, c, hj, hc, hci⟩ := source_outer_linear n M hM i hi2 hiL
  exact ⟨j, hj, OuterInvolutions.moved_le_fixed n j c hci, OuterInvolutions.finrank_fixed n j c hci,
    OuterInvolutions.finrank_moved n j c hci, OuterInvolutions.finrank_middle n j c hci, OuterInvolutions.finrank_top n j c hci,
    OuterInvolutions.movedAction_faithful n j c hc hci, OuterInvolutions.middleAction_faithful n j c hc hci,
    OuterInvolutions.topAction_faithful n j c hc hci⟩

end CFSG.Quasithin.ChapterH.Section01To04.HermitianTensor.ImageOuter
