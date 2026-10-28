module

public import Theory.SpecificGroups.Suzuki.SchurCoverReduction
public import Theory.GroupAction.CardFourCubicKlein
public import Theory.SpecificGroups.Suzuki.MultiplierFieldAction
public import Theory.GroupTheory.CoveringKernelEquiv
public import Theory.SpecificGroups.Suzuki.SchurEightCover
public import Theory.SpecificGroups.Suzuki.SchurEightUpper
public import Theory.SpecificGroups.Suzuki.SchurFamilySplitting
public import Theory.GroupTheory.UniversalCoverKernelTransport

/-!
# The Suzuki multiplier calculation

Here `SuzukiMatrixGroup m` is Sz(2^(2*m+1)); the exceptional parameter is
`m = 1`, and the remaining simple family has `m ≥ 2`. The shared `SzModel`
has the same subgroup by `szModel_eq_suzukiMatrixGroup` in
`BenderSuzuki.MatrixGroups.SuzukiModel`.

The finite universal cover and its two-group kernel are constructed in the
imported reduction. A genuine fourfold cover and an upper bound of four
certify universality. The actual nontrivial Frobenius action then recovers
the kernel's E₄ structure, and cover comparison transports it to the
canonical kernel. The constructed ordinary root section kills the canonical
kernel and makes the identity cover universal for every `m ≥ 2`.

The unconditional results below discharge all premises of the retained
conditional reductions. Both explicit covers have the unique lifting property
for finite perfect central covers in every target universe. The final two
theorems transport the full kernel calculations through actual model
isomorphisms, supplying the two Suzuki inputs to the source multiplier table.

Source: Aschbacher–Smith I.1.3(5) and the exhaustive list in I.1.3, printed
p.407/PDF p.418 of `refs/quasithin.pdf`; GLS3 sections 6.1 and 6.3.
-/

public section
universe u

open BenderSuzuki.MatrixGroups Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.LieMultipliers.Suzuki

local instance : Fact (0 < (1 : ℕ)) := ⟨by decide⟩

/-- A universal kernel of order four is elementary abelian: the genuine
Frobenius lift acts nontrivially with cube one, which excludes C4. -/
theorem kernel_equiv_four_of_card
    {S U : Type} [Group S] [Finite S] [IsQuasisimple S]
    [Group U] [Finite U] [IsQuasisimple U]
    (e : S ≃* SuzukiMatrixGroup 1) (f : Covering U S)
    (hf : Covering.IsUniversal.{0,0,0} f)
    (hfour : Nat.card f.toMonoidHom.ker = 4) :
    Nonempty (f.toMonoidHom.ker ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :=
  Theory.GroupAction.CardFourCubic.nonempty_mulEquiv_two_prod_of_cubic hfour
    (Covering.multiplierAction f hf (MulAut.congr e.symm (suzukiFieldAutomorphism 1)))
    (MultiplierFieldAction.multiplierAction_cube e f hf)
    (MultiplierFieldAction.multiplierAction_ne_one e f hf hfour)

/-- The exceptional order bound and a genuine fourfold perfect central
extension together certify that extension as universal, including E4 structure. -/
theorem exceptional_cover_of_bounds
    {E : Type} [Group E] [Finite E] [IsQuasisimple E]
    (f : Covering E (SuzukiMatrixGroup 1))
    (hfour : Nat.card f.toMonoidHom.ker = 4)
    (hupper : Nat.card (SchurCover.Kernel 1) ≤ 4) :
    Covering.IsUniversal.{0,0,u} f ∧
      Nonempty (f.toMonoidHom.ker ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  have hbound : Nat.card (SchurCover.Kernel 1) ≤ Nat.card f.toMonoidHom.ker := by
    rw [hfour]
    exact hupper
  exact ⟨Covering.isUniversal_of_kernel_card_le f hbound,
    kernel_equiv_four_of_card (MulEquiv.refl _) f
      (Covering.isUniversal_of_kernel_card_le f hbound) hfour⟩

/-- Transfer the calculated kernel through the universal-cover comparison;
this retains group structure and the actual matrix identification. -/
theorem universalKernel_equiv_four_of_bounds
    {E : Type} [Group E] [Finite E] [IsQuasisimple E]
    (f : Covering E (SuzukiMatrixGroup 1))
    (hfour : Nat.card f.toMonoidHom.ker = 4)
    (hupper : Nat.card (SchurCover.Kernel 1) ≤ 4) :
    Nonempty (SchurCover.Kernel 1 ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  obtain ⟨hf, ⟨e⟩⟩ := exceptional_cover_of_bounds.{0} f hfour hupper
  exact ⟨((SchurCover.cover_isUniversal.{0} 1).kerMulEquiv hf
    (MulEquiv.refl _)).trans e⟩

/-- For the remaining family, a local upper bound of one suffices
to make the literal identity map universal in every target universe. -/
theorem identity_isUniversal_of_kernel_bound
    (m : ℕ) [Fact (0 < m)] (hupper : Nat.card (SchurCover.Kernel m) ≤ 1) :
    Covering.IsUniversal.{0,0,u} (Covering.id : Covering (SuzukiMatrixGroup m)
      (SuzukiMatrixGroup m)) := by
  apply Covering.isUniversal_of_kernel_card_le
  simpa using hupper

/-- The same bound gives an actual trivial universal kernel. -/
theorem universalKernel_eq_bot_of_bound
    (m : ℕ) (hupper : Nat.card (SchurCover.Kernel m) ≤ 1) :
    SchurCover.Kernel m = ⊥ := by
  exact Subgroup.card_eq_one.mp (Nat.le_antisymm hupper Nat.card_pos)

/-- Apply the transfer reduction to the actual universal projection. A root
section discharges the vanishing and identity-cover conclusions simultaneously.
The ordinary-family construction below supplies this section for `m ≥ 2`. -/
theorem ordinary_conclusions_of_rootSection
    (m : ℕ) [hm : Fact (0 < m)]
    (s : SuzukiRootSubgroup m →* SchurCover.CoverGroup m)
    (hs : (PerfectCentralCovering.universalProjection (SuzukiMatrixGroup m)).comp s =
      (SuzukiRootSubgroup m).subtype) :
    SchurCover.Kernel m = ⊥ ∧
      Covering.IsUniversal.{0,0,u} (Covering.id : Covering (SuzukiMatrixGroup m)
        (SuzukiMatrixGroup m)) := by
  have hk : SchurCover.Kernel m = ⊥ := SchurCover.kernel_eq_bot_of_rootSection hm.out
    (PerfectCentralCovering.universalCover _) s hs
  refine ⟨hk, identity_isUniversal_of_kernel_bound m ?_⟩
  simp [hk]

/-- The exceptional local lift supplies the global upper bound, while a
separately constructed fourfold perfect central extension supplies the lower
bound. All maps land in the actual matrix group. -/
theorem exceptional_conclusions_of_rootLift
    {E : Type} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (SuzukiMatrixGroup 1))
    (hfour : Nat.card f.toMonoidHom.ker = 4)
    (H : Subgroup (SchurCover.CoverGroup 1))
    (hH : H.map (PerfectCentralCovering.universalProjection (SuzukiMatrixGroup 1)) =
      SuzukiRootSubgroup 1)
    (hlocal : Nat.card (H ⊓ SchurCover.Kernel 1 : Subgroup (SchurCover.CoverGroup 1)) ≤ 4) :
    PerfectCentralCovering.IsUniversal.{0,0,u} f ∧
      Nonempty (SchurCover.Kernel 1 ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  let := f.isQuasisimple
  have hb : Nat.card (SchurCover.Kernel 1) ≤ 4 :=
    (SchurCover.kernel_card_le_rootLift (by decide)
      (PerfectCentralCovering.universalCover (SuzukiMatrixGroup 1)) H hH).trans hlocal
  have hf : Covering.IsUniversal.{0,0,u} f.toCovering :=
    (exceptional_cover_of_bounds f.toCovering hfour hb).1
  refine ⟨?_, universalKernel_equiv_four_of_bounds f.toCovering hfour hb⟩
  intro M _ _ g
  let := g.isQuasisimple
  obtain ⟨a, ha, hu⟩ := hf M g.toCovering
  refine ⟨a.toMonoidHom, congrArg Covering.toMonoidHom ha, ?_⟩
  intro b hb
  have hbsurj : Function.Surjective b :=
    PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      g.toMonoidHom b (hb ▸ f.surjective) g.ker_le_center
  let b' : Covering E M := ⟨b, hbsurj⟩
  have hb' : g.toCovering.comp b' = f.toCovering := by
    apply Covering.ext
    intro x
    exact DFunLike.congr_fun hb x
  exact congrArg Covering.toMonoidHom (hu b' hb')

/-- The explicit finite fourfold permutation cover is quasisimple. -/
instance exceptional_isQuasisimple : IsQuasisimple SchurEightCover.E :=
  SchurEightCover.cover.isQuasisimple

/-- The constructed fourfold cover of the native Sz(8) is universal, and the
canonical universal kernel is E₄. The local-lift premises are discharged. -/
theorem exceptional_conclusions :
    PerfectCentralCovering.IsUniversal.{0,0,u} SchurEightCover.cover ∧
      Nonempty (SchurCover.Kernel 1 ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  obtain ⟨H, hH, hlocal⟩ := SchurCover.EightLocal.exists_rootLift
  exact exceptional_conclusions_of_rootLift SchurEightCover.cover
    SchurEightCover.cover_kernel_card H hH hlocal

/-- Universality of the explicit Sz(8) cover for every finite perfect central
target cover, in any universe. -/
theorem exceptional_cover_isUniversal :
    PerfectCentralCovering.IsUniversal.{0,0,u} SchurEightCover.cover :=
  exceptional_conclusions.1

/-- The same explicit cover in the finite quasisimple covering API. -/
theorem exceptional_covering_isUniversal :
    Covering.IsUniversal.{0,0,u} SchurEightCover.cover.toCovering :=
  PerfectCentralCovering.IsUniversal.toCovering SchurEightCover.cover
    exceptional_cover_isUniversal

/-- The kernel of the explicit universal Sz(8) cover, with its full group
structure rather than only its cardinality. -/
noncomputable def exceptionalKernelEquiv : SchurEightCover.cover.toMonoidHom.ker ≃*
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
  Classical.choice (kernel_equiv_four_of_card (MulEquiv.refl _)
    SchurEightCover.cover.toCovering exceptional_covering_isUniversal
    SchurEightCover.cover_kernel_card)

/-- The literal kernel of the canonical universal projection onto Sz(8). -/
noncomputable def exceptionalUniversalKernelEquiv : SchurCover.Kernel 1 ≃*
    (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
  Classical.choice exceptional_conclusions.{0}.2

/-- The exceptional canonical kernel has order four. -/
theorem exceptional_universalKernel_card : Nat.card (SchurCover.Kernel 1) = 4 :=
  Nat.le_antisymm SchurCover.EightLocal.kernel_card_le_four
    SchurEightCover.four_le_universalKernel_card

/-- The remaining simple Suzuki family starts at Sz(32) and has trivial
canonical universal kernel. -/
theorem ordinary_universalKernel_eq_bot (m : ℕ) (hm : 2 ≤ m) :
    SchurCover.Kernel m = ⊥ :=
  SchurCover.Family.canonicalKernel_eq_bot m hm

/-- The identity covering is universal for every nonexceptional parameter. -/
theorem ordinary_identity_isUniversal (m : ℕ) [Fact (0 < m)] (hm : 2 ≤ m) :
    Covering.IsUniversal.{0,0,u} (Covering.id : Covering (SuzukiMatrixGroup m)
      (SuzukiMatrixGroup m)) :=
  (ordinary_conclusions_of_rootSection m (SchurCover.Family.rootSection m hm)
    (SchurCover.Family.universalProjection_comp_rootSection m hm)).2

/-- The explicit ordinary-family cover is the identity of the matrix group. -/
@[expose] noncomputable def ordinaryCover (m : ℕ) (hm : 2 ≤ m) :
    PerfectCentralCovering.Cover (SuzukiMatrixGroup m) (SuzukiMatrixGroup m) where
  toMonoidHom := MonoidHom.id _
  surjective := Function.surjective_id
  isPerfect := SchurCover.isPerfect m (by omega)
  ker_le_center := by simp

/-- The explicit ordinary-family cover has trivial kernel. -/
theorem ordinaryCover_kernel (m : ℕ) (hm : 2 ≤ m) :
    (ordinaryCover m hm).toMonoidHom.ker = ⊥ := by
  simp [ordinaryCover]

/-- Every finite perfect central covering of an ordinary Suzuki group admits
a unique lift from its identity cover, with no local splitting premise. -/
theorem ordinaryCover_isUniversal (m : ℕ) (hm : 2 ≤ m) :
    PerfectCentralCovering.IsUniversal.{0,0,u} (ordinaryCover m hm) := by
  let : Fact (0 < m) := ⟨by omega⟩
  intro M _ _ g
  let := g.isQuasisimple
  obtain ⟨a, ha, _⟩ := ordinary_identity_isUniversal.{u} m hm M g.toCovering
  have hfac : g.toMonoidHom.comp a.toMonoidHom =
      (ordinaryCover m hm).toMonoidHom := congrArg Covering.toMonoidHom ha
  refine ⟨a.toMonoidHom, hfac, ?_⟩
  intro b hb
  exact PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
    g.toMonoidHom g.ker_le_center b a.toMonoidHom (hb.trans hfac.symm)

/-- I.1.3(5) for any group actually isomorphic to the native Sz(8). This
discharges the source table's `KernelInputs.suzukiEight` clause. -/
theorem schurMultiplier_equiv_four
    {S : Type u} [Group S] [Group.IsPerfect S]
    (hS : Nonempty (S ≃* SuzukiMatrixGroup 1)) :
    Nonempty (PerfectCentralCovering.schurMultiplier S ≃*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  obtain ⟨e⟩ := hS
  let : Finite S := Finite.of_equiv _ e.symm.toEquiv
  exact ⟨(PerfectCentralCovering.schurMultiplierEquivOfUniversal e
    SchurEightCover.cover.toCovering exceptional_covering_isUniversal).trans
      exceptionalKernelEquiv⟩

/-- The vanishing Suzuki rows in the exhaustive I.1.3 list, transported
through the actual model isomorphism. This is `KernelInputs.suzukiOther`. -/
theorem schurMultiplier_subsingleton
    {S : Type u} [Group S] [Group.IsPerfect S]
    (m : ℕ) (hm : 1 < m) (hS : Nonempty (S ≃* SuzukiMatrixGroup m)) :
    Subsingleton (PerfectCentralCovering.schurMultiplier S) := by
  obtain ⟨e⟩ := hS
  let : Finite S := Finite.of_equiv _ e.symm.toEquiv
  let : Fact (0 < m) := ⟨by omega⟩
  let : Subsingleton (PerfectCentralCovering.schurMultiplier (SuzukiMatrixGroup m)) := by
    change Subsingleton (SchurCover.Kernel m)
    rw [ordinary_universalKernel_eq_bot m hm]
    infer_instance
  exact (PerfectCentralCovering.schurMultiplierCongr e).injective.subsingleton

end CFSG.Quasithin.ChapterI.LieMultipliers.Suzuki

end
