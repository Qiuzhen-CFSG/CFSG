module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.SmallResidualNormalizer
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralFiveQuotient
public import Theory.GroupTheory.PPerfectHom

/-!
# The marked-five rank-one witness

In the marked-five row the witness in original 15.2.6 is Y itself.
The faithful cyclic residual image identifies its action kernel with its
two-core. The existing quotient and seed-span theorems then supply the
rank-one model and unique maximal overgroup. Normalization by C_M(V)
also supplies the cubic normalizer assertion of 15.2.7.

The Omega comparison and rank-one selection, and the cubic row, are
separate source obligations; they are not assumed in this marked-five result.
Source: Aschbacher--Smith 15.2.6--7, printed p.1109.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

private theorem residual_notation (K : Subgroup G) :
    twoResidualAmbient K = (pResidual 2 K).map K.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN,n,hn⟩
    exact ⟨hN,IsPGroup.of_card hn⟩
  · rintro ⟨hN,hn⟩
    exact ⟨hN,IsPGroup.iff_card.mp hn⟩

/-- The original residual is two-perfect with its literal relative orbit group. -/
theorem ChosenSmallSource.residual_perfect
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) :
    IsPPerfect 2 h.residual := by
  let := h.prepared.elementary
  change IsPPerfect 2 (twoResidualAmbient (conjugateSpanBy ((M ⊓ Mc).pCoreIn 2)
    (twoResidualAmbient (chosenStarredPreimage M V h.prepared.normalized) ⊔ (T : Subgroup G))))
  rw [residual_notation]
  exact isPPerfect_embedded_pResidual 2 _

/-- The literal residual is T-invariant; ambient normality is not asserted. -/
theorem ChosenSmallSource.residual_invariant
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V) :
    (T : Subgroup G) ≤ normalizer (h.residual : Set G) := by
  let := h.prepared.elementary
  exact le_sup_right.trans
    (source_chosen_centralizer_sylow_normalizes_residual T h.maximal.1.2 h.partner h.prepared).1

/-- The centralizer in a cyclic-image residual is its intrinsic two-core.
The order assumption is used only to exclude two-torsion in the action image. -/
theorem ChosenSmallSource.residual_centralizer_of_prime_image
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hc : letI := h.prepared.elementary
      Nat.card ((h.residual.subgroupOf M).map
        (actionHom M V h.prepared.normalized).rangeRestrict) = p) :
    h.residual ⊓ centralizer (V : Set G) = h.residual.pCoreIn 2 := by
  let := h.prepared.elementary
  let Y := h.residual
  let f := (actionHom M V h.prepared.normalized).rangeRestrict
  have hYM : Y ≤ M := source_caseIIResidual_le T h.maximal.1.2 (map_subtype_le _)
  let a := f.comp (inclusion hYM)
  have ha : a.range = (Y.subgroupOf M).map f := by
    ext d
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨⟨y,hYM y.property⟩,y.property,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
  have hbound := source_chosen_cyclic_kernel_le_core T h.maximal.1.2 h.partner h.prepared
    (isCyclic_of_prime_card hc)
  have hcore : a.ker.map Y.subtype ≤ M.pCoreIn 2 := by
    rintro x ⟨y,hy,rfl⟩
    exact mem_map.mpr ⟨inclusion hYM y,hbound ⟨y.property,congrArg Subtype.val hy⟩,rfl⟩
  have hi : a.ker.index = p := by rw [index_ker,ha]; exact hc
  have hk : IsPGroup 2 a.ker :=
    ((isPGroup_pCoreIn 2 M).to_le hcore).of_equiv
      (equivMapOfInjective a.ker Y.subtype Y.subtype_injective).symm
  have hodd : ¬ 2 ∣ a.ker.index := by
    rw [hi]
    exact fun hd => hp ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).mp hd).symm
  let P : Sylow 2 Y := hk.toSylow hodd
  have he : pCore 2 Y = a.ker := le_antisymm
    (pCore_isPGroup.le_sylow_of_normal P) (le_sSup ⟨inferInstance,hk⟩)
  change Y ⊓ centralizer (V : Set G) = (pCore 2 Y).map Y.subtype
  rw [he]
  ext x
  constructor
  · intro hx
    refine ⟨⟨x,hx.1⟩,?_,rfl⟩
    apply Subtype.ext
    exact show (⟨x,hYM hx.1⟩ : M) ∈ (actionHom M V h.prepared.normalized).ker from
      (actionHom_ker M V h.prepared.normalized).symm ▸ hx.2
  · rintro ⟨y,hy,rfl⟩
    refine ⟨y.property,?_⟩
    have hz : inclusion hYM y ∈ (actionHom M V h.prepared.normalized).ker :=
      congrArg Subtype.val hy
    rwa [actionHom_ker] at hz

/-- Original 15.2.6 and the cubic clause of 15.2.7 in the marked-five row,
with the source choice Y₁ = Y and all witness premises discharged. -/
theorem ChosenSmallSource.smallResidualWitness_of_marked_five
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2) :
    SmallResidualWitness h h.residual ∧ SmallCubicNormalizer h h.residual := by
  let := h.prepared.elementary
  obtain ⟨l,hd⟩ := hd
  have hp : PrimeDimensionOptions 5 2 :=
    (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  have hq := source_dihedral_five_join_quotient h.ambient T h.empty h.maximal h.centralizing
    h.partner h.many h.prepared l hp hd
  have him := source_dihedral_caseIIResidual_image h.ambient T h.empty h.maximal h.centralizing
    h.partner h.many h.prepared l hp hd
  have hc : Nat.card ((h.residual.subgroupOf M).map
      (actionHom M V h.prepared.normalized).rangeRestrict) = 5 := by
    exact (congrArg (fun K : Subgroup (internalActionImage M V h.prepared.normalized) => Nat.card K) him).trans
      ((card_map_of_injective (Jhat (imageRepresentation M V h.prepared.normalized)).subtype_injective).trans
        hd.card_kernel)
  have hw : SmallResidualWitness h h.residual :=
    ⟨le_rfl,h.residual_perfect,h.residual_invariant,Or.inr hq,
      h.residual_centralizer_of_prime_image (by decide : 5 ≠ 2) hc,
      source_dihedral_five_residual_sylow_unique h.ambient T h.empty h.maximal h.centralizing
        h.partner h.many h.prepared l hp hd⟩
  exact ⟨hw,hw.cubicNormalizer⟩

/-- A subgroup moved fully by Rc escapes Mc: if it lay in M cap Mc,
its commutator would lie in the normal two-subgroup Rc. Two-perfectness
then makes the whole subgroup trivial. This is the last step of 15.2.6. -/
theorem ChosenSmallSource.residual_subgroup_not_le_partner
    {T : Sylow 2 G} {M Mc V Y₁ : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hle : Y₁ ≤ h.residual) (hp : IsPPerfect 2 Y₁) (hne : Y₁ ≠ ⊥)
    (hm : ⁅Y₁,(M ⊓ Mc).pCoreIn 2⁆ = Y₁) : ¬ Y₁ ≤ Mc := by
  let := h.prepared.elementary
  intro hMc
  have hYM : Y₁ ≤ M := hle.trans (source_caseIIResidual_le T h.maximal.1.2 (map_subtype_le _))
  have hn : Y₁ ≤ normalizer ((M ⊓ Mc).pCoreIn 2 : Set G) :=
    (le_inf hYM hMc).trans ((M ⊓ Mc).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (M ⊓ Mc) (pCore 2 ↑(M ⊓ Mc))))
  have hR : Y₁ ≤ (M ⊓ Mc).pCoreIn 2 :=
    hm.symm.le.trans (le_normalizer_iff_commutator_le_right.mp hn)
  have htwo : IsPGroup 2 Y₁ := (isPGroup_pCoreIn 2 (M ⊓ Mc)).to_le hR
  have hid := hp.hom_eq_one_of_isPGroup htwo (MonoidHom.id Y₁)
  apply hne
  apply bot_unique
  intro y hy
  exact congrArg Y₁.subtype (DFunLike.congr_fun hid ⟨y,hy⟩)

/-- Once original 15.2.5 is supplied, every moved nontrivial two-perfect
subgroup of Y has M as its unique maximal two-local overgroup with T. -/
theorem ChosenSmallSource.residual_subgroup_unique_of_overgroups
    {T : Sylow 2 G} {M Mc V Y₁ : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hover : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hle : Y₁ ≤ h.residual) (hp : IsPPerfect 2 Y₁) (hne : Y₁ ≠ ⊥)
    (hm : ⁅Y₁,(M ⊓ Mc).pCoreIn 2⁆ = Y₁) :
    maximalTwoLocalOvergroups (Y₁ ⊔ (T : Subgroup G)) = {M} := by
  let := h.prepared.elementary
  apply Set.Subset.antisymm
  · intro N hN
    have ht : N ∈ maximalTwoLocalOvergroups (T : Subgroup G) :=
      ⟨hN.1,le_sup_right.trans hN.2⟩
    rw [hover] at ht
    rcases Set.mem_insert_iff.mp ht with rfl | ht
    · exact Set.mem_singleton _
    · obtain rfl := Set.mem_singleton_iff.mp ht
      exact (h.residual_subgroup_not_le_partner hle hp hne hm
        (le_sup_left.trans hN.2)).elim
  · apply Set.singleton_subset_iff.mpr
    exact ⟨h.maximal.1.1,sup_le
      (hle.trans (source_caseIIResidual_le T h.maximal.1.2 (map_subtype_le _))) h.maximal.1.2⟩

/-- Actual source assembly for a selected rank-one subgroup. The input
movement is the source construction Y₁=[Y₁,Rc], not a uniqueness premise.
The Omega comparison and rank-one selection still have to supply their
independent inputs before this proves original 15.2.6 unconditionally. -/
theorem ChosenSmallSource.smallResidualWitness_of_moved_selection
    {T : Sylow 2 G} {M Mc V Y₁ : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hover : maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc})
    (hle : Y₁ ≤ h.residual) (hp : IsPPerfect 2 Y₁) (hne : Y₁ ≠ ⊥)
    (hn : (T : Subgroup G) ≤ normalizer (Y₁ : Set G))
    (hm : ⁅Y₁,(M ⊓ Mc).pCoreIn 2⁆ = Y₁)
    (hq : let L := Y₁ ⊔ (M ⊓ Mc).pCoreIn 2
      Nonempty ((L ⧸ pCore 2 L) ≃* Equiv.Perm (Fin 3)) ∨
        Nonempty ((L ⧸ pCore 2 L) ≃* DihedralGroup 5) ∨
        Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0))
    (hc : Y₁ ⊓ centralizer (V : Set G) = Y₁.pCoreIn 2) :
    SmallResidualWitness h Y₁ ∧ SmallCubicNormalizer h Y₁ := by
  have hw : SmallResidualWitness h Y₁ :=
    ⟨hle,hp,hn,hq,hc,h.residual_subgroup_unique_of_overgroups hover hle hp hne hm⟩
  exact ⟨hw,hw.cubicNormalizer⟩

end CFSG.Quasithin.Chapter15.Section02
