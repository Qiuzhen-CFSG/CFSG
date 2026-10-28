module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl.Dimension
public import Theory.Representation.BinaryOffender.TimmesfeldCentralizer
public import Theory.Representation.BinaryOffender.IrreducibleDiagonal
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.CoreAction.Descent.ComponentOffender.BestProjection.CentralTwist

/-!
# Best-offender transfer across a commuting component kernel

A best offender with nontrivial SL₃(2) projection has a quadratic best-offender
replacement whose projection remains nontrivial, is injective, and has rank at
most two. If the displacement centralizer lay in the commuting kernel, its
fixed space would contain all component commutators and therefore all of V,
contrary to faithfulness. For a quadratic offender, a kernel element has a
component-invariant displacement space fixed by the offender; the full
component commutator then forces that element to act trivially.

The central-twist bound puts every element of the quadratic replacement in
the component: its nonidentity elements have nontrivial projection and
displacement at most two. Transporting this replacement along the retraction
gives an offender on the whole restricted module. No offender inequality for
the projection of the original best offender is assumed or claimed. The
conditional transfer remains available separately, while the final theorem
discharges its small-involution premise using `CentralTwist`.

Source motivation: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.1.5–11 and B.7.1, printed pp.69–73 and 118–119; the binary MS application is
C.1.31–34, pp.135–137, in the combined manuscript of 1 March 2004. The
replacement theorem used here is GLS, vol.2, Theorem 26.23(i), as proved in
`Theory.Representation.BinaryOffender.TimmesfeldCentralizer`. The transfer
reduction here is separate from the source MS classification theorem.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.ComponentOffender.BestProjection
variable {G K V : Type*} [Group G] [Group K]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)
  (i : K →* G) (r : G →* K) (hri : ∀ k, r (i k) = k)
  (hcent : r.ker ≤ centralizer (i.range : Set G))

include hri hcent in
private theorem range_normal : i.range.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  have hn : g * (i (r g))⁻¹ ∈ r.ker := by
    change r (g * (i (r g))⁻¹) = 1
    simp only [map_mul, map_inv, hri, mul_inv_cancel]
  have h1 := (centralizer_le_normalizer (i.range : Set G)) (hcent hn)
  have h2 := (le_normalizer : i.range ≤ normalizer (i.range : Set G)) (show i (r g) ∈ i.range from ⟨r g, rfl⟩)
  simpa only [inv_mul_cancel_right] using (normalizer (i.range : Set G)).mul_mem h1 h2

include hri hcent in
private theorem commutator_range_eq [IsSimpleGroup K]
    (hZ : center K = ⊥) {A : Subgroup G} (hA : A.map r ≠ ⊥) :
    ⁅i.range, A⁆ = i.range := by
  have hi : Function.Injective i := Function.LeftInverse.injective hri
  let : IsSimpleGroup i.range := (MonoidHom.ofInjective hi).symm.isSimpleGroup
  let : i.range.Normal := range_normal i r hri hcent
  have hle : ⁅i.range, A⁆ ≤ i.range := commutator_le_left _ _
  have hn : (⁅i.range, A⁆.subgroupOf i.range).Normal :=
    normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left _ _)
  rcases (Subgroup.isSimpleGroup_iff.mp (inferInstance : IsSimpleGroup i.range)).2 _ hle hn with hb | he
  · exfalso
    apply hA
    apply le_bot_iff.mp
    rintro _ ⟨a, ha, rfl⟩
    rw [← hZ]
    apply mem_center_iff.mpr
    intro k
    have hc := (commutator_eq_bot_iff_le_centralizer.mp hb) (show i k ∈ i.range from ⟨k, rfl⟩)
    have heq := (mem_centralizer_iff.mp hc) a ha
    simpa only [map_mul, hri] using congrArg r heq.symm
  · exact he

private theorem full_commutator_range
    (hfull : subspaceCommutator (ρ.comp i) ⊤ ⊤ = ⊤) :
    subspaceCommutator ρ ⊤ i.range = ⊤ := by
  apply top_unique
  calc
    ⊤ = subspaceCommutator (ρ.comp i) ⊤ ⊤ := hfull.symm
    _ ≤ subspaceCommutator ρ ⊤ i.range := ?_
  apply Submodule.span_le.mpr
  rintro _ ⟨k, _, v, _, rfl⟩
  exact Submodule.subset_span ⟨i k, ⟨k, rfl⟩, v, trivial, rfl⟩

private theorem fixedSpace_stable_of_commuting {B X : Subgroup G}
    (hc : B ≤ centralizer (X : Set G)) :
    X ≤ subspaceStabilizer ρ (fixedSpace ρ B) := by
  apply le_subspaceStabilizer
  intro x hx v hv b
  have he : b.val * x = x * b.val :=
    ((mem_centralizer_iff.mp (hc b.property)) x hx).symm
  change ρ b.val (ρ x v) = ρ x v
  rw [← Module.End.mul_apply, ← map_mul, he, map_mul, Module.End.mul_apply]
  exact congrArg (ρ x) (hv b)


private def displacementSubgroup (W : Submodule (ZMod 2) V) : Subgroup G where
  carrier := {g | ∀ v, ρ g v - v ∈ W}
  one_mem' := by intro v; simp
  mul_mem' := by
    intro g h hg hh v
    have hm := W.add_mem (hg (ρ h v)) (hh v)
    simpa only [map_mul, Module.End.mul_apply, sub_add_sub_cancel] using hm
  inv_mem' := by
    intro g hg v
    have hm := W.neg_mem (hg (ρ g⁻¹ v))
    simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply, neg_sub] using hm

private theorem displacementSubgroup_normalized (W : Submodule (ZMod 2) V)
    {X : Subgroup G} (hX : X ≤ subspaceStabilizer ρ W) :
    X ≤ normalizer (displacementSubgroup ρ W : Set G) := by
  apply le_normalizer_iff.mpr
  intro x hx a ha v
  have hm := (hX hx (ρ a (ρ x⁻¹ v) - ρ x⁻¹ v)).2 (ha (ρ x⁻¹ v))
  simpa only [map_sub, map_mul, Module.End.mul_apply, ← Module.End.mul_apply,
    ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, mul_assoc] using hm

variable [Finite G] [FiniteDimensional (ZMod 2) V]

/-- Replacement retains a nontrivial component projection when the component
is generated by its commutators with the original offender. -/
theorem displacementCentralizer_map_ne_bot
    (hfaith : Function.Injective ρ)
    (hfull : subspaceCommutator (ρ.comp i) ⊤ ⊤ = ⊤)
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    (hcomm : ⁅i.range, A⁆ = i.range)
    (hcent : r.ker ≤ centralizer (i.range : Set G)) :
    (displacementCentralizer ρ A).map r ≠ ⊥ := by
  intro hb
  have hB : displacementCentralizer ρ A ≤ r.ker := (Subgroup.map_eq_bot_iff _).mp hb
  let W := fixedSpace ρ (displacementCentralizer ρ A)
  have hW : i.range ≤ subspaceStabilizer ρ W :=
    fixedSpace_stable_of_commuting ρ (hB.trans hcent)
  have hAH : A ≤ displacementSubgroup ρ W := by
    intro a ha v
    exact displacement_mem_fixedSpace_displacementCentralizer ρ ha v
  have hLH : i.range ≤ displacementSubgroup ρ W := by
    rw [← hcomm]
    exact (commutator_mono le_rfl hAH).trans
      (le_normalizer_iff_commutator_le_right.mp (displacementSubgroup_normalized ρ W hW))
  have htop : W = ⊤ := by
    apply top_unique
    calc
      ⊤ = subspaceCommutator ρ ⊤ i.range := (full_commutator_range ρ i hfull).symm
      _ ≤ W := by
        apply Submodule.span_le.mpr
        rintro _ ⟨g, hg, v, _, rfl⟩
        exact hLH hg v
  apply hA.displacementCentralizer_ne_bot ρ
  apply le_bot_iff.mp
  intro b hb
  apply hfaith
  ext v
  rw [map_one, Module.End.one_apply]
  have hv : v ∈ W := htop ▸ Submodule.mem_top
  exact hv ⟨b, hb⟩

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- A quadratic subgroup generating the component by commutators meets its
commuting kernel trivially. -/
theorem quadratic_ker_eq_one
    (hfaith : Function.Injective ρ)
    (hfull : subspaceCommutator (ρ.comp i) ⊤ ⊤ = ⊤)
    {A : Subgroup G} (hq : IsQuadratic ρ A)
    (hcomm : ⁅i.range, A⁆ = i.range)
    (hcent : r.ker ≤ centralizer (i.range : Set G))
    {b : G} (hb : b ∈ A) (hbr : r b = 1) : b = 1 := by
  have hc : ∀ x ∈ i.range, Commute b x := by
    intro x hx
    exact ((mem_centralizer_iff.mp (hcent hbr)) x hx).symm
  let D := LinearMap.range (ρ b - LinearMap.id)
  have hD : i.range ≤ subspaceStabilizer ρ D := by
    apply le_subspaceStabilizer
    rintro x hx _ ⟨v, rfl⟩
    refine ⟨ρ x v, ?_⟩
    change ρ b (ρ x v) - ρ x v = ρ x (ρ b v - v)
    rw [map_sub]
    have he := congrArg (fun g => ρ g v) (hc x hx).eq
    simpa only [map_mul, Module.End.mul_apply] using congrArg (fun w => w - ρ x v) he
  have hDA : D ≤ fixedSpace ρ A := by
    rintro _ ⟨v, rfl⟩ a
    exact hq a a.property b hb v
  have hDX : D ≤ fixedSpace ρ i.range := by
    rw [← hcomm]
    exact le_fixedSpace_commutator_of_invariant ρ hD hDA
  apply hfaith
  ext v
  rw [map_one, Module.End.one_apply]
  apply fixes_commutatorSubspace_of_commutes_of_displacement_fixed ρ hc
    (fun w => hDX ⟨w, rfl⟩) v
  rw [full_commutator_range ρ i hfull]
  trivial

private theorem center_eq_bot_of_equiv
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) : center K = ⊥ := by
  apply le_bot_iff.mp
  intro k hk
  apply e.injective
  rw [map_one]
  have hz : e k ∈ center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
    apply mem_center_iff.mpr
    intro g
    obtain ⟨h, rfl⟩ := e.surjective g
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hk h)
  simpa only [Atlas.Comparisons.Exceptional.sl3Two_center_eq_bot, mem_bot] using hz

include hri hcent in
/-- Quadratic replacement retains nontrivial projection, and that projection
is injective and has rank at most two. -/
theorem exists_quadratic_bestOffender_injective_projection
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hfaith : Function.Injective ρ)
    (hfull : subspaceCommutator (ρ.comp i) ⊤ ⊤ = ⊤)
    {A : Subgroup G} (hA : IsBestOffender ρ A) (hproj : A.map r ≠ ⊥) :
    ∃ B ≤ A, IsBestOffender ρ B ∧ IsQuadratic ρ B ∧ B.map r ≠ ⊥ ∧
      Function.Injective (r.subgroupMap B) ∧ rank B ≤ 2 := by
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup K := e.isSimpleGroup
  have hZ := center_eq_bot_of_equiv e
  let B := displacementCentralizer ρ A
  have hBproj : B.map r ≠ ⊥ :=
    displacementCentralizer_map_ne_bot ρ i r hfaith hfull hA
      (commutator_range_eq i r hri hcent hZ hproj) hcent
  have hBq : IsQuadratic ρ B := displacementCentralizer_isQuadratic ρ A
  have hBbest : IsBestOffender ρ B := hA.displacementCentralizer_isBestOffender ρ
  have hBc : ⁅i.range, B⁆ = i.range := commutator_range_eq i r hri hcent hZ hBproj
  have hinj : Function.Injective (r.subgroupMap B) := by
    apply (injective_iff_map_eq_one _).mpr
    intro b hb
    apply Subtype.ext
    exact quadratic_ker_eq_one ρ i r hfaith hfull hBq hBc hcent b.property
      (congrArg Subtype.val hb)
  refine ⟨B, displacementCentralizer_le ρ A, hBbest, hBq, hBproj, hinj, ?_⟩
  let : IsElementaryAbelian 2 B := hBbest.1.2
  let : IsElementaryAbelian 2 (B.map r) := IsElementaryAbelian.map r
  have hr := AbelianCore.QuotientRecognition.ExtensionControl.elementary_rank_le_two
    ((B.map r).map e.toMonoidHom) (IsElementaryAbelian.map e.toMonoidHom)
  rw [rank_map_injective e.toMonoidHom e.injective] at hr
  have he : B ≃* B.map r := MulEquiv.ofBijective (r.subgroupMap B)
    ⟨hinj, r.subgroupMap_surjective B⟩
  have heq : rank B = rank (B.map r) := congrArg (Nat.log 2) (Nat.card_congr he.toEquiv)
  exact heq ▸ hr

include hri hcent in
/-- The whole-module transfer reduces to the displacement bound for an
involution with nontrivial central component. This is a conditional reduction;
the additional small-involution premise must be discharged by the model proof. -/
theorem isFFModule_of_small_involutions_in_component
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hfaith : Function.Injective ρ)
    (hfull : subspaceCommutator (ρ.comp i) ⊤ ⊤ = ⊤)
    (hsmall : ∀ a : G, a ^ 2 = 1 → r a ≠ 1 →
      fixedCodim ρ (zpowers a) ≤ 2 → a ∈ i.range)
    {A : Subgroup G} (hA : IsBestOffender ρ A) (hproj : A.map r ≠ ⊥) :
    IsFFModule (ρ.comp i) := by
  obtain ⟨B, _, hB, hBq, hBr, hinj, hrank⟩ :=
    exists_quadratic_bestOffender_injective_projection ρ i r hri hcent e hfaith hfull hA hproj
  let : IsElementaryAbelian 2 B := hB.1.2
  have hle : B ≤ i.range := by
    intro b hb
    by_cases hz : r b = 1
    · have he : b = 1 := congrArg Subtype.val
        (hinj (show r.subgroupMap B ⟨b, hb⟩ = r.subgroupMap B 1 from Subtype.ext (by simpa using hz)))
      rw [he]
      exact i.range.one_mem
    · apply hsmall b (elemPow_eq_one_of_isElementaryAbelian b hb) hz
      have hcodim := (hB.isOffender ρ).2
      have hm := Submodule.finrank_mono (fixedSpace_antitone ρ (zpowers_le.mpr hb))
      have h1 := fixedCodim_add_finrank ρ B
      have h2 := fixedCodim_add_finrank ρ (zpowers b)
      omega
  have he : (B.map r).map i = B := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      obtain ⟨k, hk⟩ := hle hb
      have hir : i (r b) = b := by rw [← hk, hri]
      rw [hir]
      exact hb
    · intro b hb
      obtain ⟨k, rfl⟩ := hle hb
      exact mem_map_of_mem i (show k ∈ B.map r by
        simpa only [hri] using mem_map_of_mem r hb)
  have hfix : fixedSpace (ρ.comp i) (B.map r) = fixedSpace ρ B := by
    rw [fixedSpace_comp_map, he]
  have hr : rank (B.map r) = rank B :=
    congrArg (Nat.log 2) (Nat.card_congr
      (MulEquiv.ofBijective (r.subgroupMap B) ⟨hinj, r.subgroupMap_surjective B⟩).toEquiv).symm
  refine ⟨B.map r, ⟨hBr, IsElementaryAbelian.map r⟩, ?_⟩
  unfold fixedCodim
  rw [hfix, hr]
  exact (hB.isOffender ρ).2

include hri hcent in
/-- A best offender with nontrivial projection to a commuting SL₃(2) component
gives an offender on the whole restricted module. The offender comes from
quadratic replacement and need not be the projection of the original subgroup.
The two-group assumption is retained in the split-kernel interface, although
the central-twist argument proves this transfer without using it. -/
theorem isFFModule_of_bestOffender_nontrivial_projection [Finite K]
    (e : K ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (_hker : IsPGroup 2 r.ker)
    (hfaith : Function.Injective ρ)
    (hfull : subspaceCommutator (ρ.comp i) ⊤ ⊤ = ⊤)
    {A : Subgroup G} (hA : IsBestOffender ρ A) (hproj : A.map r ≠ ⊥) :
    IsFFModule (ρ.comp i) := by
  exact isFFModule_of_small_involutions_in_component ρ i r hri hcent e hfaith hfull
    (CentralTwist.small_involution_mem_component ρ e i r hri hcent hfaith hfull)
    hA hproj

end CFSG.Quasithin.ChapterC.BinaryMS.ComponentOffender.BestProjection
