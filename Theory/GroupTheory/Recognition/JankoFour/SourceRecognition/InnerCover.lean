module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CubicAction
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Theory.GroupTheory.CentralExtensionSections
public import Theory.Mathieu.M22.TripleCover.Recognition

/-!
# The perfect Mathieu cover inside the retained cubic extension

Restrict the original cubic projection to the inverse image of Inn(M₂₂).
Its kernel still has order three. A cyclic kernel over a perfect quotient
is central: the derived group centralizes the kernel, and together they
generate the full preimage. Taking the derived subgroup gives a quasisimple
cover with center of order one or three, hence an actual isomorphism to
M₂₂ or its native triple cover.

This constructs the group-theoretic input for AS91 (4.1). The simple case
has not been excluded here; that needs the original binary action. No
splitting of the extension or triple-cover marking is assumed.
Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), (4.1), printed p.597, DOI 10.1007/BF01232280.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup Sporadic.Mathieu

private theorem cyclic_kernel_central_of_perfect_quotient
    {E B : Type*} [Group E] [Group B] [Group.IsPerfect B]
    (f : E →* B) (hf : Function.Surjective f) [IsCyclic f.ker] :
    f.ker ≤ center E := by
  have hs : _root_.commutator E ⊔ f.ker = ⊤ := by
    have hm : (_root_.commutator E).map f = (⊤ : Subgroup E).map f := by
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf,
        ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top, map_top_of_surjective f hf]
    simpa only [top_sup_eq] using map_eq_map_iff.mp hm
  have hD := commutator_le_centralizer_of_isCyclic_normal f.ker
  have hK : f.ker ≤ Subgroup.centralizer (f.ker : Set E) := by
    intro k hk l hl
    exact congrArg Subtype.val (mul_comm' (⟨l, hl⟩ : f.ker) ⟨k, hk⟩)
  have hall : Subgroup.centralizer (f.ker : Set E) = ⊤ :=
    top_unique (hs ▸ sup_le hD hK)
  intro k hk
  exact mem_center_iff.mpr fun y => ((hall.ge (mem_top y)) k hk).symm

theorem m22_perfect : Group.IsPerfect M22 := by
  let f := M22TripleCover.coverOfCentralQuotientEquiv M22TripleCover.centralQuotientEquiv
  let := f.isPerfect
  exact Group.IsPerfect.ofSurjective f.surjective

private theorem m22_quasisimple : IsQuasisimple M22 := by
  let := m22_perfect
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  exact ⟨((QuotientGroup.quotientMulEquivOfEq m22_center_eq_bot).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩

variable {H : Type*} [Group H]

/-- The full inverse image of the inner Mathieu automorphisms. -/
noncomputable def innerPreimage (e : CubicAutomorphismQuotient H) : Subgroup H :=
  (MulAut.conj : M22 →* MulAut M22).range.comap e.projection

/-- The retained projection, restricted to the inner preimage and identified
with the native M₂₂ using its centerless inner action. -/
noncomputable def innerProjection (e : CubicAutomorphismQuotient H) :
    innerPreimage e →* M22 :=
  (MonoidHom.ofInjective (conj_injective_of_center_eq_bot m22_center_eq_bot)).symm.toMonoidHom.comp
    (e.projection.subgroupComap (MulAut.conj : M22 →* MulAut M22).range)

theorem innerProjection_surjective (e : CubicAutomorphismQuotient H) :
    Function.Surjective (innerProjection e) :=
  (MonoidHom.ofInjective (conj_injective_of_center_eq_bot m22_center_eq_bot)).symm.surjective.comp
    (e.projection.subgroupComap_surjective_of_surjective _ e.surjective)

theorem innerProjection_conj (e : CubicAutomorphismQuotient H) (x : innerPreimage e) :
    MulAut.conj (innerProjection e x) = e.projection x := by
  exact congrArg Subtype.val
    ((MonoidHom.ofInjective (conj_injective_of_center_eq_bot m22_center_eq_bot)).apply_symm_apply
      (e.projection.subgroupComap _ x))

theorem innerProjection_ker_iff (e : CubicAutomorphismQuotient H)
    (x : innerPreimage e) : x ∈ (innerProjection e).ker ↔ (x : H) ∈ e.projection.ker := by
  change innerProjection e x = 1 ↔ e.projection x = 1
  rw [← innerProjection_conj]
  exact ((conj_injective_of_center_eq_bot m22_center_eq_bot).eq_iff' (map_one MulAut.conj)).symm

/-- The order-three kernel is retained literally under restriction. -/
noncomputable def innerKernelEquiv (e : CubicAutomorphismQuotient H) :
    (innerProjection e).ker ≃* e.projection.ker where
  toFun x := ⟨x.val.val, (innerProjection_ker_iff e x.val).mp x.property⟩
  invFun x := ⟨⟨x.val, by
    change e.projection x.val ∈ (MulAut.conj : M22 →* MulAut M22).range
    rw [x.property]
    exact one_mem _⟩, (innerProjection_ker_iff e _).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem innerProjection_kernel_card (e : CubicAutomorphismQuotient H) :
    Nat.card (innerProjection e).ker = 3 :=
  (Nat.card_congr (innerKernelEquiv e).toEquiv).trans e.kernel_card

theorem innerProjection_kernel_central (e : CubicAutomorphismQuotient H) :
    (innerProjection e).ker ≤ center (innerPreimage e) := by
  let := m22_perfect
  let : IsCyclic (innerProjection e).ker := isCyclic_of_prime_card (innerProjection_kernel_card e)
  exact cyclic_kernel_central_of_perfect_quotient _ (innerProjection_surjective e)

/-- The derived subgroup supplies a genuine perfect central M₂₂ cover. -/
noncomputable def innerDerivedCover (e : CubicAutomorphismQuotient H) :
    PerfectCentralCovering.Cover (_root_.commutator (innerPreimage e)) M22 := by
  let := m22_perfect
  exact CentralExtension.derivedCover (innerProjection e) (innerProjection_surjective e)
    (innerProjection_kernel_central e)

theorem innerDerived_quasisimple (e : CubicAutomorphismQuotient H) :
    IsQuasisimple (_root_.commutator (innerPreimage e)) := by
  let := m22_quasisimple
  exact (innerDerivedCover e).isQuasisimple

noncomputable def innerDerivedCentralQuotientEquiv (e : CubicAutomorphismQuotient H) :
    ((_root_.commutator (innerPreimage e)) ⧸ center (_root_.commutator (innerPreimage e))) ≃* M22 :=
  (innerDerivedCover e).quotientCenterEquiv.trans
    ((QuotientGroup.quotientMulEquivOfEq m22_center_eq_bot).trans QuotientGroup.quotientBot)

theorem innerDerived_kernel_eq_center (e : CubicAutomorphismQuotient H) :
    (innerDerivedCover e).toMonoidHom.ker = center (_root_.commutator (innerPreimage e)) := by
  have h := (innerDerivedCover e).comap_center
  rw [m22_center_eq_bot] at h
  exact h

theorem innerDerived_center_card_dvd_three (e : CubicAutomorphismQuotient H) :
    Nat.card (center (_root_.commutator (innerPreimage e))) ∣ 3 := by
  rw [← innerDerived_kernel_eq_center e, ← innerProjection_kernel_card e]
  let i : (innerDerivedCover e).toMonoidHom.ker →* (innerProjection e).ker := {
    toFun x := ⟨x.val.val, x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  apply card_dvd_of_injective i
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun a : (innerProjection e).ker => (a : innerPreimage e)) he

/-- The cover is embedded in the original cubic extension by its two subtype maps. -/
noncomputable def innerDerivedInclusion (e : CubicAutomorphismQuotient H) :
    (_root_.commutator (innerPreimage e)) →* H :=
  (innerPreimage e).subtype.comp (_root_.commutator (innerPreimage e)).subtype

theorem innerDerivedInclusion_injective (e : CubicAutomorphismQuotient H) :
    Function.Injective (innerDerivedInclusion e) :=
  (innerPreimage e).subtype_injective.comp (_root_.commutator (innerPreimage e)).subtype_injective

/-- The ambient inclusion commutes with the original cubic projection and
the native inner action, so the covering kernel is not discarded. -/
theorem innerDerivedInclusion_projection (e : CubicAutomorphismQuotient H)
    (x : _root_.commutator (innerPreimage e)) :
    e.projection (innerDerivedInclusion e x) = MulAut.conj ((innerDerivedCover e).toMonoidHom x) :=
  (innerProjection_conj e x).symm

variable [Finite H]

/-- This step leaves precisely the simple and genuine triple-cover cases.
The split case must still be excluded using the source action. -/
theorem innerDerived_simple_or_triple (e : CubicAutomorphismQuotient H) :
    Nonempty ((_root_.commutator (innerPreimage e)) ≃* M22) ∨
      Nonempty ((_root_.commutator (innerPreimage e)) ≃* M22TripleCover) := by
  let := innerDerived_quasisimple e
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp
    (innerDerived_center_card_dvd_three e) with hc | hc
  · left
    have hb := card_eq_one.mp hc
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hb).trans QuotientGroup.quotientBot).symm.trans
      (innerDerivedCentralQuotientEquiv e)⟩
  · exact Or.inr (M22TripleCover.nonempty_mulEquiv hc ⟨innerDerivedCentralQuotientEquiv e⟩)

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
