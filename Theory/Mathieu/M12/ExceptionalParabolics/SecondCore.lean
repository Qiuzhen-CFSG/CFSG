module

public import Theory.Mathieu.M12.ExceptionalParabolics

/-!
# Distinguishing the two M₁₂ parabolic cores

The second core is exactly the centralizer of the natural four. Consequently
that four embeds in its center, whereas the first core's quaternion central
product has center of order two. The two cores are not isomorphic. The
second core lies in the first parabolic but is not normal there, so it cannot
serve as the denominator of the printed first quotient.

This proves why both occurrences at the start of F.1.12(I)(12) must concern
L₁. Source: Aschbacher--Smith, printed p.263 (PDF p.274), with the central
product convention of E.2.16, printed p.228.
-/

public section
namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics
open scoped IsMulCommutative
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M12SmallPair
open Sporadic.Mathieu.M12SmallPair.ValueBoundParabolics

theorem secondCore_mem_iff_centralizes (g : secondParabolic) :
    g ∈ pCore 2 secondParabolic ↔
      (g : M12) ∈ Subgroup.centralizer (natural : Set M12) := by
  rw [second_pCore_eq_kernel, MonoidHom.mem_ker]
  constructor
  · intro hg x hx
    rcases (mem_natural_iff_label x).mp hx with rfl | ⟨i,rfl⟩
    · simp
    · have h := FirstCore.restrictAction_spec naturalRepresentation naturalLabel
        naturalLabel_injective natural_stable g i
      change (g : M12) * naturalLabel i * (g : M12)⁻¹ = naturalLabel (secondQuotientMap g i) at h
      rw [hg] at h
      change (g : M12) * naturalLabel i * (g : M12)⁻¹ = naturalLabel i at h
      have he := congrArg (fun x : M12 => x * (g : M12)) h
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using he.symm
  · intro hg
    apply secondQuotientMap_eq
    intro i
    change (g : M12) * naturalLabel i * (g : M12)⁻¹ = naturalLabel i
    have h := hg (naturalLabel i) ((mem_natural_iff_label _).mpr (Or.inr ⟨i,rfl⟩))
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]

theorem secondCore_image_eq_centralizer : (pCore 2 secondParabolic).map secondParabolic.subtype =
    Subgroup.centralizer (natural : Set M12) := by
  ext g
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (secondCore_mem_iff_centralizes x).mp hx
  · intro hg
    have hn : g ∈ secondParabolic := Subgroup.centralizer_le_normalizer _ hg
    exact ⟨⟨g,hn⟩,(secondCore_mem_iff_centralizes _).mpr hg,rfl⟩

theorem secondCore_center_card_ge_four : 4 ≤ Nat.card (Subgroup.center (pCore 2 secondParabolic)) := by
  let _ : IsKleinFour natural := natural_kleinFour
  let _ : IsMulCommutative natural := IsKleinFour.isMulCommutative
  have hc (x : natural) : (x : M12) ∈ Subgroup.centralizer (natural : Set M12) := by
    intro y hy
    exact congrArg (fun t : natural => (t : M12)) (mul_comm (⟨y,hy⟩ : natural) x)
  let f : natural → Subgroup.center (pCore 2 secondParabolic) := fun x =>
    ⟨⟨⟨x, Subgroup.centralizer_le_normalizer _ (hc x)⟩,
      (secondCore_mem_iff_centralizes _).mpr (hc x)⟩, by
        apply Subgroup.mem_center_iff.mpr
        intro q
        apply Subtype.ext
        apply Subtype.ext
        exact ((secondCore_mem_iff_centralizes q.val).mp q.property x x.property).symm⟩
  have hi : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun t : Subgroup.center (pCore 2 secondParabolic) =>
      (t.val.val : M12)) h)
  have h := Nat.card_le_card_of_injective f hi
  rwa [card_natural] at h

/-- The second core cannot have the printed quaternion central-product structure. -/
theorem secondCore_not_quaternion :
    ¬ Nonempty (Subgroup.QuaternionCentralProductData (pCore 2 secondParabolic)) := by
  rintro ⟨d⟩
  have h := secondCore_center_card_ge_four
  rw [d.center_card] at h
  omega

theorem cores_not_isomorphic :
    ¬ Nonempty (pCore 2 firstParabolic ≃* pCore 2 secondParabolic) := by
  rintro ⟨e⟩
  exact secondCore_not_quaternion ⟨firstCoreQuaternionData.map e⟩

/-- The intrinsic second core, with its actual inclusion into M₁₂. -/
@[expose] noncomputable def secondCoreImage : Subgroup M12 :=
  (pCore 2 secondParabolic).map secondParabolic.subtype

theorem secondCoreImage_le_sylow : secondCoreImage ≤ sylowCandidate := by
  rintro x ⟨q,hq,rfl⟩
  exact (pCore_isPGroup.le_sylow_of_normal secondParabolicSylow) hq

/-- The second core is contained in L₁ but is not a normal denominator there. -/
theorem secondCoreImage_not_normal_in_first :
    ¬ (secondCoreImage.subgroupOf firstParabolic).Normal := by
  intro hn
  have hQH : secondCoreImage ≤ firstParabolic := secondCoreImage_le_sylow.trans inf_le_left
  let e : pCore 2 secondParabolic ≃* secondCoreImage.subgroupOf firstParabolic :=
    ((pCore 2 secondParabolic).equivMapOfInjective secondParabolic.subtype
      secondParabolic.subtype_injective).trans
      (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hp : IsPGroup 2 (secondCoreImage.subgroupOf firstParabolic) :=
    pCore_isPGroup.of_surjective e.toMonoidHom e.surjective
  have hl : secondCoreImage.subgroupOf firstParabolic ≤ pCore 2 firstParabolic :=
    le_sSup ⟨hn,hp⟩
  have hc : Nat.card (secondCoreImage.subgroupOf firstParabolic) = 32 := by
    rw [← Nat.card_congr e.toEquiv, secondCore_card]
  have he := Subgroup.eq_of_le_of_card_ge hl (by rw [hc,firstCore_card])
  exact cores_not_isomorphic ⟨(MulEquiv.subgroupCongr he.symm).trans e.symm⟩

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics
