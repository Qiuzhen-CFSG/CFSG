module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Normal subgroup images in central Sylow quotients

Let M be a normal subgroup of a finite group G with center of order two.
If N is central in G and contains the image of the center of a Sylow
two-subgroup, then the image of M in G/N is isomorphic to M/Z(M).

The characteristic center of M has normal ambient image of order two.
The public `central_of_normal_card_two` lemma proves that conjugation
fixes its unique nonidentity element, so it is globally central;
normality also places it in the chosen Sylow subgroup, hence in N. Conversely,
centrality of N puts the kernel on M inside Z(M). The first isomorphism
theorem identifies the actual quotient image. The canonical variant records
that the image of each m maps to its class in M/Z(M); the original Nonempty
interface is retained as a wrapper. This element equation is needed for the
prescribed projective-core action comparison in II.3 Proposition 3.

This is the quotient transfer in the uniqueness argument of
Alperin--Brauer--Gorenstein, II.3 Proposition 2 (article page 23).
It is independent of the SL2 model and of the ambient Sylow classification.
-/

namespace Subgroup

/-- A normal subgroup of order two is central. -/
public theorem central_of_normal_card_two {G : Type*} [Group G]
    (Z : Subgroup G) [Z.Normal] (hZ : Nat.card Z = 2) : Z ≤ center G := by
  obtain ⟨z, hzne, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  intro x hx
  apply mem_center_iff.mpr
  intro g
  by_cases hxone : x = 1
  · simp [hxone]
  let xZ : Z := ⟨x, hx⟩
  let yZ : Z := ⟨g * x * g⁻¹, (inferInstance : Z.Normal).conj_mem x hx g⟩
  have hyne : yZ ≠ 1 := by
    intro hy
    have hy' : g * x * g⁻¹ = 1 := congrArg Subtype.val hy
    apply hxone
    have h := congrArg (fun a : G => g⁻¹ * a * g) hy'
    simpa [mul_assoc] using h
  have heq : yZ = xZ := (hzuniq yZ hyne).trans (hzuniq xZ (by
    intro hx'
    exact hxone (congrArg Subtype.val hx'))).symm
  have heq' : g * x * g⁻¹ = x := congrArg Subtype.val heq
  have h := congrArg (fun a : G => a * g) heq'
  simpa [mul_assoc] using h

public theorem exists_normal_center_quotient_image_equiv
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (N M : Subgroup G) [N.Normal] [M.Normal]
    (hNcentral : N ≤ center G)
    (hSN : (center (S : Subgroup G)).map (S : Subgroup G).subtype ≤ N)
    (hMcenter : Nat.card (center M) = 2) :
    ∃ e : M.map (QuotientGroup.mk' N) ≃* (M ⧸ center M),
      ∀ m : M, e ⟨QuotientGroup.mk' N m.val, ⟨m.val, m.property, rfl⟩⟩ =
        QuotientGroup.mk' (center M) m := by
  let Z : Subgroup G := (center M).map M.subtype
  have hZcard : Nat.card Z = 2 :=
    (card_map_of_injective M.subtype_injective).trans hMcenter
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZcentral : Z ≤ center G := central_of_normal_card_two Z hZcard
  have hZtwo : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by simpa using hZcard)
  have hZS : Z ≤ (S : Subgroup G) := hZtwo.le_sylow_of_normal S
  have hZN : Z ≤ N := by
    intro x hx
    apply hSN
    refine ⟨⟨x, hZS hx⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro s
    exact Subtype.ext (mem_center_iff.mp (hZcentral hx) s)
  let f : M →* G ⧸ N := (QuotientGroup.mk' N).comp M.subtype
  have hker : f.ker = center M := by
    ext m
    change (m : G ⧸ N) = 1 ↔ m ∈ center M
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hm
      apply mem_center_iff.mpr
      intro m'
      exact Subtype.ext (mem_center_iff.mp (hNcentral hm) m')
    · intro hm
      exact hZN ⟨m, hm, rfl⟩
  have hrange : f.range = M.map (QuotientGroup.mk' N) := by
    ext x
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, m.property, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, rfl⟩
  refine ⟨(MulEquiv.subgroupCongr hrange).symm.trans
    ((QuotientGroup.quotientKerEquivRange f).symm.trans
      (QuotientGroup.congr f.ker (center M) (MulEquiv.refl M) (by simpa using hker))), ?_⟩
  intro m
  have hm : (QuotientGroup.quotientKerEquivRange f) (QuotientGroup.mk' f.ker m) =
      ⟨f m, ⟨m, rfl⟩⟩ := rfl
  have hi := (QuotientGroup.quotientKerEquivRange f).symm_apply_apply
    (QuotientGroup.mk' f.ker m)
  rw [hm] at hi
  change (QuotientGroup.congr f.ker (center M) (MulEquiv.refl M) (by simpa using hker))
    ((QuotientGroup.quotientKerEquivRange f).symm ⟨f m, ⟨m, rfl⟩⟩) = _
  rw [hi]
  rfl

public theorem normal_center_quotient_image_equiv
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (N M : Subgroup G) [N.Normal] [M.Normal]
    (hNcentral : N ≤ center G)
    (hSN : (center (S : Subgroup G)).map (S : Subgroup G).subtype ≤ N)
    (hMcenter : Nat.card (center M) = 2) :
    Nonempty (M.map (QuotientGroup.mk' N) ≃* (M ⧸ center M)) := by
  obtain ⟨e, _⟩ := exists_normal_center_quotient_image_equiv S N M hNcentral hSN hMcenter
  exact ⟨e⟩

end Subgroup
