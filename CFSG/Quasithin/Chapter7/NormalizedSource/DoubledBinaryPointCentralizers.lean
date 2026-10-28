module

public import Theory.Representation.PSL3Two.NaturalDualNormalizer
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Theory.Representation.PSL3Two.OrbitStabilizers

/-!
# Point centralizers on the binary natural–dual orbit

A pointwise fixer of a nonzero natural-axis vector is inner. The marked
component action identifies its fixer with the natural point parabolic S₄.
Transport through the literal normalizer homomorphism identifies the local
quotient and its kernel. Consequently any odd subgroup of this local
centralizer has whole-orbit centralizer of index dividing three.

The actual chosen-module and paired-plane applications are in
`NonFFSourceDoubledBinaryPointCentralizers`. This supplies the local quotient
and the first clause of source 7.7.4; it does not establish the ambient
normalizer control or the centralizer containment in 7.7.3.
Source: Aschbacher–Smith, printed p.704, in `refs/quasithin.pdf`.
-/

open Subgroup Representation Representation.BinaryOffender
open BinaryLinearThree
open scoped IsMulCommutative

public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource

/-- The pointwise stabilizer of one vector for the specified action. -/
@[expose] def doubledBinaryVectorFixer {H U : Type*} [_root_.Group H]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (u : U) : Subgroup H where
  carrier := {a | ρ a u = u}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change ρ (a*b) u = u
    rw [map_mul,Module.End.mul_apply,hb,ha]
  inv_mem' := by
    intro a ha
    change ρ a⁻¹ u = u
    have hh := congrArg (ρ a⁻¹) ha
    simpa only [← Module.End.mul_apply,← map_mul,inv_mul_cancel,map_one,
      Module.End.one_apply] using hh.symm

/-- The full actor fixing a nonzero natural-axis vector is S₄. Outer operators exchange the axes, and the inner fixer is the natural point parabolic. -/
theorem doubledBinary_point_fixer
    {H J U : Type*} [_root_.Group H] [_root_.Group J]
    [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) H U) (i : J →* H)
    (q : J →* Group) (hq : Function.Surjective q)
    (E : U ≃ₗ[ZMod 2] NaturalDual.Space)
    (hE : ∀ j u, E (ρ (i j) u) = NaturalDual.action (q j) (E u))
    (a : H ≃* MulAut Group) (ha : ∀ j, a (i j) = MulAut.conj (q j))
    (hcov : ∀ b g u, E (ρ b (E.symm (NaturalDual.action g (E u)))) =
      NaturalDual.action (a b g) (E (ρ b u)))
    (v : Vector) (hv : v ≠ 0) :
    Nonempty (doubledBinaryVectorFixer ρ (E.symm (v,0)) ≃*
      Equiv.Perm (Fin 4)) := by
  let P := doubledBinaryVectorFixer ρ (E.symm (v,0))
  have hinner (b : P) : a b ∈ MulAut.innerSubgroup Group := by
    let c := E.symm.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv
      (ρ.asGroupHom b)).trans E)
    have hc (g : Group) (x : NaturalDual.Space) :
        c (NaturalDual.action g x) = NaturalDual.action (a b g) (c x) := by
      change E (ρ b (E.symm (NaturalDual.action g x))) =
        NaturalDual.action (a b g) (E (ρ b (E.symm x)))
      simpa only [E.apply_symm_apply] using hcov b g (E.symm x)
    have hb : c (v,0) = (v,0) := by
      change E (ρ b (E.symm (v,0))) = (v,0)
      rw [b.property,E.apply_symm_apply]
    by_contra ho
    have hz := (NaturalDual.outer_swaps (a b) c hc ho).1 v
    rw [hb] at hz
    exact hv hz
  let c : Group ≃* MulAut.innerSubgroup Group :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot)
  let j : P →* Group := c.symm.toMonoidHom.comp
    ((a.toMonoidHom.comp P.subtype).codRestrict _ hinner)
  have hj (b : P) : MulAut.conj (j b) = a b :=
    congrArg Subtype.val (c.apply_symm_apply _)
  have hact (b : P) (u : U) : E (ρ b u) = NaturalDual.action (j b) (E u) := by
    obtain ⟨l,hl⟩ := hq (j b)
    have he : i l = b := a.injective (by rw [ha,hl,hj])
    rw [← he,hE,hl]
  have hjv (b : P) : j b ∈ OrbitStabilizers.natural v := by
    rw [OrbitStabilizers.mem_natural]
    have he := hact b (E.symm (v,0))
    rw [b.property,E.apply_symm_apply] at he
    exact (congrArg Prod.fst he).symm
  let f : P →* OrbitStabilizers.natural v := j.codRestrict _ hjv
  have hfi : Function.Injective f := by
    intro b d hbd
    apply Subtype.ext
    apply a.injective
    rw [← hj,← hj]
    exact congrArg MulAut.conj (congrArg Subtype.val hbd)
  have hfs : Function.Surjective f := by
    intro g
    obtain ⟨l,hl⟩ := hq g
    have hlP : i l ∈ P := by
      apply E.injective
      rw [hE,hl,E.apply_symm_apply]
      apply Prod.ext ((OrbitStabilizers.mem_natural _ _).mp g.property)
      change W.dual (g : Group) 0 = 0
      exact map_zero _
    refine ⟨⟨i l,hlP⟩,?_⟩
    apply Subtype.ext
    apply (MulAut.conj_injective_of_center_eq_bot Matrix.PSL3Two.center_eq_bot)
    exact (hj ⟨i l,hlP⟩).trans ((ha l).trans (congrArg MulAut.conj hl))
  exact ⟨(MulEquiv.ofBijective f ⟨hfi,hfs⟩).trans
    (OrbitStabilizers.naturalEquivSymmetric v hv)⟩

open CFSG.Quasithin.ChapterE

/-- The literal ambient point centralizer induces exactly the vector fixer. -/
theorem doubledBinary_induced_point_fixer
    {G : Type*} [_root_.Group G] (W₀ : Subgroup G) [IsElementaryAbelian 2 W₀]
    (w : Additive W₀) :
    inducedAutomizer W₀ (centralizer ({(w.toMul : G)} : Set G)) =
      doubledBinaryVectorFixer (automizerRepresentation W₀) w := by
  ext b
  constructor
  · rintro ⟨n,hn,rfl⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    change (n : G) * (w.toMul : G) * (n : G)⁻¹ = (w.toMul : G)
    have hnc : (w.toMul : G) * (n : G) = (n : G) * (w.toMul : G) :=
      hn _ (Set.mem_singleton _)
    rw [← hnc,mul_inv_cancel_right]
  · intro hb
    obtain ⟨n,rfl⟩ := W₀.normalizerMonoidHom.rangeRestrict_surjective b
    refine ⟨n,?_,rfl⟩
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    have he := congrArg (fun y : Additive W₀ => (y.toMul : G)) hb
    change (n : G) * (w.toMul : G) * (n : G)⁻¹ = (w.toMul : G) at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The induced action has the actual centralizer as kernel, with relative index taken inside the original actor. -/
theorem doubledBinary_induced_card
    {G : Type*} [_root_.Group G] (W₀ Y : Subgroup G)
    (hY : Y ≤ normalizer (W₀ : Set G)) :
    Nat.card (inducedAutomizer W₀ Y) = (centralizer (W₀ : Set G)).relIndex Y := by
  let N := normalizer (W₀ : Set G)
  let q := W₀.normalizerMonoidHom.rangeRestrict
  have hk : q.ker = (centralizer (W₀ : Set G)).subgroupOf N := by
    rw [← normalizerMonoidHom_ker]
    ext n
    exact Subtype.ext_iff
  change Nat.card ((Y.subgroupOf N).map q) = _
  rw [← relIndex_ker,hk]
  change ((centralizer (W₀ : Set G)).comap N.subtype).relIndex (Y.subgroupOf N) = _
  rw [relIndex_comap,map_subgroupOf_eq_of_le hY]

/-- The original local point centralizer maps onto S₄ with kernel its intersection with the whole-orbit centralizer. -/
theorem doubledBinary_point_quotient
    {G : Type*} [_root_.Group G] (W₀ : Subgroup G) [IsElementaryAbelian 2 W₀]
    (w : Additive W₀)
    (he : Nonempty (doubledBinaryVectorFixer (automizerRepresentation W₀) w ≃*
      Equiv.Perm (Fin 4))) :
    ∃ π : (normalizer (W₀ : Set G) ⊓ centralizer ({(w.toMul : G)} : Set G) : Subgroup G) →*
        Equiv.Perm (Fin 4),
      Function.Surjective π ∧ π.ker = (centralizer (W₀ : Set G)).subgroupOf
        (normalizer (W₀ : Set G) ⊓ centralizer ({(w.toMul : G)} : Set G)) := by
  obtain ⟨e⟩ := he
  let C := normalizer (W₀ : Set G) ⊓ centralizer ({(w.toMul : G)} : Set G)
  let P := doubledBinaryVectorFixer (automizerRepresentation W₀) w
  let q := W₀.normalizerMonoidHom.rangeRestrict.comp
    (inclusion (show C ≤ normalizer (W₀ : Set G) from inf_le_left))
  have hq (c : C) : q c ∈ P := by
    change q c ∈ doubledBinaryVectorFixer (automizerRepresentation W₀) w
    rw [← doubledBinary_induced_point_fixer]
    exact ⟨inclusion inf_le_left c,c.property.2,rfl⟩
  let p : C →* P := q.codRestrict P hq
  have hp : Function.Surjective p := by
    intro b
    have hb := b.property
    change (b : Automizer W₀) ∈ doubledBinaryVectorFixer (automizerRepresentation W₀) w at hb
    rw [← doubledBinary_induced_point_fixer] at hb
    obtain ⟨n,hn,he⟩ := hb
    exact ⟨⟨n,n.property,hn⟩,Subtype.ext he⟩
  refine ⟨e.toMonoidHom.comp p,e.surjective.comp hp,?_⟩
  ext c
  change e (p c) = 1 ↔ (c : G) ∈ centralizer (W₀ : Set G)
  rw [← e.map_one,e.injective.eq_iff]
  have he : p c = 1 ↔ W₀.normalizerMonoidHom (inclusion inf_le_left c) = 1 := by
    constructor
    · intro hh
      exact congrArg (fun x : P => x.val.val) hh
    · intro hh
      exact Subtype.ext (Subtype.ext hh)
  rw [he]
  change inclusion inf_le_left c ∈ W₀.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

/-- An odd actor fixing a natural-axis point has image of order dividing three. The index uses its centralizer of the full orbit. -/
theorem doubledBinary_odd_point_index
    {G : Type*} [_root_.Group G] [Finite G]
    (W₀ : Subgroup G) [IsElementaryAbelian 2 W₀] (w : Additive W₀)
    (he : Nonempty (doubledBinaryVectorFixer (automizerRepresentation W₀) w ≃*
      Equiv.Perm (Fin 4)))
    (Y : Subgroup G) (hY : Y ≤ normalizer (W₀ : Set G) ⊓
      centralizer ({(w.toMul : G)} : Set G))
    (hodd : Odd (Nat.card Y)) : (centralizer (W₀ : Set G)).relIndex Y ∣ 3 := by
  obtain ⟨e⟩ := he
  have hle : inducedAutomizer W₀ Y ≤
      doubledBinaryVectorFixer (automizerRepresentation W₀) w := by
    rw [← doubledBinary_induced_point_fixer]
    exact map_mono (comap_mono (hY.trans inf_le_right))
  have hc : Nat.card (doubledBinaryVectorFixer (automizerRepresentation W₀) w) = 24 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
    rfl
  have hd : (centralizer (W₀ : Set G)).relIndex Y ∣ 24 := by
    rw [← doubledBinary_induced_card W₀ Y (hY.trans inf_le_left)]
    simpa only [hc] using card_dvd_of_le hle
  have ho := hodd.of_dvd_nat ((centralizer (W₀ : Set G)).relIndex_dvd_card Y)
  have hp : ((centralizer (W₀ : Set G)).relIndex Y).Coprime 8 := by
    simpa using ho.coprime_two_right.pow_right 3
  exact hp.dvd_of_dvd_mul_left hd

end CFSG.Quasithin.Chapter7.NormalizedSource

