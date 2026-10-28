module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.NaturalNormalizer
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Large fixed subgroups in the J.2.7 five-centralizer argument

The natural binary action of H/Q has no transvections. If an H-element fixes
at least sixteen elements of U, its displacement on U/Z has order at most
two and hence is zero. Faithfulness places the element in Q. The second
lemma transports this criterion to the literal conjugates U^(hl), Q^(hl).

Source: Aschbacher–Smith, J.2.7(5), printed p.436 (PDF p.447).
-/

public section
noncomputable section

open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

private theorem zero_of_small_displacement
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (f : Module.End (ZMod 2) W)
    (hc : Nat.card (LinearMap.range f) ≤ 2)
    (hn : Module.finrank (ZMod 2) (LinearMap.range f) ≠ 1) : f = 0 := by
  have hpow := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := LinearMap.range f)
  rw [Nat.card_zmod] at hpow
  have hdim : Module.finrank (ZMod 2) (LinearMap.range f) ≤ 1 := by
    by_contra h
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega :
      2 ≤ Module.finrank (ZMod 2) (LinearMap.range f))
    rw [← hpow] at hh
    omega
  exact LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp (by omega))

theorem mem_Q_of_centralizes_large_subgroup (t : d.toTypeRuSetup.H)
    (X : Subgroup G) (hX : X ≤ d.toTypeRuSetup.U) (hcard : 16 ≤ Nat.card X)
    (htX : (t:G) ∈ centralizer (X : Set G)) : (t:G) ∈ d.toTypeRuSetup.Q := by
  let f : Module.End (ZMod 2) FourSpace :=
    d.ru2.naturalAction.action (d.ru2.quotientMap t) - LinearMap.id
  let δ : d.toTypeRuSetup.U →* Multiplicative FourSpace :=
    (AddMonoidHom.toMultiplicative f.toAddMonoidHom).comp d.ru2.natural.coordinates
  have hk : X.subgroupOf d.toTypeRuSetup.U ≤ δ.ker := by
    intro x hx
    have he := d.ru2.natural.equivariant t x
    have hc : (t:G) * x * (t:G)⁻¹ = x := by
      rw [← htX x hx, mul_inv_cancel_right]
    have hs : (⟨(t:G)*x*(t:G)⁻¹,
      (mem_normalizer_iff.mp (d.ru2.natural.normalized t.property) x).mp x.property⟩ :
      d.toTypeRuSetup.U) = x := Subtype.ext hc
    rw [hs] at he
    change f (d.ru2.natural.coordinates x).toAdd = 0
    exact sub_eq_zero.mpr he.symm
  have hkcard : 16 ≤ Nat.card δ.ker := by
    have hh := card_le_of_le hk
    rw [Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv] at hh
    exact hcard.trans hh
  have hδcard : Nat.card δ.range ≤ 2 := by
    have hh := δ.ker.index_mul_card
    rw [index_ker,d.ru2.card_U d.card_Z] at hh
    have hb := Nat.mul_le_mul_left (Nat.card δ.range) hkcard
    rw [hh] at hb
    omega
  have hfc : Nat.card (LinearMap.range f) = Nat.card δ.range := by
    let e : δ.range ≃ LinearMap.range f := {
      toFun x := ⟨x.val.toAdd, by
        obtain ⟨u,hu⟩ := x.property
        exact ⟨(d.ru2.natural.coordinates u).toAdd,congrArg Multiplicative.toAdd hu⟩⟩
      invFun x := ⟨Multiplicative.ofAdd x.val, by
        obtain ⟨v,hv⟩ := x.property
        obtain ⟨u,hu⟩ := d.ru2.natural.onto (Multiplicative.ofAdd v)
        exact ⟨u,by change Multiplicative.ofAdd (f _) = _; rw [hu]; exact congrArg Multiplicative.ofAdd hv⟩⟩
      left_inv _ := by apply Subtype.ext; rfl
      right_inv _ := by apply Subtype.ext; rfl }
    exact (Nat.card_congr e).symm
  have hf : f=0 := zero_of_small_displacement f (hfc.symm ▸ hδcard)
    (d.ru2.naturalAction.no_rank_one (d.ru2.quotientMap t))
  have hact : d.ru2.naturalAction.action (d.ru2.quotientMap t) = 1 := sub_eq_zero.mp hf
  have ht : d.ru2.quotientMap t = 1 := d.ru2.naturalAction.injective
    (by simpa only [map_one] using hact)
  have hh : t ∈ d.ru2.quotientMap.ker := ht
  rwa [d.ru2.quotient_kernel] at hh

omit [Finite G] in
theorem conjugate_mem_centralizer {A : Subgroup G} {t : G}
    (ht : t ∈ centralizer (A : Set G)) (g : G) :
    (MulAut.conj g) t ∈ centralizer (A.conjBy g : Set G) :=
  map_centralizer_le_centralizer_image (A : Set G) (MulAut.conj g).toMonoidHom
    (mem_map.mpr ⟨t,ht,rfl⟩)

theorem mem_conjugate_Q_of_centralizes_large_subgroup (g : G)
    (X : Subgroup G) (hX : X ≤ d.toTypeRuSetup.U.conjBy g) (hcard : 16 ≤ Nat.card X)
    (hZ : d.toTypeRuSetup.Z.conjBy g ≤ d.toTypeRuSetup.U)
    {t : G} (ht : t ∈ d.toTypeRuSetup.HC) (htX : t ∈ centralizer (X : Set G)) :
    t ∈ d.toTypeRuSetup.Q.conjBy g := by
  have htH : (MulAut.conj g⁻¹) t ∈ d.toTypeRuSetup.H := by
    have hh := conjugate_mem_centralizer (centralizer_le hZ ht.2) g⁻¹
    rw [conjBy_inv] at hh
    exact hh
  have hXU : X.conjBy g⁻¹ ≤ d.toTypeRuSetup.U := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hX
    change X.conjBy g⁻¹ ≤ (d.toTypeRuSetup.U.conjBy g).conjBy g⁻¹ at hh
    rwa [conjBy_inv] at hh
  have hc : 16 ≤ Nat.card (X.conjBy g⁻¹) := by
    rw [conjBy,card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hcard
  have hm := mem_Q_of_centralizes_large_subgroup ⟨(MulAut.conj g⁻¹) t,htH⟩
    (X.conjBy g⁻¹) hXU hc (conjugate_mem_centralizer htX g⁻¹)
  exact mem_map.mpr ⟨(MulAut.conj g⁻¹) t,hm,by simp [MulAut.conj_apply, mul_assoc]⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
