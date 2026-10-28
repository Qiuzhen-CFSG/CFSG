module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.BinaryLinearThree
public import Theory.SpecificGroups.PSL3Two.Automorphisms
public import Theory.GroupTheory.PResidual.PrimeToPerfect

/-!
# Cubic action images on a natural binary SL3 block

A three-group in the block normalizer has quotient-action kernel
centralizing the entire block. Any image detected on a subgroup of the
block therefore has order dividing |Aut(SL3(2))| = 336. Its order is a power
of three, hence divides three. The central attachment of the block is
retained throughout.

Source: Aschbacher--Smith C.1.10 and the block alternative in 15.1.24,
printed pp.124 and 1101. The automorphism order uses the attributed ATLAS
exceptional-isomorphism port through its existing import.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {G D : Type*} [Group G] [Finite G] [Group D]

private theorem cubic_twoPerfect {B : Type*} [Group B] [Finite B]
    (hp : IsPGroup 3 B) : IsPPerfect 2 B := by
  have he : primeToResidual 3 B = ⊤ := by
    apply top_unique
    intro b _
    obtain ⟨n,hn⟩ := hp b
    exact mem_primeToResidual_of_pow hn
  exact (isPPerfect_primeToResidual (G := B) 3 2 (by decide)).of_surjective
    (primeToResidual 3 B).subtype (by
      intro b
      exact ⟨⟨b,he ▸ mem_top b⟩,rfl⟩)

/-- Every three-group acting on a subgroup of a natural binary SL3 block
has an action image of order at most three. The kernel condition says that
the indicated image is detected by its action on the original subgroup. -/
theorem IsSL3EvenBlock.cubic_image_card_dvd
    {L B W : Subgroup G} (hb : IsSL3EvenBlock L 1)
    (hB : IsPGroup 3 B) (hn : B ≤ normalizer (L : Set G))
    (hWL : W ≤ L) (f : B →* D)
    (hf : ∀ b : B, (∀ w ∈ W, (b : G) * w = w * b) → f b = 1) :
    Nat.card f.range ∣ 3 := by
  let : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  let a : B →* MulAut L := L.normalizerMonoidHom.comp (inclusion hn)
  let q := (quotientAut (pCore 2 L)).comp a
  let K := q.ker.map B.subtype
  have hKB : K ≤ B := map_subtype_le _
  have hKp : IsPGroup 3 K := (hB.to_subgroup q.ker).map B.subtype
  have hKn : K ≤ normalizer (L : Set G) := hKB.trans hn
  have hKc : ⁅K,L⁆ ≤ L.pCoreIn 2 := by
    apply commutator_le.mpr
    rintro k ⟨b,hb,rfl⟩ l hl
    have he := DFunLike.congr_fun (MonoidHom.mem_ker.mp hb)
      (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩)
    change quotientAut (pCore 2 L) (a b) (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩) = _ at he
    rw [quotientAut_apply_mk] at he
    have hh : a b ⟨l,hl⟩ * (⟨l,hl⟩ : L)⁻¹ ∈ pCore 2 L := by
      simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp he
    exact mem_map.mpr ⟨_,hh,rfl⟩
  have hKC := hb.centralizes_of_coreQuotient (cubic_twoPerfect hKp) hKn hKc
  have hk : q.ker ≤ f.ker := by
    intro b hb
    apply hf b
    intro w hw
    exact (hKC (mem_map_of_mem B.subtype hb) w (hWL hw)).symm
  let g := QuotientGroup.lift q.ker f hk
  have hr : g.range = f.range := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective q.ker y
      exact ⟨b,rfl⟩
    · rintro ⟨b,rfl⟩
      exact ⟨QuotientGroup.mk' q.ker b,rfl⟩
  have hd : Nat.card f.range ∣ Nat.card (MulAut (L ⧸ pCore 2 L)) := by
    rw [←hr]
    exact (card_range_dvd g).trans
      ((Nat.card_congr (QuotientGroup.quotientKerEquivRange q).toEquiv) ▸
        q.range.card_subgroup_dvd_card)
  obtain ⟨F,_,_,hF,ρ,⟨m⟩,hρ⟩ := hb.2.2
  have hc : Nat.card (MulAut (L ⧸ pCore 2 L)) = 336 := by
    have hfield : Nat.card F = 2 := by simpa using hF
    let _ := Fintype.ofFinite F
    let eF : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hfield)).symm
    let e := m.quotientIso.trans (Atlas.fieldEquivSL 3 eF)
    rw [Nat.card_congr (MulAut.congr (e.trans Matrix.PSL3Two.equiv)).toEquiv]
    exact Matrix.PSL3Two.Automorphisms.card_aut
  rw [hc] at hd
  obtain ⟨n,hn⟩ := (hB.of_surjective f.rangeRestrict f.rangeRestrict_surjective).exists_card_eq
  have hcop : Nat.Coprime (Nat.card f.range) 112 := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 112).pow_left n
  exact hcop.dvd_of_dvd_mul_right hd
end CFSG.Quasithin.ChapterC
