module
public import Theory.GroupTheory.CentralDoubleCoverFusion
public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.Fusion
public import Theory.Mathieu.M22.UniversalMultiplier.TwoPrimary.HexadLifting
public import Theory.GroupTheory.PerfectCentralCoverLocalBound
public import Theory.Representation.BinaryPermutationSixCover.Universal
public import Theory.Representation.ElementaryPerfectSplit

/-!
# Elementary-kernel rank in native M₂₂ covers

Global involution fusion makes the hexad translation preimage elementary
when the central kernel has exponent two. Transfer then makes its natural
A₆ module projection a perfect central module cover. The five-dimensional
augmentation cover bounds that kernel by one dimension.
Source: Aschbacher–Smith I.1.3(4), p.407, and the rank input of 12.7.5, p.840.
-/

public section
noncomputable section
open Subgroup PerfectCentralCovering Theory.GroupTheory
open Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace Sporadic.Mathieu.M22UniversalMultiplier.TwoRankSource

private def eightToFour :
    Multiplicative (Fin 3 → ZMod 2) →* Multiplicative (Fin 4 → ZMod 2) where
  toFun v := Multiplicative.ofAdd (fun i => if h : i.val < 3 then v.toAdd ⟨i.val, h⟩ else 0)
  map_one' := by
    change (fun i : Fin 4 => if h : i.val < 3 then (0 : Fin 3 → ZMod 2) ⟨i.val, h⟩ else 0) = 0
    ext i
    split_ifs <;> rfl
  map_mul' v w := by
    apply Multiplicative.toAdd.injective
    funext i
    change (if h : i.val < 3 then (v.toAdd + w.toAdd) ⟨i.val, h⟩ else 0) =
      (if h : i.val < 3 then v.toAdd ⟨i.val, h⟩ else 0) +
      (if h : i.val < 3 then w.toAdd ⟨i.val, h⟩ else 0)
    split_ifs <;> simp

private theorem eightToFour_injective : Function.Injective eightToFour := by
  intro v w h
  apply Multiplicative.toAdd.injective
  funext i
  have he := congrArg (fun x : Multiplicative (Fin 4 → ZMod 2) => x.toAdd i.castSucc) h
  change (if h : i.val < 3 then v.toAdd ⟨i.val, h⟩ else 0) =
    (if h : i.val < 3 then w.toAdd ⟨i.val, h⟩ else 0) at he
  simpa only [dif_pos i.isLt] using he

private def nativeEight : Multiplicative (Fin 3 → ZMod 2) →* M22 :=
  m22HexadStabilizer.subtype.comp
    ((m22SetAction m22Hexad123).ker.subtype.comp
      ((m22HexadKernelEquiv m22Hexad123_mem).symm.toMonoidHom.comp
        (M23Geometry.heptadBinaryEquiv.toMonoidHom.comp eightToFour)))

private theorem nativeEight_injective : Function.Injective nativeEight :=
  m22HexadStabilizer.subtype_injective.comp
    ((m22SetAction m22Hexad123).ker.subtype_injective.comp
      ((m22HexadKernelEquiv m22Hexad123_mem).symm.injective.comp
        (M23Geometry.heptadBinaryEquiv.injective.comp eightToFour_injective)))

/-- Global native fusion forces square-one lifts for any elementary central kernel. -/
theorem square_eq_one_of_elementary_kernel {E : Type*} [Group E] [Finite E]
    (f : Cover E M22) [IsElementaryAbelian 2 f.toMonoidHom.ker]
    (x : E) (hx : (f.toMonoidHom x) ^ 2 = 1) : x ^ 2 = 1 := by
  have h2 (z : E) (hz : z ∈ f.toMonoidHom.ker) : z ^ 2 = 1 := by
    exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 f.toMonoidHom.ker) ⟨z, hz⟩)
  by_cases h : f.toMonoidHom x = 1
  · exact h2 x h
  · exact CentralDoubleCoverFusion.square_eq_one_of_fusion f.toMonoidHom f.surjective
      f.ker_le_center h2 nativeEight nativeEight_injective m22_involutions_isConj x
      (orderOf_eq_prime_iff.mpr ⟨hx, h⟩)

private theorem coinvariants_image {U V : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) (alternatingGroup (Fin 6)) U)
    (τ : Representation (ZMod 2) (alternatingGroup (Fin 6)) V)
    (p : σ.IntertwiningMap τ) (hp : Function.Surjective p) :
    (Coinvariants.ker σ).map p.toLinearMap = Coinvariants.ker τ := by
  have he (a : alternatingGroup (Fin 6)) (v : U) : p (σ a v) = τ a (p v) :=
    LinearMap.congr_fun (p.isIntertwining' a) v
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, v⟩, rfl⟩
    change p (σ a v - v) ∈ Coinvariants.ker τ
    rw [map_sub, he]
    exact Coinvariants.sub_mem_ker a (p v)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, v⟩, rfl⟩
    obtain ⟨u, rfl⟩ := hp v
    refine ⟨σ a u - u, Coinvariants.sub_mem_ker a u, ?_⟩
    change p (σ a u - u) = τ a (p u) - p u
    rw [map_sub, he]

private theorem natural_generated :
    Coinvariants.ker (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) = ⊤ := by
  rw [← coinvariants_image _ _ (BinaryPermutation.alternatingCoreProjection (Fin 6))
    (BinaryPermutation.coreToNatural_surjective (Ω := Fin 6)), BinaryPermutation.alternatingSix_core_generated]
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (BinaryPermutation.coreToNatural_surjective (Ω := Fin 6))

/-- An elementary central kernel in a finite perfect native M₂₂ cover has order at most two. -/
theorem elementary_kernel_card_le_two {E : Type*} [Group E] [Finite E]
    (f : Cover E M22) [IsElementaryAbelian 2 f.toMonoidHom.ker] :
    Nat.card f.toMonoidHom.ker ≤ 2 := by
  let B := (m22SetAction m22Hexad123).ker
  let : B.Normal := inferInstanceAs (m22SetAction m22Hexad123).ker.Normal
  let P := m22HexadStabilizer.comap f.toMonoidHom
  let q : P →* m22HexadStabilizer :=
    (f.toMonoidHom.comp P.subtype).codRestrict _ (fun x => x.property)
  have hq : Function.Surjective q := by
    intro h
    obtain ⟨x, hx⟩ := f.surjective h.val
    exact ⟨⟨x, by change f.toMonoidHom x ∈ m22HexadStabilizer; rw [hx]; exact h.property⟩,
      Subtype.ext hx⟩
  let N := B.comap q
  let : N.Normal := ⟨fun x hx g => by
    change q (g * x * g⁻¹) ∈ B
    rw [map_mul, map_mul, map_inv]
    exact (inferInstance : B.Normal).conj_mem (q x) hx (q g)⟩
  let qN : N →* B := (q.comp N.subtype).codRestrict _ (fun x => x.property)
  have hqN : Function.Surjective qN := by
    intro v
    obtain ⟨x, hx⟩ := hq v.val
    exact ⟨⟨x, by change q x ∈ B; rw [hx]; exact v.property⟩, Subtype.ext hx⟩
  let : IsElementaryAbelian 2 B := m22HexadKernel_elementaryAbelian m22Hexad123_mem
  have hsquare (x : N) : x ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    apply square_eq_one_of_elementary_kernel f
    exact congrArg (fun v : B => (v.val : M22))
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 B) (qN x))
  let : IsElementaryAbelian 2 N := {
    toIsMulCommutative := ⟨⟨fun x y =>
      (Commute.of_orderOf_dvd_two (fun z => orderOf_dvd_of_pow_eq_one (hsquare z)) x y).eq⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsquare }
  obtain ⟨s, hs⟩ := exists_hexadSection_lift f.toMonoidHom f.surjective f.ker_le_center
    (IsElementaryAbelian.isPGroup 2 f.toMonoidHom.ker) m22Hexad123_mem
  let j := m22HexadSection m22Hexad123_mem
  let S : alternatingGroup (Fin 6) →* P := s.codRestrict P (by
    intro a
    change f.toMonoidHom (s a) ∈ m22HexadStabilizer
    rw [show f.toMonoidHom (s a) = (j a : M22) from DFunLike.congr_fun hs a]
    exact (j a).property)
  have hqS (a : alternatingGroup (Fin 6)) : q (S a) = j a :=
    Subtype.ext (DFunLike.congr_fun hs a)
  let α : alternatingGroup (Fin 6) →* MulAut N := MulAut.conjNormal.comp S
  have hα (a : alternatingGroup (Fin 6)) (x : N) :
      qN (α a x) = MulAut.conjNormal (j a) (qN x) := by
    apply Subtype.ext
    change q (S a * x.val * (S a)⁻¹) = _
    rw [map_mul, map_mul, map_inv, hqS]
    rfl
  let σ := elementaryRepresentation (p := 2) α
  let e := m22HexadNaturalCoordinates m22Hexad123_mem
  let coord : Additive N →+ BinaryPermutation.natural (Fin 6) := {
    toFun := fun x => (e (qN x.toMul)).toAdd
    map_zero' := by simp
    map_add' := by
      intro x y
      change (e (qN (x.toMul * y.toMul))).toAdd = _
      rw [map_mul, map_mul]
      rfl }
  let p : σ.IntertwiningMap (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) := {
    toLinearMap := coord.toZModLinearMap 2
    isIntertwining' := by
      intro a
      apply LinearMap.ext
      intro x
      change (e (qN (α a x.toMul))).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) a.val (e (qN x.toMul)).toAdd
      rw [hα]
      exact m22HexadNaturalCoordinates_section m22Hexad123_mem a (qN x.toMul) }
  have hp : Function.Surjective p := by
    intro v
    obtain ⟨x, hx⟩ := hqN (e.symm (Multiplicative.ofAdd v))
    refine ⟨Additive.ofMul x, ?_⟩
    change (e (qN x)).toAdd = v
    rw [hx, e.apply_symm_apply]
    rfl
  have hpker (x : N) : p (Additive.ofMul x) = 0 ↔ qN x = 1 := by
    change e (qN x) = 1 ↔ qN x = 1
    exact map_eq_one_iff e e.injective
  have hfixed : p.toLinearMap.ker ≤ fixed σ := by
    intro x hx a
    have hqx : qN x.toMul = 1 := (hpker x.toMul).mp hx
    have hfx : f.toMonoidHom x.toMul.val.val = 1 :=
      congrArg (fun v : B => (v.val : M22)) hqx
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change s a * x.toMul.val.val * (s a)⁻¹ = x.toMul.val.val
    rw [mem_center_iff.mp (f.ker_le_center hfx) (s a), mul_inv_cancel_right]
  let W := Coinvariants.ker σ
  have hWmap : W.map p.toLinearMap = ⊤ :=
    (coinvariants_image _ _ p hp).trans natural_generated
  have hWsur (v : B) : ∃ x : N, Additive.ofMul x ∈ W ∧ qN x = v := by
    obtain ⟨x, hx, he⟩ := (show (e v).toAdd ∈ W.map p.toLinearMap by rw [hWmap]; trivial)
    refine ⟨x.toMul, hx, e.injective ?_⟩
    exact Multiplicative.toAdd.injective he
  let kP : N ⋊[α] alternatingGroup (Fin 6) →* P :=
    SemidirectProduct.lift N.subtype S (by
      intro a
      apply MonoidHom.ext
      intro x
      rfl)
  let k : N ⋊[α] alternatingGroup (Fin 6) →* E := P.subtype.comp kP
  have hqk (x : N ⋊[α] alternatingGroup (Fin 6)) :
      q (kP x) = (qN x.left).val * j x.right := by
    change q (x.left.val * S x.right) = _
    rw [map_mul, hqS]
    rfl
  let κ : N ⋊[α] alternatingGroup (Fin 6) →* Multiplicative (Coinvariants σ) := {
    toFun := fun x => Multiplicative.ofAdd (Coinvariants.mk σ (Additive.ofMul x.left))
    map_one' := map_zero (Coinvariants.mk σ)
    map_mul' := by
      intro x y
      change Coinvariants.mk σ (Additive.ofMul x.left + σ x.right (Additive.ofMul y.left)) =
        Coinvariants.mk σ (Additive.ofMul x.left) + Coinvariants.mk σ (Additive.ofMul y.left)
      rw [map_add, Coinvariants.mk_self_apply] }
  let H₀ := κ.ker.map k
  have hHmap : H₀.map f.toMonoidHom = m22HexadStabilizer := by
    apply le_antisymm
    · rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      exact (kP z).property
    · intro h hh
      obtain ⟨⟨v, a'⟩, he⟩ := (m22HexadSection_isComplement m22Hexad123_mem).2 ⟨h, hh⟩
      obtain ⟨a, ha⟩ := a'.property
      obtain ⟨x, hx, hqx⟩ := hWsur v
      let z : N ⋊[α] alternatingGroup (Fin 6) := ⟨x, a⟩
      refine ⟨k z, ⟨z, ?_, rfl⟩, ?_⟩
      · change Coinvariants.mk σ (Additive.ofMul x) = 0
        exact (Coinvariants.mk_eq_zero σ).mpr hx
      · change (q (kP z) : M22) = h
        rw [hqk]
        change ((qN x).val * j a : m22HexadStabilizer).val = h
        rw [hqx, ha]
        exact congrArg Subtype.val he
  have hindex : ¬ 2 ∣ m22HexadStabilizer.index := by
    have hh := m22HexadStabilizer.card_mul_index
    rw [m22HexadStabilizer_card, m22_order] at hh
    have hi : m22HexadStabilizer.index = 77 := by omega
    rw [hi]
    decide
  have hCH := f.central_pSubgroup_le_local_lift H₀ m22HexadStabilizer hHmap hindex
    f.toMonoidHom.ker le_rfl (IsElementaryAbelian.isPGroup 2 f.toMonoidHom.ker)
  let β : P →* alternatingGroup (Fin 6) := (m22HexadMarking m22Hexad123_mem).symm.toMonoidHom.comp
    ((m22HexadSixMap m22Hexad123_mem).comp q)
  have hβS (a : alternatingGroup (Fin 6)) : β (S a) = a := by
    change (m22HexadMarking m22Hexad123_mem).symm
      (m22HexadSixMap m22Hexad123_mem (q (S a))) = a
    rw [hqS, m22HexadSixMap_section, MulEquiv.symm_apply_apply]
  have hβN (x : N) : β x.val = 1 := by
    have hx : m22HexadSixMap m22Hexad123_mem (q x.val) = 1 := by
      change q x.val ∈ (m22HexadSixMap m22Hexad123_mem).ker
      rw [m22HexadSixMap_ker]
      exact x.property
    change (m22HexadMarking m22Hexad123_mem).symm
      (m22HexadSixMap m22Hexad123_mem (q x.val)) = 1
    rw [hx, map_one]
  have hβk (x : N ⋊[α] alternatingGroup (Fin 6)) : β (kP x) = x.right := by
    change β (x.left.val * S x.right) = _
    rw [map_mul, hβN, hβS, one_mul]
  have hkerW : p.toLinearMap.ker ≤ W := by
    intro x hx
    have hqx := (hpker x.toMul).mp hx
    have hfx : f.toMonoidHom x.toMul.val.val = 1 :=
      congrArg (fun v : B => (v.val : M22)) hqx
    obtain ⟨y, hy, he⟩ := hCH hfx
    have hpEq : kP y = x.toMul.val := Subtype.ext he
    have hyr : y.right = 1 :=
      (hβk y).symm.trans ((congrArg β hpEq).trans (hβN x.toMul))
    change y.left.val * S y.right = x.toMul.val at hpEq
    rw [hyr, map_one, mul_one] at hpEq
    have hyl : y.left = x.toMul := Subtype.ext hpEq
    change Coinvariants.mk σ (Additive.ofMul y.left) = 0 at hy
    rw [hyl] at hy
    exact (Coinvariants.mk_eq_zero σ).mp hy
  have hWtop : Coinvariants.ker σ = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨w, hw, hwp⟩ := (show p x ∈ W.map p.toLinearMap by rw [hWmap]; trivial)
    change p w = p x at hwp
    have hxw : x - w ∈ p.toLinearMap.ker := by
      change p (x - w) = 0
      rw [map_sub, hwp, sub_self]
    have hsum := W.add_mem (hkerW hxw) hw
    simpa only [sub_add_cancel] using hsum
  obtain ⟨b, hb, _, _⟩ := BinaryPermutation.SixCover.core_quotient_of_alternating_cover
    σ p ⟨hp, hfixed, hWtop⟩
  have hdim : Module.finrank (ZMod 2) (Additive N) ≤ 5 := by
    have h := LinearMap.finrank_le_finrank_of_surjective hb
    simpa only [BinaryPermutation.finrank_core, Fintype.card_fin] using h
  have hcardN : Nat.card N ≤ 32 := by
    change Nat.card (Additive N) ≤ 32
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact (Nat.pow_le_pow_right (by decide : 0 < 2) hdim)
  let i : qN.ker →* f.toMonoidHom.ker :=
    (P.subtype.comp (N.subtype.comp qN.ker.subtype)).codRestrict _ (fun x =>
      congrArg (fun v : B => (v.val : M22)) x.property)
  have hii : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.toMonoidHom.ker => (z : E)) h
  have his : Function.Surjective i := by
    intro c
    let cp : P := ⟨c.val, by
      change f.toMonoidHom c.val ∈ m22HexadStabilizer
      rw [c.property]
      exact m22HexadStabilizer.one_mem⟩
    have hcq : q cp = 1 := Subtype.ext c.property
    let cn : N := ⟨cp, by change q cp ∈ B; rw [hcq]; exact B.one_mem⟩
    have hcn : qN cn = 1 := Subtype.ext hcq
    exact ⟨⟨cn, hcn⟩, rfl⟩
  have hcardK : Nat.card qN.ker = Nat.card f.toMonoidHom.ker :=
    Nat.card_congr (MulEquiv.ofBijective i ⟨hii, his⟩).toEquiv
  have hcount := qN.ker.card_mul_index
  rw [Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective qN hqN).toEquiv,
    m22HexadKernel_card m22Hexad123_mem, hcardK] at hcount
  omega

end Sporadic.Mathieu.M22UniversalMultiplier.TwoRankSource
