module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureNatural
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The companion factor in the pure-line centralizer core

The natural point stabilizer has no nonzero fixed dual vector: its
transitivity outside the fixed point and a binary triangle force any
fixed functional to vanish. An invariant nonzero part of the companion
dual factor therefore has at least four elements. Combined with the
whole natural factor, this gives at least 32 elements of the order-64
orbit in the centralizer two-core.

This proves precisely the size bound needed for the hyperplane step of
7.6.1, without assuming the entire companion factor is in the core.
NonFFSourceDoubledBinaryPureCore supplies both coordinate orientations
and the original Baer–Suzuki application. Characteristic two is explicit.
Source: Aschbacher–Smith 7.6.1, printed pp.702–703, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureDual
open BinaryLinearThree NaturalDual ChapterE DoubledBinaryPureCore
variable {G : Type*} [_root_.Group G]

private theorem triangle (z : BinaryLinearThree.Vector) (hz : z ≠ 0) :
    ∃ x y : BinaryLinearThree.Vector,
      x ≠ 0 ∧ x ≠ z ∧ y ≠ 0 ∧ y ≠ z ∧ x+y ≠ 0 ∧ x+y ≠ z := by
  revert z
  decide +kernel

/-- A natural point stabilizer has no nonzero fixed vector on the dual.
Transitivity outside the point and a triangle force the functional to vanish. -/
theorem dual_fixed_eq_zero (z : BinaryLinearThree.Vector) (hz : z ≠ 0)
    (f : Module.Dual (ZMod 2) BinaryLinearThree.Vector)
    (hf : ∀ g : Group, W g z = z → W.dual g f = f) : f = 0 := by
  have same (x y : BinaryLinearThree.Vector) (hx : x ≠ 0) (hxz : x ≠ z)
      (hy : y ≠ 0) (hyz : y ≠ z) : f x = f y := by
    obtain ⟨g,hgz,hgx⟩ := SL3DoubledNaturalOffenders.BinaryOrbits.pair_transitive
      z x z y hz hx hxz.symm hz hy hyz.symm
    have he := LinearMap.congr_fun (hf g hgz) y
    change f (W g⁻¹ y) = f y at he
    rw [← hgx,Representation.inv_self_apply] at he
    exact he.trans (congrArg f hgx)
  obtain ⟨x,y,hx,hxz,hy,hyz,hxy,hxyz⟩ := triangle z hz
  have hx0 : f x = 0 := by
    have hh := same x (x+y) hx hxz hxy hxyz
    rw [map_add,←same x y hx hxz hy hyz,ZModModule.add_self] at hh
    exact hh
  have hout (v : BinaryLinearThree.Vector) (hv : v ≠ 0) (hvz : v ≠ z) : f v = 0 :=
    (same v x hv hvz hx hxz).trans hx0
  have hz0 : f z = 0 := by
    have hzx : z+x ≠ 0 := by
      intro he
      have hh := congrArg (fun v => v+x) he
      simp only [add_assoc,ZModModule.add_self,add_zero,zero_add] at hh
      exact hxz hh.symm
    have hzxz : z+x ≠ z := fun he => hx (add_left_cancel (he.trans (add_zero z).symm))
    have hh := hout (z+x) hzx hzxz
    rwa [map_add,hx0,add_zero] at hh
  apply LinearMap.ext
  intro v
  by_cases hv : v = 0
  · rw [hv,map_zero,LinearMap.zero_apply]
  by_cases hvz : v = z
  · rw [hvz,hz0,LinearMap.zero_apply]
  exact hout v hv hvz

/-- A nonzero invariant piece of the companion dual factor has at least
four elements. An order-two piece would be fixed by the whole point stabilizer. -/
theorem dual_core_four_le [Finite G]
    (W₀ L A B Z N : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G)) (hAW : A ≤ W₀) (hBW : B ≤ W₀)
    (q : L →* Group) (hq : Function.Surjective q)
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) = action (q l) (E w))
    (hA : ∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ A)
    (hB : ∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ B)
    (hZ : Nat.card Z = 2) (hZA : Z ≤ A)
    (hN : L ⊓ centralizer (Z : Set G) ≤ normalizer (N : Set G))
    (y : G) (hyB : y ∈ B) (hyN : y ∈ N) (hy1 : y ≠ 1) :
    4 ≤ Nat.card (B ⊓ N : Subgroup G) := by
  let Q := B ⊓ N
  have hpQ := (IsElementaryAbelian.isPGroup 2 W₀).to_le (inf_le_left.trans hBW : Q ≤ W₀)
  have hnt : Nontrivial Q := by
    exact Q.nontrivial_iff_ne_bot.mpr (fun he => hy1 (mem_bot.mp (he ▸ ⟨hyB,hyN⟩)))
  obtain ⟨n,hn,hcard⟩ := hpQ.nontrivial_iff_card.mp hnt
  by_contra hlt
  have hn1 : n = 1 := by
    have hh : 2^n < 2^2 := by rw [← hcard]; omega
    have hnn := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hh
    omega
  have hcQ : Nat.card Q = 2 := by rw [hcard,hn1]; rfl
  have unique (x : Q) (hx : x ≠ 1) : (x : G) = y := by
    obtain ⟨a,ha,hall⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hcQ
    exact congrArg Subtype.val ((hall x hx).trans
      (hall ⟨y,hyB,hyN⟩ (fun he => hy1 (congrArg Subtype.val he))).symm)
  obtain ⟨z,hz,hallZ⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  let u : Additive W₀ := Additive.ofMul ⟨z,hAW (hZA z.property)⟩
  let v : Additive W₀ := Additive.ofMul ⟨y,hBW hyB⟩
  have hu : (E u).2 = 0 := (hA u).mpr (hZA z.property)
  have hv : (E v).1 = 0 := (hB v).mpr hyB
  have hu0 : (E u).1 ≠ 0 := by
    intro he
    have hh := E.map_eq_zero_iff.mp (Prod.ext he hu)
    exact hz (Subtype.ext (congrArg (fun w : Additive W₀ => (w.toMul : G)) hh))
  have hv0 : (E v).2 ≠ 0 := by
    intro he
    have hh := E.map_eq_zero_iff.mp (Prod.ext hv he)
    exact hy1 (congrArg (fun w : Additive W₀ => (w.toMul : G)) hh)
  apply hv0
  apply dual_fixed_eq_zero (E u).1 hu0
  intro g hgz
  obtain ⟨l,hl⟩ := hq g
  let b := W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)
  have hlu : automizerRepresentation W₀ b u = u := by
    apply E.injective
    rw [hE,hl]
    apply Prod.ext hgz
    change W.dual g (E u).2 = (E u).2
    rw [hu,map_zero]
  have hlz : (l : G) * (z : G) * (l : G)⁻¹ = z :=
    congrArg (fun w : Additive W₀ => (w.toMul : G)) hlu
  have hlC : (l : G) ∈ centralizer (Z : Set G) := by
    intro x hx
    by_cases hx1 : (⟨x,hx⟩ : Z) = 1
    · have he : x = 1 := congrArg Subtype.val hx1
      simp only [he,one_mul,mul_one]
    · have he : x = z := congrArg Subtype.val (hallZ ⟨x,hx⟩ hx1)
      rw [he]
      exact (mul_inv_eq_iff_eq_mul.mp hlz).symm
  let v' := automizerRepresentation W₀ b v
  have hv'B : (v'.toMul : G) ∈ B := by
    apply (hB v').mp
    change (E (automizerRepresentation W₀ b v)).1 = 0
    rw [hE,hl]
    change W g (E v).1 = 0
    rw [hv,map_zero]
  have hv'N : (v'.toMul : G) ∈ N :=
    (mem_normalizer_iff.mp (hN ⟨l.property,hlC⟩) y).mp hyN
  have hv'1 : (v'.toMul : G) ≠ 1 := by
    intro he
    change (MulAut.conj (l : G)) y = 1 at he
    exact hy1 ((MulAut.conj (l : G)).map_eq_one_iff.mp he)
  have he : v' = v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact unique ⟨v'.toMul,hv'B,hv'N⟩ (fun he => hv'1 (congrArg Subtype.val he))
  have he' := hE l v
  rw [hl] at he'
  change E v' = action g (E v) at he'
  rw [he] at he'
  exact (congrArg Prod.snd he').symm


/-- The source characteristic-two input forces at least half the whole
order-64 orbit into the literal centralizer core: all eight natural vectors
and at least four independent companion vectors. -/
theorem core_intersection_card [Finite G]
    (W₀ L A B Z S : Subgroup G) [IsElementaryAbelian 2 W₀]
    (hLN : L ≤ normalizer (W₀ : Set G)) (hAW : A ≤ W₀) (hBW : B ≤ W₀)
    (q : L →* Group) (hq : Function.Surjective q)
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) = action (q l) (E w))
    (hA : ∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ A)
    (hB : ∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ B)
    (hcardB : Nat.card B = 8) (hZ : Nat.card Z = 2) (hZA : Z ≤ A)
    (hWS : W₀ ≤ S) (hSN : S ≤ normalizer (A : Set G) ⊓ normalizer (B : Set G))
    (P : Sylow 2 (centralizer (Z : Set G)))
    (hP : (P : Subgroup _).map (centralizer (Z : Set G)).subtype = S)
    (hc : centralizer (pCore 2 (centralizer (Z : Set G)) : Set (centralizer (Z : Set G))) ≤
      pCore 2 (centralizer (Z : Set G))) :
    32 ≤ Nat.card (W₀ ⊓ (centralizer (Z : Set G)).pCoreIn 2 : Subgroup G) := by
  let C := centralizer (Z : Set G)
  let N := C.pCoreIn 2
  have hSC : S ≤ C := hP.symm.trans_le (map_subtype_le _)
  have hpS : IsPGroup 2 S := hP ▸ P.isPGroup'.map _
  have hpZ := (IsElementaryAbelian.isPGroup 2 W₀).to_le (hZA.trans hAW)
  have hZN : Z ≤ N := le_pCoreIn_of_normalizes hpZ
    (hZA.trans (hAW.trans (hWS.trans hSC))) (Subgroup.centralizer_le_normalizer _)
  have hNC : C ≤ normalizer (N : Set G) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hcardA := DoubledBinaryPureFactors.natural_factor_card W₀ A hAW E hA
  have hAZ : ¬ A ≤ Z := by
    intro hh
    have hn := Nat.card_le_card_of_injective (inclusion hh) (inclusion_injective hh)
    rw [hcardA,hZ] at hn
    omega
  have hBZ : ¬ B ≤ Z := by
    intro hh
    have hn := Nat.card_le_card_of_injective (inclusion hh) (inclusion_injective hh)
    rw [hcardB,hZ] at hn
    omega
  obtain ⟨x,hx,hxZ⟩ := exists_fixedModuloLine_outside Z A S hpS (hAW.trans hWS)
    (hSN.trans inf_le_left) hSC hAZ
  obtain ⟨y,hy,hyZ⟩ := exists_fixedModuloLine_outside Z B S hpS (hBW.trans hWS)
    (hSN.trans inf_le_right) hSC hBZ
  have hxA := ((mem_fixedModuloLine Z A S (hAW.trans (hWS.trans hSC)) hSC x).mp hx).1
  have hyB := ((mem_fixedModuloLine Z B S (hBW.trans (hWS.trans hSC)) hSC y).mp hy).1
  have hxN := fixedModuloLine_le_core Z A S hpZ hc P hP hx
  have hyN := fixedModuloLine_le_core Z B S hpZ hc P hP hy
  have hAN := DoubledBinaryPureNatural.natural_factor_le_of_fixed_seed W₀ L A Z N
    hLN hAW q hq E hE hA hZ hZA hZN (inf_le_right.trans hNC) x hxA hxN hxZ
  have hfour := dual_core_four_le W₀ L A B Z N hLN hAW hBW q hq E hE hA hB
    hZ hZA (inf_le_right.trans hNC) y hyB hyN (fun he => hyZ (he ▸ Z.one_mem))
  have hdis : Disjoint A (B ⊓ N) := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    let w : Additive W₀ := Additive.ofMul ⟨x,hAW hx.1⟩
    have he : w = 0 := E.map_eq_zero_iff.mp
      (Prod.ext ((hB w).mpr hx.2.1) ((hA w).mpr hx.1))
    exact congrArg (fun w : Additive W₀ => (w.toMul : G)) he
  have hnB : B ⊓ N ≤ normalizer (A : Set G) :=
    (inf_le_left.trans hBW).trans (((le_centralizer W₀).trans (centralizer_le hAW)).trans
      (Subgroup.centralizer_le_normalizer _))
  have hcount := card_sup_eq_mul_of_normalizes_of_disjoint A (B ⊓ N) hnB hdis
  have hle : A ⊔ (B ⊓ N) ≤ W₀ ⊓ N :=
    sup_le (le_inf hAW hAN) (le_inf (inf_le_left.trans hBW) inf_le_right)
  have hbound := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  rw [hcount,hcardA] at hbound
  change 32 ≤ Nat.card (W₀ ⊓ N : Subgroup G)
  omega

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPureDual
