module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.CentralizerPair.Orders
public import GorensteinWalter.PGL2Center

/-!
# A common Sylow and a linear central twist

Choose a Sylow two-subgroup R in the actual fixed-field PGL₂. Its center
contains an involution. The marked product comparison embeds R times the
field factor into the canonical inner model; the odd-index calculation
makes the image Sylow in that model. The central involution yields a linear
z for which zσ is another involution centralizing the same Sylow subgroup.

Projective involution descent identifies the two literal centralizers.
Normality of the actual inner model justifies restricting the conjugation.
Center-freeness of fixed-field PGL₂ excludes a nonidentity linear element
from the center of the first centralizer. The parent assembly uses these
facts to reduce generation to subfield maximality.

Source: Aschbacher--Smith, E.1.8 and E.1.14(6), printed pp.210--211 and 214;
E.1.14(6) cites Aschbacher (1982), Lemma 4.10. This local construction also
covers p=3 and p=5 and makes no perfectness assumption on PGL₂(p).
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.CentralizerPair
variable {F : Type*} [Field F] [Finite F]

private def centralizerEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x : G) : centralizer ({x} : Set G) ≃* centralizer ({e x} : Set H) where
  toFun y := ⟨e y, by
    rw [mem_centralizer_singleton_iff]
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp y.property)⟩
  invFun y := ⟨e.symm y, by
    rw [mem_centralizer_singleton_iff]
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      (mem_centralizer_singleton_iff.mp y.property)⟩
  left_inv y := Subtype.ext (e.symm_apply_apply y)
  right_inv y := Subtype.ext (e.apply_symm_apply y)
  map_mul' x y := Subtype.ext (e.map_mul x y)

/-- Projective involution descent restricts to an automorphism of the actual
inner model, since that model has index two in the full semilinear group. -/
theorem centralizer_equiv_of_field_involution {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    (x : innerModel F σ) (hx : orderOf x = 2) (hr : (x : PGammaL2 F).right = σ) :
    Nonempty (centralizer ({x} : Set (innerModel F σ)) ≃*
      centralizer ({pure σ} : Set (innerModel F σ))) := by
  let : (innerModel F σ).Normal := innerModel_normal hp hodd hF σ hσ
  have hne := ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
  obtain ⟨g, hg⟩ := projective_semilinear_involution_conj_inr
    (K := F) ⟨p, 2, hp, hodd, by decide, hF⟩ x
    ((Subgroup.orderOf_coe x).trans hx) (by rw [hr]; exact hne)
  let a : MulAut (innerModel F σ) := MulAut.conjNormal (SemidirectProduct.inl g)⁻¹
  have ha : a x = pure σ := by
    apply Subtype.ext
    change (SemidirectProduct.inl g)⁻¹ * (x : PGammaL2 F) *
      ((SemidirectProduct.inl g)⁻¹)⁻¹ = SemidirectProduct.inr σ
    simpa only [inv_inv, hr] using hg
  exact ⟨(centralizerEquiv a x).trans (MulEquiv.subgroupCongr (by rw [ha]))⟩

private theorem central_involution {G : Type*} [Group G] [Finite G] [Nontrivial G]
    (hG : IsPGroup 2 G) : ∃ z : G, orderOf z = 2 ∧ z ∈ center G := by
  let := hG.center_nontrivial
  have hZ := hG.to_subgroup (center G)
  obtain ⟨n, hn, hc⟩ := hZ.nontrivial_iff_card.mp inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center G) 2
    (hc ▸ dvd_pow_self 2 (by omega : n ≠ 0))
  exact ⟨z, (Subgroup.orderOf_coe z).trans hz, z.property⟩

/-- A central involution of a fixed-field Sylow gives a nontrivial linear
twist; the product Sylow stays Sylow in the actual inner extension. -/
theorem exists_central_twist {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    [Finite (innerModel F σ)] :
    ∃ (T : Sylow 2 (innerModel F σ)) (z : innerModel F σ),
      orderOf z = 2 ∧ (z : PGammaL2 F).right = 1 ∧
      orderOf (z * pure σ) = 2 ∧
      (T : Subgroup (innerModel F σ)) ≤ centralizer ({pure σ} : Set (innerModel F σ)) ∧
      (T : Subgroup (innerModel F σ)) ≤ centralizer ({z * pure σ} : Set (innerModel F σ)) ∧
      z ∈ centralizer ({pure σ} : Set (innerModel F σ)) := by
  classical
  let K := FixedPoints.subfield (zpowers σ) F
  let C := centralizer ({pure σ} : Set (innerModel F σ))
  let e := pureCentralizerEquiv hp hodd hF σ hσ
  let f : PGL2 K × zpowers σ →* innerModel F σ := C.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := C.subtype_injective.comp e.symm.injective
  have hfrange : f.range = C := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact (e.symm y).property
    · intro hx; exact ⟨e ⟨x, hx⟩, congrArg Subtype.val (e.symm_apply_apply _)⟩
  have hfcoe (x : PGL2 K × zpowers σ) :
      (f x : PGammaL2 F) = fixedProductMap σ x :=
    pureCentralizerEquiv_symm_coe hp hodd hF σ hσ x
  let : Finite (PGL2 K) := Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let : Finite (zpowers σ) := Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hσ]; decide)
  have hK : Nat.card K = p := fixedSubfield_card hF σ
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).1
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
  let R : Sylow 2 (PGL2 K) := default
  have hRtwo : 2 ∣ Nat.card R := by
    apply R.dvd_card_of_dvd_card
    rw [pgl2_card_formula, hK]
    apply dvd_mul_of_dvd_right
    exact even_iff_two_dvd.mp (hodd.pow.tsub_odd (by decide : Odd 1))
  let : Nontrivial R := Finite.one_lt_card_iff_nontrivial.mp
    (Nat.lt_of_lt_of_le (by decide : 1 < 2) (Nat.le_of_dvd Nat.card_pos hRtwo))
  obtain ⟨r, hr, hrZ⟩ := central_involution R.isPGroup'
  let Q : Subgroup (PGL2 K × zpowers σ) := (R : Subgroup (PGL2 K)).prod ⊤
  have hQ : IsPGroup 2 Q := by
    obtain ⟨n, hn⟩ := R.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := n + 1)
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      Subgroup.card_top, Nat.card_zpowers, hσ, hn, pow_succ]
  have hidx : ¬ 2 ∣ (Q.map f).index := by
    rw [index_map_of_injective Q hf, hfrange, index_prod, index_top, mul_one]
    exact Nat.prime_two.not_dvd_mul R.not_dvd_index
      (pureCentralizer_index_odd hp hodd hF σ hσ).not_two_dvd_nat
  let T : Sylow 2 (innerModel F σ) := (hQ.map f).toSylow hidx
  let z : innerModel F σ := f (r, 1)
  have hzo : orderOf z = 2 := by
    rw [show z = f (r, 1) from rfl, orderOf_injective f hf]
    have hi : Function.Injective (MonoidHom.inl (PGL2 K) (zpowers σ)) :=
      fun x y h => congrArg Prod.fst h
    exact (orderOf_injective _ hi (r : PGL2 K)).trans ((Subgroup.orderOf_coe r).trans hr)
  have hzr : (z : PGammaL2 F).right = 1 := by
    rw [show z = f (r, 1) from rfl, hfcoe]
    rfl
  have hzC : z ∈ C := (e.symm (r, 1)).property
  have hTC : (T : Subgroup (innerModel F σ)) ≤ C := by
    exact (map_le_range f Q).trans_eq hfrange
  have hTz : (T : Subgroup (innerModel F σ)) ≤ centralizer ({z} : Set (innerModel F σ)) := by
    rintro x ⟨y, hy, rfl⟩
    rw [mem_centralizer_singleton_iff]
    change f y * f (r, 1) = f (r, 1) * f y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Prod.ext
    · exact congrArg Subtype.val ((mem_center_iff.mp hrZ) ⟨y.1, hy.1⟩)
    · simp
  have hprod : orderOf (z * pure σ) = 2 := by
    apply (orderOf_eq_prime_iff (x := z * pure σ)).mpr
    constructor
    · have hzsq : z ^ 2 = 1 := by simpa only [hzo] using pow_orderOf_eq_one z
      have hpsq : pure σ ^ 2 = 1 := by
        apply Subtype.ext
        change (SemidirectProduct.inr σ : PGammaL2 F) ^ 2 = 1
        rw [← map_pow, ((orderOf_eq_prime_iff (x := σ)).mp hσ).1, map_one]
      have hcomm : Commute z (pure σ) :=
        (mem_centralizer_singleton_iff.mp hzC)
      rw [hcomm.mul_pow, hzsq, hpsq, one_mul]
    · intro hh
      have hh' := congrArg (fun x : innerModel F σ => (x : PGammaL2 F).right) hh
      have hsne := ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
      apply hsne
      simpa only [Subgroup.coe_mul, SemidirectProduct.mul_right, hzr,
        pure, SemidirectProduct.right_inr, one_mul, Subgroup.coe_one,
        SemidirectProduct.one_right] using hh'
  refine ⟨T, z, hzo, hzr, hprod, hTC, ?_, hzC⟩
  intro x hx
  rw [mem_centralizer_singleton_iff]
  have hz := mem_centralizer_singleton_iff.mp (hTz hx)
  have hs := mem_centralizer_singleton_iff.mp (hTC hx)
  calc
    x * (z * pure σ) = (x * z) * pure σ := (mul_assoc _ _ _).symm
    _ = (z * x) * pure σ := by rw [hz]
    _ = (z * pure σ) * x := by rw [mul_assoc, hs, ← mul_assoc]


/-- The literal pure-field centralizer has no nonidentity central element
with trivial field coordinate. -/
theorem linear_central_eq_one {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    (z : innerModel F σ)
    (hzC : z ∈ centralizer ({pure σ} : Set (innerModel F σ)))
    (hzr : (z : PGammaL2 F).right = 1)
    (hcomm : centralizer ({pure σ} : Set (innerModel F σ)) ≤
      centralizer ({z} : Set (innerModel F σ))) : z = 1 := by
  let C := centralizer ({pure σ} : Set (innerModel F σ))
  let e := pureCentralizerEquiv hp hodd hF σ hσ
  let zc : C := ⟨z, hzC⟩
  have hrepr : (z : PGammaL2 F) = fixedProductMap σ (e zc) := by
    rw [← pureCentralizerEquiv_symm_coe hp hodd hF σ hσ]
    exact congrArg (fun c : C => ((c : innerModel F σ) : PGammaL2 F))
      (e.symm_apply_apply zc).symm
  have hsnd : (e zc).2 = 1 := by
    apply Subtype.ext
    have h := congrArg SemidirectProduct.right hrepr
    rw [hzr] at h
    exact h.symm
  have hfst : (e zc).1 ∈ center (PGL2 (FixedPoints.subfield (zpowers σ) F)) := by
    rw [mem_center_iff]
    intro a
    let c : C := e.symm (a, 1)
    have hh : c * zc = zc * c := Subtype.ext
      (mem_centralizer_singleton_iff.mp (hcomm c.property))
    have he := congrArg (fun c : C => (e c).1) hh
    simpa only [map_mul, Prod.fst_mul, c, e.apply_symm_apply] using he
  rw [pgl2_center_eq_bot, mem_bot] at hfst
  have he : e zc = 1 := Prod.ext hfst hsnd
  have hz : zc = 1 := e.injective (he.trans e.map_one.symm)
  exact congrArg Subtype.val hz

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.CentralizerPair
