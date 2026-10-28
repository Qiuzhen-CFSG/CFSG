module
public import Theory.GroupTheory.BinaryWreathFrattini
public import Theory.Frattini.SquareImage

/-!
# Frattini bounds for a wreath product with a product constraint

Let d : R → C split, with C abelian. The swap acts on the pairs (r,t)
with d(r)d(t)=1. In the elementary Frattini quotient of this semidirect
product, a copy of R and the swap generate the image: the complementary
kernel factor is identified with its swapped image. Thus its Frattini
order is at most twice that of R.

For arbitrary finite R, choose a Sylow subgroup containing the section of
a Sylow of C. The resulting constrained wreath subgroup has odd index,
which transfers the same bound to every Sylow two-subgroup.

The actual consumer is the determinant-one two-block subgroup of SL₄ in
`Theory.SpecificGroups.PSL4.OddFrattiniSixteen`, used to exclude the outer
section in Aschbacher--Smith 4.4.10--11, printed p.621.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace BalancedWreath
variable {R C : Type*} [Group R] [Finite R] [CommGroup C]
local notation "C2" => Multiplicative (ZMod 2)

def base (d : R →* C) : Subgroup (R × R) := (d.coprod d).ker

def swap (d : R →* C) : MulAut (base d) where
  toFun x := ⟨(x.val.2,x.val.1),by
    change d x.val.2 * d x.val.1 = 1
    rw [mul_comm]
    exact x.property⟩
  invFun x := ⟨(x.val.2,x.val.1),by
    change d x.val.2 * d x.val.1 = 1
    rw [mul_comm]
    exact x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def action (d : R →* C) : C2 →* MulAut (base d) where
  toFun c := if c.toAdd = 0 then 1 else swap d
  map_one' := by simp
  map_mul' c e := by
    obtain ⟨c,rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ C2).surjective c
    obtain ⟨e,rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ C2).surjective e
    fin_cases c <;> fin_cases e <;>
      apply MulEquiv.ext <;> intro x <;> rfl

abbrev W (d : R →* C) := base d ⋊[action d] C2
instance finiteW (d : R →* C) : Finite (W d) :=
  Finite.of_equiv (base d × C2) SemidirectProduct.equivProd.symm

def sectionBase (d : R →* C) (s : C →* R) (hs : d.comp s = MonoidHom.id C) : R →* base d where
  toFun r := ⟨(r,(s (d r))⁻¹),by
    change d r * d ((s (d r))⁻¹) = 1
    have h := DFunLike.congr_fun hs (d r)
    change d (s (d r)) = d r at h
    rw [map_inv,h,mul_inv_cancel]⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' r t := by
    apply Subtype.ext
    change (r*t,(s (d (r*t)))⁻¹) = (r*t,(s (d r))⁻¹ * (s (d t))⁻¹)
    congr 1
    rw [map_mul,map_mul,mul_inv_rev]
    exact ((Commute.all (d t) (d r)).map s).inv_inv.eq

theorem isPGroup (d : R →* C) (hR : IsPGroup 2 R) : IsPGroup 2 (W d) := by
  obtain ⟨m,hm⟩ := hR.exists_card_eq
  have hp : IsPGroup 2 (R × R) := IsPGroup.of_card (n := m+m) (by rw [Nat.card_prod,hm,pow_add])
  have hbase : IsPGroup 2 (base d) := hp.to_subgroup _
  obtain ⟨n,hn⟩ := hbase.exists_card_eq
  apply IsPGroup.of_card (n := n+1)
  rw [SemidirectProduct.card,hn,pow_succ]
  congr 1
  exact Nat.card_zmod 2

theorem card_frattini_le (d : R →* C) (s : C →* R)
    (hs : d.comp s = MonoidHom.id C) (hR : IsPGroup 2 R) :
    Nat.card (W d ⧸ frattini (W d)) ≤ 2 * Nat.card (R ⧸ frattini R) := by
  let : Fact (IsPGroup 2 (W d)) := ⟨isPGroup d hR⟩
  let E := W d ⧸ frattini (W d)
  let : IsElementaryAbelian 2 E := isElementaryAbelian_quotient_frattini
  let q : W d →* E := QuotientGroup.mk' _
  let a : R →* W d := SemidirectProduct.inl.comp (sectionBase d s hs)
  let b : C2 →* W d := SemidirectProduct.inr
  have hphi : frattini R ≤ (q.comp a).ker :=
    Theory.GroupTheory.frattini_le_ker_of_square_image _ (fun x =>
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) _)
  let f : R ⧸ frattini R →* E := QuotientGroup.lift _ (q.comp a) hphi
  let g : (R ⧸ frattini R) × C2 →* E := f.coprod (q.comp b)
  have hswap (r : R) (hr : d r = 1) :
      q (SemidirectProduct.inl (⟨(1,r),by change d 1 * d r = 1; simp [hr]⟩ : base d)) = q (a r) := by
    have h := congrArg q (SemidirectProduct.inl_aut (φ := action d)
      (.ofAdd 1) (sectionBase d s hs r))
    have he : action d (.ofAdd 1) (sectionBase d s hs r) =
        (⟨(1,r),by change d 1 * d r = 1; simp [hr]⟩ : base d) := by
      apply Subtype.ext
      change ((s (d r))⁻¹,r) = (1,r)
      simp [hr]
    rw [he] at h
    simp only [map_mul,map_inv] at h
    rw [mul_comm (q (SemidirectProduct.inr (.ofAdd 1))),mul_inv_cancel_right] at h
    exact h
  have hg : Function.Surjective g := by
    intro e
    obtain ⟨⟨⟨⟨r,t⟩,hrt⟩,c⟩,rfl⟩ := QuotientGroup.mk'_surjective (frattini (W d)) e
    let k := s (d r) * t
    have hk : d k = 1 := by
      have h := DFunLike.congr_fun hs (d r)
      change d (s (d r)) = d r at h
      change d r * d t = 1 at hrt
      simpa only [k,map_mul,h] using hrt
    refine ⟨(QuotientGroup.mk' (frattini R) (r*k),c),?_⟩
    change q (a (r*k)) * q (b c) = q ⟨⟨(r,t),hrt⟩,c⟩
    have he : (⟨(r,t),hrt⟩ : base d) =
        sectionBase d s hs r * ⟨(1,k),by change d 1 * d k = 1; simp [hk]⟩ := by
      apply Subtype.ext
      change (r,t) = (r*1,(s (d r))⁻¹ * k)
      simp [k]
    have he2 : q (SemidirectProduct.inl (⟨(r,t),hrt⟩ : base d)) = q (a r)*q (a k) := by
      rw [he,SemidirectProduct.inl.map_mul,q.map_mul,hswap k hk]
      rfl
    have he3 : q (⟨⟨(r,t),hrt⟩,c⟩ : W d) =
        q (SemidirectProduct.inl (⟨(r,t),hrt⟩ : base d)) * q (b c) :=
      by rw [SemidirectProduct.mk_eq_inl_mul_inr,q.map_mul]
    rw [he3,he2]
    exact congrArg (fun x => x * q (b c)) ((q.comp a).map_mul r k)
  have hc := Nat.card_le_card_of_surjective g hg
  have hC : Nat.card C2 = 2 := by change Nat.card (ZMod 2) = 2; exact Nat.card_zmod 2
  simpa only [Nat.card_prod,hC,Nat.mul_comm] using hc

end BalancedWreath

namespace BalancedWreath
open Subgroup
open scoped IsMulCommutative
variable {R C H D : Type*} [Group R] [Finite R] [CommGroup C]
  [Group H] [CommGroup D]
local notation "C2" => Multiplicative (ZMod 2)

def mapBase (d : R →* C) (e : H →* D) (f : R →* H) (c : C →* D)
    (h : e.comp f = c.comp d) : base d →* base e where
  toFun x := ⟨(f x.val.1,f x.val.2),by
    have h1 := DFunLike.congr_fun h x.val.1
    have h2 := DFunLike.congr_fun h x.val.2
    change e (f x.val.1) * e (f x.val.2) = 1
    change e (f x.val.1) = c (d x.val.1) at h1
    change e (f x.val.2) = c (d x.val.2) at h2
    rw [h1,h2,←map_mul]
    exact (congrArg c x.property).trans (map_one c)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

def map (d : R →* C) (e : H →* D) (f : R →* H) (c : C →* D)
    (h : e.comp f = c.comp d) : W d →* W e :=
  SemidirectProduct.map (mapBase d e f c h) (MonoidHom.id _) (by
    intro k
    obtain ⟨k,rfl⟩ := (Multiplicative.ofAdd : ZMod 2 ≃ C2).surjective k
    fin_cases k <;> rfl)

omit [Finite R] in
theorem map_injective (d : R →* C) (e : H →* D) (f : R →* H) (c : C →* D)
    (h : e.comp f = c.comp d) (hf : Function.Injective f) :
    Function.Injective (map d e f c h) := by
  intro x y hxy
  have hl := congrArg (fun z : W e => z.left.val) hxy
  have hr := congrArg SemidirectProduct.right hxy
  apply SemidirectProduct.ext
  · exact Subtype.ext (Prod.ext (hf (congrArg Prod.fst hl)) (hf (congrArg Prod.snd hl)))
  · exact hr

variable [Finite C]
omit [Finite R] [Finite C] in
theorem card_mul (d : R →* C) (hd : Function.Surjective d) :
    Nat.card (W d) * Nat.card C = 2 * Nat.card R ^ 2 := by
  have hsurj : Function.Surjective (d.coprod d) := by
    intro c
    obtain ⟨r,rfl⟩ := hd c
    exact ⟨(r,1),by simp⟩
  have hc := (d.coprod d).ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hsurj,card_top,Nat.card_prod] at hc
  have hC : Nat.card C2 = 2 := by change Nat.card (ZMod 2) = 2; exact Nat.card_zmod 2
  rw [SemidirectProduct.card,hC]
  change Nat.card (d.coprod d).ker * 2 * Nat.card C = _
  calc
    _ = 2 * (Nat.card (d.coprod d).ker * Nat.card C) := by ring
    _ = _ := by rw [hc,pow_two]

theorem sylow_card_frattini_le
    (d : R →* C) (s : C →* R) (hs : d.comp s = MonoidHom.id C)
    (b : ℕ) (hb : ∀ P : Sylow 2 R, Nat.card (P ⧸ frattini P) ≤ b)
    (Q : Sylow 2 (W d)) : Nat.card (Q ⧸ frattini Q) ≤ 2*b := by
  let U : Sylow 2 C := default
  let : Unique (Sylow 2 C) := Sylow.unique_of_normal U inferInstance
  obtain ⟨P,hP⟩ := (U.isPGroup'.map s).exists_le_sylow
  have hdet (x : P) : d (x : R) ∈ U := by
    obtain ⟨S,hS⟩ := (P.isPGroup'.map d).exists_le_sylow
    have he : S = U := Subsingleton.elim _ _
    exact he ▸ hS (mem_map_of_mem d x.property)
  let dP : P →* U := (d.comp (P : Subgroup R).subtype).codRestrict U hdet
  let sU : U →* P := (s.comp (U : Subgroup C).subtype).codRestrict P
    (fun x => hP (mem_map_of_mem s x.property))
  have hsU : dP.comp sU = MonoidHom.id U := by
    ext x
    exact DFunLike.congr_fun hs x.val
  have hdP : Function.Surjective dP := by
    intro x
    exact ⟨sU x,DFunLike.congr_fun hsU x⟩
  have hd : Function.Surjective d := by
    intro x
    exact ⟨s x,DFunLike.congr_fun hs x⟩
  let f := map dP d (P : Subgroup R).subtype (U : Subgroup C).subtype rfl
  have hf : Function.Injective f := map_injective _ _ _ _ _ Subtype.val_injective
  have hcard := card_mul d hd
  have hsmall := card_mul dP hdP
  have hrange : Nat.card f.range = Nat.card (W dP) :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
  have hidx : Odd f.range.index := by
    have he := f.range.card_mul_index
    rw [hrange] at he
    have heq : f.range.index * (U : Subgroup C).index = (P : Subgroup R).index ^ 2 := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (Nat.card_pos (α := W dP)) (Nat.card_pos (α := U)))
      calc
        Nat.card (W dP) * Nat.card U * (f.range.index * (U : Subgroup C).index) =
          (Nat.card (W dP) * f.range.index) * (Nat.card U * (U : Subgroup C).index) := by ring
        _ = Nat.card (W d) * Nat.card C := by rw [he,(U : Subgroup C).card_mul_index]
        _ = 2 * Nat.card R ^ 2 := hcard
        _ = (2 * Nat.card P ^ 2) * (P : Subgroup R).index ^ 2 := by
          rw [←(P : Subgroup R).card_mul_index]; ring
        _ = _ := by rw [←hsmall]
    have ho : Odd ((P : Subgroup R).index ^ 2) :=
      (show Odd (P : Subgroup R).index from by
        rw [←Nat.not_even_iff_odd,even_iff_two_dvd]; exact P.not_dvd_index).pow
    rw [←heq] at ho
    exact (Nat.odd_mul.mp ho).1
  have hp : IsPGroup 2 f.range := (isPGroup dP P.isPGroup').of_surjective
    f.rangeRestrict f.rangeRestrict_surjective
  let S := hp.toSylow hidx.not_two_dvd_nat
  rw [Theory.GroupTheory.SylowFrattiniBounds.card_congr (Q.equiv S)]
  change Nat.card (f.range ⧸ frattini f.range) ≤ _
  rw [←Theory.GroupTheory.SylowFrattiniBounds.card_congr (MonoidHom.ofInjective hf)]
  exact (card_frattini_le dP sU hsU P.isPGroup').trans (Nat.mul_le_mul_left 2 (hb P))

end BalancedWreath
