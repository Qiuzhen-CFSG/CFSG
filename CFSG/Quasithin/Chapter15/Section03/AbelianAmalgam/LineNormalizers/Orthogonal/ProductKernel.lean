module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.Residual

/-!
# The two-group kernel on the line in `Y_E T_E`

The line residual has cubic image and its kernel on the line is its two-core.
The Sylow intersection normalizes that kernel. Write an element centralizing
`E` as `yt`, using the proved normalization and setwise-product theorem.
The actions of `y` and `t` are inverse, with orders dividing three and a power
of two; both are trivial. The element therefore lies in the product of the
residual kernel with `T_E`, which is a two-group.

This proves the kernel hypothesis needed for the genuine S₃ quotient and
`O₂(Y_E T_E)=C_{Y_E T_E}(E)`. Full action of `Y_E T_E` is a separate input;
no assertion from 15.3.67 is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.66(5), printed p.1152, PDF p.1169.
-/

@[expose] public section

open Subgroup OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
open GoldschmidtCore.LocalRelations GoldschmidtCore.LocalRelations.OrthogonalProducts
variable {G : Type*} [Group G] [Finite G] {V M : Subgroup G}

/-- The actual action kernel of the source product on its line is a two-group. -/
theorem lineProduct_kernel_isPGroup (d : NaturalAction V M) (Y T E : Subgroup G)
    (hYM : Y ≤ M) (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e, hEV e.property⟩)
    (himage : actionImage d Y = pResidual 2 IsometryGroup)
    (hYcore : Stellmacher.twoCoreAmbient Y = Y ⊓ centralizer (V : Set G))
    (hT : IsPGroup 2 T) (hTY : T ≤ normalizer (Y : Set G)) :
    IsPGroup 2 ((centralizer (E : Set G)).subgroupOf (lineY Y E ⊔ lineT T E)) := by
  let N := lineY Y E ⊓ centralizer (E : Set G)
  have hN : N = Stellmacher.twoCoreAmbient (lineY Y E) :=
    (lineY_centralizer_line_eq_module d Y E hYM hEV hcard hs himage).trans
      (lineY_twoCore d Y E hYM hEV himage hYcore).symm
  have hpN : IsPGroup 2 N := by
    rw [hN]
    exact pCore_isPGroup.map (lineY Y E).subtype
  have hNC : lineNormalizer E ≤ normalizer (centralizer (E : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer (E : Set G))).mp
      inferInstance
  have hn : lineT T E ≤ normalizer (N : Set G) :=
    (le_inf (lineT_le_normalizer_lineY Y T E hTY) (inf_le_right.trans hNC)).trans
      inf_normalizer_le_normalizer_inf
  have hp : IsPGroup 2 (N ⊔ lineT T E : Subgroup G) :=
    hpN.to_sup_of_normal_left' (hT.to_le inf_le_left) hn
  have hC : (lineY Y E ⊔ lineT T E) ⊓ centralizer (E : Set G) ≤ N ⊔ lineT T E := by
    rintro x ⟨hx,hxc⟩
    change x ∈ ((lineY Y E ⊔ lineT T E : Subgroup G) : Set G) at hx
    rw [lineY_sup_lineT_product Y T E hTY] at hx
    obtain ⟨y,hy,t,ht,rfl⟩ := hx
    let yN : lineNormalizer E := ⟨y,(lineY_le Y E).trans inf_le_right hy⟩
    let tN : lineNormalizer E := ⟨t,ht.2⟩
    let f := E.normalizerMonoidHom
    have hyt : f yN * f tN = 1 := by
      rw [← map_mul]
      change yN * tN ∈ f.ker
      rw [E.normalizerMonoidHom_ker]
      exact hxc
    have hcube : f yN ^ 3 = 1 := by
      rw [← map_pow]
      change yN ^ 3 ∈ f.ker
      rw [E.normalizerMonoidHom_ker]
      exact centralizer_le hEV
        (lineY_cube_centralizes_module d Y E hYM hEV himage y hy)
    obtain ⟨n,hn⟩ := hT ⟨t,ht.1⟩
    have htPower : tN ^ 2 ^ n = 1 := by
      apply Subtype.ext
      exact congrArg (fun u : T => (u : G)) hn
    have hyPower : f yN ^ 2 ^ n = 1 := by
      rw [eq_inv_of_mul_eq_one_left hyt, inv_pow, ← map_pow, htPower, map_one, inv_one]
    have hyfix : f yN = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 2 3).pow_left n)
        (orderOf_dvd_of_pow_eq_one hyPower) (orderOf_dvd_of_pow_eq_one hcube))
    have hyC : y ∈ centralizer (E : Set G) := by
      have hh : yN ∈ f.ker := hyfix
      rw [E.normalizerMonoidHom_ker] at hh
      exact hh
    exact mul_mem (mem_sup_left ⟨hy,hyC⟩) (mem_sup_right ht)
  have hrel : (centralizer (E : Set G)).subgroupOf (lineY Y E ⊔ lineT T E) ≤
      (N ⊔ lineT T E).subgroupOf (lineY Y E ⊔ lineT T E) :=
    fun x hx => hC ⟨x.property,hx⟩
  exact hp.comap_subtype.to_le hrel

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
