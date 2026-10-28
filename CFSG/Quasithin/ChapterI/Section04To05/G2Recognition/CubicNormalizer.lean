module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CubicCentralizer
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CubicTorus
public import Theory.GroupTheory.QuaternionSylowOddNormalizer

/-!
# The literal ambient cubic normalizers

For every cubic x in H₁, the characteristic odd-core-by-involution
subgroup of C_G(x) and Frattini's argument give
N_G(⟨x⟩)=O(C_G(x))(H∩N_G(⟨x⟩)). The chosen common torus makes the
second factor explicit: the normalizer is the odd core times the opposite
SL₂(3) factor times that torus. Both original factor embeddings and the
symmetric formula are retained. Local normalizers have order144 and
ambient normalizers have order48 times the odd-core order.

This completes the normalizer assertion of Fong–Wong, Nagoya Math. J.36
(1969), §3B(ii), printed p.156, in the genuine I.4.5 configuration.
The prime-three multiplicity and G₂(3) recognition remain unproved here.
`Chapter14CubicNormalizer` applies this family to SourceLocalData.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
def cubicNormalizer (x : c.H₁) : Subgroup G := normalizer (zpowers ((x:c.H):G) : Set G)
theorem cubic_normalizer_split (x : c.H₁) (hx : orderOf x = 3) :
    cubicNormalizer c x = cubicOddCore c x ⊔ (c.H ⊓ cubicNormalizer c x) := by
  let C := cubicCentralizer c x
  let D := cubicOddCore c x
  let N := cubicNormalizer c x
  let NC := normalizer (C : Set G)
  have hCN : C ≤ N := by
    change centralizer ({((x:c.H):G)} : Set G) ≤ normalizer (zpowers ((x:c.H):G) : Set G)
    rw [←centralizer_closure,←zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hDC : D ≤ C := map_subtype_le _
  have hNN : N ≤ NC := by
    have hh := normalizer_le_normalizer_centralizer (zpowers ((x:c.H):G))
    have he : centralizer (zpowers ((x:c.H):G) : Set G) = C := by
      rw [zpowers_eq_closure,centralizer_closure]; rfl
    rw [he] at hh
    exact hh
  obtain ⟨z,hz,_,hH⟩ := exists_marked_involution c
  have hzC : (z:G) ∈ C := mem_centralizer_singleton_iff.mpr
    (mem_centralizer_singleton_iff.mp (hH ▸ x.val.property)).symm
  let zz : C := ⟨z,hzC⟩
  have hz2 : orderOf zz = 2 := (orderOf_coe zz).symm.trans ((orderOf_coe z).trans hz)
  obtain ⟨P,_,hP⟩ := cubic_quaternion_sylow c x hx
  have he := normalizer_eq_oddCore_sup_inf_centralizer_of_quaternion_sylow C P hP zz hz2
  change NC = D ⊔ (NC ⊓ centralizer ({(z:G)} : Set G)) at he
  rw [←hH] at he
  have hnorm : NC ⊓ c.H ≤ normalizer (D : Set G) :=
    inf_le_left.trans (normalizer_le_normalizer_characteristic_image C (pPrimeCore 2 C))
  apply le_antisymm ?_ (sup_le (hDC.trans hCN) inf_le_right)
  intro g hg
  have hh : g ∈ D ⊔ (NC ⊓ c.H) := he ▸ hNN hg
  change g ∈ (↑(D ⊔ (NC ⊓ c.H)) : Set G) at hh
  rw [coe_mul_of_right_le_normalizer_left _ _ hnorm] at hh
  obtain ⟨d,hd,h,hh,heq⟩ := hh
  have hhN : h ∈ N := by
    have hmem := N.mul_mem (N.inv_mem ((hDC.trans hCN) hd)) hg
    simpa only [←heq,inv_mul_cancel_left] using hmem
  exact heq ▸ (D ⊔ (c.H ⊓ N)).mul_mem (mem_sup_left hd) (mem_sup_right ⟨hh.2,hhN⟩)

theorem cubic_normalizer_of_local_inverter (x : c.H₁) (hx : orderOf x=3)
    (n : c.H) (hinv : n*(x:c.H)*n⁻¹=(x:c.H)⁻¹) :
    cubicNormalizer c x = cubicOddCore c x ⊔ c.H₂.map c.H.subtype ⊔ zpowers (n:G) := by
  have hm := map_subtype_normalizer_zpowers c.H (x:c.H)
  change (normalizer (zpowers (x:c.H) : Set c.H)).map c.H.subtype =
    c.H ⊓ cubicNormalizer c x at hm
  rw [cubic_normalizer_split c x hx,←hm,left_cubic_local_normalizer c x hx n hinv,
    Subgroup.map_sup,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers,
    ←sup_assoc,←sup_assoc]
  exact congrArg (fun U : Subgroup G => U ⊔ zpowers (n:G))
    (sup_eq_left.mpr ((cubic_line_le_oddCore c x hx).trans
      (show cubicOddCore c x ≤ cubicOddCore c x ⊔ c.H₂.map c.H.subtype from le_sup_left)))

theorem cubic_centralizer_card (x : c.H₁) (hx : orderOf x=3) :
    Nat.card (cubicCentralizer c x) = Nat.card (cubicOddCore c x) * 24 := by
  have hn : c.H₂.map c.H.subtype ≤ normalizer (cubicOddCore c x : Set G) :=
    (opposite_factor_le_cubic_centralizer c x).trans
      ((cubicCentralizer c x).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 (cubicCentralizer c x))))
  have hcard : Nat.card c.H₂ = 24 := (Nat.card_congr c.H₂_model.some.toEquiv).trans
    GLS3.Chapter5.SchurPresentation.sl23_card_eq
  rw [cubic_centralizer_split c x hx,
    card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn (disjoint_iff.mpr (cubic_oddCore_inf_factor c x)),
    card_map_of_injective c.H.subtype_injective,hcard]

theorem cubic_normalizer_card_of_local_inverter (x : c.H₁) (hx : orderOf x=3)
    (n : c.H) (hn : orderOf n=2) (hinv : n*(x:c.H)*n⁻¹=(x:c.H)⁻¹) :
    Nat.card (cubicNormalizer c x) = Nat.card (cubicOddCore c x) * 48 := by
  have hxG : orderOf ((x:c.H):G)=3 := (orderOf_coe (x:c.H)).trans ((orderOf_coe x).trans hx)
  have hnG : orderOf (n:G)=2 := (orderOf_coe n).trans hn
  have hh := cubic_normalizer_card_of_involutive_inverter ((x:c.H):G) (n:G) hxG hnG
    (congrArg Subtype.val hinv)
  change Nat.card (cubicNormalizer c x) = Nat.card (cubicCentralizer c x) * 2 at hh
  rw [hh,cubic_centralizer_card c x hx,mul_assoc]
  rfl

namespace CubicTorus
variable {c} (t : CubicTorus c)

theorem left_ambient_normalizer :
    cubicNormalizer c t.x = cubicOddCore c t.x ⊔ c.H₂.map c.H.subtype ⊔
      t.torus.map c.H.subtype := by
  have hZ : zpowers (t.z:G) ≤ c.H₂.map c.H.subtype := zpowers_le.mpr
    (mem_map_of_mem c.H.subtype (t.central_line ▸ mem_zpowers t.z).2)
  rw [cubic_normalizer_of_local_inverter c t.x t.x_order t.n t.invert_left,
    torus,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers,←sup_assoc]
  exact congrArg (fun U : Subgroup G => U ⊔ zpowers (t.n:G))
    (sup_eq_left.mpr (hZ.trans
      (show c.H₂.map c.H.subtype ≤ cubicOddCore c t.x ⊔ c.H₂.map c.H.subtype from le_sup_right))).symm

theorem right_ambient_normalizer :
    cubicNormalizer (swapFactors c) t.y = cubicOddCore (swapFactors c) t.y ⊔
      c.H₁.map c.H.subtype ⊔ t.torus.map c.H.subtype := by
  have hZ : zpowers (t.z:G) ≤ c.H₁.map c.H.subtype := zpowers_le.mpr
    (mem_map_of_mem c.H.subtype (t.central_line ▸ mem_zpowers t.z).1)
  have hh := cubic_normalizer_of_local_inverter (swapFactors c) t.y t.y_order t.n t.invert_right
  change cubicNormalizer (swapFactors c) t.y = cubicOddCore (swapFactors c) t.y ⊔
    c.H₁.map c.H.subtype ⊔ zpowers (t.n:G) at hh
  rw [hh,torus,Subgroup.map_sup,MonoidHom.map_zpowers,MonoidHom.map_zpowers,←sup_assoc]
  exact congrArg (fun U : Subgroup G => U ⊔ zpowers (t.n:G))
    (sup_eq_left.mpr (hZ.trans
      (show c.H₁.map c.H.subtype ≤ cubicOddCore (swapFactors c) t.y ⊔ c.H₁.map c.H.subtype from le_sup_right))).symm
theorem left_local_normalizer_card :
    Nat.card (normalizer (zpowers (t.x:c.H) : Set c.H)) = 144 := by
  rw [cubic_normalizer_card_of_involutive_inverter (t.x:c.H) t.n
    ((orderOf_coe t.x).trans t.x_order) t.n_order t.invert_left,
    left_cubic_local_centralizer_card c t.x t.x_order]

theorem right_local_normalizer_card :
    Nat.card (normalizer (zpowers (t.y:c.H) : Set c.H)) = 144 := by
  rw [cubic_normalizer_card_of_involutive_inverter (t.y:c.H) t.n
    ((orderOf_coe t.y).trans t.y_order) t.n_order t.invert_right]
  have hh := left_cubic_local_centralizer_card (swapFactors c) t.y t.y_order
  change Nat.card (Subgroup.centralizer ({(t.y:c.H)} : Set c.H)) = 72 at hh
  exact congrArg (fun n : ℕ => n*2) hh

theorem left_ambient_normalizer_card :
    Nat.card (cubicNormalizer c t.x) = Nat.card (cubicOddCore c t.x) * 48 :=
  cubic_normalizer_card_of_local_inverter c t.x t.x_order t.n t.n_order t.invert_left

theorem right_ambient_normalizer_card :
    Nat.card (cubicNormalizer (swapFactors c) t.y) = Nat.card (cubicOddCore (swapFactors c) t.y) * 48 :=
  cubic_normalizer_card_of_local_inverter (swapFactors c) t.y t.y_order t.n t.n_order t.invert_right
end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
