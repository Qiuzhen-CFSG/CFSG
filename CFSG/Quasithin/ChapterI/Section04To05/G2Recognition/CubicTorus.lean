module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CubicLocal
public import Theory.SpecificGroups.SL2.ThreeCubicInverter
public import Theory.GroupTheory.CubicNormalizerInverter

/-!
# The common torus and the two cubic line normalizers

The involution complement to H₁H₂ acts outerly on both SL₂(3) factors.
The matrix calculation supplies a cubic element inverted in each factor.
Together with the original shared central involution, this complement
generates an actual Klein four torus. The normalizer of either chosen
cubic line in H is the opposite factor times the line and this torus.
All elements and subgroup embeddings belong to the original configuration.

These are the q=3 torus and local normalizer in Fong–Wong, Nagoya Math.
J.36 (1969), §3, equations (3.1)–(3.2) and §3B(ii), pp.155–156.
`CubicNormalizer` passes to ambient normalizers, and
`Chapter14CubicNormalizer` supplies the actual dimension-four consumer.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)
attribute [local instance] G2ThreeConfiguration.H₁_normal G2ThreeConfiguration.H₂_normal
private theorem left_factor_action_outer (n : c.H) (hout : n ∉ c.H₁ ⊔ c.H₂)
    (y : c.H₁) : (MulAut.conjNormal n : MulAut c.H₁) ≠ MulAut.conj y := by
  intro he
  have hcent : (y:c.H)⁻¹*n ∈ centralizer (c.H₁ : Set c.H) := by
    intro t ht
    have hh := congrArg (fun f : MulAut c.H₁ => (f ⟨t,ht⟩ : c.H)) he
    change n*t*n⁻¹=(y:c.H)*t*(y:c.H)⁻¹ at hh
    have he' : ((y:c.H)⁻¹*n)*t*((y:c.H)⁻¹*n)⁻¹=t := by
      calc
        _ = (y:c.H)⁻¹*(n*t*n⁻¹)*(y:c.H) := by group
        _ = t := by rw [hh]; group
    exact (mul_inv_eq_iff_eq_mul.mp he').symm
  rw [left_factor_centralizer c] at hcent
  apply hout
  simpa only [mul_inv_cancel_left] using
    (c.H₁ ⊔ c.H₂).mul_mem (mem_sup_left y.property) (mem_sup_right hcent)

theorem outside_involution_inverts_left_cubic (n : c.H) (hn : orderOf n = 2)
    (hout : n ∉ c.H₁ ⊔ c.H₂) :
    ∃ x : c.H₁, orderOf x = 3 ∧ n*(x:c.H)*n⁻¹=(x:c.H)⁻¹ := by
  let a : MulAut c.H₁ := MulAut.conjNormal n
  have ha : Function.Involutive a := by
    intro t
    apply Subtype.ext
    change n*(n*(t:c.H)*n⁻¹)*n⁻¹=(t:c.H)
    have hn2 : n*n=1 := by simpa only [pow_two,hn] using pow_orderOf_eq_one n
    calc
      _ = (n*n)*(t:c.H)*(n*n)⁻¹ := by group
      _ = t := by rw [hn2,one_mul,inv_one,mul_one]
  obtain ⟨x,hx,he⟩ := Matrix.SpecialLinearGroup.involutive_outer_inverts_cubic_of_equiv
    c.H₁_model.some a ha (left_factor_action_outer c n hout)
  exact ⟨x,hx,congrArg Subtype.val he⟩

theorem exists_common_cubic_inverter :
    ∃ (n : c.H) (x : c.H₁) (y : c.H₂), orderOf n=2 ∧ n∉c.H₁⊔c.H₂ ∧
      orderOf x=3 ∧ orderOf y=3 ∧
      n*(x:c.H)*n⁻¹=(x:c.H)⁻¹ ∧ n*(y:c.H)*n⁻¹=(y:c.H)⁻¹ := by
  obtain ⟨_,n,_,_,hn,hout,_,_⟩ := exists_fused_involution_complement c
  obtain ⟨x,hx,hix⟩ := outside_involution_inverts_left_cubic c n hn hout
  obtain ⟨y,hy,hiy⟩ := outside_involution_inverts_left_cubic (swapFactors c) n hn
    (by change n ∉ c.H₂ ⊔ c.H₁; rwa [sup_comm])
  exact ⟨n,x,y,hn,hout,hx,hy,hix,hiy⟩

theorem left_cubic_local_normalizer (x : c.H₁) (hx : orderOf x=3)
    (n : c.H) (hinv : n*(x:c.H)*n⁻¹=(x:c.H)⁻¹) :
    normalizer (zpowers (x:c.H) : Set c.H) = c.H₂ ⊔ zpowers (x:c.H) ⊔ zpowers n := by
  rw [cubic_normalizer_eq_centralizer_sup_inverter (x:c.H) n ((orderOf_coe x).trans hx) hinv,
    left_cubic_local_centralizer c x hx]

/-- The actual cubic lines and the common torus marking in the two factors. -/
structure CubicTorus where
  z : c.H
  n : c.H
  x : c.H₁
  y : c.H₂
  z_order : orderOf z = 2
  n_order : orderOf n = 2
  x_order : orderOf x = 3
  y_order : orderOf y = 3
  central_line : zpowers z = c.H₁ ⊓ c.H₂
  centralizer : c.H = centralizer ({(z:G)} : Set G)
  outside : n ∉ c.H₁ ⊔ c.H₂
  invert_left : n*(x:c.H)*n⁻¹=(x:c.H)⁻¹
  invert_right : n*(y:c.H)*n⁻¹=(y:c.H)⁻¹

theorem exists_cubic_torus : Nonempty (CubicTorus c) := by
  obtain ⟨z,hz,hline,hH⟩ := exists_marked_involution c
  obtain ⟨n,x,y,hn,hout,hx,hy,hix,hiy⟩ := exists_common_cubic_inverter c
  exact ⟨⟨z,n,x,y,hz,hn,hx,hy,hline,hH,hout,hix,hiy⟩⟩

namespace CubicTorus
variable {c} (t : CubicTorus c)
def torus : Subgroup c.H := zpowers t.z ⊔ zpowers t.n

omit [Finite G] in
theorem torus_kleinFour : IsKleinFour t.torus := by
  have hzn : t.z ≠ t.n := by
    intro he
    apply t.outside
    rw [←he]
    exact mem_sup_left ((t.central_line ▸ mem_zpowers t.z).1)
  have hc : Commute t.z t.n := by
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp (t.centralizer ▸ t.n.property)).symm
  have hh := isKleinFour_closure_pair_of_orderOf t.z t.n t.z_order t.n_order hzn hc
  have he : t.torus = closure ({t.z,t.n} : Set c.H) := by
    simp only [torus,zpowers_eq_closure,←Subgroup.closure_union,Set.singleton_union]
  exact he ▸ hh

theorem left_local_normalizer :
    normalizer (zpowers (t.x:c.H) : Set c.H) = c.H₂ ⊔ zpowers (t.x:c.H) ⊔ t.torus := by
  rw [left_cubic_local_normalizer c t.x t.x_order t.n t.invert_left,torus,←sup_assoc,
    sup_eq_left.mpr ((t.central_line.le.trans inf_le_right).trans le_sup_left)]

theorem right_local_normalizer :
    normalizer (zpowers (t.y:c.H) : Set c.H) = c.H₁ ⊔ zpowers (t.y:c.H) ⊔ t.torus := by
  have hh := left_cubic_local_normalizer (swapFactors c) t.y t.y_order t.n t.invert_right
  change normalizer (zpowers (t.y:c.H) : Set c.H) = c.H₁ ⊔ zpowers (t.y:c.H) ⊔ zpowers t.n at hh
  rw [hh,torus,←sup_assoc,
    sup_eq_left.mpr ((t.central_line.le.trans inf_le_left).trans le_sup_left)]
end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
