module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CoreCentralizer
public import Theory.GroupTheory.QuaternionCentralProductNineOrbit
public import Theory.GroupTheory.QuaternionCentralProductInvolutionCensus
public import Theory.GroupTheory.CharacteristicCentralizerSylow

/-!
# The involution orbit and its two centralizers

Self-centralization and |H| = 576 supply independent cubic actors on the
marked quaternion factors. They fuse all eighteen noncentral involutions
of Q₁Q₂ inside H, so their H-centralizers have order 32. The established
fusion through the elementary eight puts every such involution in the
ambient class of the marked involution; its full centralizer has order 576.

These different centralizer orders feed the normalizer argument in
SplitExtension. Chapter14Extension applies the results to the original
source configuration. Source: Fong–Wong §2C and §2F, Nagoya Math. J.36
(1969), pp.151–154; Aschbacher–Smith I.4.5, printed p.417.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

theorem core_noncentral_involutions_conjugate (x y : quaternionCore c)
    (hx : orderOf x = 2) (hxZ : x ∉ center (quaternionCore c))
    (hy : orderOf y = 2) (hyZ : y ∉ center (quaternionCore c)) :
    IsConj (x : c.H) (y : c.H) := by
  let d := quaternionCoreData c
  obtain ⟨a⟩ := independent_cubics_of_normal_quaternion_product_card_576
    (quaternionCore c) d (core_self_centralizing c) (H_card c)
  exact isConj_noncentral_involutions_of_order_nine (quaternionCore c)
    (core_self_centralizing c) d.left d.right d.left_model d.right_model
    d.span d.intersection_card d.commute a.A a.card x y hx hxZ hy hyZ

theorem core_involution_local_centralizer_card (x : quaternionCore c)
    (hx : orderOf x = 2) (hxZ : x ∉ center (quaternionCore c)) :
    Nat.card (centralizer ({(x : c.H)} : Set c.H)) = 32 := by
  have hh := (quaternionCoreData c).card_centralizer_mul_eighteen_of_transitive
    (quaternionCore c) (core_noncentral_involutions_conjugate c) x hx hxZ
  rw [H_card c] at hh
  omega

theorem core_noncentral_involution_fusion (x : quaternionCore c)
    (hx : orderOf x = 2) (hxZ : x ∉ center (quaternionCore c)) :
    ∃ z : G, orderOf z = 2 ∧ c.H = centralizer ({z} : Set G) ∧
      IsConj z ((x : c.H) : G) := by
  obtain ⟨z,t,hz,hH,ht,htZ,hf⟩ := exists_distinguished_fusion_in_quaternionCore c
  exact ⟨z,hz,hH,hf.trans (c.H.subtype.map_isConj
    (core_noncentral_involutions_conjugate c t x ht htZ hx hxZ))⟩

theorem core_involution_ambient_centralizer_card (x : quaternionCore c)
    (hx : orderOf x = 2) (hxZ : x ∉ center (quaternionCore c)) :
    Nat.card (centralizer ({((x : c.H) : G)} : Set G)) = 576 := by
  obtain ⟨z,_,hH,hf⟩ := core_noncentral_involution_fusion c x hx hxZ
  rw [← card_centralizer_eq_of_isConj z _ hf,← hH,H_card c]

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
