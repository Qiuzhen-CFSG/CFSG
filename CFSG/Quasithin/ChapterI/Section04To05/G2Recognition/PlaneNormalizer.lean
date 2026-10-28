module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MarkedCubic

/-!
# Normalizers and fusion of the marked cubic plane

The original SL₂(3) factors supply two nonconjugate cubic lines A and B.
The actual M supplies a conjugate cubic line D in E = A ∨ B whose ambient
class differs from both. Since E has just four cubic lines, an element
normalizing E cannot move both A and B: their two images, A, B and D
would be five distinct lines. The subgroup-union argument then shows
that the whole normalizer fixes at least one of A and B.

If both cubic odd cores have order three, the established factor-line
normalizers lie in H, so N_G(E) lies in H. Conversely this containment
forces E to be Sylow by the normalizer-index congruence. Burnside fusion
then gives an actual conjugator in H for every ambient fusion between
elements of E.

This uses the literal markings in Aschbacher–Smith I.4(G1)–(G2), printed
p.417, including the elementary eight and PSL₃(2) quotient in M. It is a
reduction of the exceptional q=3 branch, not its exclusion: Fong–Wong
§4D (Nagoya Math. J.36 (1969), pp.164–166) excludes q₁=q₂=3, and Fong
§6 (Nagoya Math. J.39 (1970), pp.74–76) appeals to Janko for that case.
The Sylow-nine and order-27-core exclusions, BN-pair construction and
Atlas comparison remain with `qt-i45-g2-recognition`. The companion
`Chapter14PlaneNormalizer` applies this family to SourceLocalData.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

private theorem four_point_fixed {X : Type*} [Finite X] (hc : Nat.card X = 4)
    (a b d a' b' : X) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (ha'b : a' ≠ b) (hb'a : b' ≠ a) (ha'd : a' ≠ d) (hb'd : b' ≠ d)
    (ha'b' : a' ≠ b') : a' = a ∨ b' = b := by
  classical
  let : Fintype X := Fintype.ofFinite X
  by_contra! h
  have hh := Finset.card_le_univ ({a,b,d,a',b'} : Finset X)
  have hfive : ({a,b,d,a',b'} : Finset X).card = 5 := by
    simp [hab, had, hbd, ha'b',
      Ne.symm ha'b, Ne.symm hb'a, Ne.symm ha'd, Ne.symm hb'd,
      Ne.symm h.1, Ne.symm h.2]
  rw [hfive, ← Nat.card_eq_fintype_card, hc] at hh
  omega

private theorem factor_line_avoids_M_conjugate (x : c.H₁) (hx : orderOf x = 3)
    (m : c.M) (u g : G) :
    (zpowers ((x:c.H):G)).map (MulAut.conj g).toMonoidHom ≠
      (zpowers (m:G)).map (MulAut.conj u).toMonoidHom := by
  intro he
  apply cubic_factor_line_not_conjugate_M c x hx m (u⁻¹*g)
  have hh := congrArg (map (MulAut.conj u⁻¹).toMonoidHom) he
  rw [map_map, map_map] at hh
  have hleft : (MulAut.conj u⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (u⁻¹*g)).toMonoidHom := by
    ext v
    simp [MulAut.conj_apply, mul_assoc]
  have hright : (MulAut.conj u⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
      MonoidHom.id G := by
    ext v
    simp [MulAut.conj_apply, mul_assoc]
  rwa [hleft, hright, map_id] at hh

private theorem cubic_plane_normalizer_le_union (x : c.H₁) (y : c.H₂)
    (hx : orderOf x=3) (hy : orderOf y=3) :
    (normalizer ((zpowers ((x:c.H):G) ⊔ zpowers ((y:c.H):G) : Subgroup G) : Set G) : Set G) ⊆
      (cubicNormalizer c x : Set G) ∪ (cubicNormalizer (swapFactors c) y : Set G) := by
  classical
  let A := zpowers ((x:c.H):G)
  let B := zpowers ((y:c.H):G)
  let E := A ⊔ B
  obtain ⟨hE, hEc⟩ := cubic_plane_data c x y hx hy
  let : IsElementaryAbelian 3 E := hE
  obtain ⟨m,u,hm,hu,_,_⟩ := exists_marked_M_diagonal c x y hx hy
  let D := (zpowers (m:G)).map (MulAut.conj u).toMonoidHom
  have hDE : D ≤ E := by
    dsimp [D]
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr hu
  have hAc : Nat.card A=3 := by rw [Nat.card_zpowers,orderOf_coe,orderOf_coe,hx]
  have hBc : Nat.card B=3 := by rw [Nat.card_zpowers,orderOf_coe,orderOf_coe,hy]
  have hDc : Nat.card D=3 := by
    rw [card_map_of_injective (MulAut.conj u).injective,Nat.card_zpowers,orderOf_coe,hm]
  let X := {L : Subgroup E // Nat.card L=3}
  have hX : Nat.card X=4 := IsElementaryAbelian.TernarySylowLine.card_cubic_subgroups hEc
  let a : X := ⟨A.subgroupOf E,(Nat.card_congr
    (subgroupOfEquivOfLe (show A ≤ E from le_sup_left)).toEquiv).trans hAc⟩
  let b : X := ⟨B.subgroupOf E,(Nat.card_congr
    (subgroupOfEquivOfLe (show B ≤ E from le_sup_right)).toEquiv).trans hBc⟩
  let d : X := ⟨D.subgroupOf E,(Nat.card_congr (subgroupOfEquivOfLe hDE).toEquiv).trans hDc⟩
  have ha : a.val.map E.subtype=A := map_subgroupOf_eq_of_le le_sup_left
  have hb : b.val.map E.subtype=B := map_subgroupOf_eq_of_le le_sup_right
  have hd : d.val.map E.subtype=D := map_subgroupOf_eq_of_le hDE
  have hid : (MulAut.conj (1:G)).toMonoidHom = MonoidHom.id G := by
    ext v
    simp
  have hab : A ≠ B := by
    simpa only [hid, map_id] using
      cubic_lines_not_conjugate c x y hx 1
  have had : A ≠ D := by
    simpa only [hid, map_id] using
      factor_line_avoids_M_conjugate c x hx m u 1
  have hbd : B ≠ D := by
    simpa only [hid, map_id] using
      factor_line_avoids_M_conjugate (swapFactors c) y hy m u 1
  intro g hg
  let f := E.normalizerMonoidHom ⟨g,hg⟩
  let aa : X := ⟨a.val.map f.toMonoidHom,(card_map_of_injective f.injective).trans a.property⟩
  let bb : X := ⟨b.val.map f.toMonoidHom,(card_map_of_injective f.injective).trans b.property⟩
  have hcompat (L : Subgroup E) :
      (L.map f.toMonoidHom).map E.subtype =
        (L.map E.subtype).map (MulAut.conj g).toMonoidHom := by
    rw [map_map,map_map]
    rfl
  have haa : aa.val.map E.subtype=A.map (MulAut.conj g).toMonoidHom := (hcompat a.val).trans (congrArg _ ha)
  have hbb : bb.val.map E.subtype=B.map (MulAut.conj g).toMonoidHom := (hcompat b.val).trans (congrArg _ hb)
  have lift {v w : X} (he : v=w) : v.val.map E.subtype=w.val.map E.subtype :=
    congrArg (fun L : X => L.val.map E.subtype) he
  have hfix : aa=a ∨ bb=b := by
    apply four_point_fixed hX a b d aa bb
    · intro he; exact hab (ha.symm.trans ((lift he).trans hb))
    · intro he; exact had (ha.symm.trans ((lift he).trans hd))
    · intro he; exact hbd (hb.symm.trans ((lift he).trans hd))
    · intro he
      exact cubic_lines_not_conjugate c x y hx g (haa.symm.trans ((lift he).trans hb))
    · intro he
      exact cubic_lines_not_conjugate (swapFactors c) y x hy g (hbb.symm.trans ((lift he).trans ha))
    · intro he
      exact factor_line_avoids_M_conjugate c x hx m u g (haa.symm.trans ((lift he).trans hd))
    · intro he
      exact factor_line_avoids_M_conjugate (swapFactors c) y hy m u g (hbb.symm.trans ((lift he).trans hd))
    · intro he
      exact hab ((map_injective (MulAut.conj g).injective)
        (haa.symm.trans ((lift he).trans hbb)))
  rcases hfix with he|he
  · exact Or.inl (mem_normalizer_iff_map_conj_eq.mpr (haa.symm.trans ((lift he).trans ha)))
  · exact Or.inr (mem_normalizer_iff_map_conj_eq.mpr (hbb.symm.trans ((lift he).trans hb)))

/-- The full normalizer of the actual plane fixes one of its original factor lines. -/
theorem cubic_plane_normalizer_fixes_factor (x : c.H₁) (y : c.H₂)
    (hx : orderOf x=3) (hy : orderOf y=3) :
    normalizer ((zpowers ((x:c.H):G) ⊔ zpowers ((y:c.H):G) : Subgroup G) : Set G) ≤
        cubicNormalizer c x ∨
      normalizer ((zpowers ((x:c.H):G) ⊔ zpowers ((y:c.H):G) : Subgroup G) : Set G) ≤
        cubicNormalizer (swapFactors c) y :=
  SubgroupClass.subset_union.mp (cubic_plane_normalizer_le_union c x y hx hy)

/-- Two smallest cubic cores force the entire plane normalizer into the original H. -/
theorem cubic_plane_normalizer_le_H_of_small_cores (x : c.H₁) (y : c.H₂)
    (hx : orderOf x=3) (hy : orderOf y=3)
    (hDx : Nat.card (cubicOddCore c x)=3)
    (hDy : Nat.card (cubicOddCore (swapFactors c) y)=3) :
    normalizer ((zpowers ((x:c.H):G) ⊔ zpowers ((y:c.H):G) : Subgroup G) : Set G) ≤ c.H := by
  rcases cubic_plane_normalizer_fixes_factor c x y hx hy with h|h
  · exact h.trans ((cubic_normalizer_le_H_iff c x hx).mpr hDx)
  · exact h.trans ((cubic_normalizer_le_H_iff (swapFactors c) y hy).mpr hDy)

namespace CubicTorus
variable {c} (t : CubicTorus c)

/-- Containment of the literal plane normalizer detects the two smallest cores. -/
theorem plane_normalizer_le_H_iff_small_cores :
    normalizer ((zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G) : Set G) ≤ c.H ↔
      Nat.card (cubicOddCore c t.x)=3 ∧
        Nat.card (cubicOddCore (swapFactors c) t.y)=3 := by
  constructor
  · intro hn
    apply t.small_cores_iff_not_cube_dvd.mpr
    intro hd
    have hc := (cubic_plane_data c t.x t.y t.x_order t.y_order).2
    have hmod := Sylow.card_normalizer_modEq_card (p := 3) (n := 2) hc
    have hdiv := (hmod.dvd_iff dvd_rfl).mpr hd
    have hh := hdiv.trans (card_dvd_of_le hn)
    rw [H_card c] at hh
    norm_num at hh
  · rintro ⟨hx,hy⟩
    exact cubic_plane_normalizer_le_H_of_small_cores c t.x t.y t.x_order t.y_order hx hy

/-- The plane is ambient Sylow exactly when its normalizer lies in H. -/
theorem plane_sylow_iff_normalizer_le_H :
    (∃ P : Sylow 3 G, (P : Subgroup G) =
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)) ↔
    normalizer ((zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G) : Set G) ≤ c.H :=
  t.cubic_plane_sylow_iff.trans t.plane_normalizer_le_H_iff_small_cores.symm

/-- In the Sylow-nine branch, every ambient element fusion in the plane is induced in H. -/
theorem plane_fusion_in_H_of_sylow
    (hSylow : ∃ P : Sylow 3 G, (P : Subgroup G) =
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (a b : G)
    (ha : a ∈ zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (hb : b ∈ zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G))
    (hab : IsConj a b) : ∃ h ∈ c.H, MulAut.conj h a=b := by
  have hN := t.plane_sylow_iff_normalizer_le_H.mp hSylow
  obtain ⟨P,hP⟩ := hSylow
  let : IsElementaryAbelian 3 P := hP.symm ▸
    (cubic_plane_data c t.x t.y t.x_order t.y_order).1
  obtain ⟨g,hg⟩ := isConj_iff.mp hab
  obtain ⟨n,hn,he⟩ := P.conj_eq_normalizer_conj_of_mem a g⁻¹
    (by change a ∈ (P:Subgroup G); rwa [hP])
    (by change _ ∈ (P:Subgroup G); simpa only [hP,inv_inv,hg] using hb)
  change n ∈ normalizer ((P:Subgroup G):Set G) at hn
  rw [hP] at hn
  refine ⟨n⁻¹,c.H.inv_mem (hN hn),?_⟩
  change n⁻¹*a*(n⁻¹)⁻¹=b
  rw [inv_inv]
  simpa only [inv_inv,hg] using he.symm

end CubicTorus

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
