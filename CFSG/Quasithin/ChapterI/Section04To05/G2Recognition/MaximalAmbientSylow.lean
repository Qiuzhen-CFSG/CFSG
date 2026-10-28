module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalSylowNormalizer

/-!
# Ambient Sylow alignment of the original large cubic extensions

For each original order243 core D, the extension S=D⟨y⟩ has order729
and normalizer of order2916. Normalizer control therefore promotes S
to an ambient Sylow subgroup. Align the opposite extension by Sylow
conjugacy; this aligns their whole Borels as well. The two marked cubic
lines are nonconjugate, hence distinct, and span the common Sylow center.
Their cubic normalizers intersect in precisely the whole order2916 Borel.
The two original marked cores generate S and intersect in order81.

These statements retain the original ambient groups, derived lines and
conjugating map. They discharge the Sylow placement and whole-overlap
requirements in the original completion construction. Compatible Atlas
endpoint isomorphisms, both commuting squares, generation and the marked
involutions still require proofs. The literal SourceLocalData application
is Chapter14SylowAlignment. Source: Aschbacher–Smith I.4(G1)–(G2) and
I.4.5, printed p.417, continuing the cubic-normalizer calculations of
Fong–Wong §3B, Nagoya Math. J.36 (1969), p.156.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus

/-- The original extension is the full three-core of its ambient normalizer. -/
theorem maximal_extension_normalizer_threeCore (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    (normalizer (t.leftCoreExtension:Set G)).pCoreIn 3=t.leftCoreExtension := by
  rw [t.maximal_sylow_normalizer_eq hc,t.maximal_leftCubicBorel_threeCore hc]

/-- The local order729 subgroup is Sylow in the original ambient group. -/
theorem maximal_extension_sylow (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    ∃ P : Sylow 3 G, (P:Subgroup G)=t.leftCoreExtension := by
  let S := t.leftCoreExtension
  let N := normalizer (S:Set G)
  have hi : S.relIndex N=4 := by
    have hh := relIndex_mul_relIndex (⊥:Subgroup G) S N bot_le S.le_normalizer
    simp only [relIndex_bot_left] at hh
    have hN : Nat.card N=2916 := by
      change Nat.card (normalizer (t.leftCoreExtension:Set G))=2916
      rw [t.maximal_sylow_normalizer_eq hc]
      exact (t.maximal_leftCubicBorel_split hc).2.2.2
    rw [t.maximal_leftCoreExtension_card hc,hN] at hh
    omega
  have hlocal : ¬3∣S.relIndex N := by rw [hi]; decide
  have hglobal := not_dvd_relIndex_of_normalizer_inf_le S N ⊤
    (t.maximal_leftCubicBorel_split hc).1 le_top hlocal inf_le_left
  exact ⟨(t.maximal_leftCubicBorel_split hc).1.toSylow
    (by simpa only [relIndex_top_right] using hglobal),rfl⟩

/-- Both original marked extensions can be placed on the same ambient Sylow. -/
theorem maximal_extensions_conjugate (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    ∃ g : G, t.swap.leftCoreExtension.map (MulAut.conj g).toMonoidHom=t.leftCoreExtension := by
  obtain ⟨P,hP⟩ := t.maximal_extension_sylow hc
  obtain ⟨Q,hQ⟩ := t.swap.maximal_extension_sylow (t.oddCore_card_eq.symm.trans hc)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g,?_⟩
  have hh := congrArg Sylow.toSubgroup hg
  change (Q:Subgroup G).map (MulAut.conj g).toMonoidHom=(P:Subgroup G) at hh
  rwa [hP,hQ] at hh


omit [Finite G] in
private theorem line_le_center (t : CubicTorus c) :
    zpowers ((t.x:c.H):G)≤centerIn t.leftCoreExtension := by
  refine le_inf ((cubic_line_le_oddCore c t.x t.x_order).trans le_sup_left) ?_
  apply le_centralizer_iff.mp
  rw [zpowers_eq_closure,centralizer_closure]
  exact sup_le (map_subtype_le _)
    ((zpowers_le.mpr (mem_map_of_mem c.H.subtype t.y.property)).trans
      (opposite_factor_le_cubic_centralizer c t.x))

/-- Aligning the original Sylows aligns their whole Borels. -/
theorem maximal_aligned_borels (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) (g : G)
    (hg : t.swap.leftCoreExtension.map (MulAut.conj g).toMonoidHom=t.leftCoreExtension) :
    t.swap.leftCubicBorel.map (MulAut.conj g).toMonoidHom=t.leftCubicBorel := by
  rw [←t.swap.maximal_sylow_normalizer_eq (t.oddCore_card_eq.symm.trans hc),
    map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,hg,
    t.maximal_sylow_normalizer_eq hc]

/-- The two original marked derived lines span the aligned Sylow center. -/
theorem maximal_aligned_center_lines (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) (g : G)
    (hg : t.swap.leftCoreExtension.map (MulAut.conj g).toMonoidHom=t.leftCoreExtension) :
    zpowers ((t.x:c.H):G) ⊔
      (zpowers ((t.y:c.H):G)).map (MulAut.conj g).toMonoidHom=centerIn t.leftCoreExtension := by
  let X := zpowers ((t.x:c.H):G)
  let Y := (zpowers ((t.y:c.H):G)).map (MulAut.conj g).toMonoidHom
  let K := centerIn t.leftCoreExtension
  have hX : Nat.card X=3 := by rw [Nat.card_zpowers,orderOf_coe,orderOf_coe,t.x_order]
  have hY : Nat.card Y=3 := by
    rw [card_map_of_injective (MulAut.conj g).injective,
      Nat.card_zpowers,orderOf_coe,orderOf_coe,t.y_order]
  have hXK : X≤K := t.line_le_center
  have hYK : Y≤K := by
    have hh := map_mono (f:=(MulAut.conj g).toMonoidHom) t.swap.line_le_center
    rw [centerIn_map_equiv,hg] at hh
    exact hh
  have hne : X≠Y := fun he => cubic_lines_not_conjugate (swapFactors c)
    t.y t.x t.y_order g he.symm
  have hle : X⊔Y≤K := sup_le hXK hYK
  have hd : Nat.card (X⊔Y:Subgroup G)∣9 := by
    have hh := card_dvd_of_le hle
    rwa [t.maximal_extension_center_card hc] at hh
  have hmin : 3≤Nat.card (X⊔Y:Subgroup G) := hX ▸ card_le_of_le (show X≤X⊔Y from le_sup_left)
  have hbig : Nat.card (X⊔Y:Subgroup G)≠3 := by
    intro hh
    have hx : X=X⊔Y := eq_of_le_of_card_ge le_sup_left (by rw [hX,hh])
    have hy : Y=X⊔Y := eq_of_le_of_card_ge le_sup_right (by rw [hY,hh])
    exact hne (hx.trans hy.symm)
  have hcard : Nat.card (X⊔Y:Subgroup G)=9 := by
    obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_three (m:=2)).mp hd
    interval_cases k <;> norm_num only [Nat.reducePow] at he
    · omega
    · exact (hbig he).elim
    · exact he
  exact eq_of_le_of_card_ge hle (by rw [t.maximal_extension_center_card hc,hcard])

/-- The conjugated original endpoint pair has exactly the required whole Borel overlap. -/
theorem maximal_aligned_endpoint_overlap (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) (g : G)
    (hg : t.swap.leftCoreExtension.map (MulAut.conj g).toMonoidHom=t.leftCoreExtension) :
    cubicNormalizer c t.x ⊓
      (cubicNormalizer (swapFactors c) t.y).map (MulAut.conj g).toMonoidHom=t.leftCubicBorel := by
  have hright : (cubicNormalizer (swapFactors c) t.y).map (MulAut.conj g).toMonoidHom=
      normalizer ((zpowers ((t.y:c.H):G)).map (MulAut.conj g).toMonoidHom:Set G) :=
    map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective
  apply le_antisymm
  · rw [hright]
    change normalizer (zpowers ((t.x:c.H):G):Set G)⊓_≤_
    have hh := normalizer_inf_normalizer_le_normalizer_sup
      (zpowers ((t.x:c.H):G)) ((zpowers ((t.y:c.H):G)).map (MulAut.conj g).toMonoidHom)
    rw [t.maximal_aligned_center_lines hc g hg,
      ←t.maximal_extension_normalizer hc,t.maximal_sylow_normalizer_eq hc] at hh
    exact hh
  · refine le_inf t.leftCubicBorel_le ?_
    rw [←t.maximal_aligned_borels hc g hg]
    exact map_mono t.swap.leftCubicBorel_le

/-- The two aligned original cores generate the common Sylow and meet in order81. -/
theorem maximal_aligned_core_pair (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) (g : G)
    (hg : t.swap.leftCoreExtension.map (MulAut.conj g).toMonoidHom=t.leftCoreExtension) :
    let R := (cubicOddCore (swapFactors c) t.y).map (MulAut.conj g).toMonoidHom
    cubicOddCore c t.x ⊔ R=t.leftCoreExtension ∧
      Nat.card (cubicOddCore c t.x⊓R:Subgroup G)=81 ∧
      ⁅R,R⁆=(zpowers ((t.y:c.H):G)).map (MulAut.conj g).toMonoidHom := by
  let D := cubicOddCore c t.x
  let R := (cubicOddCore (swapFactors c) t.y).map (MulAut.conj g).toMonoidHom
  let S := t.leftCoreExtension
  have hDc : Nat.card D=243 := hc
  have hy := t.oddCore_card_eq.symm.trans hc
  have hRc : Nat.card R=243 := by
    rw [card_map_of_injective (MulAut.conj g).injective,hy]
  have hDS : D≤S := le_sup_left
  have hRS : R≤S := by
    change R≤t.leftCoreExtension
    rw [←hg]
    exact map_mono (show cubicOddCore (swapFactors c) t.y≤t.swap.leftCoreExtension from le_sup_left)
  have hderived : ⁅R,R⁆=(zpowers ((t.y:c.H):G)).map (MulAut.conj g).toMonoidHom := by
    rw [←Subgroup.map_commutator]
    have hh := t.swap.maximal_core_derived hy
    change ⁅cubicOddCore (swapFactors c) t.y,cubicOddCore (swapFactors c) t.y⁆=
      zpowers ((t.y:c.H):G) at hh
    exact congrArg (fun U : Subgroup G => U.map (MulAut.conj g).toMonoidHom) hh
  have hne : D≠R := by
    intro he
    have hh := t.maximal_core_derived hc
    change ⁅D,D⁆=_ at hh
    rw [he,hderived] at hh
    exact cubic_lines_not_conjugate (swapFactors c) t.y t.x t.y_order g hh
  have hle : D⊔R≤S := sup_le hDS hRS
  have hd : Nat.card (D⊔R:Subgroup G)∣3^6 := by
    have hh := card_dvd_of_le hle
    rwa [t.maximal_leftCoreExtension_card hc] at hh
  have hmin : 243≤Nat.card (D⊔R:Subgroup G) :=
    hDc ▸ card_le_of_le (show D≤D⊔R from le_sup_left)
  have hbad : Nat.card (D⊔R:Subgroup G)≠243 := by
    intro hh
    have hd : D=D⊔R := eq_of_le_of_card_ge le_sup_left (by rw [hDc,hh])
    have hr : R=D⊔R := eq_of_le_of_card_ge le_sup_right (by rw [hRc,hh])
    exact hne (hd.trans hr.symm)
  have hjoin : D⊔R=S := by
    obtain ⟨k,hk,he⟩ := (Nat.dvd_prime_pow Nat.prime_three (m:=6)).mp hd
    have hlo : 5≤k := (Nat.pow_le_pow_iff_right (by decide : 1<3)).mp (he ▸ hmin)
    have heq : k=6 := by
      by_contra hn
      have hk5 : k=5 := by omega
      exact hbad (by simpa only [hk5,Nat.reducePow] using he)
    apply eq_of_le_of_card_ge hle
    rw [t.maximal_leftCoreExtension_card hc,he,heq]
    decide
  have hn : R≤normalizer (D:Set G) := by
    apply hRS.trans
    apply S.le_normalizer.trans
    rw [t.maximal_sylow_normalizer_eq hc,t.maximal_core_normalizer hc]
    exact t.leftCubicBorel_le
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes D R hn
  rw [hDc,hRc,hjoin,t.maximal_leftCoreExtension_card hc] at hh
  refine ⟨hjoin,?_,hderived⟩
  change Nat.card (D⊓R:Subgroup G)=81
  omega

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
