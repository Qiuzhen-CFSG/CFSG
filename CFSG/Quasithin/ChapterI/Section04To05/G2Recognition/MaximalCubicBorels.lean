module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalPlaneNormalizer
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.TernaryCompletion
public import Theory.GroupTheory.PCorePrimeToIndex
public import Theory.GroupTheory.RelativeComplementProjection

/-!
# The original cubic normalizers and their index-four subgroups

For a marked order-243 core D and the opposite cubic y, S = D⟨y⟩ has
order729. The original Klein four A normalizes S, and B = SA has order2916
and index four in N_G(⟨x⟩). Within that cubic normalizer, B is exactly the
normalizer of S. All of these are subgroups of the original ambient group.

The two original cubic normalizers intersect in N_G(⟨x,y⟩), of order324,
and so do their two index-four subgroups. Thus these particular markings
are not an adjacent parabolic pair. The construction of compatible
conjugate endpoints for the ternary Atlas amalgam remains necessary.

Source: Aschbacher–Smith I.4(G1)–(G2), printed p.417, and the cubic
normalizer calculation of Fong–Wong §3B(ii), Nagoya Math. J.36 (1969),
p.156. The completion step is the one cited in I.4.5 via Aschbacher02b
and F.4.26. Chapter14MaximalBorels applies the conclusions to SourceLocalData.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus

/-- The marked odd core extended by the opposite original cubic. -/
def leftCoreExtension (t : CubicTorus c) : Subgroup G :=
  cubicOddCore c t.x ⊔ zpowers ((t.y:c.H):G)

/-- The original torus extension inside the left cubic normalizer. -/
def leftCubicBorel (t : CubicTorus c) : Subgroup G :=
  t.leftCoreExtension ⊔ t.torus.map c.H.subtype

omit [Finite G] in
private theorem original_core_normalized (t : CubicTorus c) :
    cubicNormalizer c t.x ≤ normalizer (cubicOddCore c t.x:Set G) := by
  have h := normalizer_le_normalizer_centralizer (zpowers ((t.x:c.H):G))
  have he : Subgroup.centralizer (zpowers ((t.x:c.H):G):Set G)=cubicCentralizer c t.x := by
    rw [zpowers_eq_closure,centralizer_closure]; rfl
  rw [he] at h
  exact h.trans (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 _))

omit [Finite G] in
private theorem opposite_line_normalizes_core (t : CubicTorus c) :
    zpowers ((t.y:c.H):G) ≤ normalizer (cubicOddCore c t.x:Set G) := by
  apply (zpowers_le.mpr (mem_map_of_mem c.H.subtype t.y.property)).trans
  apply (opposite_factor_le_cubic_centralizer c t.x).trans
  exact (cubicCentralizer c t.x).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 _))

private theorem core_extension_le_cubic_normalizer (t : CubicTorus c) :
    t.leftCoreExtension ≤ cubicNormalizer c t.x := by
  rw [t.left_ambient_normalizer]
  exact sup_le (le_sup_left.trans le_sup_left)
    ((zpowers_le.mpr (mem_map_of_mem c.H.subtype t.y.property)).trans
      (le_sup_right.trans le_sup_left))

private theorem torus_normalizes_core_extension (t : CubicTorus c) :
    t.torus.map c.H.subtype ≤ normalizer (t.leftCoreExtension:Set G) := by
  have hA : t.torus.map c.H.subtype ≤ cubicNormalizer c t.x := by
    rw [t.left_ambient_normalizer]; exact le_sup_right
  exact (le_inf (hA.trans t.original_core_normalized)
    (t.torus_normalizes_plane_subgroup _ le_sup_right)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- The original plane is the entire intersection with H. -/
theorem leftCoreExtension_inf_H (t : CubicTorus c) :
    t.leftCoreExtension ⊓ c.H =
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) := by
  let D := cubicOddCore c t.x
  let Y := zpowers ((t.y:c.H):G)
  have hYH : Y≤c.H := zpowers_le.mpr t.y.val.property
  apply le_antisymm
  · intro g hg
    have hm : g∈(D:Set G)*(Y:Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left D Y t.opposite_line_normalizes_core]
      exact hg.1
    obtain ⟨d,hd,y,hy,hdy⟩ := hm
    have hdH : d∈c.H := by
      have hh := c.H.mul_mem hg.2 (c.H.inv_mem (hYH hy))
      simpa only [←hdy,mul_inv_cancel_right] using hh
    have hdX := (cubic_oddCore_fixed c t.x t.x_order).le ⟨hd,hdH⟩
    exact hdy ▸ mul_mem_sup hdX hy
  · exact le_inf (sup_le_sup (cubic_line_le_oddCore c t.x t.x_order) le_rfl)
      (sup_le (zpowers_le.mpr t.x.val.property) hYH)

/-- The large marked core gives a concrete order729 three-subgroup. -/
theorem maximal_leftCoreExtension_card (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    Nat.card t.leftCoreExtension=729 := by
  have hYL : zpowers ((t.y:c.H):G)≤c.H₂.map c.H.subtype :=
    zpowers_le.mpr (mem_map_of_mem c.H.subtype t.y.property)
  have hd : Disjoint (cubicOddCore c t.x) (zpowers ((t.y:c.H):G)) :=
    (disjoint_iff.mpr (cubic_oddCore_inf_factor c t.x)).mono_right hYL
  rw [leftCoreExtension,card_sup_eq_mul_of_normalizes_of_disjoint _ _
    t.opposite_line_normalizes_core hd,hc,Nat.card_zpowers,orderOf_coe,orderOf_coe,t.y_order]

/-- The chosen torus splits the local order729 subgroup. -/
theorem maximal_leftCubicBorel_split (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    IsPGroup 3 t.leftCoreExtension ∧
      t.torus.map c.H.subtype ≤ normalizer (t.leftCoreExtension:Set G) ∧
      Disjoint t.leftCoreExtension (t.torus.map c.H.subtype) ∧
      Nat.card t.leftCubicBorel=2916 := by
  let : IsKleinFour (t.torus.map c.H.subtype) := t.ambient_torus_kleinFour
  have hd : Disjoint t.leftCoreExtension (t.torus.map c.H.subtype) :=
    disjoint_of_coprime_natCard (by
      rw [t.maximal_leftCoreExtension_card hc,IsKleinFour.card_four]; decide)
  refine ⟨IsPGroup.of_card (p:=3) (n:=6) (t.maximal_leftCoreExtension_card hc),
    t.torus_normalizes_core_extension,hd,?_⟩
  rw [leftCubicBorel,card_sup_eq_mul_of_normalizes_of_disjoint _ _
    t.torus_normalizes_core_extension hd,t.maximal_leftCoreExtension_card hc,
    IsKleinFour.card_four]

/-- The local Borel retains its literal inclusion in the cubic normalizer. -/
theorem leftCubicBorel_le (t : CubicTorus c) :
    t.leftCubicBorel ≤ cubicNormalizer c t.x := by
  apply sup_le t.core_extension_le_cubic_normalizer
  rw [t.left_ambient_normalizer]
  exact le_sup_right

/-- The whole marked plane normalizer lies in both local Borels. -/
theorem maximal_plane_normalizer_le_leftCubicBorel (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    normalizer
      ((zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G):Set G) ≤
        t.leftCubicBorel := by
  rw [(t.maximal_plane_normalizer_split hc).1]
  exact sup_le_sup (sup_le
    (sup_le_sup (cubic_line_le_oddCore c t.x t.x_order) le_rfl)
    (inf_le_left.trans le_sup_left)) le_rfl

/-- The original, unaligned cubic normalizers have the plane normalizer
as their whole intersection. -/
theorem maximal_cubic_normalizers_intersection (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    cubicNormalizer c t.x ⊓ cubicNormalizer (swapFactors c) t.y =
      normalizer
        ((zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G):Set G) := by
  apply le_antisymm (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have he := t.oddCore_card_eq
  have hy : Nat.card (cubicOddCore (swapFactors c) t.y)=243 := he.symm.trans hc
  refine le_inf ((t.maximal_plane_normalizer_le_leftCubicBorel hc).trans t.leftCubicBorel_le) ?_
  have hh := (t.swap.maximal_plane_normalizer_le_leftCubicBorel hy).trans t.swap.leftCubicBorel_le
  change normalizer ((zpowers ((t.y:c.H):G) ⊔ zpowers ((t.x:c.H):G) : Subgroup G):Set G) ≤
    cubicNormalizer (swapFactors c) t.y at hh
  rw [sup_comm] at hh
  exact hh

/-- Their two local Borels have that same whole intersection, not the
order2916 intersection required of adjacent ternary parabolics. -/
theorem maximal_cubic_borels_intersection (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    t.leftCubicBorel ⊓ t.swap.leftCubicBorel =
      normalizer
        ((zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G):Set G) := by
  apply le_antisymm
  · exact (inf_le_inf t.leftCubicBorel_le t.swap.leftCubicBorel_le).trans
      (t.maximal_cubic_normalizers_intersection hc).le
  · refine le_inf (t.maximal_plane_normalizer_le_leftCubicBorel hc) ?_
    have hy := t.oddCore_card_eq.symm.trans hc
    simpa only [swap,swapFactors,sup_comm] using
      t.swap.maximal_plane_normalizer_le_leftCubicBorel hy

/-- The subgroup of order729 has exactly the constructed Borel as its
normalizer inside the original cubic normalizer. -/
theorem maximal_leftCoreExtension_normalizer (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    cubicNormalizer c t.x ⊓ normalizer (t.leftCoreExtension:Set G)=t.leftCubicBorel := by
  let D := cubicOddCore c t.x
  let S := t.leftCoreExtension
  let N := cubicNormalizer c t.x
  let E := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  have hnD : c.H⊓N≤normalizer (D:Set G) := inf_le_right.trans t.original_core_normalized
  apply le_antisymm
  · intro g hg
    have hsplit : N=D⊔(c.H⊓N) := cubic_normalizer_split c t.x t.x_order
    have hm : g∈(D:Set G)*((c.H⊓N):Set G) := by
      have hm' : g∈(↑(D⊔(c.H⊓N)):Set G) := hsplit ▸ hg.1
      rw [coe_mul_of_right_le_normalizer_left D (c.H⊓N) hnD] at hm'
      exact hm'
    obtain ⟨d,hd,h,hh,hdh⟩ := hm
    have hdS : d∈S := mem_sup_left hd
    have hhS : h∈normalizer (S:Set G) := by
      have hv := (normalizer (S:Set G)).mul_mem
        ((normalizer (S:Set G)).inv_mem (S.le_normalizer hdS)) hg.2
      simpa only [←hdh,inv_mul_cancel_left] using hv
    have hhE : h∈normalizer (E:Set G) := by
      change h∈normalizer
        ((zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G):Set G)
      rw [←t.leftCoreExtension_inf_H]
      exact inf_normalizer_le_normalizer_inf ⟨hhS,c.H.le_normalizer hh.1⟩
    exact hdh ▸ (t.leftCubicBorel).mul_mem (mem_sup_left hdS)
      (t.maximal_plane_normalizer_le_leftCubicBorel hc hhE)
  · exact le_inf t.leftCubicBorel_le
      (sup_le S.le_normalizer t.torus_normalizes_core_extension)

/-- The original cubic normalizer acts on four cosets of this Borel. -/
theorem maximal_leftCubicBorel_index (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    t.leftCubicBorel.relIndex (cubicNormalizer c t.x)=4 := by
  have hh := (t.leftCubicBorel.subgroupOf (cubicNormalizer c t.x)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe t.leftCubicBorel_le).toEquiv,
    (t.maximal_leftCubicBorel_split hc).2.2.2,t.left_ambient_normalizer_card,hc] at hh
  change 2916 * t.leftCubicBorel.relIndex (cubicNormalizer c t.x)=243*48 at hh
  omega

/-- It is Sylow in this cubic normalizer, with the actual inclusion. -/
theorem maximal_leftCoreExtension_local_sylow (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    ∃ P : Sylow 3 (cubicNormalizer c t.x),
      (P:Subgroup (cubicNormalizer c t.x)).map (cubicNormalizer c t.x).subtype=
        t.leftCoreExtension := by
  let S := t.leftCoreExtension.subgroupOf (cubicNormalizer c t.x)
  have hS : Nat.card S=729 :=
    (Nat.card_congr (subgroupOfEquivOfLe t.core_extension_le_cubic_normalizer).toEquiv).trans
      (t.maximal_leftCoreExtension_card hc)
  have hi : S.index=16 := by
    have hh := S.card_mul_index
    rw [hS,t.left_ambient_normalizer_card,hc] at hh
    omega
  let P : Sylow 3 (cubicNormalizer c t.x) :=
    (IsPGroup.of_card (p:=3) (n:=6) hS).toSylow (by rw [hi]; decide)
  exact ⟨P,map_subgroupOf_eq_of_le t.core_extension_le_cubic_normalizer⟩

/-- The opposite original SL₂(3) and the actual outer involution. -/
def leftCubicLevi (t : CubicTorus c) : Subgroup G :=
  c.H₂.map c.H.subtype ⊔ zpowers (t.n:G)

private theorem leftCubicLevi_le (t : CubicTorus c) :
    t.leftCubicLevi≤cubicNormalizer c t.x := by
  rw [cubic_normalizer_of_local_inverter c t.x t.x_order t.n t.invert_left]
  exact sup_le (le_sup_right.trans le_sup_left) le_sup_right

/-- The chosen local actor has order48. -/
theorem leftCubicLevi_card (t : CubicTorus c) : Nat.card t.leftCubicLevi=48 := by
  classical
  let L := c.H₂.map c.H.subtype
  let : c.H₂.Normal := c.H₂_normal
  have hn : zpowers (t.n:G)≤normalizer (L:Set G) := by
    apply zpowers_le.mpr
    exact (c.H₂.le_normalizer_map c.H.subtype)
      (mem_map_of_mem c.H.subtype (show t.n∈normalizer (c.H₂:Set c.H) by
        rw [normalizer_eq_top]; trivial))
  have hd : Disjoint L (zpowers (t.n:G)) := by
    apply disjoint_iff.mpr
    apply bot_unique
    rintro a ⟨ha,han⟩
    change a∈L at ha
    change a∈zpowers (t.n:G) at han
    rw [mem_zpowers_iff_mem_range_orderOf,orderOf_coe,t.n_order] at han
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp han
    have hi' : i<2 := Finset.mem_range.mp hi
    interval_cases i
    · simp
    · have hnL : (t.n:G)∈L := by simpa using ha
      have hnH : t.n∈c.H₂ := (mem_map_iff_mem c.H.subtype_injective).mp hnL
      exact (t.outside (mem_sup_right hnH)).elim
  have hL : Nat.card L=24 := by
    rw [card_map_of_injective c.H.subtype_injective]
    exact (Nat.card_congr c.H₂_model.some.toEquiv).trans
      GLS3.Chapter5.SchurPresentation.sl23_card_eq
  rw [leftCubicLevi,card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn hd,
    hL,Nat.card_zpowers,orderOf_coe,t.n_order]

omit [Finite G] in
/-- The actual cubic odd core is normal in its line normalizer. -/
theorem left_core_normal_in_cubic_normalizer (t : CubicTorus c) :
    ((cubicOddCore c t.x).subgroupOf (cubicNormalizer c t.x)).Normal :=
  normal_subgroupOf_of_le_normalizer t.original_core_normalized

/-- The core and this actual order48 actor form an internal semidirect product. -/
theorem maximal_left_cubic_levi_split (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    cubicNormalizer c t.x=cubicOddCore c t.x⊔t.leftCubicLevi ∧
      Disjoint (cubicOddCore c t.x) t.leftCubicLevi := by
  have he : cubicNormalizer c t.x=cubicOddCore c t.x⊔t.leftCubicLevi := by
    rw [cubic_normalizer_of_local_inverter c t.x t.x_order t.n t.invert_left,
      leftCubicLevi,sup_assoc]
  refine ⟨he,disjoint_iff.mpr ?_⟩
  apply card_eq_one.mp
  have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (cubicOddCore c t.x) t.leftCubicLevi
    (t.leftCubicLevi_le.trans t.original_core_normalized)
  rw [hc,t.leftCubicLevi_card,←he,t.left_ambient_normalizer_card,hc] at hh
  omega

/-- The quotient is identified with the literal chosen actor subgroup. -/
theorem maximal_left_cubic_quotient (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    letI := t.left_core_normal_in_cubic_normalizer
    Nonempty ((cubicNormalizer c t.x ⧸
      (cubicOddCore c t.x).subgroupOf (cubicNormalizer c t.x)) ≃* t.leftCubicLevi) := by
  let := t.left_core_normal_in_cubic_normalizer
  obtain ⟨he,hd⟩ := t.maximal_left_cubic_levi_split hc
  exact ⟨relativeQuotientEquiv (by rw [he]; exact le_sup_left)
    t.leftCubicLevi_le he.symm hd⟩

/-- The original marked core, not a substituted residual, is O₃ of its
whole cubic normalizer. -/
theorem maximal_cubic_normalizer_threeCore (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    (cubicNormalizer c t.x).pCoreIn 3=cubicOddCore c t.x := by
  let C := cubicCentralizer c t.x
  let N := cubicNormalizer c t.x
  let D := cubicOddCore c t.x
  have hCN : C≤N := by
    change Subgroup.centralizer ({((t.x:c.H):G)}:Set G) ≤
      normalizer (zpowers ((t.x:c.H):G):Set G)
    rw [←centralizer_closure,←zpowers_eq_closure]
    exact Subgroup.centralizer_le_normalizer _
  have hDN : D≤N := (map_subtype_le _).trans hCN
  have hi : (C.subgroupOf N).index=2 := by
    have hh := (C.subgroupOf N).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv,
      cubic_centralizer_card c t.x t.x_order,t.left_ambient_normalizer_card,hc] at hh
    omega
  have hPC : C.pCoreIn 3=D := by
    change (pCore 3 C).map C.subtype=(pPrimeCore 2 C).map C.subtype
    rw [t.left_threeCore]
  apply le_antisymm
  · have hm := map_mono (f:=N.subtype)
      (pCore_le_map_pCore_of_prime_not_dvd_index (p:=3) (C.subgroupOf N)
        (by rw [hi]; decide))
    change N.pCoreIn 3≤((C.subgroupOf N).pCoreIn 3).map N.subtype at hm
    have hk : IsPGroup 3 N.subtype.ker := by
      rw [(MonoidHom.ker_eq_bot_iff N.subtype).mpr N.subtype_injective]
      exact IsPGroup.of_card (p:=3) (n:=0) (by simp)
    rw [map_pCoreIn_of_ker_isPGroup N.subtype hk,
      map_subgroupOf_eq_of_le hCN,hPC] at hm
    exact hm
  · exact le_pCoreIn_of_normalizes t.left_oddCore_isThreeGroup hDN t.original_core_normalized

/-- The constructed order729 subgroup is O₃ of the local Borel. -/
theorem maximal_leftCubicBorel_threeCore (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    t.leftCubicBorel.pCoreIn 3=t.leftCoreExtension := by
  obtain ⟨hp,hn,_,hB⟩ := t.maximal_leftCubicBorel_split hc
  have hle : t.leftCoreExtension≤t.leftCubicBorel.pCoreIn 3 :=
    le_pCoreIn_of_normalizes hp le_sup_left (sup_le t.leftCoreExtension.le_normalizer hn)
  have hcop : Nat.Coprime (Nat.card (t.leftCubicBorel.pCoreIn 3)) 4 := by
    obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 3 t.leftCubicBorel).exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 4).pow_left k
  have hd : Nat.card (t.leftCubicBorel.pCoreIn 3)∣729 := by
    have hh := card_dvd_of_le (pCoreIn_le 3 t.leftCubicBorel)
    rw [hB] at hh
    exact hcop.dvd_of_dvd_mul_left hh
  exact (eq_of_le_of_card_ge hle (by
    rw [t.maximal_leftCoreExtension_card hc]
    exact Nat.le_of_dvd (by decide) hd)).symm

/-- No completion of the exact ternary Atlas amalgam can use these two
unaligned original normalizers as its endpoint ranges: its middle already
has order2916, while their whole overlap has order324. This is an obstruction
to that placement, not to I.4.5 or to a suitably conjugated placement. -/
theorem maximal_original_pair_not_completion (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=243) :
    ¬ ∃ d : TernaryCompletion.Completion G,
      d.left.range=cubicNormalizer c t.x ∧
      d.right.range=cubicNormalizer (swapFactors c) t.y := by
  rintro ⟨d,hl,hr⟩
  have hm := le_inf d.middle_le_left d.middle_le_right
  rw [hl,hr,t.maximal_cubic_normalizers_intersection hc] at hm
  have hd := card_dvd_of_le hm
  rw [t.maximal_plane_normalizer_card hc] at hd
  have hmid := d.middle_card
  change Nat.card d.middle.range=Nat.card
    (Atlas.G2.LieParabolicSetup.parabolic₁ (F:=ZMod 3) ⊓
      Atlas.G2.LieParabolicSetup.parabolic₂ : Subgroup (Atlas.G2.Model (ZMod 3))) at hmid
  rw [Atlas.G2.LieParabolicSetup.parabolics_intersection,Atlas.G2.card_borel,
    Nat.card_zmod] at hmid
  rw [hmid] at hd
  norm_num at hd

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
