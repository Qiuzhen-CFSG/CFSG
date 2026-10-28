module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.OddCoreGeometry
public import Theory.GroupTheory.DisjointConjugateCenter
public import Theory.GroupTheory.Commutator.PTimesQ


/-!
# Small cubic cores and the nonabelian order-27 exclusion

The two marked odd cores have order three simultaneously. If one is small,
the opposite cubic has its entire centralizer in H. Thompson's P × Q lemma,
with the marked central involution as the coprime actor, then forces the
other core into H, where its intersection is its original cubic line.

Every marked core of order 27 is elementary abelian. The faithful opposite
SL₂(3) action on the literal core quotient first gives C_G(D) = Z(D) for
any core larger than three. A nonabelian core of order 27 therefore gives
a Sylow subgroup of order 81 whose center is its original factor line.
Both cores cannot do this, since their lines are not conjugate. The other
core must consequently be elementary of order 27. Its product with the
opposite cubic is another Sylow subgroup of order 81. If its center had
order three, P × Q would again force this core into H. This contradicts
Sylow conjugacy and excludes the nonabelian case.

Source: Aschbacher–Smith I.4(G1)–(G2), printed p.417. Compare the Sylow-center
step of Fong, Nagoya Math. J.39 (1970), §6C, pp.75–77, and the P × Q lemma
in Aschbacher–Smith A.1.18, printed p.24. Here the explicit q=3 configuration
supplies all premises. We do not use Fong's q>3 invariant-line selection.
The Sylow-nine and elementary order-27 branches, and the actual Atlas
recognition equivalence, remain open. `Chapter14OddCoreExclusions` applies
these reductions to the original source-local data.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus
variable (t : CubicTorus c)

/-- A large marked core has no ambient centralizer outside its own center. -/
theorem left_oddCore_centralizer (hlarge : Nat.card (cubicOddCore c t.x) ≠ 3) :
    Subgroup.centralizer (cubicOddCore c t.x : Set G) =
      (center (cubicOddCore c t.x)).map (cubicOddCore c t.x).subtype := by
  let D := cubicOddCore c t.x
  let W := cubicCoreLine c t.x
  let q := QuotientGroup.mk' W
  let L := c.H₂.map c.H.subtype
  have hn : L ≤ normalizer (D:Set G) :=
    (opposite_factor_le_cubic_centralizer c t.x).trans
      ((cubicCentralizer c t.x).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 (cubicCentralizer c t.x))))
  apply le_antisymm
  · intro g hg
    have hgC : g ∈ cubicCentralizer c t.x := mem_centralizer_singleton_iff.mpr
      (hg _ (cubic_line_le_oddCore c t.x t.x_order (mem_zpowers _))).symm
    rw [cubic_centralizer_split c t.x t.x_order] at hgC
    change g ∈ (↑(D ⊔ L):Set G) at hgC
    rw [coe_mul_of_right_le_normalizer_left D L hn] at hgC
    obtain ⟨d,hd,l,hl,he⟩ := hgC
    obtain ⟨ll,hll,rfl⟩ := hl
    let b : c.H₂ := ⟨ll,hll⟩
    let dd : D := ⟨d,hd⟩
    have hρ : cubicOppositeQuotientAction c t.x b = 1 := by
      apply MulEquiv.ext
      intro v
      obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective W v
      rw [cubicOppositeQuotientAction_mk]
      change q (cubicOppositeAction c t.x b a) = q a
      have hact : cubicOppositeAction c t.x b a = dd⁻¹*a*dd := by
        apply Subtype.ext
        change (ll:G)*(a:G)*(ll:G)⁻¹ = d⁻¹*(a:G)*d
        have hc := hg a a.property
        rw [←he] at hc
        change (a:G) * (d * (ll:G)) = (d * (ll:G)) * (a:G) at hc
        calc
          _ = d⁻¹*((a:G)*(d*(ll:G)))*(ll:G)⁻¹ := by rw [hc]; group
          _ = _ := by group
      rw [hact,map_mul,map_mul,map_inv]
      let : IsElementaryAbelian 3 (D ⧸ W) := t.left_oddCore_quotient_elementary
      have hc : Commute (q dd) (q a) := mul_comm' _ _
      rw [hc.inv_left.eq, mul_assoc,inv_mul_cancel,mul_one]
    have hb : b = 1 := t.left_oddCore_quotient_action_faithful hlarge
      (hρ.trans (map_one _).symm)
    have hgD : g ∈ D := by
      have hll1 : (ll:G)=1 := congrArg (fun b : c.H₂ => ((b:c.H):G)) hb
      change d * (ll:G) = g at he
      have heq : d = g := by simpa only [hll1, mul_one] using he
      exact heq ▸ hd
    refine ⟨⟨g,hgD⟩,mem_center_iff.mpr ?_,rfl⟩
    intro a
    exact Subtype.ext (hg a a.property)
  · rintro g ⟨a,ha,rfl⟩ d hd
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨d,hd⟩)

private theorem core_sup_cubic_card (hcard : Nat.card (cubicOddCore c t.x)=27) :
    Nat.card (cubicOddCore c t.x ⊔ zpowers ((t.y:c.H):G) : Subgroup G)=81 := by
  let D := cubicOddCore c t.x
  let B := zpowers ((t.y:c.H):G)
  have hBL : B ≤ c.H₂.map c.H.subtype := zpowers_le.mpr
    (mem_map_of_mem c.H.subtype t.y.property)
  have hBC : B ≤ cubicCentralizer c t.x :=
    hBL.trans (opposite_factor_le_cubic_centralizer c t.x)
  have hn : B ≤ normalizer (D:Set G) := hBC.trans
    ((cubicCentralizer c t.x).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 (cubicCentralizer c t.x))))
  have hd : Disjoint D B := disjoint_iff.mpr (bot_unique
    ((inf_le_inf_left D hBL).trans (cubic_oddCore_inf_factor c t.x).le))
  rw [card_sup_eq_mul_of_normalizes_of_disjoint D B hn hd,
      hcard,Nat.card_zpowers,orderOf_coe,orderOf_coe,t.y_order]

private theorem central_line_twentySeven_sylow (hcard : Nat.card (cubicOddCore c t.x)=27)
    (hZ : (center (cubicOddCore c t.x)).map (cubicOddCore c t.x).subtype =
      zpowers ((t.x:c.H):G)) :
    let R := cubicOddCore c t.x ⊔ zpowers ((t.y:c.H):G)
    Nat.card R=81 ∧ (center R).map R.subtype=zpowers ((t.x:c.H):G) ∧
      ∃P:Sylow 3 G,(P:Subgroup G)=R := by
  let D := cubicOddCore c t.x
  let B := zpowers ((t.y:c.H):G)
  let W := zpowers ((t.x:c.H):G)
  let R := D ⊔ B
  have hBL : B ≤ c.H₂.map c.H.subtype := zpowers_le.mpr
    (mem_map_of_mem c.H.subtype t.y.property)
  have hBC : B ≤ cubicCentralizer c t.x :=
    hBL.trans (opposite_factor_le_cubic_centralizer c t.x)
  have hc : Nat.card R=81 := t.core_sup_cubic_card hcard
  have hCD : Subgroup.centralizer (D:Set G)=W := (t.left_oddCore_centralizer (by omega)).trans hZ
  have hWR : W ≤ R := (cubic_line_le_oddCore c t.x t.x_order).trans le_sup_left
  have hRC : R ≤ Subgroup.centralizer (W:Set G) := by
    change R ≤ Subgroup.centralizer (zpowers ((t.x:c.H):G):Set G)
    rw [zpowers_eq_closure,centralizer_closure]
    exact sup_le (map_subtype_le _) hBC
  have hZR : (center R).map R.subtype=W := by
    apply le_antisymm
    · rintro a ⟨v,hv,rfl⟩
      rw [←hCD]
      intro d hd
      exact congrArg Subtype.val (mem_center_iff.mp hv ⟨d,(le_sup_left:D≤R) hd⟩)
    · intro w hw
      refine ⟨⟨w,hWR hw⟩,mem_center_iff.mpr ?_,rfl⟩
      intro a
      exact Subtype.ext ((hRC a.property w hw).symm)
  have hRN : R ≤ normalizer (W:Set G) := hRC.trans (Subgroup.centralizer_le_normalizer _)
  have hN : Nat.card (normalizer (W:Set G))=27*48 := by
    change Nat.card (cubicNormalizer c t.x)=_
    rw [t.left_ambient_normalizer_card,hcard]
  have hlocal : ¬3∣R.relIndex (normalizer (W:Set G)) := by
    have hh := relIndex_mul_relIndex (⊥:Subgroup G) R (normalizer (W:Set G)) bot_le hRN
    simp only [relIndex_bot_left,hc,hN] at hh
    have he : R.relIndex (normalizer (W:Set G))=16 := by omega
    rw [he]; decide
  have hcontrol : normalizer (R:Set G) ≤ normalizer (W:Set G) := by
    rw [←hZR]
    exact normalizer_le_normalizer_characteristic_image R (center R)
  have hp : IsPGroup 3 R := IsPGroup.of_card (n:=4) hc
  have hg := not_dvd_relIndex_of_normalizer_inf_le R (normalizer (W:Set G)) ⊤ hp le_top
    hlocal (inf_le_left.trans hcontrol)
  have hi : ¬3∣R.index := by simpa only [relIndex_top_right] using hg
  exact ⟨hc,hZR,hp.toSylow hi,rfl⟩


private theorem core_small_of_opposite_fixed_le_H
    (hf : cubicOddCore c t.x ⊓
      Subgroup.centralizer (zpowers ((t.y:c.H):G) : Set G) ≤ c.H) :
    Nat.card (cubicOddCore c t.x)=3 := by
  let D := cubicOddCore c t.x
  let P := zpowers ((t.y:c.H):G)
  let Q := zpowers (t.z:G)
  have hCQ : Subgroup.centralizer (Q:Set G)=c.H := by
    dsimp only [Q]
    rw [zpowers_eq_closure,centralizer_closure,←t.centralizer]
  have hPC : P ≤ cubicCentralizer c t.x :=
    (zpowers_le.mpr (mem_map_of_mem c.H.subtype t.y.property)).trans
      (opposite_factor_le_cubic_centralizer c t.x)
  have hQC : Q ≤ cubicCentralizer c t.x := zpowers_le.mpr
    (mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (t.centralizer ▸ t.x.val.property)).symm)
  have hCN : cubicCentralizer c t.x ≤ normalizer (D:Set G) :=
    (cubicCentralizer c t.x).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 (cubicCentralizer c t.x)))
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n:=1) (by
    simp only [P,Nat.card_zpowers,orderOf_coe,t.y_order,pow_one])
  have hQcop : Nat.Coprime 3 (Nat.card Q) := by
    rw [show Q=zpowers (t.z:G) from rfl,Nat.card_zpowers,orderOf_coe,t.z_order]
    decide
  have hPQ : ⁅P,Q⁆=⊥ := commutator_eq_bot_iff_le_centralizer.mpr (by
    rw [hCQ]
    exact zpowers_le.mpr t.y.val.property)
  have hfix : D ⊓ Subgroup.centralizer (P:Set G) ≤ Subgroup.centralizer (Q:Set G) := by
    rw [hCQ]
    exact hf
  have hDQ := p_times_q_centralizer P Q D hPp t.left_oddCore_isThreeGroup hQcop
    (hPC.trans hCN) (hQC.trans hCN) hPQ hfix
  have hDH : D ≤ c.H := by
    rw [←hCQ]
    exact commutator_eq_bot_iff_le_centralizer.mp hDQ
  have he := cubic_oddCore_fixed c t.x t.x_order
  rw [inf_eq_left.mpr hDH] at he
  change Nat.card D=3
  rw [he,Nat.card_zpowers,orderOf_coe,orderOf_coe,t.x_order]

private theorem left_core_small_of_right
    (hy : Nat.card (cubicOddCore (swapFactors c) t.y)=3) :
    Nat.card (cubicOddCore c t.x)=3 := by
  apply t.core_small_of_opposite_fixed_le_H
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
    ((cubic_normalizer_le_H_iff (swapFactors c) t.y t.y_order).mpr hy))

/-- The two marked odd cores have order three simultaneously. -/
theorem oddCore_three_iff :
    Nat.card (cubicOddCore c t.x)=3 ↔
      Nat.card (cubicOddCore (swapFactors c) t.y)=3 := by
  exact ⟨fun h => t.swap.left_core_small_of_right h,t.left_core_small_of_right⟩

private theorem not_both_central_line_twentySeven (hx : Nat.card (cubicOddCore c t.x)=27)
    (hy : Nat.card (cubicOddCore (swapFactors c) t.y)=27)
    (hZx : (center (cubicOddCore c t.x)).map (cubicOddCore c t.x).subtype =
      zpowers ((t.x:c.H):G))
    (hZy : (center (cubicOddCore (swapFactors c) t.y)).map
      (cubicOddCore (swapFactors c) t.y).subtype = zpowers ((t.y:c.H):G)) : False := by
  obtain ⟨hc₁,hZ₁,P,hP⟩ := t.central_line_twentySeven_sylow hx hZx
  obtain ⟨hc₂,hZ₂,Q,hQ⟩ := t.swap.central_line_twentySeven_sylow hy hZy
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G P Q
  have hPQ : (P:Subgroup G).map (MulAut.conj g).toMonoidHom=(Q:Subgroup G) :=
    congrArg Sylow.toSubgroup hg
  have hZP : centerIn (P:Subgroup G)=zpowers ((t.x:c.H):G) := by
    rw [hP,centerIn_eq_map_center]; exact hZ₁
  have hZQ : centerIn (Q:Subgroup G)=zpowers ((t.y:c.H):G) := by
    rw [hQ,centerIn_eq_map_center]; exact hZ₂
  apply cubic_lines_not_conjugate c t.x t.y t.x_order g
  rw [←hZP,centerIn_map_equiv,hPQ,hZQ]

private theorem opposite_not_maximal_of_central_line_twentySeven (hx : Nat.card (cubicOddCore c t.x)=27)
    (hZx : (center (cubicOddCore c t.x)).map (cubicOddCore c t.x).subtype =
      zpowers ((t.x:c.H):G)) :
    Nat.card (cubicOddCore (swapFactors c) t.y) ≠ 243 := by
  intro hy
  obtain ⟨hc,hZ,P,hP⟩ := t.central_line_twentySeven_sylow hx hZx
  have hd : 3^5 ∣ Nat.card G := by
    simpa only [hy, show 3^5 = 243 from rfl] using (cubicOddCore (swapFactors c) t.y).card_subgroup_dvd_card
  have hp := P.pow_dvd_card_of_pow_dvd_card hd
  have hcP : Nat.card P=81 := by rw [←hc,←hP]
  rw [hcP] at hp
  norm_num at hp


private theorem opposite_elementary_of_nonabelian_twentySeven (hx : Nat.card (cubicOddCore c t.x)=27)
    (hne : ¬IsElementaryAbelian 3 (cubicOddCore c t.x)) :
    Nat.card (cubicOddCore (swapFactors c) t.y)=27 ∧
      IsElementaryAbelian 3 (cubicOddCore (swapFactors c) t.y) := by
  obtain ⟨_,hZx⟩ := (t.left_oddCore_twentySeven hx).resolve_left hne
  have hy3 : Nat.card (cubicOddCore (swapFactors c) t.y)≠3 := by
    intro h
    have hh := t.left_core_small_of_right h
    omega
  have hy27 : Nat.card (cubicOddCore (swapFactors c) t.y)=27 :=
    ((t.right_oddCore_orders.resolve_left hy3).resolve_right (t.opposite_not_maximal_of_central_line_twentySeven hx hZx))
  refine ⟨hy27, ?_⟩
  rcases t.right_oddCore_twentySeven hy27 with he|⟨_,hZy⟩
  · exact he
  · exact (t.not_both_central_line_twentySeven hx hy27 hZx hZy).elim


private theorem elementary_twentySeven_no_small_sylow_center
    (hc : Nat.card (cubicOddCore c t.x)=27)
    (he : IsElementaryAbelian 3 (cubicOddCore c t.x))
    (P : Sylow 3 G) (hPc : Nat.card P=81) (hPz : Nat.card (center P)=3) : False := by
  let D := cubicOddCore c t.x
  let B := zpowers ((t.y:c.H):G)
  let X := zpowers ((t.x:c.H):G)
  let R := D ⊔ B
  let F := D ⊓ Subgroup.centralizer (B:Set G)
  have hRc : Nat.card R=81 := t.core_sup_cubic_card hc
  have hRp : IsPGroup 3 R := IsPGroup.of_card (n:=4) hRc
  obtain ⟨S,hRS⟩ := hRp.exists_le_sylow
  have hSc : Nat.card S=81 := (Nat.card_congr (S.equiv P).toEquiv).trans hPc
  have hReq : R=(S:Subgroup G) := eq_of_le_of_card_ge hRS (by rw [hRc]; exact hSc.le)
  have hRz : Nat.card (centerIn R)=3 := by
    rw [hReq,centerIn_eq_map_center,card_map_of_injective (S:Subgroup G).subtype_injective]
    exact (Nat.card_congr (centerCongr (S.equiv P)).toEquiv).trans hPz
  have hFZ : F ≤ centerIn R := by
    let : IsElementaryAbelian 3 D := he
    intro f hf
    refine ⟨(le_sup_left:D≤R) hf.1, ?_⟩
    have hDC : D ≤ Subgroup.centralizer ({f}:Set G) := by
      intro d hd
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mul_comm' (⟨d,hd⟩:D) ⟨f,hf.1⟩))
    have hBC : B ≤ Subgroup.centralizer ({f}:Set G) := by
      intro b hb
      exact mem_centralizer_singleton_iff.mpr (hf.2 b hb)
    intro r hr
    exact mem_centralizer_singleton_iff.mp ((sup_le hDC hBC) hr)
  have hXF : X ≤ F := by
    refine le_inf (cubic_line_le_oddCore c t.x t.x_order) ?_
    apply le_centralizer_iff.mp
    change B ≤ Subgroup.centralizer (zpowers ((t.x:c.H):G):Set G)
    rw [zpowers_eq_closure,centralizer_closure]
    exact (zpowers_le.mpr (mem_map_of_mem c.H.subtype t.y.property)).trans
      (opposite_factor_le_cubic_centralizer c t.x)
  have hFX : X=F := eq_of_le_of_card_ge hXF (by
    have hh := card_le_of_le hFZ
    rw [show Nat.card X=3 from by
      rw [Nat.card_zpowers,orderOf_coe,orderOf_coe,t.x_order]]
    rwa [hRz] at hh)
  have hh := t.core_small_of_opposite_fixed_le_H (show F ≤ c.H from
    hFX ▸ (zpowers_le.mpr t.x.val.property))
  omega

/-- The actual left odd core cannot be nonabelian of order 27. -/
theorem left_oddCore_twentySeven_elementary (hc : Nat.card (cubicOddCore c t.x)=27) :
    IsElementaryAbelian 3 (cubicOddCore c t.x) := by
  by_contra he
  obtain ⟨_,hZ⟩ := (t.left_oddCore_twentySeven hc).resolve_left he
  obtain ⟨hR,hZR,P,hP⟩ := t.central_line_twentySeven_sylow hc hZ
  have hPc : Nat.card P=81 := by rw [←hR,←hP]
  have hPz : Nat.card (center P)=3 := by
    rw [←card_map_of_injective (P:Subgroup G).subtype_injective,hP,hZR,
      Nat.card_zpowers,orderOf_coe,orderOf_coe,t.x_order]
  obtain ⟨hy,heY⟩ := t.opposite_elementary_of_nonabelian_twentySeven hc he
  exact t.swap.elementary_twentySeven_no_small_sylow_center hy heY P hPc hPz


/-- The same ambient centralizer identity for the original right core. -/
theorem right_oddCore_centralizer
    (hlarge : Nat.card (cubicOddCore (swapFactors c) t.y) ≠ 3) :
    Subgroup.centralizer (cubicOddCore (swapFactors c) t.y : Set G) =
      (center (cubicOddCore (swapFactors c) t.y)).map
        (cubicOddCore (swapFactors c) t.y).subtype :=
  t.swap.left_oddCore_centralizer hlarge

/-- The actual right odd core cannot be nonabelian of order 27. -/
theorem right_oddCore_twentySeven_elementary
    (hc : Nat.card (cubicOddCore (swapFactors c) t.y)=27) :
    IsElementaryAbelian 3 (cubicOddCore (swapFactors c) t.y) :=
  t.swap.left_oddCore_twentySeven_elementary hc

/-- In the remaining left order-27 branch the elementary core is self-centralizing. -/
theorem left_oddCore_twentySeven_selfCentralizing
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    Subgroup.centralizer (cubicOddCore c t.x : Set G) = cubicOddCore c t.x := by
  let : IsElementaryAbelian 3 (cubicOddCore c t.x) := t.left_oddCore_twentySeven_elementary hc
  rw [t.left_oddCore_centralizer (by omega),center_eq_top,←MonoidHom.range_eq_map,range_subtype]

/-- The same self-centralizing conclusion for the original right core. -/
theorem right_oddCore_twentySeven_selfCentralizing
    (hc : Nat.card (cubicOddCore (swapFactors c) t.y)=27) :
    Subgroup.centralizer (cubicOddCore (swapFactors c) t.y : Set G) =
      cubicOddCore (swapFactors c) t.y :=
  t.swap.left_oddCore_twentySeven_selfCentralizing hc

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
