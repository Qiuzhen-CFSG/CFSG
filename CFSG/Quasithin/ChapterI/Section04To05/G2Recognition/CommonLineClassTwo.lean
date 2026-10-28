module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.DiagonalSylow
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.PlaneFusion
public import Theory.GroupTheory.PGroup.CubicCenterInvolution

/-!
# Class two in the smaller common-line Sylow case

Let D and E be the actual marked cubic odd cores of order 27, and let
P = O(C_G(D ∩ E)). Both cores lie in P, and C_P(z) is the original cubic
plane of order nine. If P has order 243, Brauer–Wielandt makes one of
the other two torus involutions have fixed subgroup of order three.
Its fixed subgroups in D and E already have order three, so this fixed
subgroup is D ∩ E = Z(P). The cubic-center involution lemma makes P
extraspecial of exponent three. In particular P normalizes D and E.

These retain all original markings from Aschbacher–Smith I.4(G1)–(G2),
printed p.417. `CommonLine243Exclusion` consumes the class-two result to
exclude this Sylow order; no class-two assumption is added to the source.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus

theorem left_oddCore_le_commonLineCore (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    cubicOddCore c t.x ≤ t.commonLineCore := by
  let D := cubicOddCore c t.x
  let E := cubicOddCore (swapFactors c) t.y
  let C := Subgroup.centralizer ((D⊓E:Subgroup G):Set G)
  let O := pPrimeCore 2 C
  let : IsElementaryAbelian 3 D := t.left_oddCore_twentySeven_elementary hc
  have hDC : D≤C := D.le_centralizer.trans (centralizer_le inf_le_left)
  have hcard : Nat.card (D.subgroupOf C)=27 :=
    (Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv).trans hc
  have hr : O.relIndex (D.subgroupOf C)=1 := Nat.eq_one_of_dvd_coprimes
    (show Nat.Coprime O.index (Nat.card (D.subgroupOf C)) by
      rw [(t.core_intersection_oddCore_index hc).1,hcard]; decide)
    (O.relIndex_dvd_index_of_normal _) (relIndex_dvd_card _ _)
  have hh := map_mono (f:=C.subtype) (relIndex_eq_one.mp hr)
  rwa [map_subgroupOf_eq_of_le hDC] at hh

theorem right_oddCore_le_commonLineCore (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    cubicOddCore (swapFactors c) t.y ≤ t.commonLineCore := by
  have hh := t.swap.left_oddCore_le_commonLineCore (t.right_oddCore_twentySeven_of_left hc)
  change cubicOddCore (swapFactors c) t.y ≤
    (pPrimeCore 2 (Subgroup.centralizer
      ((cubicOddCore (swapFactors c) t.y ⊓ cubicOddCore c t.x : Subgroup G):Set G))).map
        (Subgroup.centralizer
          ((cubicOddCore (swapFactors c) t.y ⊓ cubicOddCore c t.x : Subgroup G):Set G)).subtype at hh
  rw [inf_comm (cubicOddCore (swapFactors c) t.y)] at hh
  exact hh

private theorem fixed_card_dvd_nine (_t : CubicTorus c) (P : Subgroup G)
    (hp : Odd (Nat.card P)) (v : G) (hv : orderOf v=2) :
    Nat.card (P ⊓ Subgroup.centralizer ({v}:Set G) : Subgroup G) ∣ 9 := by
  let F := P ⊓ Subgroup.centralizer ({v}:Set G)
  have ho : Odd (Nat.card F) := hp.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hd : Nat.card F ∣ 64*9 := by
    have hh := card_dvd_of_le (show F≤Subgroup.centralizer ({v}:Set G) from inf_le_right)
    rwa [involution_centralizer_card c v hv] at hh
  exact (ho.coprime_two_right.pow_right 6).dvd_of_dvd_mul_left hd

private theorem commonLineCore_odd (t : CubicTorus c) : Odd (Nat.card t.commonLineCore) := by
  obtain ⟨i,hi⟩ := t.commonLineCore_isThreeGroup.exists_card_eq
  rw [hi]
  exact (by decide : Odd (3:ℕ)).pow

theorem commonLineCore_fixed_marked_involution (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    t.commonLineCore ⊓ Subgroup.centralizer ({(t.z:G)}:Set G) =
      zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) := by
  let B := zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G)
  have hB : Nat.card B=9 := (cubic_plane_data c t.x t.y t.x_order t.y_order).2
  have hBP : B≤t.commonLineCore := sup_le
    ((cubic_line_le_oddCore c t.x t.x_order).trans (t.left_oddCore_le_commonLineCore hc))
    ((cubic_line_le_oddCore (swapFactors c) t.y t.y_order).trans
      (t.right_oddCore_le_commonLineCore hc))
  have hBH : B≤c.H := sup_le (zpowers_le.mpr t.x.val.property)
    (zpowers_le.mpr t.y.val.property)
  apply Eq.symm
  apply eq_of_le_of_card_ge (le_inf hBP (t.centralizer ▸ hBH))
  rw [hB]
  exact Nat.le_of_dvd (by decide) (t.fixed_card_dvd_nine _ t.commonLineCore_odd _
    ((orderOf_coe t.z).trans t.z_order))

private theorem core_outer_fixed_cards (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    Nat.card (cubicOddCore c t.x ⊓ Subgroup.centralizer ({(t.n:G)}:Set G) : Subgroup G)=3 ∧
    Nat.card (cubicOddCore c t.x ⊓ Subgroup.centralizer ({(t.z:G)*(t.n:G)}:Set G) : Subgroup G)=3 := by
  have h := cubic_oddCore_card_square c t.x t.x_order t.z t.n t.z_order t.n_order
    t.centralizer t.central_line t.outside t.invert_left
  rw [hc] at h
  have hn : Nat.card (cubicOddCore c t.x ⊓ Subgroup.centralizer ({(t.n:G)}:Set G) : Subgroup G)=3 := by
    nlinarith [sq_nonneg (Nat.card (cubicOddCore c t.x ⊓
      Subgroup.centralizer ({(t.n:G)}:Set G) : Subgroup G) - 3 : ℤ)]
  obtain ⟨q,hq,hqn⟩ := opposite_factor_swaps_torus_involutions c t.z t.n
    t.central_line t.n_order t.outside
  have hqC : (q:G) ∈ cubicCentralizer c t.x :=
    opposite_factor_le_cubic_centralizer c t.x (mem_map_of_mem c.H.subtype hq)
  have hqD : (q:G) ∈ normalizer (cubicOddCore c t.x:Set G) :=
    (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 _))
      ((cubicCentralizer c t.x).le_normalizer hqC)
  have he := (cubicOddCore c t.x).card_inf_centralizer_conj (q:G) hqD (t.n:G)
  rw [show (q:G)*(t.n:G)*(q:G)⁻¹=(t.z:G)*(t.n:G) from congrArg Subtype.val hqn] at he
  exact ⟨hn,he.symm.trans hn⟩

private theorem commonLineCore_torus_setup (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    ∃ a b : normalizer (t.commonLineCore:Set G),
      (a:G)=(t.z:G) ∧ (b:G)=(t.n:G) ∧ a^2=1 ∧ b^2=1 ∧ Commute a b ∧
      orderOf (((a*b):normalizer (t.commonLineCore:Set G)):G)=2 := by
  have hn : t.torus.map c.H.subtype ≤ normalizer (t.commonLineCore:Set G) := by
    rw [t.commonLineCore_normalizer hc]
    exact t.torus_normalizes_core_intersection
  let a : normalizer (t.commonLineCore:Set G) := ⟨t.z,hn (mem_map_of_mem c.H.subtype
    (mem_sup_left (mem_zpowers t.z)))⟩
  let b : normalizer (t.commonLineCore:Set G) := ⟨t.n,hn (mem_map_of_mem c.H.subtype
    (mem_sup_right (mem_zpowers t.n)))⟩
  have ha : a^2=1 := Subtype.ext (by
    change (t.z:G)^2=1
    simpa only [orderOf_coe,t.z_order] using pow_orderOf_eq_one (t.z:G))
  have hb : b^2=1 := Subtype.ext (by
    change (t.n:G)^2=1
    simpa only [orderOf_coe,t.n_order] using pow_orderOf_eq_one (t.n:G))
  have hab : Commute a b := Subtype.ext
    (mem_centralizer_singleton_iff.mp (t.centralizer ▸ t.n.property)).symm
  refine ⟨a,b,rfl,rfl,ha,hb,hab,?_⟩
  apply orderOf_eq_prime
  · have hh := hab.mul_pow 2
    rw [ha,hb,one_mul] at hh
    exact congrArg Subtype.val hh
  · intro hh
    have hni : (t.n:G)⁻¹=(t.n:G) := inv_eq_of_mul_eq_one_left
      (by simpa only [orderOf_coe,t.n_order,pow_two] using pow_orderOf_eq_one (t.n:G))
    have hzn : t.z=t.n := Subtype.ext ((eq_inv_of_mul_eq_one_left hh).trans hni)
    apply t.outside
    rw [←hzn]
    exact mem_sup_left ((t.central_line ▸ mem_zpowers t.z).1)

/-- The smaller surviving Sylow order has a torus involution fixing exactly its center. -/
theorem commonLineCore_central_fixed_involution_of_card243 (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) (hp : Nat.card t.commonLineCore=243) :
    ∃ v : G, (v=(t.n:G) ∨ v=(t.z:G)*(t.n:G)) ∧ orderOf v=2 ∧
      v∈normalizer (t.commonLineCore:Set G) ∧
      t.commonLineCore ⊓ Subgroup.centralizer ({v}:Set G)=
        cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y := by
  let P := t.commonLineCore
  let D := cubicOddCore c t.x
  let E := cubicOddCore (swapFactors c) t.y
  obtain ⟨a,b,ha,hb,ha2,hb2,hab,hab2⟩ := t.commonLineCore_torus_setup hc
  have hformula := P.card_three_odd_centralizers t.commonLineCore_odd a b ha2 hb2 hab
  have hz : Nat.card (P ⊓ Subgroup.centralizer ({(a:G)}:Set G) : Subgroup G)=9 := by
    rw [ha,t.commonLineCore_fixed_marked_involution hc]
    exact (cubic_plane_data c t.x t.y t.x_order t.y_order).2
  have hnb := t.fixed_card_dvd_nine P t.commonLineCore_odd (b:G)
    (by rw [hb,orderOf_coe,t.n_order])
  have hnab := t.fixed_card_dvd_nine P t.commonLineCore_odd ((a*b:normalizer (P:Set G)):G) hab2
  have hcommon : Nat.card ((P ⊓ Subgroup.centralizer ({(a:G)}:Set G)) ⊓
      Subgroup.centralizer ({(b:G)}:Set G) : Subgroup G)=1 := by
    apply card_eq_one.mpr
    rw [eq_bot_iff_forall]
    intro w hw
    have hwB : w∈zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) := by
      rw [←t.commonLineCore_fixed_marked_involution hc]
      exact ⟨hw.1.1,ha ▸ hw.1.2⟩
    have hwN : w*(t.n:G)=(t.n:G)*w := mem_centralizer_singleton_iff.mp (hb ▸ hw.2)
    have he : w⁻¹=w := (t.plane_inverted w hwB).symm.trans (by
      change (t.n:G)*w*(t.n:G)⁻¹=w
      rw [←hwN,mul_inv_cancel_right])
    have hw2 : w^2=1 := (pow_two w).trans (by simpa only [he] using inv_mul_cancel w)
    have hd : orderOf w ∣ 9 :=
      (cubic_plane_data c t.x t.y t.x_order t.y_order).2 ▸
        (zpowers ((t.x:c.H):G) ⊔ zpowers ((t.y:c.H):G) : Subgroup G).orderOf_dvd_natCard hwB
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 9 2)
      hd (orderOf_dvd_of_pow_eq_one hw2))
  rw [hp,hz,hcommon] at hformula
  have hsmall : Nat.card (P ⊓ Subgroup.centralizer ({(b:G)}:Set G) : Subgroup G)=3 ∨
      Nat.card (P ⊓ Subgroup.centralizer ({((a*b:normalizer (P:Set G)):G)}:Set G) : Subgroup G)=3 := by
    obtain ⟨i,hi,hei⟩ := (Nat.dvd_prime_pow Nat.prime_three (m:=2)).mp hnb
    obtain ⟨j,hj,hej⟩ := (Nat.dvd_prime_pow Nat.prime_three (m:=2)).mp hnab
    rw [hei,hej] at hformula ⊢
    interval_cases i
    all_goals interval_cases j
    all_goals norm_num at hformula
    all_goals norm_num
  have hfixed (v : G) (hd : Nat.card (D ⊓ Subgroup.centralizer ({v}:Set G) : Subgroup G)=3)
      (he : Nat.card (E ⊓ Subgroup.centralizer ({v}:Set G) : Subgroup G)=3)
      (hf : Nat.card (P ⊓ Subgroup.centralizer ({v}:Set G) : Subgroup G)=3) :
      P ⊓ Subgroup.centralizer ({v}:Set G)=D⊓E := by
    have hdEq := eq_of_le_of_card_ge
      (inf_le_inf_right (Subgroup.centralizer ({v}:Set G)) (t.left_oddCore_le_commonLineCore hc))
      (by rw [hd,hf])
    have heEq := eq_of_le_of_card_ge
      (inf_le_inf_right (Subgroup.centralizer ({v}:Set G)) (t.right_oddCore_le_commonLineCore hc))
      (by rw [he,hf])
    apply eq_of_le_of_card_ge
    · exact le_inf (hdEq ▸ inf_le_left) (heEq ▸ inf_le_left)
    · rw [hf,t.oddCore_intersection_card_of_twentySeven hc]
  obtain ⟨hDn,hDzn⟩ := t.core_outer_fixed_cards hc
  obtain ⟨hEn,hEzn⟩ := t.swap.core_outer_fixed_cards (t.right_oddCore_twentySeven_of_left hc)
  rcases hsmall with h|h
  · refine ⟨b,Or.inl hb,by rw [hb,orderOf_coe,t.n_order],b.property,?_⟩
    apply hfixed _ _ _ h <;> rw [hb]
    · exact hDn
    · exact hEn
  · have habval : ((a*b:normalizer (P:Set G)):G)=(t.z:G)*(t.n:G) := by
      change (a:G)*(b:G)=_; rw [ha,hb]
    refine ⟨a*b,Or.inr habval,hab2,(a*b).property,?_⟩
    apply hfixed _ _ _ h <;> rw [habval]
    · exact hDzn
    · exact hEzn

/-- The smaller surviving common-line Sylow subgroup is extraspecial of exponent three. -/
theorem commonLineCore_extraspecial_of_card243 (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) (hp : Nat.card t.commonLineCore=243) :
    IsExtraspecial 3 t.commonLineCore ∧ (∀ x : t.commonLineCore, x^3=1) ∧
      ⁅t.commonLineCore,t.commonLineCore⁆≤
        cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y := by
  let P := t.commonLineCore
  let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
  have hcenter : (center P).map P.subtype=K := by
    rw [←centerIn_eq_map_center]
    exact t.commonLineCore_center hc
  have hZ : Nat.card (center P)=3 := by
    rw [←card_map_of_injective P.subtype_injective,hcenter]
    exact t.oddCore_intersection_card_of_twentySeven hc
  have hne : center P≠⊤ := by
    intro he
    rw [he,card_top,hp] at hZ
    omega
  obtain ⟨v,_,hv,hvN,hfix⟩ := t.commonLineCore_central_fixed_involution_of_card243 hc hp
  let a := P.normalizerMonoidHom ⟨v,hvN⟩
  have ha : Function.Involutive a := by
    intro x
    have hv2 : (⟨v,hvN⟩:normalizer (P:Set G))^2=1 := Subtype.ext
      (by change v^2=1; simpa only [hv] using pow_orderOf_eq_one v)
    have hh : a^2=1 := by
      change (P.normalizerMonoidHom ⟨v,hvN⟩)^2=1
      rw [←map_pow,hv2,map_one]
    exact congrArg (fun f : MulAut P => f x) hh
  have hf (x : P) : a x=x ↔ x∈center P := by
    have hx : a x=x ↔ (x:G)∈P ⊓ Subgroup.centralizer ({v}:Set G) := by
      constructor
      · intro h
        exact ⟨x.property,mem_centralizer_singleton_iff.mpr
          (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val h)).symm⟩
      · intro h
        apply Subtype.ext
        change v*(x:G)*v⁻¹=(x:G)
        rw [←mem_centralizer_singleton_iff.mp h.2,mul_inv_cancel_right]
    rw [hfix] at hx
    change a x=x ↔ (x:G)∈K at hx
    rw [←hcenter] at hx
    exact hx.trans (mem_map_iff_mem P.subtype_injective)
  obtain ⟨hexp,hcube,hclass⟩ := a.extraspecial_three_of_fixed_center ha hZ hne hf
  refine ⟨hexp,hcube,?_⟩
  change ⁅P,P⁆≤K
  rw [←map_subtype_commutator,←hcenter]
  exact map_mono hclass

/-- Class two makes both original order-27 cores normal in the common-line Sylow group. -/
theorem commonLineCore_normalizes_cores_of_card243 (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) (hp : Nat.card t.commonLineCore=243) :
    t.commonLineCore≤normalizer (cubicOddCore c t.x:Set G) ∧
      t.commonLineCore≤normalizer (cubicOddCore (swapFactors c) t.y:Set G) := by
  have hd := (t.commonLineCore_extraspecial_of_card243 hc hp).2.2
  exact ⟨le_normalizer_iff_commutator_le_right.mpr
    ((commutator_mono le_rfl (t.left_oddCore_le_commonLineCore hc)).trans (hd.trans inf_le_left)),
    le_normalizer_iff_commutator_le_right.mpr
    ((commutator_mono le_rfl (t.right_oddCore_le_commonLineCore hc)).trans (hd.trans inf_le_right))⟩


end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
