module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.CommonLine243Exclusion
/-!
# The actual paired-core join in the remaining Sylow-729 branch

For the marked order-27 cores D and E, the common line K is central in
P = O(C_G(K)). The Klein four action decomposes each core into its three
involution-fixed subgroups. One outer involution fixes exactly K in both
cores. The other has abelian fixed subgroup in P, since every odd subgroup
of an involution centralizer has order dividing nine. Together with the
already proved cubic displacement identities this gives [D,E] ≤ K.

Consequently J = D join E has order 243, center and derived group K,
and elementary central quotient: J is extraspecial. Its index three in P
makes it normal in P, and the actual torus preserves both marked cores,
so the full normalizer of P preserves J as well.

Source: Aschbacher–Smith I.4(G1)–(G2), printed p.417. This continues the
exceptional q=3 branch with the actual markings; it does not assert that
Sylow order 729 itself is impossible. The literal Chapter14 application
is in Chapter14PairedCoreJoin.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace CubicTorus

omit [Finite G] in
private theorem torus_setup (t : CubicTorus c) (U : Subgroup G)
    (hn : t.torus.map c.H.subtype ≤ normalizer (U:Set G)) :
    ∃ a b : normalizer (U:Set G), (a:G)=(t.z:G) ∧ (b:G)=(t.n:G) ∧
      a^2=1 ∧ b^2=1 ∧ Commute a b := by
  let a : normalizer (U:Set G) := ⟨t.z,hn (mem_map_of_mem c.H.subtype
    (mem_sup_left (mem_zpowers t.z)))⟩
  let b : normalizer (U:Set G) := ⟨t.n,hn (mem_map_of_mem c.H.subtype
    (mem_sup_right (mem_zpowers t.n)))⟩
  refine ⟨a,b,rfl,rfl,?_,?_,?_⟩
  · apply Subtype.ext
    change (t.z:G)^2=1
    simpa only [orderOf_coe,t.z_order] using pow_orderOf_eq_one (t.z:G)
  · apply Subtype.ext
    change (t.n:G)^2=1
    simpa only [orderOf_coe,t.n_order] using pow_orderOf_eq_one (t.n:G)
  · exact Subtype.ext (mem_centralizer_singleton_iff.mp
      (t.centralizer ▸ t.n.property)).symm

private theorem torus_normalizes_left_core (t : CubicTorus c) :
    t.torus.map c.H.subtype ≤ normalizer (cubicOddCore c t.x:Set G) := by
  have hn := normalizer_le_normalizer_centralizer (zpowers ((t.x:c.H):G))
  have he : Subgroup.centralizer (zpowers ((t.x:c.H):G):Set G)=cubicCentralizer c t.x := by
    rw [zpowers_eq_closure,centralizer_closure]; rfl
  rw [he] at hn
  have ht : t.torus.map c.H.subtype ≤ cubicNormalizer c t.x := by
    rw [t.left_ambient_normalizer]; exact le_sup_right
  exact ht.trans (hn.trans (normalizer_le_normalizer_characteristic_image _ (pPrimeCore 2 _)))

private theorem core_torus_decomposition (t : CubicTorus c) :
    cubicOddCore c t.x =
      (zpowers ((t.x:c.H):G) ⊔
        (cubicOddCore c t.x ⊓ Subgroup.centralizer ({(t.n:G)}:Set G))) ⊔
        (cubicOddCore c t.x ⊓ Subgroup.centralizer ({(t.z:G)*(t.n:G)}:Set G)) := by
  let D := cubicOddCore c t.x
  obtain ⟨a,b,ha,hb,ha2,hb2,hab⟩ := t.torus_setup D t.torus_normalizes_left_core
  have habv : ((a*b:normalizer (D:Set G)):G)=(t.z:G)*(t.n:G) := by
    change (a:G)*(b:G)=_; rw [ha,hb]
  apply le_antisymm
  · intro d hd
    obtain ⟨u,hu,v,hv,w,hw,rfl⟩ := D.exists_three_odd_centralizers
      (cubic_oddCore_odd c t.x) a b ha2 hb2 hab d hd
    rw [ha,←t.centralizer] at hu
    have huX := (cubic_oddCore_fixed c t.x t.x_order).le hu
    rw [hb] at hv
    rw [habv] at hw
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left huX))
      (mem_sup_left (mem_sup_right hv))) (mem_sup_right hw)
  · exact sup_le (sup_le (cubic_line_le_oddCore c t.x t.x_order) inf_le_left) inf_le_left

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

private theorem common_fixed_alternative (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    let D := cubicOddCore c t.x
    let E := cubicOddCore (swapFactors c) t.y
    let K := D ⊓ E
    (D ⊓ Subgroup.centralizer ({(t.n:G)}:Set G)=K ∧
      E ⊓ Subgroup.centralizer ({(t.n:G)}:Set G)=K) ∨
    (D ⊓ Subgroup.centralizer ({(t.z:G)*(t.n:G)}:Set G)=K ∧
      E ⊓ Subgroup.centralizer ({(t.z:G)*(t.n:G)}:Set G)=K) := by
  let D := cubicOddCore c t.x
  let E := cubicOddCore (swapFactors c) t.y
  let K := D ⊓ E
  have hK : Nat.card K=3 := t.oddCore_intersection_card_of_twentySeven hc
  obtain ⟨a,b,ha,hb,ha2,hb2,hab⟩ := t.torus_setup K t.torus_normalizes_core_intersection
  have habv : ((a*b:normalizer (K:Set G)):G)=(t.z:G)*(t.n:G) := by
    change (a:G)*(b:G)=_; rw [ha,hb]
  have hfix : K ⊓ Subgroup.centralizer ({(a:G)}:Set G)=⊥ := by
    apply bot_unique
    rw [ha,←t.centralizer]
    have hle : K ⊓ c.H ≤ zpowers ((t.x:c.H):G) :=
      (inf_le_inf_right c.H inf_le_left).trans (cubic_oddCore_fixed c t.x t.x_order).le
    have hf : zpowers ((t.x:c.H):G) ≤ c.H₁.map c.H.subtype :=
      zpowers_le.mpr (mem_map_of_mem c.H.subtype t.x.property)
    exact (le_inf (inf_le_left.trans inf_le_right) (hle.trans hf)).trans
      (cubic_oddCore_inf_factor (swapFactors c) t.y).le
  have hformula := K.card_three_odd_centralizers (by rw [hK]; decide) a b ha2 hb2 hab
  rw [hK,hfix,bot_inf_eq,card_bot,hb,habv] at hformula
  have hn : Nat.card (K ⊓ Subgroup.centralizer ({(t.n:G)}:Set G) : Subgroup G)=3 ∨
      Nat.card (K ⊓ Subgroup.centralizer ({(t.z:G)*(t.n:G)}:Set G) : Subgroup G)=3 := by
    have hd := card_dvd_of_le (show K ⊓ Subgroup.centralizer ({(t.n:G)}:Set G)≤K from inf_le_left)
    rw [hK] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h|h
    · exact Or.inr (by simpa only [h,one_mul,one_pow,mul_one] using hformula.symm)
    · exact Or.inl h
  have hEq (v : G) (hv : Nat.card (K ⊓ Subgroup.centralizer ({v}:Set G) : Subgroup G)=3)
      (hD : Nat.card (D ⊓ Subgroup.centralizer ({v}:Set G) : Subgroup G)=3)
      (hE : Nat.card (E ⊓ Subgroup.centralizer ({v}:Set G) : Subgroup G)=3) :
      D ⊓ Subgroup.centralizer ({v}:Set G)=K ∧ E ⊓ Subgroup.centralizer ({v}:Set G)=K := by
    have hKC : K ⊓ Subgroup.centralizer ({v}:Set G)=K :=
      eq_of_le_of_card_ge inf_le_left (by rw [hv,hK])
    have hKD := eq_of_le_of_card_ge (inf_le_inf_right (Subgroup.centralizer ({v}:Set G))
      (show K≤D from inf_le_left)) (by rw [hv,hD])
    have hKE := eq_of_le_of_card_ge (inf_le_inf_right (Subgroup.centralizer ({v}:Set G))
      (show K≤E from inf_le_right)) (by rw [hv,hE])
    exact ⟨hKD.symm.trans hKC,hKE.symm.trans hKC⟩
  obtain ⟨hDn,hDm⟩ := t.core_outer_fixed_cards hc
  obtain ⟨hEn,hEm⟩ := t.swap.core_outer_fixed_cards (t.right_oddCore_twentySeven_of_left hc)
  exact hn.elim (fun h => Or.inl (hEq _ h hDn hEn))
    (fun h => Or.inr (hEq _ h hDm hEm))

/-- Odd fixed groups of ambient involutions are abelian. -/
theorem commonLineCore_involution_fixed_commutative (t : CubicTorus c) (v : G) (hv : orderOf v=2) :
    IsMulCommutative (t.commonLineCore ⊓ Subgroup.centralizer ({v}:Set G) : Subgroup G) := by
  let F := t.commonLineCore ⊓ Subgroup.centralizer ({v}:Set G)
  have hodd : Odd (Nat.card F) := by
    have ho : Odd (Nat.card t.commonLineCore) := by
      obtain ⟨i,hi⟩ := t.commonLineCore_isThreeGroup.exists_card_eq
      rw [hi]; exact (by decide : Odd (3:ℕ)).pow
    exact ho.of_dvd_nat (card_dvd_of_le inf_le_left)
  have hd : Nat.card F ∣ 9 := by
    have hh := card_dvd_of_le (show F≤Subgroup.centralizer ({v}:Set G) from inf_le_right)
    rw [involution_centralizer_card c v hv] at hh
    exact (hodd.coprime_two_right.pow_right 6).dvd_of_dvd_mul_left hh
  obtain ⟨i,hi,he⟩ := (Nat.dvd_prime_pow Nat.prime_three (m:=2)).mp hd
  interval_cases i
  · let : Subsingleton F := (Nat.card_eq_one_iff_unique.mp he).1
    exact ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
  · let : IsCyclic F := isCyclic_of_prime_card (p:=3) he
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p:=3) he

omit [Finite G] in
private theorem outer_product_order (t : CubicTorus c) : orderOf ((t.z:G)*(t.n:G))=2 := by
  have hz2 : (t.z:G)^2=1 := by
    simpa only [orderOf_coe,t.z_order] using pow_orderOf_eq_one (t.z:G)
  have hn2 : (t.n:G)^2=1 := by
    simpa only [orderOf_coe,t.n_order] using pow_orderOf_eq_one (t.n:G)
  have hcomm : Commute (t.z:G) (t.n:G) :=
    (mem_centralizer_singleton_iff.mp (t.centralizer ▸ t.n.property)).symm
  apply orderOf_eq_prime
  · rw [hcomm.mul_pow,hz2,hn2,one_mul]
  · intro hh
    have hni : (t.n:G)⁻¹=(t.n:G) := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hn2)
    have hzn : t.z=t.n := Subtype.ext ((eq_inv_of_mul_eq_one_left hh).trans hni)
    apply t.outside
    rw [←hzn]
    exact mem_sup_left ((t.central_line ▸ mem_zpowers t.z).1)

/-- The two actual elementary cores commute modulo their common line. -/
theorem paired_cores_commutator_le (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    ⁅cubicOddCore c t.x,cubicOddCore (swapFactors c) t.y⁆ ≤
      cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y := by
  let D := cubicOddCore c t.x
  let E := cubicOddCore (swapFactors c) t.y
  let K := D ⊓ E
  let X := zpowers ((t.x:c.H):G)
  let Y := zpowers ((t.y:c.H):G)
  let P := t.commonLineCore
  have he := t.right_oddCore_twentySeven_of_left hc
  have hDP : D≤P := t.left_oddCore_le_commonLineCore hc
  have hEP : E≤P := t.right_oddCore_le_commonLineCore hc
  have hKP : K≤P := inf_le_left.trans hDP
  have hKC : K≤Subgroup.centralizer (P:Set G) := (t.commonLineCore_centralizer hc).ge
  have hPN : P≤normalizer (K:Set G) :=
    (le_centralizer_iff.mp hKC).trans (Subgroup.centralizer_le_normalizer _)
  have hXD : X≤D := cubic_line_le_oddCore c t.x t.x_order
  have hYE : Y≤E := cubic_line_le_oddCore (swapFactors c) t.y t.y_order
  have hXE : ⁅X,E⁆≤K := by
    have hh := commutator_mono (show X≤E⊔X from le_sup_right) (show E≤E⊔X from le_sup_left)
    have heq := t.swap.left_core_extension_derived he
    change ⁅E⊔X,E⊔X⁆=E⊓D at heq
    rw [heq,inf_comm] at hh
    exact hh
  have hYD : ⁅Y,D⁆≤K := by
    have hh := commutator_mono (show Y≤D⊔Y from le_sup_right) (show D≤D⊔Y from le_sup_left)
    rwa [t.left_core_extension_derived hc] at hh
  have hK (A : Subgroup G) (hA : A≤P) : ⁅K,A⁆≤K := by
    rw [commutator_eq_bot_iff_le_centralizer.mpr (hKC.trans (centralizer_le hA))]
    exact bot_le
  have hfinish (A B : Subgroup G) (hAD : A≤D) (hBE : B≤E)
      (hD : D=(X⊔K)⊔A) (hE : E=(Y⊔K)⊔B)
      (hAB : ⁅A,B⁆=⊥) : ⁅D,E⁆≤K := by
    have hAE : ⁅A,E⁆≤K := by
      rw [commutator_comm,hE]
      apply commutator_sup_le_of_relative_normal P _ _ _ K hPN
        (sup_le (hYE.trans hEP) hKP) (hBE.trans hEP)
      · exact commutator_sup_le_of_relative_normal P Y K A K hPN (hYE.trans hEP) hKP
          ((commutator_mono le_rfl hAD).trans hYD) (hK A (hAD.trans hDP))
      · rw [commutator_comm,hAB]; exact bot_le
    rw [hD]
    exact commutator_sup_le_of_relative_normal P _ A E K hPN
      (sup_le (hXD.trans hDP) hKP) (hAD.trans hDP)
      (commutator_sup_le_of_relative_normal P X K E K hPN (hXD.trans hDP) hKP
        hXE (hK E hEP)) hAE
  have hfixcomm (v : G) (hv : orderOf v=2) :
      ⁅D ⊓ Subgroup.centralizer ({v}:Set G),E ⊓ Subgroup.centralizer ({v}:Set G)⁆=⊥ := by
    let F := P ⊓ Subgroup.centralizer ({v}:Set G)
    let : IsMulCommutative F := t.commonLineCore_involution_fixed_commutative v hv
    have hDF : D ⊓ Subgroup.centralizer ({v}:Set G)≤F := inf_le_inf_right _ hDP
    have hEF : E ⊓ Subgroup.centralizer ({v}:Set G)≤F := inf_le_inf_right _ hEP
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (hDF.trans (F.le_centralizer.trans (centralizer_le hEF)))
  have hD := t.core_torus_decomposition
  have hE := t.swap.core_torus_decomposition
  change E = (Y ⊔ (E ⊓ Subgroup.centralizer ({(t.n:G)}:Set G))) ⊔
    (E ⊓ Subgroup.centralizer ({(t.z:G)*(t.n:G)}:Set G)) at hE
  rcases t.common_fixed_alternative hc with ⟨hd,he⟩|⟨hd,he⟩
  · rw [hd] at hD
    rw [he] at hE
    exact hfinish _ _ inf_le_left inf_le_left hD hE (hfixcomm _ t.outer_product_order)
  · rw [hd] at hD
    rw [he] at hE
    apply hfinish _ _ inf_le_left inf_le_left _ _
      (hfixcomm _ ((orderOf_coe t.n).trans t.n_order))
    · exact hD.trans (by dsimp only [K,D,E,X]; ac_rfl)
    · exact hE.trans (by dsimp only [K,D,E,Y]; ac_rfl)

/-- The paired cores generate a group of order 243, normal in the ambient Sylow group. -/
theorem paired_cores_join_card_normal (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    Nat.card (cubicOddCore c t.x ⊔ cubicOddCore (swapFactors c) t.y : Subgroup G)=243 ∧
      t.commonLineCore≤normalizer
        ((cubicOddCore c t.x ⊔ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G) := by
  let D := cubicOddCore c t.x
  let E := cubicOddCore (swapFactors c) t.y
  let J := D⊔E
  let P := t.commonLineCore
  have hDE : D≤normalizer (E:Set G) :=
    le_normalizer_iff_commutator_le_right.mpr ((t.paired_cores_commutator_le hc).trans inf_le_right)
  have hJ : Nat.card J=243 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes E D hDE
    rw [hc,t.right_oddCore_twentySeven_of_left hc,inf_comm E D,
      t.oddCore_intersection_card_of_twentySeven hc,sup_comm E D] at hh
    change 27*27=3*Nat.card J at hh
    omega
  have hJP : J≤P := sup_le (t.left_oddCore_le_commonLineCore hc) (t.right_oddCore_le_commonLineCore hc)
  have hi : (J.subgroupOf P).index=3 := by
    have hh := (J.subgroupOf P).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hJP).toEquiv,hJ,t.commonLineCore_card729 hc] at hh
    omega
  exact ⟨hJ,(normal_subgroupOf_iff_le_normalizer hJP).mp
    (normal_of_index_three_of_isPGroup t.commonLineCore_isThreeGroup _ hi)⟩


/-- The normal order-243 join has precisely the original common line as center and derived subgroup. -/
theorem paired_cores_join_center_derived (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    let J := cubicOddCore c t.x ⊔ cubicOddCore (swapFactors c) t.y
    let K := cubicOddCore c t.x ⊓ cubicOddCore (swapFactors c) t.y
    Subgroup.centralizer (J:Set G)=K ∧ centerIn J=K ∧ ⁅J,J⁆=K := by
  let D := cubicOddCore c t.x
  let E := cubicOddCore (swapFactors c) t.y
  let J := D⊔E
  let K := D⊓E
  let P := t.commonLineCore
  let : IsElementaryAbelian 3 D := t.left_oddCore_twentySeven_elementary hc
  let : IsElementaryAbelian 3 E := t.right_oddCore_twentySeven_elementary
    (t.right_oddCore_twentySeven_of_left hc)
  have hJP : J≤P := sup_le (t.left_oddCore_le_commonLineCore hc) (t.right_oddCore_le_commonLineCore hc)
  have hKJ : K≤J := inf_le_left.trans le_sup_left
  have hKC : K≤Subgroup.centralizer (J:Set G) :=
    (t.commonLineCore_centralizer hc).ge.trans (centralizer_le hJP)
  have hC : Subgroup.centralizer (J:Set G)=K := by
    apply le_antisymm _ hKC
    have hd := centralizer_le (show D≤J from le_sup_left)
    have he := centralizer_le (show E≤J from le_sup_right)
    rw [t.left_oddCore_twentySeven_selfCentralizing hc] at hd
    rw [t.right_oddCore_twentySeven_selfCentralizing (t.right_oddCore_twentySeven_of_left hc)] at he
    exact le_inf hd he
  have hZ : centerIn J=K := by
    change J ⊓ Subgroup.centralizer (J:Set G)=K
    rw [hC]; exact inf_eq_right.mpr hKJ
  refine ⟨hC,hZ,?_⟩
  apply le_antisymm
  · have hJN : J≤normalizer (K:Set G) :=
      (le_centralizer_iff.mp hKC).trans (Subgroup.centralizer_le_normalizer _)
    have hDD : ⁅D,D⁆≤K := by
      rw [commutator_eq_bot_iff_le_centralizer.mpr D.le_centralizer]; exact bot_le
    have hEE : ⁅E,E⁆≤K := by
      rw [commutator_eq_bot_iff_le_centralizer.mpr E.le_centralizer]; exact bot_le
    have hDE := t.paired_cores_commutator_le hc
    have hED : ⁅E,D⁆≤K := by rw [commutator_comm]; exact hDE
    have hDJ : ⁅D,J⁆≤K := by
      rw [commutator_comm]
      exact commutator_sup_le_of_relative_normal J D E D K hJN le_sup_left le_sup_right hDD hED
    have hEJ : ⁅E,J⁆≤K := by
      rw [commutator_comm]
      exact commutator_sup_le_of_relative_normal J D E E K hJN le_sup_left le_sup_right hDE hEE
    exact commutator_sup_le_of_relative_normal J D E J K hJN le_sup_left le_sup_right hDJ hEJ
  · have hR : D ⊔ zpowers ((t.y:c.H):G)≤J := sup_le le_sup_left
      ((cubic_line_le_oddCore (swapFactors c) t.y t.y_order).trans le_sup_right)
    have hh := commutator_mono hR hR
    rwa [t.left_core_extension_derived hc] at hh

/-- The actual join is extraspecial of order 3⁵. -/
theorem paired_cores_join_extraspecial (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    IsExtraspecial 3 (cubicOddCore c t.x ⊔ cubicOddCore (swapFactors c) t.y : Subgroup G) := by
  let D := cubicOddCore c t.x
  let E := cubicOddCore (swapFactors c) t.y
  let J := D⊔E
  let K := D⊓E
  obtain ⟨_,hZ,hderived⟩ := t.paired_cores_join_center_derived hc
  have hZmap : (center J).map J.subtype=K := by rw [←centerIn_eq_map_center]; exact hZ
  have hZcard : Nat.card (center J)=3 := by
    rw [←card_map_of_injective J.subtype_injective,hZmap]
    exact t.oddCore_intersection_card_of_twentySeven hc
  have hclass : _root_.commutator J≤center J := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_subtype_commutator,hderived,hZmap]
  have hquotcomm : IsMulCommutative (J ⧸ center J) :=
    Normal.quotient_commutative_iff_commutator_le.mpr hclass
  let := hquotcomm
  let q := QuotientGroup.mk' (center J)
  have hDE : E≤normalizer (D:Set G) := le_normalizer_iff_commutator_le_right.mpr
    (by rw [commutator_comm];exact (t.paired_cores_commutator_le hc).trans inf_le_left)
  have hcube (u : J) : (q u)^3=1 := by
    have hu := u.property
    change (u:G) ∈ (↑(D⊔E):Set G) at hu
    rw [coe_mul_of_right_le_normalizer_left D E hDE] at hu
    obtain ⟨d,hd,e,he,hprod⟩ := hu
    let d' : J := ⟨d,mem_sup_left hd⟩
    let e' : J := ⟨e,mem_sup_right he⟩
    have heq : u=d'*e' := Subtype.ext hprod.symm
    have hd3 : d'^3=1 := Subtype.ext (congrArg (fun u : D => (u:G)) (t.left_oddCore_cube ⟨d,hd⟩))
    have he3 : e'^3=1 := Subtype.ext (congrArg (fun u : E => (u:G)) (t.right_oddCore_cube ⟨e,he⟩))
    rw [heq,map_mul,(Commute.all (q d') (q e')).mul_pow,←map_pow,←map_pow,hd3,he3,map_one,one_mul]
  have hEA : IsElementaryAbelian 3 (J ⧸ center J) := {
    toIsMulCommutative := hquotcomm
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro u; obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (center J) u; exact hcube v) }
  refine ⟨hZcard,hEA,QuotientGroup.nontrivial_iff.mpr ?_⟩
  intro he
  have hcard := (t.paired_cores_join_card_normal hc).1
  rw [he,card_top,hcard] at hZcard
  omega

/-- The normalizer of the Sylow subgroup preserves the actual extraspecial join. -/
theorem paired_cores_join_normalizer (t : CubicTorus c)
    (hc : Nat.card (cubicOddCore c t.x)=27) :
    normalizer (t.commonLineCore:Set G)≤normalizer
      ((cubicOddCore c t.x ⊔ cubicOddCore (swapFactors c) t.y : Subgroup G):Set G) := by
  rw [(t.commonLineCore_normalizer_split hc).1]
  apply sup_le (t.paired_cores_join_card_normal hc).2
  have hleft := t.torus_normalizes_left_core
  have hright := t.swap.torus_normalizes_left_core
  change t.torus.map c.H.subtype≤normalizer (cubicOddCore (swapFactors c) t.y:Set G) at hright
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [Subgroup.map_sup,mem_normalizer_iff_map_conj_eq.mp (hleft hg),
    mem_normalizer_iff_map_conj_eq.mp (hright hg)]

end CubicTorus
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
