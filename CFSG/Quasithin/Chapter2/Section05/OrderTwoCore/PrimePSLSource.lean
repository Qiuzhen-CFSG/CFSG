module
public import CFSG.Quasithin.Chapter2.Section05.OrderTwoCore.InnerCentralizerSource
public import CFSG.Quasithin.Chapter2.Section05.OrderTwoCore.SelectedEightSource
public import CFSG.Quasithin.Chapter2.Section05.OrderTwoCore.CosetFusionSource
public import Theory.GroupTheory.FourNormalizerFusion
public import Theory.GroupTheory.ConjugateCentralizerEightFusion
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.EarlyCoreSource
/-!
# Excluding the original order-two core in the inner prime PSL₂ branch

The literal inner quotient makes H=K×⟨t⟩, and the original component and
odd-core argument gives C_G(t)=H. On the selected elementary eight, the
t-class is exactly the four points outside K. Four-normalizers in K and
its conjugates act transitively on the other three points. The original
largest-pair Sylow fixes t, contradicting this four-point action.
Source: Aschbacher--Smith 2.5.21, printed p.565.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z : G}

private theorem mem_zpowers_two {t a : G} (ht : orderOf t=2) :
    a∈zpowers t ↔ a=1 ∨ a=t := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,ht]
  constructor
  · intro ha
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ha
    have hnlt : n<2 := Finset.mem_range.mp hn
    interval_cases n <;> simp
  · rintro (rfl|rfl)
    · exact Finset.mem_image.mpr ⟨0,by decide,by simp⟩
    · exact Finset.mem_image.mpr ⟨1,by decide,by simp⟩

 theorem MathieuSourceSetup.prime_psl_twoCore_card_ne_two
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M=∅)
    (hgen : H=K⊔(S:Subgroup H).map H.subtype)
    (hb : ¬IsBenderModel K) (hstar : H∈gammaStar (Chapter1.He G) M)
    {p : ℕ} [Fact p.Prime]
    (eK : K≃*PSL(2,ZMod p)) (eQ : (H⧸pCore 2 H)≃*PSL(2,ZMod p)) :
    Nat.card (twoCore H)≠2 := by
  intro hcard
  let Y := (S:Subgroup H).map H.subtype
  have hzK := MathieuSourceSetup.inner_central_mark_mem_component_of_core_card_two
    c hG hempty hgen hb hcard (eQ.trans eK.symm)
  obtain ⟨t,ht,htC,hHt,hnot,_,hKfusion,hcoset⟩ :=
    MathieuSourceSetup.linear_core_coset_involution_fusion c hG hempty hgen hb hzK (ZMod p) eK
  have hCt : twoCore H=zpowers t :=
    (eq_of_le_of_card_ge (zpowers_le.mpr htC) (by rw [Nat.card_zpowers,ht,hcard])).symm
  have htY : t∈Y := by
    have he := MathieuSourceSetup.core_eq_sylow_centralizer c hgen
    exact (he ▸ htC).1
  have htZ : t∈centerIn Y := ⟨htY,fun y hy =>
    mem_centralizer_singleton_iff.mp (hHt (map_subtype_le _ hy))⟩
  have hCH : centralizer ({t}:Set G)=H :=
    order_two_core_source_centralizer_eq c hG hempty hgen hb hstar hzK t ht htC htZ hCt
  have hHK : H=K⊔zpowers t := by
    rw [←hCt]
    exact MathieuSourceSetup.inner_quotient_sup_core c hG hempty hgen (eQ.trans eK.symm)
  have havoid (k:G) (hk:k∈K) : ¬IsConj t k := by
    intro hf
    obtain ⟨g,hg⟩ := isConj_iff.mp hf
    have ho : orderOf k=2 := by
      rw [←hg]
      exact (MulAut.conj g).orderOf_eq t |>.trans ht
    exact hnot (hf.trans (hKfusion k hk ho).symm)
  have htK : t∉K := fun hk => havoid t hk (IsConj.refl t)
  obtain ⟨U,L,E,hpair,hUS,_,_,hFY,hFe,hFc,_,hZF,hLF,_⟩ :=
    MathieuSourceSetup.selected_eight_of_core_card_two c hG hempty hgen hb hstar hcard
  let F := E⊔twoCore H
  let : IsElementaryAbelian 2 F := hFe
  have htF : t∈F := (show twoCore H≤F from le_sup_right) htC
  have hFC : F≤centralizer ({t}:Set G) := hFY.trans ((map_subtype_le _).trans hHt)
  have hzF : z∈F := hZF ⟨(c.localSetup hG structural115Input localC129Input_knownSimple).mem_sylow,
    (c.localSetup hG structural115Input localC129Input_knownSimple).central⟩
  obtain ⟨_,P,hP⟩ := largest_pair_normal_two_normalizer_of_source c hG hpair
    (IsElementaryAbelian.isPGroup 2 F) hzF (hLF ▸ inf_le_right)
  have hfix : ∀a∈(P:Subgroup (normalizer (F:Set G))), MulAut.conj (a:G) t=t := by
    intro a ha
    have haU : (a:G)∈U := hP ▸ mem_map_of_mem (normalizer (F:Set G)).subtype ha
    exact mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_singleton_iff.mp (hHt (map_subtype_le _ (hUS haU))))
  have hclass (u:G) (hu:u∈F) : IsConj t u ↔ u∉K := by
    constructor
    · exact fun hf hk => havoid u hk hf
    · intro huK
      have huH : u∈K⊔zpowers t := hHK ▸ map_subtype_le _ (hFY hu)
      have hNK : zpowers t≤normalizer (K:Set G) :=
        (zpowers_le.mpr (show t∈centralizer (K:Set G) from fun k hk =>
          mem_centralizer_singleton_iff.mp (hHt (c.component_le hk)))).trans
            (Subgroup.centralizer_le_normalizer _)
      have huProd : u∈(K:Set G)*(zpowers t:Set G) := by
        rw [←coe_mul_of_right_le_normalizer_left K (zpowers t) hNK]
        exact huH
      obtain ⟨k,hk,a,ha,rfl⟩ := huProd
      change k∈K at hk
      change k*a∈F at hu
      change k*a∉K at huK
      change IsConj t (k*a)
      rcases (mem_zpowers_two ht).mp ha with ha|ha
      · rw [ha,mul_one] at huK
        exact (huK hk).elim
      · rw [ha] at hu huK ⊢
        have hkt : k*t=t*k := mem_centralizer_singleton_iff.mp (hHt (c.component_le hk))
        rw [hkt] at hu ⊢
        apply hcoset k hk
        exact orderOf_eq_prime_iff.mpr
          ⟨elemPow_eq_one_of_isElementaryAbelian _ hu,
            fun he => huK (by rw [hkt,he];exact K.one_mem)⟩
  have hfour (A:Subgroup G) (hAK:A≤K) (hA:IsKleinFour A)
      (a:G) (ha:a∈A) (b:G) (hbA:b∈A) (ha1:a≠1) (hb1:b≠1) :
      ∃n∈K⊓normalizer (A:Set G),MulAut.conj n a=b := by
    let :=hA
    obtain ⟨eN⟩ := MathieuSourceSetup.four_normalizer c
      (MathieuSourceSetup.small_remaining_component c hG hempty hgen hb) A hAK
    exact four_normalizer_fusion_in K A hAK eN a b ha hbA ha1 hb1
  exact elementaryEight_conjugate_centralizers_false K F hFc t htF htK hFC
    (hCH.trans hHK) havoid hclass hfour P hfix
/-- The original prime PSL₂ branch constructs the nonabelian-core crossing,
with the order-two-core exclusion discharged by the selected-eight argument. -/
theorem MathieuSourceSetup.prime_psl_source_core_crossing
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ IsBenderModel K) (hstar : H ∈ gammaStar (Chapter1.He G) M)
    {p : ℕ} [Fact p.Prime] (hp : 7 ≤ p) (hfm : IsFermatOrMersennePrime p)
    (eK : K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p))
    (eQ : (H ⧸ pCore 2 H) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) :
    ∃ t zK x : G, orderOf t = 2 ∧ orderOf zK = 2 ∧ t ∈ twoCore H ∧
      zK ∈ K ∧ x ∈ c.T ∧ x ∉ (S : Subgroup H).map H.subtype ∧
      x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      x ^ 2 ∈ (S : Subgroup H).map H.subtype ∧
      x⁻¹ * t * x = zK ∧ z = t * zK ∧ z ≠ zK ∧ ¬ IsConj t z ∧
      H ≤ centralizer ({t} : Set G) ∧
      ∃ P : Sylow 2 (centralizer ({t} : Set G)),
        (P : Subgroup (centralizer ({t} : Set G))).map (centralizer ({t} : Set G)).subtype =
          (S : Subgroup H).map H.subtype := by
  exact MathieuSourceSetup.prime_psl_large_core_crossing c hG hempty hgen hb hp hfm eK eQ
    (MathieuSourceSetup.two_lt_core_card_of_ne_two c hG hempty hgen hb
      (MathieuSourceSetup.prime_psl_twoCore_card_ne_two c hG hempty hgen hb hstar eK eQ))

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
