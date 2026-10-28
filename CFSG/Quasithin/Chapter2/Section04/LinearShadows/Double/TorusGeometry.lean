module
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.Fitting.Centralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.OddFixedPoints
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
/-!
# Fixed-point geometry of the paired linear torus

A torus with no common fixed point kills the central intersection of two
commuting short blocks. Their Sylow subgroups then form a direct product.
The natural rank-one calculation makes each odd torus factor act freely on
its own Sylow factor, so precisely the two coordinate torus factors can
have nonzero fixed points. An automorphism preserving the torus and Sylow
product permutes these factors. The original noncommuting module mark
excludes interchange and fixes all four factors.

Source: Aschbacher–Smith, proof of 2.4.7, printed p.540. The source adapter
in `TorusGeometrySource` supplies the original paired block and torus data.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter2.LinearDouble
variable {G : Type*} [Group G] [Finite G]

theorem short_center_le_sylow (L : Subgroup G) (hL : ChapterC.IsShort L)
    (P : Sylow 2 L) : center L ≤ (P : Subgroup L) := by
  apply le_trans ?_ (fitting_pCore_le_sylow P)
  rw [←hL.centralizer_blockU]
  exact center_le_centralizer _

theorem commuting_blocks_disjoint (L₁ L₂ R D : Subgroup G)
    (hL₁ : ChapterC.IsShort L₁) (P₁ : Sylow 2 L₁)
    (hP₁ : (P₁ : Subgroup L₁).map L₁.subtype ≤ R)
    (hcomm : L₂ ≤ centralizer (L₁ : Set G)) (hD : D ≤ L₁ ⊔ L₂)
    (hfixed : R ⊓ centralizer (D : Set G) = ⊥) : Disjoint L₁ L₂ := by
  have hmeet : L₁ ⊓ L₂ ≤ R := by
    rintro x ⟨hx₁,hx₂⟩
    have hz : (⟨x,hx₁⟩ : L₁) ∈ center L₁ := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp (hcomm hx₂) y y.property)
    exact hP₁ (mem_map_of_mem L₁.subtype (short_center_le_sylow L₁ hL₁ P₁ hz))
  rw [disjoint_iff]
  apply bot_unique
  rw [←hfixed]
  refine le_inf hmeet ?_
  apply le_centralizer_iff.mp
  apply hD.trans
  exact sup_le ((le_centralizer_iff.mp hcomm).trans (centralizer_le inf_le_right))
    (hcomm.trans (centralizer_le inf_le_left))

theorem short_center_eq_bot_of_fixed_zero (L K R D : Subgroup G)
    (hL : ChapterC.IsShort L) (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype ≤ R)
    (hcomm : K ≤ centralizer (L : Set G)) (hD : D ≤ L ⊔ K)
    (hfixed : R ⊓ centralizer (D : Set G) = ⊥) : center L = ⊥ := by
  apply bot_unique
  intro x hx
  apply Subtype.ext
  change (x : G) = 1
  apply mem_bot.mp
  rw [←hfixed]
  refine ⟨hP (mem_map_of_mem L.subtype (short_center_le_sylow L hL P hx)),?_⟩
  have hzL : (x : G) ∈ centralizer (L : Set G) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val (mem_center_iff.mp hx (⟨y,hy⟩ : L))
  have hzK : (x : G) ∈ centralizer (K : Set G) := le_centralizer_iff.mp hcomm x.property
  have hc : L ⊔ K ≤ centralizer ({(x : G)} : Set G) := by
    apply sup_le <;> intro y hy
    · exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hzL) y hy)
    · exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hzK) y hy)
  exact mem_centralizer_iff.mpr (fun y hy =>
    (mem_centralizer_singleton_iff.mp (hc (hD hy))))

theorem short_odd_sylow_faithful (L D R : Subgroup G)
    (hL : ChapterC.IsShort L) (P : Sylow 2 L)
    (hP : (P : Subgroup L).map L.subtype = R)
    (hDL : D ≤ L) (hodd : Odd (Nat.card D))
    (hDR : D ≤ normalizer (R : Set G)) :
    Function.Injective (R.normalizerMonoidHom.comp (inclusion hDR)) := by
  apply (R.normalizerMonoidHom.comp (inclusion hDR)).ker_eq_bot_iff.mp
  apply bot_unique
  intro x hx
  have hxC : (x : G) ∈ centralizer (R : Set G) := by
    have hh : (⟨x,hDR x.property⟩ : normalizer (R : Set G)) ∈ R.normalizerMonoidHom.ker := hx
    rwa [normalizerMonoidHom_ker] at hh
  have hxU : (⟨x,hDL x.property⟩ : L) ∈ centralizer (ChapterC.blockU L : Set L) := by
    apply mem_centralizer_iff.mpr
    intro u hu
    apply Subtype.ext
    exact mem_centralizer_iff.mp hxC u (hP ▸ mem_map_of_mem L.subtype
      (fitting_pCore_le_sylow P (ChapterC.blockU_le_core hu)))
  have hxQ : (x : G) ∈ (pCore 2 L).map L.subtype :=
    mem_map_of_mem L.subtype (hL.centralizer_blockU ▸ hxU)
  have hdis : Disjoint ((pCore 2 L).map L.subtype) D := by
    obtain ⟨k,hk⟩ := ((pCore_isPGroup (p := 2) (G := L)).map L.subtype).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact (Nat.coprime_two_left.mpr hodd).pow_left k
  exact show x = 1 from Subtype.ext (disjoint_def.mp hdis hxQ x.property)

theorem short_sylow_ne_bot (L : Subgroup G) (hL : ChapterC.IsShort L)
    (P : Sylow 2 L) : (P : Subgroup L).map L.subtype ≠ ⊥ := by
  intro he
  apply hL.blockU_ne_bot
  apply bot_unique
  intro u hu
  apply Subtype.ext
  have hmem := mem_map_of_mem L.subtype
    (fitting_pCore_le_sylow P (ChapterC.blockU_le_core hu))
  rwa [he,mem_bot] at hmem

theorem centerless_sylow_odd_free (L D R : Subgroup G) {n : ℕ}
    (hL : ChapterC.IsL2EvenBlock L n)
    (hcore : pCore 2 L = ChapterC.blockU L) (hZ : center L = ⊥)
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = R)
    (hDL : D ≤ L) (ho : Odd (Nat.card D)) :
    ∀ a ∈ D, ∀ r ∈ R, r ≠ 1 → Commute a r → a = 1 := by
  intro a ha r hr hr1 har
  by_contra ha1
  let A := zpowers a
  have hAD : A ≤ D := zpowers_le.mpr ha
  have hAL := hAD.trans hDL
  have hAo : Odd (Nat.card (A.subgroupOf L)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAL).toEquiv]
    exact ho.of_dvd_nat (card_dvd_of_le hAD)
  have hAn : A.subgroupOf L ≠ ⊥ := by
    intro he
    have ham : (⟨a,hDL ha⟩ : L) ∈ A.subgroupOf L := mem_zpowers a
    rw [he,mem_bot] at ham
    exact ha1 (congrArg Subtype.val ham)
  obtain ⟨u,hu,rfl⟩ := hP ▸ hr
  have huc : u ∈ centralizer (A.subgroupOf L : Set L) := by
    apply mem_centralizer_iff.mpr
    rintro z ⟨k,hk⟩
    apply Subtype.ext
    change (z : G) * (u : G) = (u : G) * (z : G)
    change a ^ k = (z : G) at hk
    rw [←hk]
    exact (har.zpow_left k).eq
  have hucenter := hL.sylow_odd_fixed_le_center hcore P (A.subgroupOf L) hAo hAn ⟨hu,huc⟩
  rw [hZ,mem_bot] at hucenter
  exact hr1 (congrArg Subtype.val hucenter)

omit [Finite G] in
private theorem commuting_sup_decompose (A B : Subgroup G)
    (hc : A ≤ centralizer (B : Set G)) {x : G} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, a*b=x := by
  have hn : B ≤ normalizer (A : Set G) :=
    (le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)
  have hm : x ∈ (A : Set G) * (B : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left _ _ hn]
    exact hx
  exact hm

omit [Finite G] in
private theorem commute_product_components (L K : Subgroup G)
    (hd : Disjoint L K) (hc : L ≤ centralizer (K : Set G))
    (a b : L) (c d : K) (he : Commute ((a:G)*c) ((b:G)*d)) :
    Commute (a:G) (b:G) ∧ Commute (c:G) (d:G) := by
  let f : L × K →* G := L.subtype.noncommCoprod K.subtype
    (fun l k => (hc l.property k k.property).symm)
  have hi : Function.Injective f := mul_injective_of_disjoint hd
  have hh : (a,c)*(b,d) = (b,d)*(a,c) := hi
    ((f.map_mul (a,c) (b,d)).trans (he.eq.trans (f.map_mul (b,d) (a,c)).symm))
  exact ⟨congrArg (fun p : L × K => (p.1:G)) hh,
    congrArg (fun p : L × K => (p.2:G)) hh⟩

omit [Finite G] in
theorem paired_torus_kernel_dichotomy (L₁ L₂ R₁ R₂ D₁ D₂ : Subgroup G)
    (hd : Disjoint L₁ L₂) (hc : L₁ ≤ centralizer (L₂ : Set G))
    (hR₁ : R₁ ≤ L₁) (hR₂ : R₂ ≤ L₂) (hD₁ : D₁ ≤ L₁) (hD₂ : D₂ ≤ L₂)
    (hfree₁ : ∀ a ∈ D₁, ∀ r ∈ R₁, r ≠ 1 → Commute a r → a = 1)
    (hfree₂ : ∀ a ∈ D₂, ∀ r ∈ R₂, r ≠ 1 → Commute a r → a = 1)
    (A : Subgroup G) (hA : A ≤ D₁ ⊔ D₂)
    (hne : (R₁ ⊔ R₂) ⊓ centralizer (A : Set G) ≠ ⊥) : A ≤ D₁ ∨ A ≤ D₂ := by
  obtain ⟨r,hr,hr1⟩ := ((R₁ ⊔ R₂) ⊓ centralizer (A : Set G)).bot_or_exists_ne_one.resolve_left hne
  obtain ⟨r₁,hr₁,r₂,hr₂,rfl⟩ := commuting_sup_decompose R₁ R₂
    (hR₁.trans (hc.trans (centralizer_le hR₂))) hr.1
  have ha (a : G) (ha : a ∈ A) : ∃ a₁ ∈ D₁, ∃ a₂ ∈ D₂,
      a₁*a₂=a ∧ Commute a₁ r₁ ∧ Commute a₂ r₂ := by
    obtain ⟨a₁,ha₁,a₂,ha₂,he⟩ := commuting_sup_decompose D₁ D₂
      (hD₁.trans (hc.trans (centralizer_le hD₂))) (hA ha)
    have hh := commute_product_components L₁ L₂ hd hc
      ⟨a₁,hD₁ ha₁⟩ ⟨r₁,hR₁ hr₁⟩ ⟨a₂,hD₂ ha₂⟩ ⟨r₂,hR₂ hr₂⟩
      (show Commute (a₁*a₂) (r₁*r₂) by rw [he]; exact mem_centralizer_iff.mp hr.2 a ha)
    exact ⟨a₁,ha₁,a₂,ha₂,he,hh⟩
  by_cases h₁ : r₁ = 1
  · have h₂ : r₂ ≠ 1 := by simpa only [h₁,one_mul] using hr1
    left
    intro a haA
    obtain ⟨a₁,ha₁,a₂,ha₂,he,_,hcomm⟩ := ha a haA
    rw [hfree₂ a₂ ha₂ r₂ hr₂ h₂ hcomm,mul_one] at he
    exact he ▸ ha₁
  · right
    intro a haA
    obtain ⟨a₁,ha₁,a₂,ha₂,he,hcomm,_⟩ := ha a haA
    rw [hfree₁ a₁ ha₁ r₁ hr₁ h₁ hcomm,one_mul] at he
    exact he ▸ ha₂

omit [Finite G] in
theorem paired_torus_fixed_space (R₁ R₂ D₂ : Subgroup G)
    (hc : R₁ ≤ centralizer (R₂ : Set G))
    (hRD : R₁ ≤ centralizer (D₂ : Set G)) (hD₂ : D₂ ≠ ⊥)
    (hfree₂ : ∀ a ∈ D₂, ∀ r ∈ R₂, r ≠ 1 → Commute a r → a = 1) :
    (R₁ ⊔ R₂) ⊓ centralizer (D₂ : Set G) = R₁ := by
  apply le_antisymm _ (le_inf le_sup_left hRD)
  rintro r ⟨hr,hfix⟩
  obtain ⟨r₁,hr₁,r₂,hr₂,rfl⟩ := commuting_sup_decompose R₁ R₂ hc hr
  have hr₂fix : r₂ ∈ centralizer (D₂ : Set G) := by
    have hh := (centralizer (D₂ : Set G)).mul_mem
      ((centralizer (D₂ : Set G)).inv_mem (hRD hr₁)) hfix
    simpa only [inv_mul_cancel_left] using hh
  have hr₂one : r₂ = 1 := by
    by_contra hr₂ne
    obtain ⟨a,ha,ha1⟩ := D₂.bot_or_exists_ne_one.resolve_left hD₂
    exact ha1 (hfree₂ a ha r₂ hr₂ hr₂ne (mem_centralizer_iff.mp hr₂fix a ha))
  simpa only [hr₂one,mul_one] using hr₁

omit [Finite G] in
private theorem map_centralizer_equiv (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom = centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · rintro _ ⟨a,ha,rfl⟩
    apply mem_centralizer_iff.mpr
    rintro _ ⟨b,hb,rfl⟩
    exact (e.map_mul b a).symm.trans ((congrArg e (mem_centralizer_iff.mp ha b hb)).trans
      (e.map_mul a b))
  · intro x hx
    refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
    apply mem_centralizer_iff.mpr
    intro a ha
    apply e.injective
    simpa only [e.map_mul,e.apply_symm_apply] using
      mem_centralizer_iff.mp hx (e a) (mem_map_of_mem e.toMonoidHom ha)

omit [Finite G] in
private theorem map_fixed_subgroup (R A : Subgroup G) (e : G ≃* G) :
    (R ⊓ centralizer (A : Set G)).map e.toMonoidHom =
      R.map e.toMonoidHom ⊓ centralizer (A.map e.toMonoidHom : Set G) := by
  rw [map_inf _ _ _ e.injective,map_centralizer_equiv]

theorem torus_factor_image (R D D₁ D₂ : Subgroup G)
    (hD₁ : D₁ ≤ D) (hD₂ : D₂ ≤ D) (hcard : Nat.card D₁ = Nat.card D₂)
    (hC₁ : R ⊓ centralizer (D₁ : Set G) ≠ ⊥)
    (hC₂ : R ⊓ centralizer (D₂ : Set G) ≠ ⊥)
    (hmax : ∀ A : Subgroup G, A ≤ D → R ⊓ centralizer (A : Set G) ≠ ⊥ → A ≤ D₁ ∨ A ≤ D₂)
    (e : G ≃* G) (hR : R.map e.toMonoidHom = R) (hD : D.map e.toMonoidHom = D) :
    (D₁.map e.toMonoidHom = D₁ ∨ D₁.map e.toMonoidHom = D₂) ∧
      (D₂.map e.toMonoidHom = D₁ ∨ D₂.map e.toMonoidHom = D₂) := by
  have hh (A : Subgroup G) (hAD : A ≤ D) (hAn : R ⊓ centralizer (A : Set G) ≠ ⊥)
      (hc₁ : Nat.card A = Nat.card D₁) (hc₂ : Nat.card A = Nat.card D₂) :
      A.map e.toMonoidHom = D₁ ∨ A.map e.toMonoidHom = D₂ := by
    have hmap : R ⊓ centralizer (A.map e.toMonoidHom : Set G) ≠ ⊥ := by
      rw [←hR,←map_fixed_subgroup]
      exact fun hz => hAn (((R ⊓ centralizer (A : Set G)).map_eq_bot_iff_of_injective e.injective).mp hz)
    rcases hmax _ ((map_mono hAD).trans_eq hD) hmap with h₁ | h₂
    · exact Or.inl (eq_of_le_of_card_ge h₁ (by rw [card_map_of_injective e.injective,hc₁]))
    · exact Or.inr (eq_of_le_of_card_ge h₂ (by rw [card_map_of_injective e.injective,hc₂]))
  exact ⟨hh D₁ hD₁ hC₁ rfl hcard, hh D₂ hD₂ hC₂ hcard.symm rfl⟩

theorem fixed_torus_factors_of_noncommuting (R D R₁ R₂ D₁ D₂ U : Subgroup G)
    (hR₁ : R₁ ≠ ⊥) (hR₂ : R₂ ≠ ⊥) (hU : U ≤ R₁)
    (hcomm : R₂ ≤ centralizer (R₁ : Set G))
    (hD₁ : D₁ ≤ D) (hD₂ : D₂ ≤ D) (hcard : Nat.card D₁ = Nat.card D₂)
    (hDne : D₁ ≠ D₂)
    (hC₁ : R ⊓ centralizer (D₁ : Set G) = R₂)
    (hC₂ : R ⊓ centralizer (D₂ : Set G) = R₁)
    (hmax : ∀ A : Subgroup G, A ≤ D → R ⊓ centralizer (A : Set G) ≠ ⊥ → A ≤ D₁ ∨ A ≤ D₂)
    (x : G) (hxR : x ∈ normalizer (R : Set G)) (hxD : x ∈ normalizer (D : Set G))
    (hnc : ¬ U.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U : Set G)) :
    x ∈ normalizer (D₁ : Set G) ∧ x ∈ normalizer (D₂ : Set G) ∧
      x ∈ normalizer (R₁ : Set G) ∧ x ∈ normalizer (R₂ : Set G) := by
  let e := MulAut.conj x⁻¹
  have hRmap : R.map e.toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem hxR)
  have hDmap : D.map e.toMonoidHom = D :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (D : Set G)).inv_mem hxD)
  have hp := torus_factor_image R D D₁ D₂ hD₁ hD₂ hcard
    (hC₁ ▸ hR₂) (hC₂ ▸ hR₁) hmax e hRmap hDmap
  have h₂ : D₂.map e.toMonoidHom = D₂ := by
    rcases hp.2 with he | he
    · have hr : R₁.map e.toMonoidHom = R₂ := by
        rw [←hC₂,map_fixed_subgroup,hRmap,he,hC₁]
      exact False.elim (hnc ((map_mono hU).trans (hr.le.trans
        (hcomm.trans (centralizer_le hU)))))
    · exact he
  have h₁ : D₁.map e.toMonoidHom = D₁ := by
    rcases hp.1 with he | he
    · exact he
    · exact False.elim (hDne (map_injective e.injective (he.trans h₂.symm)))
  have hr₁ : R₁.map e.toMonoidHom = R₁ := by
    rw [←hC₂,map_fixed_subgroup,hRmap,h₂,hC₂]
  have hr₂ : R₂.map e.toMonoidHom = R₂ := by
    rw [←hC₁,map_fixed_subgroup,hRmap,h₁,hC₁]
  have hnormal (A : Subgroup G) (hA : A.map e.toMonoidHom = A) : x ∈ normalizer (A : Set G) := by
    have hinv : x⁻¹ ∈ normalizer (A : Set G) := mem_normalizer_iff_map_conj_eq.mpr hA
    simpa only [inv_inv] using (normalizer (A : Set G)).inv_mem hinv
  exact ⟨hnormal D₁ h₁,hnormal D₂ h₂,hnormal R₁ hr₁,hnormal R₂ hr₂⟩

end CFSG.Quasithin.Chapter2.LinearDouble
