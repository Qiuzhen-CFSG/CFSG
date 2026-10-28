module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.SetupSource
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.InternalSylow
public import CFSG.Quasithin.ChapterC.Section06.NaturalCoordinates
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# Initial Borel tori for two commuting linear blocks

The two internal rank-one parameter maps split the actual Thompson group as
R = R₁R₂C, where C centralizes both blocks and R. The block Sylow normalizers
normalize R; uniqueness of the maximal overgroup of the source Sylow group
identifies them with M∩Lᵢ. Schur–Zassenhaus then supplies cyclic complements
Dᵢ of order 2ⁿ−1. Their commuting product is direct because block centers
are two-groups. Hall conjugacy gives the source normalizer supplement.

All factors retain their literal embeddings in the original ambient group.
The central factor C remains available to the subsequent fixed-space argument.

Source: Aschbacher–Smith, the double linear-block argument in §2.4,
printed pp.539–540, using C.5.3–6 and the original Borel construction of 2.4.1.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Double
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

omit [Finite G] in
private theorem centralizer_join (A B : Subgroup G) :
    centralizer ((A ⊔ B : Subgroup G) : Set G) = centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  apply le_antisymm
  · exact le_inf (centralizer_le (show A ≤ A ⊔ B from le_sup_left))
      (centralizer_le (show B ≤ A ⊔ B from le_sup_right))
  · exact le_centralizer_iff.mpr
      (sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right))

omit [Finite G] in
private theorem paired_internal_decomposition
    {S L₁ L₂ : Subgroup G} {F₁ F₂ : Type*} [Field F₁] [Field F₂]
    (h₁ : RankOne.Setup S L₁ F₁) (h₂ : RankOne.Setup S L₂ F₂)
    (hi₁ : h₁.coordinates.IsInternal) (hi₂ : h₂.coordinates.IsInternal)
    (hc : L₂ ≤ centralizer (L₁ : Set G))
    (hq : ChapterB.baumann S ⊓ centralizer ((RankOne.U L₁ ⊔ RankOne.U L₂ : Subgroup G) : Set G) =
      (RankOne.U L₁ ⊔ RankOne.U L₂) ⊔
        (ChapterB.baumann S ⊓ centralizer ((L₁ ⊔ L₂ : Subgroup G) : Set G))) :
    ChapterB.baumann S = ((ChapterB.baumann S ⊓ L₁) ⊔ (ChapterB.baumann S ⊓ L₂)) ⊔
      (ChapterB.baumann S ⊓ centralizer ((L₁ ⊔ L₂ : Subgroup G) : Set G)) := by
  let B := ChapterB.baumann S
  let E := ((B ⊓ L₁) ⊔ (B ⊓ L₂)) ⊔ (B ⊓ centralizer ((L₁ ⊔ L₂ : Subgroup G) : Set G))
  apply le_antisymm _ (sup_le (sup_le inf_le_left inf_le_left) inf_le_left)
  intro g hg
  obtain ⟨t₁,ht₁,hp₁⟩ := hi₁ ⟨g,hg⟩
  let a : B := t₁⁻¹ * ⟨g,hg⟩
  have ha : (a : G) ∈ centralizer (RankOne.U L₁ : Set G) := by
    apply (h₁.coordinates.parameter_kernel a).mp
    simp only [a,map_mul,map_inv,hp₁,inv_mul_cancel]
  obtain ⟨t₂,ht₂,hp₂⟩ := hi₂ a
  let b : B := t₂⁻¹ * a
  have hb₂ : (b : G) ∈ centralizer (RankOne.U L₂ : Set G) := by
    apply (h₂.coordinates.parameter_kernel b).mp
    simp only [b,map_mul,map_inv,hp₂,inv_mul_cancel]
  have ht₂C : (t₂ : G) ∈ centralizer (RankOne.U L₁ : Set G) :=
    (hc.trans (centralizer_le (map_subtype_le _))) ht₂
  have hb₁ : (b : G) ∈ centralizer (RankOne.U L₁ : Set G) :=
    (centralizer (RankOne.U L₁ : Set G)).mul_mem
      ((centralizer (RankOne.U L₁ : Set G)).inv_mem ht₂C) ha
  have hbQ : (b : G) ∈ B ⊓ centralizer ((RankOne.U L₁ ⊔ RankOne.U L₂ : Subgroup G) : Set G) := by
    refine ⟨b.property,?_⟩
    change (b : G) ∈ centralizer ((RankOne.U L₁ ⊔ RankOne.U L₂ : Subgroup G) : Set G)
    rw [centralizer_join]
    exact ⟨hb₁,hb₂⟩
  have hQE : ((RankOne.U L₁ ⊔ RankOne.U L₂) ⊔
      (B ⊓ centralizer ((L₁ ⊔ L₂ : Subgroup G) : Set G))) ≤ E :=
    sup_le (sup_le
      ((le_inf h₁.module_le (map_subtype_le _)).trans (le_sup_left.trans le_sup_left))
      ((le_inf h₂.module_le (map_subtype_le _)).trans (le_sup_right.trans le_sup_left))) le_sup_right
  have hbE : (b : G) ∈ E := hQE (hq ▸ hbQ)
  have ht₁E : (t₁ : G) ∈ E := (show B ⊓ L₁ ≤ E from le_sup_left.trans le_sup_left) ⟨t₁.property,ht₁⟩
  have ht₂E : (t₂ : G) ∈ E := (show B ⊓ L₂ ≤ E from le_sup_right.trans le_sup_left) ⟨t₂.property,ht₂⟩
  have he := E.mul_mem ht₁E (E.mul_mem ht₂E hbE)
  simpa only [b,a,coe_mul,coe_inv,mul_inv_cancel_left] using he

/-- The source retains its central factor until the later torus fixed-space
argument. Both Sylow intersections are already the literal intersections
with the original S. -/
theorem source_decomposition
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    {M₀ : Subgroup G} {n : ℕ} (c : DoubleLinearSourceSetup d M₀ n)
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀) (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L₁ := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    let C := R ⊓ centralizer ((L₁ ⊔ c.second : Subgroup G) : Set G)
    R = ((R ⊓ L₁) ⊔ (R ⊓ c.second)) ⊔ C ∧
      R ⊓ L₁ = S ⊓ L₁ ∧ R ⊓ c.second = S ⊓ c.second ∧
      C ≤ centralizer (R : Set G) ∧
      (∃ P : Sylow 2 L₁, (P : Subgroup L₁).map L₁.subtype = R ⊓ L₁) ∧
      (∃ P : Sylow 2 c.second, (P : Subgroup c.second).map c.second.subtype = R ⊓ c.second) := by
  let := c.field₁_field
  let := c.field₂_field
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L₁ := d.block.map d.H.subtype
  let B := ChapterB.baumann S
  let U := RankOne.U L₁ ⊔ RankOne.U c.second
  let C := B ⊓ centralizer ((L₁ ⊔ c.second : Subgroup G) : Set G)
  have hBR := (c.core_pair T hST.le hSM hMT hi).1
  have hex : ∃ t : M₀, (t : G) ∈ S ∧ L₁.conjBy (t : G) = c.second := by
    obtain ⟨t,ht,he⟩ := c.exchange
    exact ⟨⟨t,hSM ht⟩,ht,he⟩
  have hH : d.H = (L₁ ⊔ c.second) ⊔ S := by rw [c.join,d.ambient_L0_sup_sylow]
  have hSN : S ≤ normalizer ((L₁ ⊔ c.second : Subgroup G) : Set G) :=
    c.join.symm ▸ (c.original.R_le_H.trans c.original.normalizes_residual)
  have hp := c.marked₁.two_block_source_product c.marked₂ c.commutes d.H M₀ S hSM
    c.original.R_normal hSN hH (d.no_common_normal_of_index_two T hST.le M₀ hSM hMT hi)
    c.x c.x_mem hi c.permutes hex c.noncommuting
  have hdec := paired_internal_decomposition c.marked₁ c.marked₂
    (c.marked₁.internal_of_linear hL) (c.marked₂.internal_of_linear c.second_type) c.commutes hp.1
  have hCcore : C ≤ twoCore d.H := by
    have hq := (d.core_source hG T hST).2.1
    change B ⊓ centralizer ((L₁ ⊔ c.second : Subgroup G) : Set G) ≤ _
    rw [c.join]
    exact (inf_le_inf inf_le_left le_rfl).trans (le_sup_right.trans_eq hq.symm)
  let : IsElementaryAbelian 2 (twoCore d.H) := (d.core_source hG T hST).2.2.2.1
  have hCC : C ≤ centralizer (C : Set G) := hCcore.trans
    ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hCcore))
  have hCB : C ≤ centralizer (B : Set G) := by
    apply le_centralizer_iff.mp
    change ChapterB.baumann S ≤ centralizer (C : Set G)
    rw [hdec]
    refine sup_le (sup_le ?_ ?_) hCC
    · exact inf_le_right.trans (le_centralizer_iff.mp
        (inf_le_right.trans (centralizer_le (show L₁ ≤ L₁ ⊔ c.second from le_sup_left))))
    · exact inf_le_right.trans (le_centralizer_iff.mp
        (inf_le_right.trans (centralizer_le (show c.second ≤ L₁ ⊔ c.second from le_sup_right))))
  have h₁ := c.marked₁.source_sylow_intersection c.original.R_twoGroup
  have h₂ := c.marked₂.source_sylow_intersection c.original.R_twoGroup
  obtain ⟨P₁,hP₁⟩ := c.marked₁.source_sylow_block c.original.R_twoGroup
  obtain ⟨P₂,hP₂⟩ := c.marked₂.source_sylow_block c.original.R_twoGroup
  simpa only [S,L₁,B,C,hBR] using
    (show B = ((B ⊓ L₁) ⊔ (B ⊓ c.second)) ⊔ C ∧ B ⊓ L₁ = S ⊓ L₁ ∧
      B ⊓ c.second = S ⊓ c.second ∧ C ≤ centralizer (B : Set G) ∧
      (∃ P : Sylow 2 L₁, (P : Subgroup L₁).map L₁.subtype = B ⊓ L₁) ∧
      (∃ P : Sylow 2 c.second, (P : Subgroup c.second).map c.second.subtype = B ⊓ c.second)
      from ⟨hdec,h₁,h₂,hCB,⟨P₁,hP₁⟩,⟨P₂,hP₂⟩⟩)

open scoped MatrixGroups
open Matrix.SpecialLinearGroup

private theorem sylow_normalizer_eq_intersection
    {L : Subgroup G} {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    (P : Sylow 2 L) (hPM : (P : Subgroup L).map L.subtype ≤ M)
    (houtside : ¬ L ≤ M)
    (hNM : (normalizer (P : Set L)).map L.subtype ≤ M) :
    normalizer (P : Set L) = M.subgroupOf L := by
  obtain ⟨_,_,F,_,_,hF,_,τ,⟨m⟩,_⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q : L →* SL(2,F) := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    ext x
    exact m.quotientIso.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  exact le_antisymm (map_le_iff_le_comap.mp hNM)
    (proper_overgroup_le_sylow_normalizer_of_two_kernel q hq P
      (hk ▸ pCore_isPGroup.le_sylow_of_normal P) _ (map_le_iff_le_comap.mp hPM)
      (fun he => houtside (subgroupOf_eq_top.mp he)))

private theorem source_normalizer_le
    (d : MinimalBlockSetup M) {n : ℕ}
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (R : Subgroup G) (hSR : (d.S : Subgroup d.H).map d.H.subtype ≤ normalizer (R : Set G))
    (P : Sylow 2 (d.block.map d.H.subtype))
    (hP : (P : Subgroup (d.block.map d.H.subtype)).map (d.block.map d.H.subtype).subtype =
      R ⊓ d.block.map d.H.subtype) :
    normalizer (R : Set G) ⊓ d.H ≤ M := by
  let L := d.block.map d.H.subtype
  obtain ⟨_,_,F,_,_,hF,_,τ,⟨m⟩,_⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q : L →* SL(2,F) := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  let N := (normalizer (R : Set G)).subgroupOf d.H
  have hN : N ≠ ⊤ := by
    intro he
    have hHN : d.H ≤ normalizer (R : Set G) := subgroupOf_eq_top.mp he
    have hLN : L ≤ normalizer ((R ⊓ L : Subgroup G) : Set G) :=
      (le_inf ((map_subtype_le _).trans hHN) L.le_normalizer).trans inf_normalizer_le_normalizer_inf
    have htop : (normalizer ((R ⊓ L : Subgroup G) : Set G)).subgroupOf L = ⊤ :=
      subgroupOf_eq_top.mpr hLN
    rw [← hP,subgroupOf_normalizer_eq (map_subtype_le _)] at htop
    simp only [subgroupOf,comap_map_eq_self_of_injective
      (d.block.map d.H.subtype).subtype_injective,P.coe_coe] at htop
    exact sylow_normalizer_ne_top_of_surjective q hq P htop
  have hSB : (d.S : Subgroup d.H) ≤ M.subgroupOf d.H := by
    intro s hs
    exact d.full_pair.1.1.2.1 (mem_map_of_mem d.H.subtype hs)
  have hSN : (d.S : Subgroup d.H) ≤ N := by
    intro s hs
    exact hSR (mem_map_of_mem d.H.subtype hs)
  have hNM := d.minimal_parabolic.1.le_maximal
    ⟨hSB,d.intersection_maximal.covBy_top⟩ hSN (lt_top_iff_ne_top.mpr hN)
  rintro g ⟨hg,hgH⟩
  exact hNM (show (⟨g,hgH⟩ : d.H) ∈ N from hg)

omit [Finite G] in
private theorem normalizes_of_paired_decomposition
    {R L₁ L₂ C : Subgroup G} (hdec : R = ((R ⊓ L₁) ⊔ (R ⊓ L₂)) ⊔ C)
    (hc : L₁ ≤ centralizer (L₂ : Set G)) (hC : C ≤ centralizer (L₁ : Set G)) :
    normalizer ((R ⊓ L₁ : Subgroup G) : Set G) ⊓ L₁ ≤ normalizer (R : Set G) := by
  conv_rhs => rw [hdec]
  apply (le_inf ?_ ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · apply (le_inf inf_le_left ?_).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
    exact inf_le_right.trans (hc.trans ((centralizer_le inf_le_right).trans (Subgroup.centralizer_le_normalizer _)))
  · exact inf_le_right.trans ((le_centralizer_iff.mp hC).trans (Subgroup.centralizer_le_normalizer _))

/-- Both literal block intersections are their Sylow normalizers. -/
theorem source_borels
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    {M₀ : Subgroup G} {n : ℕ} (c : DoubleLinearSourceSetup d M₀ n)
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀) (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L₁ := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    (∃ P : Sylow 2 L₁, (P : Subgroup L₁).map L₁.subtype = R ⊓ L₁ ∧
      normalizer (P : Set L₁) = M.subgroupOf L₁) ∧
    (∃ P : Sylow 2 c.second, (P : Subgroup c.second).map c.second.subtype = R ⊓ c.second ∧
      normalizer (P : Set c.second) = M.subgroupOf c.second) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L₁ := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let C := R ⊓ centralizer ((L₁ ⊔ c.second : Subgroup G) : Set G)
  obtain ⟨hdec,h₁,h₂,hC,⟨P₁,hP₁⟩,⟨P₂,hP₂⟩⟩ := source_decomposition d hG T hST c hL hSM hMT hi
  have hSR : S ≤ normalizer (R : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Stellmacher.elementaryAbelianMaxJ S).map (MulAut.conj s).toMonoidHom = _
    rw [←Stellmacher.elementaryAbelianMaxJ_map_equiv,MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hs)]
  have hNM := source_normalizer_le d hL R hSR P₁ hP₁
  have hSM' : S ≤ M := d.full_pair.1.1.2.1
  have h₁N : (normalizer (P₁ : Set L₁)).map L₁.subtype ≤ normalizer (R : Set G) := by
    apply (le_inf ?_ (map_subtype_le _)).trans
      (normalizes_of_paired_decomposition hdec (le_centralizer_iff.mp c.commutes)
        (inf_le_right.trans (centralizer_le (show L₁ ≤ L₁ ⊔ c.second from le_sup_left))))
    rw [← hP₁]
    exact (P₁ : Subgroup L₁).le_normalizer_map L₁.subtype
  have hdec' : R = ((R ⊓ c.second) ⊔ (R ⊓ L₁)) ⊔ C := by
    exact hdec.trans (congrArg (fun A : Subgroup G => A ⊔ C) (sup_comm _ _))
  have h₂N : (normalizer (P₂ : Set c.second)).map c.second.subtype ≤ normalizer (R : Set G) := by
    apply (le_inf ?_ (map_subtype_le _)).trans
      (normalizes_of_paired_decomposition hdec'
        c.commutes (inf_le_right.trans (centralizer_le (show c.second ≤ L₁ ⊔ c.second from le_sup_right))))
    rw [← hP₂]
    exact (P₂ : Subgroup c.second).le_normalizer_map c.second.subtype
  have h₂H : c.second ≤ d.H := le_sup_right.trans (c.join.le.trans (map_subtype_le _))
  have h₂out : ¬ c.second ≤ M := by
    intro hh
    obtain ⟨s,hs,he⟩ := c.exchange
    have hh' := map_mono (f := (MulAut.conj s⁻¹).toMonoidHom) hh
    have hm := mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer (M.inv_mem (hSM' hs)))
    change c.second.conjBy s⁻¹ ≤ M.conjBy s⁻¹ at hh'
    change M.conjBy s⁻¹ = M at hm
    rw [← he,conjBy_inv,hm] at hh'
    exact d.outside hh'
  refine ⟨⟨P₁,hP₁,?_⟩,⟨P₂,hP₂,?_⟩⟩
  · exact sylow_normalizer_eq_intersection hL P₁ (hP₁ ▸ h₁ ▸ inf_le_left.trans hSM')
      d.outside ((le_inf h₁N ((map_subtype_le _).trans (map_subtype_le _))).trans hNM)
  · exact sylow_normalizer_eq_intersection c.second_type P₂ (hP₂ ▸ h₂ ▸ inf_le_left.trans hSM')
      h₂out ((le_inf h₂N ((map_subtype_le _).trans h₂H)).trans hNM)

/-- One of the two original cyclic Borel complements. All subgroups are
retained in the source ambient group. -/
structure BorelTorus (M R L : Subgroup G) (n : ℕ) where
  sylow : Sylow 2 L
  sylow_eq : (sylow : Subgroup L).map L.subtype = R ⊓ L
  torus : Subgroup G
  le_intersection : torus ≤ M ⊓ L
  odd : Odd (Nat.card torus)
  cyclic : IsCyclic torus
  card : Nat.card torus = 2^n - 1
  nontrivial : torus ≠ ⊥
  normalizes_sylow : torus ≤ normalizer ((R ⊓ L : Subgroup G) : Set G)
  sylow_sup_torus : (R ⊓ L) ⊔ torus = M ⊓ L

private theorem exists_borel_torus
    {R L : Subgroup G} {n : ℕ} (hL : ChapterC.IsL2EvenBlock L n)
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = R ⊓ L)
    (hB : normalizer (P : Set L) = M.subgroupOf L) :
    Nonempty (BorelTorus M R L n) := by
  let B := M.subgroupOf L
  have hPB : (P : Subgroup L) ≤ B := by
    change (P : Subgroup L) ≤ M.subgroupOf L
    rw [←hB]
    exact le_normalizer
  let Q := P.subtype hPB
  have hBN : B ≤ normalizer ((P : Subgroup L) : Set L) := by
    simpa only [P.coe_coe] using hB.ge
  let : (Q : Subgroup B).Normal := (normal_subgroupOf_iff_le_normalizer hPB).mpr hBN
  obtain ⟨E,hE⟩ := exists_right_complement'_of_coprime Q.card_coprime_index
  let D := E.map B.subtype
  have hDodd : Odd (Nat.card D) := by
    rw [card_map_of_injective B.subtype_injective,←hE.symm.index_eq_card]
    exact Nat.not_even_iff_odd.mp (fun h => Q.not_dvd_index (even_iff_two_dvd.mp h))
  have hgen : (P : Subgroup L) ⊔ D = B := by
    have he := congrArg (Subgroup.map B.subtype) hE.sup_eq_top
    simpa only [Subgroup.map_sup,Q,Sylow.coe_subtype,map_subgroupOf_eq_of_le hPB,
      ←MonoidHom.range_eq_map,range_subtype] using he
  have hdis : Disjoint (P : Subgroup L) D := by
    have hd := disjoint_map B.subtype_injective hE.disjoint
    simpa only [Q,Sylow.coe_subtype,map_subgroupOf_eq_of_le hPB] using hd
  have hDN : D ≤ normalizer ((P : Subgroup L) : Set L) :=
    (map_subtype_le _).trans hBN
  obtain ⟨hn,_,F,_,_,hF,_,τ,⟨m⟩,_⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q : L →* SL(2,F) := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    ext x
    exact m.quotientIso.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  obtain ⟨e⟩ := sylow_normalizer_complement_equiv_units q hq P
    (hk ▸ pCore_isPGroup.le_sylow_of_normal P) D hDN hdis (hgen.trans hB.symm)
  have hcyc : IsCyclic D := isCyclic_of_injective e.toMonoidHom e.injective
  have hc : Nat.card D = 2^n - 1 := by rw [Nat.card_congr e.toEquiv,Nat.card_units,hF]
  have hne : D ≠ ⊥ := by
    intro he
    have hlarge : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by decide) (by omega)
    rw [he,Nat.card_eq_fintype_card] at hc
    norm_num at hc
    omega
  let D₀ := D.map L.subtype
  have hc₀ : Nat.card D₀ = Nat.card D := card_map_of_injective L.subtype_injective
  have hB₀ : B.map L.subtype = M ⊓ L := by
    change (M.comap L.subtype).map L.subtype = M ⊓ L
    rw [map_comap_eq,range_subtype,inf_comm]
  have hgen₀ : (R ⊓ L) ⊔ D₀ = M ⊓ L := by
    have he := congrArg (Subgroup.map L.subtype) hgen
    simpa only [Subgroup.map_sup,hP,hB₀] using he
  refine ⟨{
    sylow := P
    sylow_eq := hP
    torus := D₀
    le_intersection := hB₀ ▸ map_mono (map_subtype_le E)
    odd := hc₀ ▸ hDodd
    cyclic := ?_
    card := hc₀.trans hc
    nontrivial := ?_
    normalizes_sylow := ?_
    sylow_sup_torus := hgen₀ }⟩
  · let := hcyc
    let eD := D.equivMapOfInjective L.subtype L.subtype_injective
    exact isCyclic_of_surjective eD.toMonoidHom eD.surjective
  · intro he
    exact hne ((map_injective L.subtype_injective) (he.trans (map_bot L.subtype).symm))
  · rw [←hP]
    exact (map_mono hDN).trans ((P : Subgroup L).le_normalizer_map L.subtype)

/-- The initial paired Borel torus, before adjoining an outside conjugate
or proving that its fixed subgroup on R is trivial. -/
structure PairedBorelData (M S R L₁ L₂ H : Subgroup G) (n : ℕ) where
  first : BorelTorus M R L₁ n
  second : BorelTorus M R L₂ n
  commutes : first.torus ≤ centralizer (second.torus : Set G)
  disjoint : Disjoint first.torus second.torus
  first_intersection : (first.torus ⊔ second.torus) ⊓ L₁ = first.torus
  second_intersection : (first.torus ⊔ second.torus) ⊓ L₂ = second.torus
  normalizes_R : first.torus ⊔ second.torus ≤ normalizer (R : Set G)
  sylow_normalizes : S ≤ normalizer ((R ⊔ (first.torus ⊔ second.torus) : Subgroup G) : Set G)
  supplement : H = (L₁ ⊔ L₂) ⊔ (S ⊓ normalizer ((first.torus ⊔ second.torus : Subgroup G) : Set G))

@[expose] def PairedBorelData.torus {S R L₁ L₂ H : Subgroup G} {n : ℕ}
    (b : PairedBorelData M S R L₁ L₂ H n) : Subgroup G := b.first.torus ⊔ b.second.torus

omit [Finite G] in
/-- The multiplication map realizes the original torus as a direct product. -/
theorem PairedBorelData.direct {S R L₁ L₂ H : Subgroup G} {n : ℕ}
    (b : PairedBorelData M S R L₁ L₂ H n) :
    ∃ e : b.first.torus × b.second.torus ≃* b.torus,
      ∀ a d, (e (a,d) : G) = (a : G) * (d : G) :=
  exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ b.disjoint b.commutes


private theorem odd_torus_disjoint_commuting_block
    {L K D : Subgroup G} (hL : ChapterC.IsShort L)
    (P : Sylow 2 L) (hDL : D ≤ L) (ho : Odd (Nat.card D))
    (hc : K ≤ centralizer (L : Set G)) : Disjoint D K := by
  let A := (P : Subgroup L).map L.subtype
  have hp : IsPGroup 2 A := P.isPGroup'.map L.subtype
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  have hd : Disjoint D A := disjoint_of_coprime_natCard (by
    rw [hk]
    exact (Nat.coprime_two_left.mpr ho).symm.pow_right k)
  apply disjoint_def.mpr
  intro x hxD hxK
  apply disjoint_def.mp hd hxD
  let y : L := ⟨x,hDL hxD⟩
  have hy : y ∈ centralizer (ChapterC.blockU L : Set L) := by
    intro z hz
    apply Subtype.ext
    exact hc hxK z.val z.property
  have hyP : y ∈ (P : Subgroup L) :=
    (pCore_isPGroup.le_sylow_of_normal P) (hL.centralizer_blockU ▸ hy)
  exact mem_map_of_mem L.subtype hyP

omit [Finite G] in
private theorem join_inf_eq_of_commuting
    {A B L : Subgroup G} (hAL : A ≤ L) (hBL : Disjoint B L)
    (hc : A ≤ centralizer (B : Set G)) : (A ⊔ B) ⊓ L = A := by
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B
    (hBL.symm.mono hAL le_rfl) hc
  apply le_antisymm _ (le_inf le_sup_left hAL)
  rintro g ⟨hg,hgL⟩
  obtain ⟨⟨a,b⟩,hab⟩ := e.surjective ⟨g,hg⟩
  have hab' : (a : G) * (b : G) = g := (he a b).symm.trans (congrArg Subtype.val hab)
  have hbL : (b : G) ∈ L := by
    have hm := L.mul_mem (L.inv_mem (hAL a.property)) hgL
    simpa only [← hab',inv_mul_cancel_left] using hm
  have hb1 := disjoint_def.mp hBL b.property hbL
  rw [hb1,mul_one] at hab'
  exact hab' ▸ a.property

private theorem pair_borel_normalizations
    {S R L₁ L₂ : Subgroup G} {n : ℕ}
    (b₁ : BorelTorus M R L₁ n) (b₂ : BorelTorus M R L₂ n)
    (hc : L₂ ≤ centralizer (L₁ : Set G))
    (hdec : R = ((R ⊓ L₁) ⊔ (R ⊓ L₂)) ⊔ (R ⊓ centralizer ((L₁ ⊔ L₂ : Subgroup G) : Set G)))
    (hSM : S ≤ M) (hSR : S ≤ normalizer (R : Set G))
    (hp₁ : ∀ s ∈ S, L₁.conjBy s = L₁ ∨ L₁.conjBy s = L₂)
    (hp₂ : ∀ s ∈ S, L₂.conjBy s = L₁ ∨ L₂.conjBy s = L₂) :
    let D := b₁.torus ⊔ b₂.torus
    D ≤ normalizer (R : Set G) ∧ S ≤ normalizer ((R ⊔ D : Subgroup G) : Set G) := by
  let C := R ⊓ centralizer ((L₁ ⊔ L₂ : Subgroup G) : Set G)
  have h₁N : b₁.torus ≤ normalizer (R : Set G) :=
    (le_inf b₁.normalizes_sylow (b₁.le_intersection.trans inf_le_right)).trans
      (normalizes_of_paired_decomposition hdec (le_centralizer_iff.mp hc)
        (inf_le_right.trans (centralizer_le (show L₁ ≤ L₁ ⊔ L₂ from le_sup_left))))
  have hdec' : R = ((R ⊓ L₂) ⊔ (R ⊓ L₁)) ⊔ C :=
    hdec.trans (congrArg (fun A : Subgroup G => A ⊔ C) (sup_comm _ _))
  have h₂N : b₂.torus ≤ normalizer (R : Set G) :=
    (le_inf b₂.normalizes_sylow (b₂.le_intersection.trans inf_le_right)).trans
      (normalizes_of_paired_decomposition hdec' hc
        (inf_le_right.trans (centralizer_le (show L₂ ≤ L₁ ⊔ L₂ from le_sup_right))))
  let B := (M ⊓ L₁) ⊔ (M ⊓ L₂)
  have hB : B = ((R ⊓ L₁) ⊔ (R ⊓ L₂)) ⊔ (b₁.torus ⊔ b₂.torus) := by
    rw [show B = (M ⊓ L₁) ⊔ (M ⊓ L₂) from rfl,←b₁.sylow_sup_torus,←b₂.sylow_sup_torus]
    exact sup_sup_sup_comm _ _ _ _
  have hRD : R ⊔ (b₁.torus ⊔ b₂.torus) = R ⊔ B := by
    rw [hB]
    symm
    calc
      R ⊔ (((R ⊓ L₁) ⊔ (R ⊓ L₂)) ⊔ (b₁.torus ⊔ b₂.torus)) =
          (R ⊔ ((R ⊓ L₁) ⊔ (R ⊓ L₂))) ⊔ (b₁.torus ⊔ b₂.torus) := (sup_assoc _ _ _).symm
      _ = R ⊔ (b₁.torus ⊔ b₂.torus) := congrArg (fun A : Subgroup G => A ⊔ (b₁.torus ⊔ b₂.torus))
        (sup_eq_left.mpr (sup_le inf_le_left inf_le_left))
  have hSB : S ≤ normalizer (B : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    suffices hh : B.conjBy s ≤ B from eq_of_le_of_card_ge hh (by rw [card_map_of_injective (MulAut.conj s).injective])
    have hm : M.conjBy s = M := mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer (hSM hs))
    have h₁ : (M ⊓ L₁).conjBy s ≤ B := by
      change (M ⊓ L₁).map (MulAut.conj s).toMonoidHom ≤ B
      rw [map_inf _ _ _ (MulAut.conj s).injective]
      change M.conjBy s ⊓ L₁.conjBy s ≤ B
      rw [hm]
      rcases hp₁ s hs with he | he <;> rw [he]
      · exact le_sup_left
      · exact le_sup_right
    have h₂ : (M ⊓ L₂).conjBy s ≤ B := by
      change (M ⊓ L₂).map (MulAut.conj s).toMonoidHom ≤ B
      rw [map_inf _ _ _ (MulAut.conj s).injective]
      change M.conjBy s ⊓ L₂.conjBy s ≤ B
      rw [hm]
      rcases hp₂ s hs with he | he <;> rw [he]
      · exact le_sup_left
      · exact le_sup_right
    change ((M ⊓ L₁) ⊔ (M ⊓ L₂)).map (MulAut.conj s).toMonoidHom ≤ B
    rw [Subgroup.map_sup]
    exact sup_le h₁ h₂
  refine ⟨sup_le h₁N h₂N,?_⟩
  rw [hRD]
  exact (le_inf hSR hSB).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

open scoped IsMulCommutative Pointwise

omit [Finite G] in
theorem PairedBorelData.abelian {S R L₁ L₂ H : Subgroup G} {n : ℕ}
    (b : PairedBorelData M S R L₁ L₂ H n) : IsMulCommutative b.torus := by
  let := b.first.cyclic
  let := b.second.cyclic
  obtain ⟨e,_⟩ := b.direct
  refine ⟨⟨fun x y => e.symm.injective ?_⟩⟩
  rw [e.symm.map_mul,e.symm.map_mul,mul_comm]

omit [Finite G] in
theorem PairedBorelData.odd {S R L₁ L₂ H : Subgroup G} {n : ℕ}
    (b : PairedBorelData M S R L₁ L₂ H n) : Odd (Nat.card b.torus) := by
  obtain ⟨e,_⟩ := b.direct
  rw [←Nat.card_congr e.toEquiv,Nat.card_prod]
  exact b.first.odd.mul b.second.odd

omit [Finite G] in
theorem PairedBorelData.card {S R L₁ L₂ H : Subgroup G} {n : ℕ}
    (b : PairedBorelData M S R L₁ L₂ H n) : Nat.card b.torus = (2^n-1)^2 := by
  obtain ⟨e,_⟩ := b.direct
  rw [←Nat.card_congr e.toEquiv,Nat.card_prod,b.first.card,b.second.card,pow_two]

omit [Finite G] in
theorem PairedBorelData.pow_eq_one {S R L₁ L₂ H : Subgroup G} {n : ℕ}
    (b : PairedBorelData M S R L₁ L₂ H n) (z : b.torus) : z^(2^n-1)=1 := by
  obtain ⟨e,_⟩ := b.direct
  obtain ⟨⟨a,d⟩,rfl⟩ := e.surjective z
  rw [←map_pow e]
  have ha : a^(2^n-1)=1 := b.first.card ▸ pow_card_eq_one' (x := a)
  have hd : d^(2^n-1)=1 := b.second.card ▸ pow_card_eq_one' (x := d)
  simp only [Prod.pow_mk,ha,hd,←Prod.one_eq_mk,e.map_one]

private theorem initial_torus_supplement
    {S R L C D H : Subgroup G}
    (hR : IsPGroup 2 R) (hRS : R ≤ S)
    (hD : IsMulCommutative D) (ho : Odd (Nat.card D))
    (hDR : D ≤ normalizer (R : Set G))
    (hSRD : S ≤ normalizer ((R ⊔ D : Subgroup G) : Set G))
    (hLH : L ≤ H) (hSH : S ≤ H)
    (hgen : L ⊔ S = H) (hRLC : R ≤ L ⊔ C)
    (hCS : C ≤ S) (hCD : C ≤ centralizer (D : Set G)) :
    H = L ⊔ (S ⊓ normalizer (D : Set G)) := by
  let K := R ⊔ D
  let := hD
  let : Group.IsNilpotent R := hR.isNilpotent
  have hsolv : Group.IsSolvable K := Group.isSolvable_sup_of_normalizes R D hDR
  have hoRK : Odd (R.relIndex K) := by
    rw [show K=R⊔D from rfl,OddHall.relIndex_normalized_sup R D hDR]
    exact ho.of_dvd_nat (relIndex_dvd_card _ _)
  let P := hR.comap_subtype.toSylow (show ¬2∣(R.subgroupOf K).index from
    fun hd => (Nat.not_even_iff_odd.mpr hoRK) (even_iff_two_dvd.mpr hd))
  have hP : (P : Subgroup K).map K.subtype = R := map_subgroupOf_eq_of_le le_sup_left
  have hHall := OddHall.oddHall_of_normalized_sup hR (Nat.coprime_two_left.mpr ho) hDR rfl
  have hfrat := OddHall.normal_sylow_frattini K R S D hsolv hRS hSRD P hP le_sup_right hHall
  apply le_antisymm _ (sup_le hLH (inf_le_left.trans hSH))
  rw [←hgen]
  apply sup_le le_sup_left
  intro s hs
  obtain ⟨r,hr,t,ht,rfl⟩ := (show s ∈ (R : Set G) * ((S ⊓ normalizer (D : Set G) : Subgroup G) : Set G) from hfrat ▸ (show s ∈ (S : Set G) from hs))
  apply (L ⊔ (S ⊓ normalizer (D : Set G))).mul_mem
  · exact (hRLC.trans (sup_le le_sup_left
      ((le_inf hCS (hCD.trans (Subgroup.centralizer_le_normalizer _))).trans le_sup_right))) hr
  · exact (show S ⊓ normalizer (D : Set G) ≤ L ⊔ (S ⊓ normalizer (D : Set G)) from le_sup_right) ht

/-- The two original Borel complements and the source Sylow-normalizer
supplement, before the later fixed-space argument. -/
theorem source_borel_torus
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    {M₀ : Subgroup G} {n : ℕ} (c : DoubleLinearSourceSetup d M₀ n)
    (hL : ChapterC.IsL2EvenBlock (d.block.map d.H.subtype) n)
    (hSM : (d.S : Subgroup d.H).map d.H.subtype ≤ M₀) (hMT : M₀ ≤ (T : Subgroup G))
    (hi : ((d.S : Subgroup d.H).map d.H.subtype).relIndex M₀ = 2) :
    let S := (d.S : Subgroup d.H).map d.H.subtype
    let L₁ := d.block.map d.H.subtype
    let R := Stellmacher.elementaryAbelianMaxJ S
    Nonempty (PairedBorelData M S R L₁ c.second d.H n) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let L₁ := d.block.map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let C := R ⊓ centralizer ((L₁ ⊔ c.second : Subgroup G) : Set G)
  obtain ⟨⟨P₁,hP₁,hB₁⟩,⟨P₂,hP₂,hB₂⟩⟩ := source_borels d hG T hST c hL hSM hMT hi
  obtain ⟨b₁⟩ := exists_borel_torus hL P₁ hP₁ hB₁
  obtain ⟨b₂⟩ := exists_borel_torus c.second_type P₂ hP₂ hB₂
  obtain ⟨hdec,_,_,hC,_,_⟩ := source_decomposition d hG T hST c hL hSM hMT hi
  have h₁L : b₁.torus ≤ L₁ := b₁.le_intersection.trans inf_le_right
  have h₂L : b₂.torus ≤ c.second := b₂.le_intersection.trans inf_le_right
  have hc : b₁.torus ≤ centralizer (b₂.torus : Set G) :=
    h₁L.trans ((le_centralizer_iff.mp c.commutes).trans (centralizer_le h₂L))
  have hd₁ := odd_torus_disjoint_commuting_block hL.2.1 b₁.sylow h₁L b₁.odd c.commutes
  have hd₂ := odd_torus_disjoint_commuting_block c.second_type.2.1 b₂.sylow h₂L b₂.odd
    (le_centralizer_iff.mp c.commutes)
  have hd : Disjoint b₁.torus b₂.torus := hd₁.mono le_rfl h₂L
  have hSR : S ≤ normalizer (R : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (Stellmacher.elementaryAbelianMaxJ S).map (MulAut.conj s).toMonoidHom = _
    rw [←Stellmacher.elementaryAbelianMaxJ_map_equiv,MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer hs)]
  have hn := pair_borel_normalizations b₁ b₂ c.commutes hdec d.full_pair.1.1.2.1 hSR c.permutes (fun s hs => (c.permutes_second s hs).symm)
  let D := b₁.torus ⊔ b₂.torus
  obtain ⟨e,he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting b₁.torus b₂.torus hd hc
  let := b₁.cyclic
  let := b₂.cyclic
  have hDa : IsMulCommutative D := by
    refine ⟨⟨fun x y => e.symm.injective ?_⟩⟩
    rw [e.symm.map_mul,e.symm.map_mul,mul_comm]
  have hDo : Odd (Nat.card D) := by
    rw [←Nat.card_congr e.toEquiv,Nat.card_prod]
    exact b₁.odd.mul b₂.odd
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  have hLL : L₁ ⊔ c.second ≤ d.H := c.join.le.trans (map_subtype_le _)
  have hDL : D ≤ L₁ ⊔ c.second := sup_le (h₁L.trans le_sup_left) (h₂L.trans le_sup_right)
  have hgen : (L₁ ⊔ c.second) ⊔ S = d.H := by rw [c.join,d.ambient_L0_sup_sylow]
  have hRLC : R ≤ (L₁ ⊔ c.second) ⊔ C := by
    exact hdec.le.trans (sup_le (sup_le (inf_le_right.trans (le_sup_left.trans le_sup_left))
      (inf_le_right.trans (le_sup_right.trans le_sup_left))) le_sup_right)
  have hsupp := initial_torus_supplement (c.original.R_twoGroup.to_le hRS) hRS hDa hDo hn.1 hn.2
    hLL (map_subtype_le _) hgen hRLC (inf_le_left.trans hRS)
    (inf_le_right.trans (centralizer_le hDL))
  refine ⟨{
    first := b₁
    second := b₂
    commutes := hc
    disjoint := hd
    first_intersection := join_inf_eq_of_commuting h₁L hd₂ hc
    second_intersection := ?_
    normalizes_R := hn.1
    sylow_normalizes := hn.2
    supplement := hsupp }⟩
  rw [sup_comm]
  exact join_inf_eq_of_commuting h₂L hd₁ (le_centralizer_iff.mp hc)

end CFSG.Quasithin.Chapter2.LinearShadows.Double
