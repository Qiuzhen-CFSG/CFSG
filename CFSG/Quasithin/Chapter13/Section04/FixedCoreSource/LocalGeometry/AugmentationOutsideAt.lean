module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OrdinaryOutsideAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.AugmentationCoveredAction
public import Theory.GroupTheory.PerfectCenterFrattini
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Outside subgroup control in both fixed-core quotient rows

The full normalizer action on the augmentation module detects conjugation
on the central quotient of L/O2(L). Perfectness of L/O2(L) makes this
central-quotient automorphism action faithful. Hence an element in the
permutation kernel centralizes the full L/O2(L), including its center in
the covered row. In particular [L,O^2(C_M(V))] lies in O2(L) in both rows.

If a two-perfect subgroup normal in an outside overgroup has full A6
image, its commutator with the common Sylow lifts through the central
supplement: perfectness first removes the center, then the two-core.
This would put L inside the outside overgroup, contradicting the trivial
two-core of their join. Its proper Sylow overgroup image is therefore a
{2,3}-group. The {2,3}-residual has trivial quotient action, and the literal
commutator/characteristic-two argument forces that residual to vanish.

This proves the required 13.3.8 clause for either original augmentation
row, without identifying centralCore(L) with O2(L) or assuming M=LT.
AugmentationSelectionAt applies it to construct an actual escaping
component. Structural facts retain their genuine same-G,T guards.

Source: Aschbacher--Smith 13.3.8 and 13.4.5--6,
printed pp.886--887,898. The earlier ordinary APIs remain unchanged.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Nonsolvable
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V Y H : Subgroup G}

omit [Finite G] in
/-- The full two-core quotient detects trivial action on the marked central quotient.
This retains the central three in the covered row. -/
theorem permutation_kernel_commutator_le_twoCore
    (D : ChosenModule T L V) (m : CoreMarking D)
    (q : normalizer (L : Set G) →* Equiv.Perm (Fin 6))
    (hqL : ∀ l : L, q (inclusion L.le_normalizer l) =
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).val)
    {N : Subgroup G} (hNM : N ≤ normalizer (L : Set G))
    (hqn : ∀ n (hn : n ∈ N), q ⟨n,hNM hn⟩ = 1)
    [Group.IsPerfect (L ⧸ pCore 2 L)] :
    ⁅L,N⁆ ≤ L.pCoreIn 2 := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro n hn l hl
  let a : normalizer (L : Set G) := ⟨n,hNM hn⟩
  let f := quotientAut (pCore 2 L) (L.normalizerMonoidHom a)
  have hf : f = 1 := by
    apply MulAut.centralQuotientAction_injective (augmentationCentralQuotient D m)
    rw [map_one]
    apply MulEquiv.ext
    intro b
    obtain ⟨c,rfl⟩ := m.quotient.surjective b
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (centralCore L) c
    rw [←augmentationCentralQuotient_apply D m k, MulAut.centralQuotientAction_apply]
    simp only [f,quotientAut_apply_mk,MulAut.one_apply,augmentationCentralQuotient_apply]
    apply Subtype.ext
    have he : inclusion L.le_normalizer (L.normalizerMonoidHom a k) =
        a * inclusion L.le_normalizer k * a⁻¹ := Subtype.ext rfl
    rw [←hqL,he,map_mul,map_mul,map_inv,hqn n hn,one_mul,inv_one,mul_one,hqL]
  let k : L := ⟨l,hl⟩
  have he : QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom a k) =
      QuotientGroup.mk' (pCore 2 L) k := by
    have hh := congrArg (fun b : MulAut (L ⧸ pCore 2 L) => b (QuotientGroup.mk' (pCore 2 L) k)) hf
    simpa only [f,quotientAut_apply_mk,MulAut.one_apply] using hh
  refine ⟨L.normalizerMonoidHom a k / k,QuotientGroup.eq_iff_div_mem.mp he,?_⟩
  change (n*l*n⁻¹)/l = ⁅n,l⁆
  simp only [div_eq_mul_inv,commutatorElement_def]

/-- The actual residual of C_M(V) centralizes L/O2(L), in both source rows. -/
theorem normalizer_action_residual_twoCore_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    ⁅L,normalizerActionResidual L V⁆ ≤ L.pCoreIn 2 := by
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  obtain ⟨q,_,hqL,hker⟩ := exists_core_normalizer_permutation D m
    (normalizer_component_le_module_at h structural D m)
  have hc : normalizerActionResidual L V ≤
      normalizer (L : Set G) ⊓ centralizer (V : Set G) := map_subtype_le _
  apply permutation_kernel_commutator_le_twoCore D m q hqL (hc.trans inf_le_left)
  intro n hn
  change (⟨n,(hc hn).1⟩ : normalizer (L : Set G)) ∈ q.ker
  rw [hker]
  exact (hc hn).2

private theorem alternating_sylow_commutator (P : Sylow 2 (alternatingGroup (Fin 6))) :
    ⁅(⊤ : Subgroup (alternatingGroup (Fin 6))), (P : Subgroup (alternatingGroup (Fin 6)))⁆ = ⊤ := by
  let A := alternatingGroup (Fin 6)
  let C := ⁅(⊤ : Subgroup A), (P : Subgroup A)⁆
  let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  let : C.Normal := normalizer_eq_top_iff.mp (top_unique (normalizer_commutator_ge_left _ _))
  rcases (inferInstance : C.Normal).eq_bot_or_eq_top with hc | hc
  · have hp : (P : Subgroup A) ≤ center A := by
      have hh := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
      intro s hs
      exact mem_center_iff.mpr (fun a => hh hs a (mem_top a))
    have hb : (P : Subgroup A) = ⊥ :=
      le_bot_iff.mp (hp.trans (alternatingGroup.center_eq_bot (by simp)).le)
    have he : Nat.card (P : Subgroup A) = 8 := by
      calc
        _ = Nat.card (Theory.SpecificGroups.SymmetricSix.a6BorelSylow :
            Subgroup (alternatingGroup (Fin 6))) :=
          P.card_eq_multiplicity.trans
            Theory.SpecificGroups.SymmetricSix.a6BorelSylow.card_eq_multiplicity.symm
        _ = 8 := Theory.SpecificGroups.SymmetricSix.a6Borel_order
    rw [hb] at he
    norm_num at he
  · exact hc

private theorem outside_join_core_free
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hH : H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G)) :
    pCore 2 (L ⊔ H : Subgroup G) = ⊥ := by
  by_contra hne
  let J := L ⊔ H
  have hQne : J.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact hne (((pCore 2 J).map_eq_bot_iff_of_injective J.subtype_injective).mp he)
  have hn : J ≤ normalizer (J.pCoreIn 2 : Set G) :=
    J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hu := (h.source_normalizer_maximal_unique_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).2
  have hb : J ≤ normalizer (L : Set G) := hn.trans
    (normalizer_le_of_unique_maximalTwoLocal hu (isPGroup_pCoreIn 2 J) hQne
      ((sup_le le_sup_left (show (T : Subgroup G) ≤ J from fun x hx => mem_sup_right (hH.1.2 hx))).trans hn))
  exact hH.2 (fun x hx => hb (mem_sup_right hx))

private theorem augmentation_full_image_le
    (D : ChosenModule T L V) (m : CoreMarking D)
    (q : normalizer (L : Set G) →* Equiv.Perm (Fin 6))
    (hqL : ∀ l : L, q (inclusion L.le_normalizer l) =
      (m.quotient (QuotientGroup.mk' (centralCore L) l)).val)
    (hYM : Y ≤ normalizer (L : Set G))
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hfull : alternatingGroup (Fin 6) ≤ (Y.subgroupOf (normalizer (L : Set G))).map q)
    [Group.IsPerfect L] : Y ≥ L := by
  let M := normalizer (L : Set G)
  let A := L.subgroupOf M
  let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨P,hP⟩ := (T.subtype D.sylow_normalizes_component).exists_subgroupOf_eq_of_normal A
  let e := subgroupOfEquivOfLe L.le_normalizer
  let S := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hST : ∀ s ∈ (S : Subgroup L), s.val ∈ (T : Subgroup G) := by
    rintro s ⟨a,ha,rfl⟩
    rw [hP] at ha
    exact ha
  let f : L →* alternatingGroup (Fin 6) :=
    m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hf : Function.Surjective f := m.quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = centralCore L := by
    rw [MonoidHom.ker_comp_of_injective _ _ m.quotient.injective, QuotientGroup.ker_mk']
  let B := Y.subgroupOf L
  have hcomm : ⁅(⊤ : Subgroup (alternatingGroup (Fin 6))),
      ((S.mapSurjective hf) : Subgroup _)⁆ ≤ B.map f := by
    apply commutator_le.mpr
    intro a _ b hb
    obtain ⟨y,hy,hey⟩ := hfull a.property
    obtain ⟨s,hs,rfl⟩ := hb
    have hcL : ⁅y.val,s.val⁆ ∈ L := by
      rw [←commutatorElement_inv]
      exact L.inv_mem (le_normalizer_iff_commutator_le_left.mp hYM
        (commutator_mem_commutator s.property hy))
    have hcY : ⁅y.val,s.val⁆ ∈ Y :=
      le_normalizer_iff_commutator_le_left.mp hTY
        (commutator_mem_commutator hy (hST s hs))
    refine ⟨⟨⁅y.val,s.val⁆,hcL⟩,hcY,?_⟩
    apply Subtype.ext
    have he : inclusion L.le_normalizer (⟨⁅y.val,s.val⁆,hcL⟩ : L) =
        ⁅y,inclusion L.le_normalizer s⁆ := Subtype.ext rfl
    change (m.quotient (QuotientGroup.mk' (centralCore L) ⟨⁅y.val,s.val⁆,hcL⟩)).val = _
    rw [←hqL,he,map_commutatorElement,hey,hqL]
    rfl
  have hB : B.map f = ⊤ := top_unique ((alternating_sylow_commutator _).symm ▸ hcomm)
  have hsupC : B ⊔ centralCore L = ⊤ := by
    have hh := congrArg (comap f) hB
    simpa only [comap_map_eq,hk,comap_top] using hh
  let q₂ := QuotientGroup.mk' (pCore 2 L)
  have hsup : B ⊔ pCore 2 L = ⊤ := by
    have hcent : (centralCore L).map q₂ = center (L ⧸ pCore 2 L) :=
      map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
    have hs := congrArg (map q₂) hsupC
    rw [Subgroup.map_sup,hcent,map_top_of_surjective q₂ (QuotientGroup.mk'_surjective _)] at hs
    have he := eq_top_of_sup_center_eq_top (B.map q₂) hs
    have hh := congrArg (comap q₂) he
    simpa only [comap_map_eq,q₂,QuotientGroup.ker_mk',comap_top] using hh
  have hn : pCore 2 L ≤ normalizer (B : Set L) := by
    intro s hs
    rw [mem_normalizer_iff]
    intro y
    exact mem_normalizer_iff.mp (hTY (hST s (pCore_isPGroup.le_sylow_of_normal S hs))) y.val
  let : B.Normal := normalizer_eq_top_iff.mp (top_unique
    (hsup ▸ sup_le B.le_normalizer hn))
  have hquot : IsPGroup 2 (L ⧸ B) := isPGroup_quotient_of_sup_eq_top B _ pCore_isPGroup hsup
  let := hquot.isNilpotent
  have htop : (⊤ : Subgroup L) ≤ B := le_of_isPerfect_of_solvable_quotient ⊤ B
  intro l hl
  exact htop (show (⟨l,hl⟩ : L) ∈ (⊤ : Subgroup L) from trivial)

/-- The original 13.3.8 conclusion for either genuine augmentation quotient row,
without a normalizer supplement. Normality is relative to the outside H. -/
theorem augmentation_outside_twoThree_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G))
    (Y : Subgroup G) (hYH : Y ≤ H) (hnY : H ≤ normalizer (Y : Set G))
    (hp : IsPPerfect 2 Y) (hYM : Y ≤ normalizer (L : Set G)) :
    IsPiGroup twoThreePrimes Y := by
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quasisimple
  let M := normalizer (L : Set G)
  obtain ⟨q,_,hqL,_⟩ := Nonsolvable.exists_core_normalizer_permutation D m
    (normalizer_component_le_module_at h structural D m)
  let a := q.comp (inclusion hYM)
  have ha (y : Y) : a y ∈ alternatingGroup (Fin 6) := by
    rw [←Equiv.Perm.twoResidual_eq_alternating]
    apply map_pResidual_le 2 a
    exact mem_map_of_mem a ((pResidual_eq_top_iff 2 Y).mpr hp ▸ mem_top y)
  let g : Y →* alternatingGroup (Fin 6) := a.codRestrict _ ha
  let A := L.subgroupOf M
  let : A.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨P,hP⟩ := (T.subtype D.sylow_normalizes_component).exists_subgroupOf_eq_of_normal A
  let e := subgroupOfEquivOfLe L.le_normalizer
  let S := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hST : ∀ s ∈ (S : Subgroup L), s.val ∈ (T : Subgroup G) := by
    rintro s ⟨b,hb,rfl⟩
    rw [hP] at hb
    exact hb
  let f : L →* alternatingGroup (Fin 6) :=
    m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L))
  have hf : Function.Surjective f := m.quotient.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := S.mapSurjective hf
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) := hH.1.2.trans hnY
  have hn : (R : Subgroup (alternatingGroup (Fin 6))) ≤ normalizer (g.range : Set _) := by
    apply le_normalizer_iff.mpr
    intro s hs y hy
    obtain ⟨s,hs,rfl⟩ := hs
    obtain ⟨y,rfl⟩ := hy
    let b : Y := ⟨s.val * y.val * s.val⁻¹,le_normalizer_iff.mp hTY s.val (hST s hs) y.val y.property⟩
    refine ⟨b,?_⟩
    apply Subtype.ext
    change q (inclusion hYM b) = (f s).val * a y * (f s).val⁻¹
    have he : inclusion hYM b = (inclusion L.le_normalizer s) *
        inclusion hYM y * (inclusion L.le_normalizer s)⁻¹ := Subtype.ext rfl
    rw [he,map_mul,map_mul,map_inv,hqL]
    rfl
  let J := g.range ⊔ (R : Subgroup (alternatingGroup (Fin 6)))
  have hJ : J ≠ ⊤ := by
    intro hj
    let : g.range.Normal := normalizer_eq_top_iff.mp
      (top_unique (hj ▸ sup_le g.range.le_normalizer hn))
    have hquot : IsPGroup 2 ((alternatingGroup (Fin 6)) ⧸ g.range) :=
      isPGroup_quotient_of_sup_eq_top _ _ R.isPGroup' hj
    let := hquot.isNilpotent
    let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    have hr : (⊤ : Subgroup (alternatingGroup (Fin 6))) ≤ g.range :=
      le_of_isPerfect_of_solvable_quotient ⊤ g.range
    have hfull : alternatingGroup (Fin 6) ≤ (Y.subgroupOf M).map q := by
      intro b hb
      obtain ⟨y,hy⟩ := hr (show (⟨b,hb⟩ : alternatingGroup (Fin 6)) ∈ ⊤ from trivial)
      exact ⟨inclusion hYM y,y.property,congrArg Subtype.val hy⟩
    let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
    have hLH := (augmentation_full_image_le D m q hqL hYM hTY hfull).trans hYH
    have hcore := outside_join_core_free h structural hH
    have he : L ⊔ H = H := sup_eq_right.mpr hLH
    rw [he] at hcore
    exact hH.1.1 (by simp only [pCoreIn,hcore,Subgroup.map_bot])
  have hc : Nat.card g.range ∣ 24 :=
    (card_dvd_of_le (show g.range ≤ J from le_sup_left)).trans
      (Theory.SpecificGroups.SymmetricSix.proper_sylow_overgroup_card_dvd_twenty_four
        R J le_sup_right hJ)
  have hpi : IsPiGroup twoThreePrimes g.range := by
    rw [IsPiGroup_iff]
    intro p hd
    change p.val = 2 ∨ p.val = 3
    have hd' : p.val ∣ 2^3*3 := hd.trans hc
    rcases p.property.dvd_mul.mp hd' with hd | hd
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
        (p.property.dvd_of_dvd_pow hd) |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp hd |>.resolve_left p.property.ne_one)
  have hr : piResidual twoThreePrimes Y ≤ g.ker :=
    piResidual_le_ker_of_range twoThreePrimes g hpi
  let N := (piResidual twoThreePrimes Y).map Y.subtype
  have hNM : N ≤ M := (map_subtype_le _).trans hYM
  have hqN (n : G) (hn : n ∈ N) : q ⟨n,hNM hn⟩ = 1 := by
    obtain ⟨y,hy,rfl⟩ := hn
    exact congrArg Subtype.val (hr hy)
  have hQH : L.pCoreIn 2 ≤ H := by
    exact (pCoreIn_le_sylow L S).trans (fun s hs => by
      obtain ⟨s,hs,rfl⟩ := hs
      exact hH.1.2 (hST s hs))
  apply twoThree_of_residual_commutator L H Y (L.pCoreIn 2) hYH hnY hQH
    (isPGroup_pCoreIn 2 L)
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    ?_ (outside_join_core_free h structural hH)
    ((Chapter1.mem_He_iff).mp (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T) hH.1))
  exact permutation_kernel_commutator_le_twoCore D m q hqL hNM hqN

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
