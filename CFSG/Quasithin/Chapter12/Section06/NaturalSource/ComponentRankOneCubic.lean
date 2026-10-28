module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentRankTwoNonlinear
public import Theory.GroupTheory.PrimeRankNormalIntersection
public import Theory.SpecificGroups.PSL2.BinarySylowFixerCentralizer
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters

/-!
# The original cubic line in the rank-one component

The original elementary Sylow P of order nine normalizes the selected K.
The ambient three-rank is at most two and K has three-rank one, so P meets
K in a line of order three. The actual H to H/O₂(H) projection is injective
on P; the image of that line is exactly P-star intersection K-star.
The original residual centralization embeds this same line into the fixed
subgroup of every original V action, with its literal quotient map retained.

Transport to an actual model supplies a Sylow-fixing involution with a cubic
fixed subgroup. Binary PSL₂ cannot have such a fixed subgroup. The genuine
PSL₂(4) to A₅ comparison then completes the alternating-row exclusions.
All original marking, TI, nonsingular-centralizer and point-geometry inputs
remain explicit. The remaining model inspection, abelian span, 12.6.27--34
and universal NaturalReduction are subsequent source obligations.

Source: Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
open Subgroup Theory.GroupTheory

private theorem cubic_intersection_card {J : Type*} [Group J] [Finite J]
    (A B : Subgroup J) [IsElementaryAbelian 3 A]
    (hA : Nat.card A = 9) (hn : A ≤ normalizer (B : Set J))
    (hJ : primeRank 3 J ≤ 2) (hB : primeRank 3 B = 1) :
    Nat.card (A ⊓ B : Subgroup J) = 3 := by
  have h3 : 3 ∣ Nat.card B := by
    by_contra hh
    have := PrimeRank.eq_zero_iff_not_dvd_card.mpr hh
    omega
  have hne := A.inf_ne_bot_of_elementary_plane B hn h3 hA hJ
  let W := A ⊓ B
  let : IsElementaryAbelian 3 W := IsElementaryAbelian.of_le (show W ≤ A from inf_le_left)
  let : IsElementaryAbelian 3 (W.subgroupOf B) := IsElementaryAbelian.subgroupOf inf_le_right
  have hu := (primeRank_le_iff_elementary_card_le B).mp hB.le (W.subgroupOf B) inferInstance
  rw [Nat.card_congr (subgroupOfEquivOfLe (show W ≤ B from inf_le_right)).toEquiv] at hu
  have hd : Nat.card W ∣ 3 ^ 2 := by
    have hh := card_dvd_of_le (show W ≤ A from inf_le_left)
    norm_num only [hA] at hh ⊢
    exact hh
  obtain ⟨i,hi,hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
  interval_cases i
  · exact (hne (card_eq_one.mp hc)).elim
  · exact hc
  · norm_num at hc hu
    omega

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1)
  (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
  (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
  (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)

include hz hTV hTz hbound hH hn a in
/-- The literal original P intersection K is a cubic line. -/
theorem SourceHypothesis.original_selectedComponent_sylow_intersection_card
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    let A := (P : Subgroup (D.fullSetup hZ T z).L₁).map (D.fullSetup hZ T z).L₁.subtype
    Nat.card (A ⊓ c.K : Subgroup G) = 3 := by
  let E := D.fullSetup hZ T z
  let A := (P : Subgroup E.L₁).map E.L₁.subtype
  have hAH : A ≤ H := (map_subtype_le _).trans (fun x hx => hH.1.2 (Or.inl hx))
  obtain ⟨hP,hPc⟩ := S.original_point_residual_sylow D hZ z hz hTz P
  let := hP
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.map_subtype
  let : IsElementaryAbelian 3 (A.subgroupOf H) := IsElementaryAbelian.subgroupOf hAH
  have hcard : Nat.card (A.subgroupOf H) = 9 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv,
      card_map_of_injective E.L₁.subtype_injective]
    exact hPc
  have hnA : A.subgroupOf H ≤ normalizer (c.K.subgroupOf H : Set H) :=
    (comap_mono ((map_subtype_le _).trans
      (S.original_residual_normalizes_selectedComponent D hZ z hz hH c))).trans
      (c.K.le_normalizer_comap H.subtype)
  have hrH : primeRank 3 H ≤ 2 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 H) pCore_isPGroup]
    exact S.original_star_three_rank D hZ z hz hH
  have hrK : primeRank 3 (c.K.subgroupOf H) = 1 :=
    (primeRank_equiv 3 (subgroupOfEquivOfLe c.le_H)).trans
      (S.original_selectedComponent_rank_one D hZ z hz hTV hTz hbound hH hn c a hTI hns)
  have hc := cubic_intersection_card (A.subgroupOf H) (c.K.subgroupOf H) hcard hnA hrH hrK
  change Nat.card ((A ⊓ c.K).subgroupOf H) = 3 at hc
  rwa [Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ c.K ≤ H from inf_le_left.trans hAH)).toEquiv] at hc

include hz hTV hTz hbound hH hn a in
/-- The same cubic line survives the actual star quotient, which commutes
with this particular intersection. -/
theorem SourceHypothesis.original_selectedComponent_sylow_intersection_star
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    let A := (P : Subgroup (D.fullSetup hZ T z).L₁).map (D.fullSetup hZ T z).L₁.subtype
    Nat.card (Nonabelian.Setup.star H (A ⊓ c.K)) = 3 ∧
      Nonabelian.Setup.star H (A ⊓ c.K) =
        Nonabelian.Setup.star H A ⊓ Nonabelian.Setup.star H c.K := by
  let E := D.fullSetup hZ T z
  let A := (P : Subgroup E.L₁).map E.L₁.subtype
  let W := A ⊓ c.K
  let q := QuotientGroup.mk' (pCore 2 H)
  obtain ⟨hA,hAc,hiq⟩ := S.original_point_sylow_star D hZ z hz hTz hH P
  let := hA
  have hWH : W ≤ H := inf_le_right.trans c.le_H
  have hi : Function.Injective (q.subgroupMap (W.subgroupOf H)) := by
    intro x y he
    have hxy := @hiq (⟨x.val,x.property.1⟩ : A.subgroupOf H)
      (⟨y.val,y.property.1⟩ : A.subgroupOf H) (congrArg Subtype.val he)
    exact Subtype.ext (congrArg (fun w : A.subgroupOf H => w.val) hxy)
  let e := MulEquiv.ofBijective (q.subgroupMap (W.subgroupOf H))
    ⟨hi,q.subgroupMap_surjective _⟩
  have hcW : Nat.card (Nonabelian.Setup.star H W) = 3 := by
    change Nat.card ((W.subgroupOf H).map q) = 3
    rw [←Nat.card_congr e.toEquiv,Nat.card_congr (subgroupOfEquivOfLe hWH).toEquiv]
    exact S.original_selectedComponent_sylow_intersection_card D hZ z hz hTV hTz hbound hH hn c a hTI hns P
  refine ⟨hcW,?_⟩
  have hnA : Nonabelian.Setup.star H A ≤ normalizer (Nonabelian.Setup.star H c.K : Set _) :=
    (map_mono (comap_mono (map_subtype_le _))).trans
      (S.original_residual_star_normalizes_selectedComponent D hZ z hz hH c)
  have hcI := cubic_intersection_card (Nonabelian.Setup.star H A) (Nonabelian.Setup.star H c.K)
    hAc hnA (S.original_star_three_rank D hZ z hz hH)
    (c.three_rank_eq_star.symm.trans
      (S.original_selectedComponent_rank_one D hZ z hz hTV hTz hbound hH hn c a hTI hns))
  apply eq_of_le_of_card_ge
  · exact le_inf (map_mono (comap_mono inf_le_left)) (map_mono (comap_mono inf_le_right))
  · exact le_of_eq (hcI.trans hcW.symm)

include hz hTV hTz hbound hH hn a in
/-- The original cubic intersection embeds in the fixed group of each actual
V action, retaining its literal quotient projection. -/
theorem SourceHypothesis.original_selectedComponent_sylow_intersection_fixed
    (P : Sylow 3 (D.fullSetup hZ T z).L₁)
    (t : MulAut (Nonabelian.Setup.star H c.K))
    (ht : t ∈ (V.subgroupOf c.localActor).map a.action) :
    let A := (P : Subgroup (D.fullSetup hZ T z).L₁).map (D.fullSetup hZ T z).L₁.subtype
    ∃ f : (A ⊓ c.K : Subgroup G) →* t.fixedSubgroup,
      Function.Injective f ∧ ∀ x,
        (f x).val.val = QuotientGroup.mk' (pCore 2 H)
          ⟨x.val,c.le_H x.property.2⟩ := by
  let E := D.fullSetup hZ T z
  let A := (P : Subgroup E.L₁).map E.L₁.subtype
  let W := A ⊓ c.K
  let B := Nonabelian.Setup.star H c.K
  let q := QuotientGroup.mk' (pCore 2 H)
  let j : W →* H := inclusion (show W ≤ H from inf_le_right.trans c.le_H)
  let b : W →* B := (q.comp j).codRestrict B
    (fun x => mem_map_of_mem q x.property.2)
  obtain ⟨v,hv,rfl⟩ := ht
  have hb (x : W) : b x ∈ (a.action v).fixedSubgroup := by
    rw [MulAut.mem_fixedSubgroup]
    apply Subtype.ext
    rw [a.conjugation]
    have hxA : q (j x) ∈ Nonabelian.Setup.star H E.L₁ :=
      mem_map_of_mem q (show (j x).val ∈ E.L₁ from
        (map_subtype_le (P : Subgroup E.L₁)) x.property.1)
    have hvV : q (inclusion a.local_le v) ∈ Nonabelian.Setup.star H V :=
      mem_map_of_mem q hv
    have hc := S.original_point_residual_star_centralizes D hZ z hz hTV hTz hbound
      hH hn hxA _ hvV
    change q (inclusion a.local_le v) * q (j x) * (q (inclusion a.local_le v))⁻¹ = q (j x)
    rw [hc,mul_inv_cancel_right]
  let f := b.codRestrict (a.action v).fixedSubgroup hb
  refine ⟨f,?_,fun _ => rfl⟩
  intro x y he
  have hiq := (S.original_point_sylow_star D hZ z hz hTz hH P).2.2
  have hxy := @hiq (⟨j x,x.property.1⟩ : A.subgroupOf H)
    (⟨j y,y.property.1⟩ : A.subgroupOf H)
    (congrArg (fun w : (a.action v).fixedSubgroup => w.val.val) he)
  exact Subtype.ext (congrArg (fun w : A.subgroupOf H => w.val.val) hxy)

include hz hTV hTz hbound hH hn a in
/-- Every model of the same original component has a Sylow-fixing involution
whose fixed group contains the original cubic intersection. -/
theorem SourceHypothesis.original_selectedComponent_model_fixed_cubic
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {B : Type*} [Group B] [Finite B] (e : Nonabelian.Setup.star H c.K ≃* B) :
    ∃ t : MulAut (Nonabelian.Setup.star H c.K),
      t ∈ (V.subgroupOf c.localActor).map a.action ∧
      orderOf (MulAut.congr e t) = 2 ∧
      (∃ Q : Sylow 2 B, ∀ x ∈ Q, MulAut.congr e t x = x) ∧
      3 ∣ Nat.card (MulAut.congr e t).fixedSubgroup := by
  let U := (V.subgroupOf c.localActor).map a.action
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 (by
    rw [show Nat.card U = 2 from a.module_card])
  refine ⟨t,t.property,((MulAut.congr e).orderOf_eq _).trans
    ((Subgroup.orderOf_coe t).trans ht),?_,?_⟩
  · obtain ⟨R,hR⟩ := S.original_action_module_fixes_component_sylow
      D hZ z hz hTV hTz hbound hH hn c a
    refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    change e ((t : MulAut _) (e.symm (e x))) = e x
    rw [e.symm_apply_apply,hR t t.property x hx]
  · let P : Sylow 3 (D.fullSetup hZ T z).L₁ := default
    obtain ⟨f,hf,_⟩ := S.original_selectedComponent_sylow_intersection_fixed
      D hZ z hz hTV hTz hbound hH hn c a P t t.property
    have hd := card_dvd_of_injective f hf
    rw [S.original_selectedComponent_sylow_intersection_card
      D hZ z hz hTV hTz hbound hH hn c a hTI hns P] at hd
    rwa [←Nat.card_congr (MulAut.fixedSubgroupCongr e (t : MulAut _)).toEquiv]

include hz hTV hTz hbound hH hn a in
/-- The original selected component is not PSL₂ in characteristic two. -/
theorem SourceHypothesis.original_selectedComponent_not_binaryLinearTwo
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {F : Type*} [Field F] [Finite F] [CharP F 2] :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃*
      BenderSuzuki.MatrixGroups.PSL2MatrixGroup F) := by
  rintro ⟨e⟩
  obtain ⟨t,_,ht,⟨Q,hQ⟩,hd⟩ := S.original_selectedComponent_model_fixed_cubic
    D hZ z hz hTV hTz hbound hH hn c a hTI hns e
  have htwo := Theory.PSL2.sylow_fixed_involution_isTwoGroup Q (MulAut.congr e t) ht hQ
  obtain ⟨k,hk⟩ := htwo.exists_card_eq
  rw [hk] at hd
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

include hz hTV hTz hbound hH hn a in
/-- Exclusion of the literal binary linear-two row of Theorem C. -/
theorem SourceHypothesis.original_selectedComponent_not_binaryLinearTwo_model
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) (n : ℕ) :
    ¬ ClassicalGroup.IsPSL (Nonabelian.Setup.star H c.K) 2 (2^n) := by
  rintro ⟨F,hFfield,hFfinite,hF,he⟩
  let := hFfield
  let := hFfinite
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  exact S.original_selectedComponent_not_binaryLinearTwo D hZ z hz hTV hTz hbound
    hH hn c a hTI hns he

include hz hTV hTz hbound hH hn a in
/-- The A₅ row is the actual four-element-field PSL₂ comparison. -/
theorem SourceHypothesis.original_selectedComponent_not_alternatingFive
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃* alternatingGroup (Fin 5)) := by
  rintro ⟨e⟩
  exact S.original_selectedComponent_not_binaryLinearTwo D hZ z hz hTV hTz hbound
    hH hn c a hTI hns
    ⟨e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩

include hz hTV hTz hbound hH hn a in
/-- Every alternating row in Theorem C is excluded for the original component. -/
theorem SourceHypothesis.original_selectedComponent_not_alternating
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {n : ℕ} (hn8 : n ≤ 8) :
    ¬ Nonempty (Nonabelian.Setup.star H c.K ≃* alternatingGroup (Fin n)) := by
  intro he
  by_cases hn5 : n < 5
  · obtain ⟨e⟩ := he
    let : Group.IsSolvable (alternatingGroup (Fin n)) := by
      by_cases hn4 : n = 4
      · subst n
        exact alternatingGroup_fin_four_isSolvable
      · let := alternatingGroup.isMulCommutative_of_card_le_three
          (α := Fin n) (by simpa using (show n ≤ 3 by omega))
        exact Group.isSolvable_of_comm (isMulCommutative_iff.mp inferInstance)
    let : Group.IsSolvable (Nonabelian.Setup.star H c.K) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    let := c.component.2
    let : IsSimpleGroup (Nonabelian.Setup.star H c.K) :=
      S.original_selectedComponent_simple D hZ z hz hTV hTz hbound hH hn c a hTI hns
    exact Group.IsPerfect.not_isSolvable (Nonabelian.Setup.star H c.K) inferInstance
  · have hcases : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hcases with rfl | rfl | h78
    · exact S.original_selectedComponent_not_alternatingFive D hZ z hz hTV hTz hbound
        hH hn c a hTI hns he
    · exact S.original_selectedComponent_not_alternatingSix D hZ z hz hTz hH c a he
    · exact S.original_selectedComponent_not_alternatingSevenEight D hZ z hz hTV hTz
        hbound hH hn c a h78 he

end CFSG.Quasithin.Chapter12.Section06
