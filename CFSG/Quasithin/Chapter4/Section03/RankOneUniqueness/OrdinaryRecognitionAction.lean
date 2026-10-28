module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.OrdinaryPreparation
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The actual fixed-radical action for ordinary recognition

For the original source configuration, conjugation maps R₀ = C_{O₂(I)}(L)
onto a nontrivial two-subgroup of Aut(K) fixing the original embedded L.
The source normalizer control forces nontriviality. Both the Sylow subgroup
S = T ∩ H and S ∩ K are retained, as is the faithful quotient KS/C_{KS}(K).
Cauchy's theorem produces an involution in this same image. Perfectness of K
makes its action on K/Z(K) faithful, so the involution survives in any actual
central-quotient model. The original L-image in that quotient is nonsolvable.

The center is proved to equal O₂(K); it is not assumed trivial. These are
inputs to the marked local-pair inspection, not symplectic recognition.
Source: Aschbacher--Smith C.3.1, pp.149--151, and 4.3.6, printed p.614.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
namespace SourceConfiguration

/-- Conjugation by the original local overgroup on its normal component. -/
@[expose] noncomputable def ordinaryAction (c : SourceConfiguration T L) :
    c.H →* MulAut c.K := by
  let := c.component_normal
  exact MulAut.conjNormal

/-- The original L, using both literal inclusions into the component. -/
abbrev ordinaryLocal (c : SourceConfiguration T L) : Subgroup c.K :=
  (L.subgroupOf c.H).subgroupOf c.K

/-- The original S = T ∩ H, inside H. -/
abbrev ordinarySylowInH (c : SourceConfiguration T L) : Subgroup c.H :=
  ((T : Subgroup G) ⊓ c.H).subgroupOf c.H

/-- The actual fixed radical's image under conjugation on K. -/
@[expose] noncomputable def ordinaryFixedRadicalImage (c : SourceConfiguration T L) :
    Subgroup (MulAut c.K) :=
  (c.ordinaryFixedRadical.subgroupOf c.H).map c.ordinaryAction

omit [Finite G] in
theorem ordinaryAction_apply (c : SourceConfiguration T L) (h : c.H) (k : c.K) :
    ((c.ordinaryAction h k : c.H) : G) = (h : G) * ((k : c.H) : G) * (h : G)⁻¹ := rfl

omit [Finite G] in
theorem ordinaryAction_ker (c : SourceConfiguration T L) :
    c.ordinaryAction.ker = centralizer (c.K : Set c.H) := by
  ext h
  constructor
  · intro hh k hk
    have he := congrArg (fun x : c.K => (x : c.H))
      (DFunLike.congr_fun hh ⟨k,hk⟩)
    change h * k * h⁻¹ = k at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hh
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    change h * (k : c.H) * h⁻¹ = k
    exact mul_inv_eq_iff_eq_mul.mpr (hh k k.property).symm

omit [Finite G] in
theorem ordinaryFixedRadical_le_sylow (c : SourceConfiguration T L) :
    c.ordinaryFixedRadical ≤ (T : Subgroup G) ⊓ c.H :=
  inf_le_left.trans (c.core_sylow.le.trans inf_le_left)

omit [Finite G] in
theorem ordinaryFixedRadicalImage_isTwoGroup (c : SourceConfiguration T L) :
    IsPGroup 2 c.ordinaryFixedRadicalImage :=
  ((isPGroup_pCoreIn 2 c.I).to_le inf_le_left).comap_subtype.map c.ordinaryAction

theorem ordinaryFixedRadicalImage_ne_bot (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K) :
    c.ordinaryFixedRadicalImage ≠ ⊥ := by
  intro he
  have hk := (map_eq_bot_iff (c.ordinaryFixedRadical.subgroupOf c.H)).mp he
  rw [c.ordinaryAction_ker] at hk
  apply c.ordinaryFixedRadical_not_centralizes_component D ho
  intro r hr k hK
  obtain ⟨k,hK,rfl⟩ := hK
  exact congrArg Subtype.val
    (hk (show (⟨r,(c.ordinaryFixedRadical_le_sylow hr).2⟩ : c.H) ∈
      c.ordinaryFixedRadical.subgroupOf c.H from hr) k hK)

omit [Finite G] in
theorem ordinaryFixedRadicalImage_le_sylowImage (c : SourceConfiguration T L) :
    c.ordinaryFixedRadicalImage ≤ c.ordinarySylowInH.map c.ordinaryAction :=
  map_mono (subgroupOf_mono c.H c.ordinaryFixedRadical_le_sylow)

omit [Finite G] in
theorem ordinaryFixedRadicalImage_fixes_original (c : SourceConfiguration T L) :
    c.ordinaryFixedRadicalImage ≤ fixingSubgroup (MulAut c.K) (c.ordinaryLocal : Set c.K) := by
  rintro _ ⟨r,hr,rfl⟩
  rw [mem_fixingSubgroup_iff]
  intro l hl
  apply Subtype.ext
  apply Subtype.ext
  change (r : G) * ((l : c.H) : G) * (r : G)⁻¹ = ((l : c.H) : G)
  exact mul_inv_eq_iff_eq_mul.mpr (hr.2 _ hl).symm

theorem ordinaryFixedRadicalImage_normalized (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) :
    c.ordinarySylowInH.map c.ordinaryAction ≤
      normalizer (c.ordinaryFixedRadicalImage : Set (MulAut c.K)) := by
  have hn : c.ordinarySylowInH ≤ normalizer (c.ordinaryFixedRadical.subgroupOf c.H : Set c.H) := by
    intro s hs r
    have hs' : (s : G) ∈ L ⊔ ((T : Subgroup G) ⊓ c.H ⊔ zpowers c.t) :=
      (le_sup_left.trans le_sup_right : (T : Subgroup G) ⊓ c.H ≤ _) hs
    exact c.ordinaryFixedRadical_normalized D hs' (r : G)
  exact (map_mono hn).trans ((c.ordinaryFixedRadical.subgroupOf c.H).le_normalizer_map _)

theorem ordinary_exists_involutory_fixer (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K) :
    ∃ a : MulAut c.K, a ∈ c.ordinaryFixedRadicalImage ∧ orderOf a = 2 ∧
      ∀ l ∈ c.ordinaryLocal, a l = l := by
  obtain ⟨a,ha,hne⟩ := (c.ordinaryFixedRadicalImage.bot_or_exists_ne_one.resolve_left
    (c.ordinaryFixedRadicalImage_ne_bot D ho))
  have hn : (⟨a,ha⟩ : c.ordinaryFixedRadicalImage) ≠ 1 := fun he => hne (congrArg Subtype.val he)
  have hd := (c.ordinaryFixedRadicalImage_isTwoGroup.dvd_orderOf hn).trans
    (orderOf_dvd_natCard (⟨a,ha⟩ : c.ordinaryFixedRadicalImage))
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := c.ordinaryFixedRadicalImage) 2 hd
  refine ⟨b,b.property,?_,?_⟩
  · exact (Subgroup.orderOf_coe b).trans hb
  · have hh := c.ordinaryFixedRadicalImage_fixes_original b.property
    rw [mem_fixingSubgroup_iff] at hh
    exact hh

omit [Finite G] in
/-- The full original Sylow intersection preserves its intersection with K. -/
theorem ordinaryAction_preserves_component_sylow (c : SourceConfiguration T L)
    (s : c.H) (hs : s ∈ c.ordinarySylowInH) :
    (c.ordinarySylowInH.subgroupOf c.K).map (c.ordinaryAction s).toMonoidHom =
      c.ordinarySylowInH.subgroupOf c.K := by
  apply le_antisymm
  · rintro _ ⟨k,hk,rfl⟩
    change s * (k : c.H) * s⁻¹ ∈ c.ordinarySylowInH
    exact c.ordinarySylowInH.mul_mem (c.ordinarySylowInH.mul_mem hs hk)
      (c.ordinarySylowInH.inv_mem hs)
  · intro k hk
    refine ⟨(c.ordinaryAction s).symm k,?_,(c.ordinaryAction s).apply_symm_apply k⟩
    let := c.component_normal
    change ((MulAut.conjNormal s).symm k : c.H) ∈ c.ordinarySylowInH
    rw [MulAut.conjNormal_symm_apply]
    exact c.ordinarySylowInH.mul_mem
      (c.ordinarySylowInH.mul_mem (c.ordinarySylowInH.inv_mem hs) hk) hs

/-- The literal S ∩ K is a Sylow subgroup of the actual component. -/
theorem ordinary_component_sylow (c : SourceConfiguration T L) :
    ∃ P : Sylow 2 c.K, (P : Subgroup c.K) = c.ordinarySylowInH.subgroupOf c.K := by
  obtain ⟨S,hS⟩ := c.sylow
  have he : (S : Subgroup c.H) = c.ordinarySylowInH := by
    apply map_injective c.H.subtype_injective
    rw [map_subgroupOf_eq_of_le inf_le_right]
    exact hS
  let := c.component_normal
  simpa only [he] using S.exists_subgroupOf_eq_of_normal c.K

/-- The image of the original S is Sylow in the actual conjugation image of H. -/
theorem ordinary_action_sylow (c : SourceConfiguration T L) :
    ∃ P : Sylow 2 c.ordinaryAction.range,
      (P : Subgroup c.ordinaryAction.range).map c.ordinaryAction.range.subtype =
        c.ordinarySylowInH.map c.ordinaryAction := by
  obtain ⟨S,hS⟩ := c.sylow
  have he : (S : Subgroup c.H) = c.ordinarySylowInH := by
    apply map_injective c.H.subtype_injective
    rw [map_subgroupOf_eq_of_le inf_le_right]
    exact hS
  refine ⟨S.mapSurjective c.ordinaryAction.rangeRestrict_surjective,?_⟩
  rw [Sylow.coe_mapSurjective,map_map,he]
  rfl

/-- The original ordinary component has a two-group center, not an assumed trivial center. -/
theorem ordinary_center_eq_twoCore (c : SourceConfiguration T L)
    (ho : IsComponent c.H c.K) : center c.K = pCore 2 c.K := by
  let := ho.2
  exact IsQuasisimple.center_eq_pCore (ho.1.pPrimeCore_eq_bot c.c28.oddCore_eq_bot c.K)

omit [Finite G] in
theorem ordinaryLocal_le (c : SourceConfiguration T L) : L.subgroupOf c.H ≤ c.K := by
  intro x hx
  obtain ⟨k,hk,he⟩ := c.le_component hx
  exact (Subtype.ext he : k = x) ▸ hk

/-- Literal identification of the original local inside K with L. -/
@[expose] noncomputable def ordinaryLocalEquiv (c : SourceConfiguration T L) :
    c.ordinaryLocal ≃* L :=
  (subgroupOfEquivOfLe (ordinaryLocal_le c)).trans
    (subgroupOfEquivOfLe (c.le_I.trans c.I_le_H))

omit [Finite G] in
/-- The source normalizer hypothesis collapses the original conjugate span. -/
theorem ordinary_span_eq (c : SourceConfiguration T L) :
    conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
  le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)

omit [Finite G] in
theorem ordinaryLocal_perfect (c : SourceConfiguration T L) :
    Group.IsPerfect c.ordinaryLocal := by
  let : Group.IsPerfect L := c.ordinary_span_eq ▸ c.c28.span_perfect
  exact Group.IsPerfect.ofSurjective
    (f := c.ordinaryLocalEquiv.symm.toMonoidHom) c.ordinaryLocalEquiv.symm.surjective

/-- The original local remains nontrivial and perfect after the actual central quotient. -/
theorem ordinary_quotient_local_nonsolvable (c : SourceConfiguration T L)
    (ho : IsComponent c.H c.K) :
    ¬ Group.IsSolvable (c.ordinaryLocal.map (QuotientGroup.mk' (center c.K))) := by
  have hL : L ≠ ⊥ := by
    intro he
    have hh := c.c28.module_le
    rw [c.ordinary_span_eq] at hh
    exact c.c28.module_nontrivial (bot_unique (hh.trans he.le))
  let : Nontrivial L := L.nontrivial_iff_ne_bot.mpr hL
  let : Nontrivial c.ordinaryLocal := c.ordinaryLocalEquiv.toEquiv.nontrivial
  let := c.ordinaryLocal_perfect
  let q := QuotientGroup.mk' (center c.K)
  have hne : c.ordinaryLocal.map q ≠ ⊥ := by
    intro he
    have hle : c.ordinaryLocal ≤ pCore 2 c.K := by
      rw [← c.ordinary_center_eq_twoCore ho]
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff c.ordinaryLocal).mp he
    exact Group.IsPerfect.not_isNilpotent c.ordinaryLocal (pCore_isPGroup.to_le hle).isNilpotent
  let : Nontrivial (c.ordinaryLocal.map q) := (c.ordinaryLocal.map q).nontrivial_iff_ne_bot.mpr hne
  let : Group.IsPerfect (c.ordinaryLocal.map q) := Group.IsPerfect.map q
  exact Group.IsPerfect.not_isSolvable _

/-- The same nonidentity source involution survives passage to any marked central quotient. -/
theorem ordinary_exists_quotient_involutory_fixer (c : SourceConfiguration T L)
    (D : Chapter12.Section02.ChosenModule T L V) (ho : IsComponent c.H c.K)
    {S : Type*} [Group S] (e : (c.K ⧸ center c.K) ≃* S) :
    ∃ a : MulAut S, orderOf a = 2 ∧
      ∀ l ∈ c.ordinaryLocal.map (e.toMonoidHom.comp (QuotientGroup.mk' (center c.K))), a l = l := by
  let := ho.2
  obtain ⟨a,ha,hao,hfix⟩ := c.ordinary_exists_involutory_fixer D ho
  refine ⟨MulAut.centralQuotientAction e a,?_,?_⟩
  · exact (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) a).trans hao
  · rintro l ⟨k,hk,rfl⟩
    exact (MulAut.centralQuotientAction_apply e a k).trans
      (congrArg (fun x => e (QuotientGroup.mk' (center c.K) x)) (hfix k hk))


omit [Finite G] in
/-- The fixed radical's actual image preserves the same S ∩ K, without
changing the Sylow subgroup by model conjugacy. -/
theorem ordinaryFixedRadicalImage_preserves_component_sylow
    (c : SourceConfiguration T L) {a : MulAut c.K}
    (ha : a ∈ c.ordinaryFixedRadicalImage) :
    (c.ordinarySylowInH.subgroupOf c.K).map a.toMonoidHom =
      c.ordinarySylowInH.subgroupOf c.K := by
  obtain ⟨s,hs,rfl⟩ := c.ordinaryFixedRadicalImage_le_sylowImage ha
  exact c.ordinaryAction_preserves_component_sylow s hs

omit [Finite G] in
/-- Centralization here is in the actual automorphism image of the original L. -/
theorem ordinaryFixedRadicalImage_centralizes_original_image
    (c : SourceConfiguration T L) :
    c.ordinaryFixedRadicalImage ≤
      centralizer ((L.subgroupOf c.H).map c.ordinaryAction : Set (MulAut c.K)) := by
  rintro _ ⟨r,hr,rfl⟩ _ ⟨l,hl,rfl⟩
  rw [← map_mul,← map_mul]
  exact congrArg c.ordinaryAction (Subtype.ext (hr.2 l hl))

/-- The literal KS subgroup, inside H, whose faithful quotient occurs in 4.3.6. -/
abbrev ordinaryKS (c : SourceConfiguration T L) : Subgroup c.H :=
  c.K ⊔ c.ordinarySylowInH

/-- Restrict the original conjugation action to the source KS. -/
@[expose] noncomputable def ordinaryKSAction (c : SourceConfiguration T L) :
    c.ordinaryKS →* MulAut c.K := c.ordinaryAction.comp c.ordinaryKS.subtype

omit [Finite G] in
/-- The kernel is the literal C_{KS}(K), with no center removed by assumption. -/
theorem ordinaryKSAction_ker (c : SourceConfiguration T L) :
    c.ordinaryKSAction.ker = (centralizer (c.K : Set c.H)).subgroupOf c.ordinaryKS := by
  change c.ordinaryAction.ker.comap c.ordinaryKS.subtype = _
  rw [c.ordinaryAction_ker]
  rfl

/-- The faithful quotient used in the source is the actual automorphism image. -/
noncomputable def ordinaryKSQuotientEquiv (c : SourceConfiguration T L) :
    (c.ordinaryKS ⧸ c.ordinaryKSAction.ker) ≃* c.ordinaryKSAction.range :=
  QuotientGroup.quotientKerEquivRange c.ordinaryKSAction

omit [Finite G] in
/-- The same R₀ image lies in the source KS action, not just in Aut(K). -/
theorem ordinaryFixedRadicalImage_le_KSAction_range (c : SourceConfiguration T L) :
    c.ordinaryFixedRadicalImage ≤ c.ordinaryKSAction.range := by
  rintro _ ⟨r,hr,rfl⟩
  refine ⟨⟨r,?_⟩,rfl⟩
  exact (le_sup_right : c.ordinarySylowInH ≤ c.ordinaryKS)
    (c.ordinaryFixedRadical_le_sylow hr)

/-- In KS/C_{KS}(K), the unchanged source S still maps to a Sylow subgroup. -/
theorem ordinary_KS_action_sylow (c : SourceConfiguration T L) :
    ∃ P : Sylow 2 c.ordinaryKSAction.range,
      (P : Subgroup c.ordinaryKSAction.range).map c.ordinaryKSAction.range.subtype =
        c.ordinarySylowInH.map c.ordinaryAction := by
  obtain ⟨S,hS⟩ := c.sylow
  have he : (S : Subgroup c.H) = c.ordinarySylowInH := by
    apply map_injective c.H.subtype_injective
    rw [map_subgroupOf_eq_of_le inf_le_right]
    exact hS
  have hs : (S : Subgroup c.H) ≤ c.ordinaryKS := he.le.trans le_sup_right
  let Q := S.subtype hs
  refine ⟨Q.mapSurjective c.ordinaryKSAction.rangeRestrict_surjective,?_⟩
  rw [Sylow.coe_mapSurjective,map_map]
  change (Q : Subgroup c.ordinaryKS).map
    (c.ordinaryAction.comp c.ordinaryKS.subtype) = _
  rw [←map_map]
  have hQ : (Q : Subgroup c.ordinaryKS).map c.ordinaryKS.subtype = (S : Subgroup c.H) :=
    map_subgroupOf_eq_of_le hs
  rw [hQ,he]

end SourceConfiguration
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
