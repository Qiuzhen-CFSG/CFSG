module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.SourceSelectionOrdinaryNormalizer
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.SylowNormalIntersection
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Quotients
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# The ordinary source action before full-normalizer identification

For the aligned outside choice, R = O₂(I) equals S ∩ O₂(LT), where
S = T ∩ H. A strict extension of S inside its normalizer in T preserves
R and L. Uniqueness over that extension controls N_G(C_R(L)). Since the
ordinary component K centralizes the nontrivial O₂(H), C_R(L) is nontrivial;
escape of K then forces its conjugation image in Aut(K) to be nontrivial.
Cauchy and perfect central-quotient rigidity give the actual involutory fixer.

The original full Sylow and local C-component descend through K/Z(K).
These constructions require relative normality K ◁ H, rather than the
still unproved identification H = N_G(K). SourceSelectionOrdinaryRows
uses them to remove genuine ordinary model cases from that identification.
The earlier SourceConfiguration APIs remain unchanged.

Source: Aschbacher–Smith 4.3.3–6, printed pp.613–615. The action and quotient
calculations adapt OrdinaryPreparation, OrdinaryRecognitionAction and
OrdinaryRecognitionPlacement to the earlier OutsideChoice boundary.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
namespace OutsideChoice

/-- The fixed part of the selected intermediate radical, before full-normalizer equality. -/
noncomputable abbrev ordinaryFixedRadical (c : OutsideChoice T L) : Subgroup G :=
  c.intermediate.pCoreIn 2 ⊓ centralizer (L : Set G)

/-- The original L viewed through the two literal subgroup inclusions. -/
abbrev ordinaryLocal (c : OutsideChoice T L) (K : Subgroup c.H) : Subgroup K :=
  (L.subgroupOf c.H).subgroupOf K

/-- Conjugation by H on its relatively normal component. -/
@[expose] noncomputable def ordinaryAction (c : OutsideChoice T L)
    (K : Subgroup c.H) (hKN : K.Normal) : c.H →* MulAut K := by
  let := hKN
  exact MulAut.conjNormal

/-- The fixed radical lies in the original full Sylow intersection. -/
theorem ordinaryFixedRadical_le_sylow
    (c : OutsideChoice T L) (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    c.ordinaryFixedRadical ≤ (T : Subgroup G) ⊓ c.H := by
  rw [ordinaryFixedRadical,c.intermediate_core D h]
  exact le_inf (inf_le_left.trans (inf_le_left.trans
    ((source_core_section_intersection D h).le.trans inf_le_left)))
    (inf_le_left.trans inf_le_right)

/-- The nontrivial two-core of H lies in the fixed radical. -/
theorem ordinaryFixedRadical_ne_bot
    (c : OutsideChoice T L) (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (K : Subgroup c.H) (ho : IsComponent c.H K) (hLK : L ≤ K.map c.H.subtype) :
    c.ordinaryFixedRadical ≠ ⊥ := by
  have hQ : c.H.pCoreIn 2 ≤ c.ordinaryFixedRadical :=
    le_inf (core_le_of_relative_radical (c.c28 D h).isRadical)
      ((c.ordinary_core_centralizes K ho).trans (centralizer_le hLK))
  exact fun he => (c.c28 D h).core_nontrivial (bot_unique (hQ.trans_eq he))

/-- Strict-extension uniqueness controls the ambient fixed-radical normalizer. -/
theorem ordinaryFixedRadical_normalizer_le
    (c : OutsideChoice T L) (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (K : Subgroup c.H) (ho : IsComponent c.H K) (hLK : L ≤ K.map c.H.subtype) :
    normalizer (c.ordinaryFixedRadical : Set G) ≤ normalizer (L : Set G) := by
  let S := (T : Subgroup G) ⊓ c.H
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  obtain ⟨t,ht,htout,htn,_⟩ := exists_outside_normalizer_square_mem _ _ T.isPGroup'
    (c.sylow_data D h hpsl).1
  let X := S ⊔ zpowers t
  have hSX : S < X := by
    apply lt_of_le_of_ne le_sup_left
    intro he
    exact htout (he.ge (mem_sup_right (mem_zpowers t)))
  have hXT : X ≤ (T : Subgroup G) := sup_le inf_le_left (zpowers_le.mpr ht)
  have hXS : X ≤ normalizer (S : Set G) := sup_le S.le_normalizer (zpowers_le.mpr htn)
  have hQT : Q ≤ (T : Subgroup G) :=
    (source_core_section_intersection D h).le.trans inf_le_left
  have hR : c.intermediate.pCoreIn 2 = S ⊓ Q := by
    rw [c.intermediate_core D h]
    apply le_antisymm
    · exact le_inf (le_inf (inf_le_left.trans hQT) inf_le_right) inf_le_left
    · exact le_inf inf_le_right (inf_le_left.trans inf_le_right)
  have hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G) :=
    le_sup_right.trans ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hLR : L ≤ normalizer (c.intermediate.pCoreIn 2 : Set G) :=
    (le_conjugateSpanBy L _).trans (c.c28 D h).span_normalizes_radical
  have hXR : X ≤ normalizer (c.intermediate.pCoreIn 2 : Set G) := by
    rw [hR]
    exact (le_inf hXS (hXT.trans hTQ)).trans inf_normalizer_le_normalizer_inf
  have hn : L ⊔ X ≤ normalizer (c.ordinaryFixedRadical : Set G) :=
    (le_inf (sup_le hLR hXR)
      ((sup_le L.le_normalizer (hXT.trans D.sylow_normalizes_component)).trans
        (normalizer_le_normalizer_centralizer L))).trans inf_normalizer_le_normalizer_inf
  exact normalizer_le_of_unique_maximalTwoLocal (c.strict_unique D h hSX hXT).2.2
    ((isPGroup_pCoreIn 2 c.intermediate).to_le inf_le_left)
    (c.ordinaryFixedRadical_ne_bot D h K ho hLK) hn

/-- Escape of K forces the fixed radical to act nontrivially on K. -/
theorem ordinaryFixedRadical_not_centralizes
    (c : OutsideChoice T L) (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (K : Subgroup c.H) (ho : IsComponent c.H K) (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) :
    ¬ c.ordinaryFixedRadical ≤ centralizer (K.map c.H.subtype : Set G) := by
  intro hc
  exact hout ((le_centralizer_iff.mp hc).trans ((Subgroup.centralizer_le_normalizer _).trans
    (c.ordinaryFixedRadical_normalizer_le D h hpsl K ho hLK)))

/-- Cauchy supplies an involution in the actual fixed-radical action on K. -/
theorem ordinary_exists_involutory_fixer
    (c : OutsideChoice T L) (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (K : Subgroup c.H) (ho : IsComponent c.H K) (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal) :
    ∃ a : MulAut K, orderOf a = 2 ∧ ∀ l ∈ c.ordinaryLocal K, a l = l := by
  let f := c.ordinaryAction K hKN
  let A := (c.ordinaryFixedRadical.subgroupOf c.H).map f
  have hp : IsPGroup 2 A :=
    ((isPGroup_pCoreIn 2 c.intermediate).to_le inf_le_left).comap_subtype.map f
  have hne : A ≠ ⊥ := by
    intro he
    have hk := (map_eq_bot_iff (c.ordinaryFixedRadical.subgroupOf c.H)).mp he
    apply c.ordinaryFixedRadical_not_centralizes D h hpsl K ho hLK hout
    intro r hr k hkK
    obtain ⟨k,hkK,rfl⟩ := hkK
    let rH : c.H := ⟨r,(c.ordinaryFixedRadical_le_sylow D h hr).2⟩
    have hh := DFunLike.congr_fun (hk (show rH ∈ c.ordinaryFixedRadical.subgroupOf c.H from hr))
      (⟨k,hkK⟩ : K)
    have hh' := congrArg (fun b : K => ((b : c.H) : G)) hh
    change r * (k : G) * r⁻¹ = (k : G) at hh'
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  obtain ⟨a,ha,hane⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have ha1 : (⟨a,ha⟩ : A) ≠ 1 := fun he => hane (congrArg Subtype.val he)
  have hd := (hp.dvd_orderOf ha1).trans (orderOf_dvd_natCard (⟨a,ha⟩ : A))
  obtain ⟨b,hb⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 hd
  refine ⟨b,(Subgroup.orderOf_coe b).trans hb,?_⟩
  obtain ⟨r,hr,he⟩ := b.property
  intro l hl
  rw [←he]
  apply Subtype.ext
  apply Subtype.ext
  change (r : G) * ((l : c.H) : G) * (r : G)⁻¹ = ((l : c.H) : G)
  exact mul_inv_eq_iff_eq_mul.mpr (hr.2 _ hl).symm

/-- The same source involution survives any actual central-quotient marking. -/
theorem ordinary_exists_quotient_involutory_fixer
    (c : OutsideChoice T L) (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (K : Subgroup c.H) (ho : IsComponent c.H K) (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal)
    {J : Type*} [Group J] (e : (K ⧸ center K) ≃* J) :
    ∃ a : MulAut J, orderOf a = 2 ∧
      ∀ l ∈ (c.ordinaryLocal K).map (e.toMonoidHom.comp (QuotientGroup.mk' (center K))),
        a l = l := by
  let := ho.2
  obtain ⟨a,hao,hfix⟩ := c.ordinary_exists_involutory_fixer D h hpsl K ho hLK hout hKN
  refine ⟨MulAut.centralQuotientAction e a,?_,?_⟩
  · exact (orderOf_injective (MulAut.centralQuotientAction e)
      (MulAut.centralQuotientAction_injective e) a).trans hao
  · rintro l ⟨k,hk,rfl⟩
    exact (MulAut.centralQuotientAction_apply e a k).trans
      (congrArg (fun x => e (QuotientGroup.mk' (center K) x)) (hfix k hk))

omit [Finite G] in
/-- Containment of the original L through the inclusion K ≤ H. -/
theorem ordinaryLocal_le (c : OutsideChoice T L) {K : Subgroup c.H}
    (hLK : L ≤ K.map c.H.subtype) : L.subgroupOf c.H ≤ K := by
  intro x hx
  obtain ⟨k,hk,he⟩ := hLK hx
  exact (Subtype.ext he : k = x) ▸ hk

/-- The embedded local subgroup is literally isomorphic to the original L. -/
@[expose] noncomputable def ordinaryLocalEquiv (c : OutsideChoice T L)
    {K : Subgroup c.H} (hLK : L ≤ K.map c.H.subtype) : c.ordinaryLocal K ≃* L :=
  (subgroupOfEquivOfLe (c.ordinaryLocal_le hLK)).trans (subgroupOfEquivOfLe c.contains)

/-- The same local pair descends to every central quotient model, with the
full Sylow intersection and the original embedding of L. -/
theorem ordinary_model_local_data
    (c : OutsideChoice T L) (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (K : Subgroup c.H) (ho : IsComponent c.H K) (hLK : L ≤ K.map c.H.subtype)
    (hout : ¬ K.map c.H.subtype ≤ normalizer (L : Set G)) (hKN : K.Normal)
    {J : Type*} [Group J] (e : (K ⧸ center K) ≃* J) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    ∃ P : Sylow 2 K,
      (P : Subgroup K) = (((T : Subgroup G) ⊓ c.H).subgroupOf c.H).subgroupOf K ∧
      (c.ordinaryLocal K).map f ∈ ChapterA.Section03.localCComponents
        (P.mapSurjective (f := f) (e.surjective.comp (QuotientGroup.mk'_surjective (center K))) : Subgroup J) ∧
      (c.ordinaryLocal K).map f ≠ ⊤ := by
  let := hKN
  let := ho.2
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hk : f.ker = center K := by
    ext k
    change e (QuotientGroup.mk' (center K) k) = 1 ↔ k ∈ center K
    rw [←map_one e,e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff k
  let : Group.IsSolvable f.ker := by
    rw [hk]
    exact Group.isSolvable_of_comm fun x y => mul_comm x y
  obtain ⟨S,hS⟩ := (c.sylow_data D h hpsl).2.2
  have he : (S : Subgroup c.H) = ((T : Subgroup G) ⊓ c.H).subgroupOf c.H := by
    apply map_injective c.H.subtype_injective
    rw [map_subgroupOf_eq_of_le inf_le_right]
    exact hS
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal K
  have hl : L.subgroupOf c.H ∈ ChapterA.Section03.localCComponents S := by
    rw [he]
    exact (c.local_component D h hpsl).1
  have hlK := ChapterA.Section03.SourceEmbeddings.local_restrict hl (c.ordinaryLocal_le hLK)
  rw [←hP] at hlK
  refine ⟨P,hP.trans (congrArg (fun S : Subgroup c.H => S.subgroupOf K) he),
    Chapter1.Section02.localCComponents_map_of_solvable_ker hlK f,?_⟩
  intro htop
  have ht : (⊤ : Subgroup K) ≤ c.ordinaryLocal K :=
    perfect_le_of_map_le_of_central_kernel f (by rw [hk]) ⊤ (c.ordinaryLocal K)
      (by rw [htop]; exact le_top)
  apply hout
  rintro _ ⟨k,hk,rfl⟩
  exact L.le_normalizer (ht (show (⟨k,hk⟩ : K) ∈ (⊤ : Subgroup K) from trivial))

/-- A central quotient preserves nonsolvability of the original perfect L. -/
theorem ordinary_quotient_local_nonsolvable
    (c : OutsideChoice T L) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (K : Subgroup c.H) (hLK : L ≤ K.map c.H.subtype)
    {J : Type*} [Group J] (e : (K ⧸ center K) ≃* J) :
    ¬ Group.IsSolvable ((c.ordinaryLocal K).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (center K)))) := by
  let A := c.ordinaryLocal K
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let a := c.ordinaryLocalEquiv hLK
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_faithful.1.1
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := a.symm.toMonoidHom) a.symm.surjective
  have hne : A.map f ≠ ⊥ := by
    intro he
    have hker := (map_eq_bot_iff A).mp he
    have hcent : A ≤ center K := by
      intro x hx
      have hh : e (QuotientGroup.mk' (center K) x) = 1 := hker hx
      exact (QuotientGroup.eq_one_iff x).mp
        (e.injective (hh.trans (map_one e).symm))
    have hcomm : IsMulCommutative A := by
      refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
      exact mem_center_iff.mp (hcent y.property) x
    let := hcomm
    have hsol : Group.IsSolvable L := Group.isSolvable_of_surjective (f := a.toMonoidHom) a.surjective
    exact Chapter1.mem_L_not_isSolvable h.maximal_faithful.1.1 hsol
  let : Nontrivial (A.map f) := (A.map f).nontrivial_iff_ne_bot.mpr hne
  let : Group.IsPerfect (A.map f) := Group.IsPerfect.map f
  exact Group.IsPerfect.not_isSolvable _

end OutsideChoice
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
