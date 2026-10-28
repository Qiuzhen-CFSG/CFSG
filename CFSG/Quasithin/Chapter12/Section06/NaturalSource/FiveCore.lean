module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ResidualOrthogonal
public import Theory.GroupTheory.PResidual.NormalizerLift
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupAction.SupercriticalDetection
public import Theory.GroupAction.SupercriticalTwoPerfect
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical

/-!
# The original moved five-core and its supercritical models

F.9's exact centralizer preimage places O₂(H) in N_H(V). Local uniqueness
then puts it in N_G(L), and the original point centralizer makes it
normalize L₁. Recovering this two-perfect residual from its quotient
preimage lifts the full normalizer of L₁-star through H → H/O₂(H).

The proved normalizing-pair exclusion and Baer--Suzuki put V in the
two-core of N_H(L₁), hence V-star in the two-core of N_{H-star}(L₁-star).
Every odd normal core contained in this normalizer is therefore centralized
by V-star. In particular a moved five-core cannot centralize L₁-star.

Choose an actual supercritical subgroup of that five-core. The original
L₁ has order prime to five, so coprime detection retains its nontrivial
conjugation action, as well as the nontrivial V-star action. A.1.25 supplies
the elementary plane or extraspecial group of order 125, with genuine
model isomorphisms. The cyclic order-five alternative would give a
nontrivial two-group image of the two-perfect L₁ and is impossible.

All actions are restrictions of conjugation in the literal H/O₂(H).
The earlier geometry remains explicit. Irreducibility on the supercritical
Frattini quotient, inversion, the binary displacement contradiction,
five-core centralization and the final source theorem remain obligations.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original two-core normalizes the original point residual. -/
theorem SourceHypothesis.original_core_normalizes_point_residual
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    H.pCoreIn 2 ≤ normalizer ((D.fullSetup hZ T z).L₁ : Set G) := by
  let E := D.fullSetup hZ T z
  have he := (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.2.2.2
  have hNV : normalizer (V : Set G) ≤ normalizer (L : Set G) :=
    S.chosen.normal_subgroup_normalizer_le S.source.toHypothesis1221
      (S.chosen.le_sylow.trans le_sup_right) S.chosen.ne_bot
      (sup_le S.chosen.normalizes hTV)
  have hQV : H.pCoreIn 2 ≤ normalizer (V : Set G) := by
    rintro _ ⟨x,hx,rfl⟩
    have hh : x ∈ (centralizer (Nonabelian.Setup.star H V : Set (H ⧸ pCore 2 H))).comap
        (QuotientGroup.mk' (pCore 2 H)) := by
      change QuotientGroup.mk' (pCore 2 H) x ∈ centralizer (Nonabelian.Setup.star H V : Set (H ⧸ pCore 2 H))
      rw [show QuotientGroup.mk' (pCore 2 H) x = 1 from (QuotientGroup.eq_one_iff _).mpr hx]
      exact one_mem _
    rwa [he] at hh
  have hQG : H.pCoreIn 2 ≤ normalizer (E.Gz : Set G) :=
    (pCoreIn_le 2 H).trans (hH.2.1.trans E.Gz.le_normalizer)
  exact ((le_inf (hQV.trans hNV) hQG).trans inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image (L ⊓ E.Gz) (pResidual 2 (L ⊓ E.Gz : Subgroup G)))

/-- The normalizing-pair theorem puts V in the two-core of the relative normalizer. -/
theorem SourceHypothesis.original_module_le_residualNormalizer_twoCore
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    V ≤ (H ⊓ normalizer ((D.fullSetup hZ T z).L₁ : Set G)).pCoreIn 2 := by
  classical
  by_contra hnot
  let E := D.fullSetup hZ T z
  let N := H ⊓ normalizer (E.L₁ : Set G)
  have hVN : V ≤ N := by
    intro v hv
    obtain ⟨hH,hN,_⟩ := (E.mem_residualCentralizer H v).mp
      (S.original_module_le_residualCentralizer D hZ z hH hv)
    exact ⟨hH,hN⟩
  obtain ⟨g,hg,_,hpair⟩ := exists_noncentralizing_conjugate_sup_not_isPGroup
    N V hVN (IsElementaryAbelian.isPGroup 2 V) hnot
  exact hpair (S.original_normalizing_pair_isTwoGroup D hZ z hz hTV hTz hbound hns hH hn g hg.1 hg.2)

/-- The two-core bound holds in the actual quotient normalizer, with full preimage lifting. -/
theorem SourceHypothesis.original_star_module_le_residualNormalizer_twoCore
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    Nonabelian.Setup.star H V ≤
      (normalizer (Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ : Set (H ⧸ pCore 2 H))).pCoreIn 2 := by
  let E := D.fullSetup hZ T z
  let A := E.L₁.subgroupOf H
  let q := QuotientGroup.mk' (pCore 2 H)
  let N := H ⊓ normalizer (E.L₁ : Set G)
  have hAH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hpA : IsPPerfect 2 A :=
    (isPPerfect_embedded_pResidual 2 (L ⊓ E.Gz)).of_surjective
      (subgroupOfEquivOfLe hAH).symm.toMonoidHom (subgroupOfEquivOfLe hAH).symm.surjective
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hnq : q.ker ≤ normalizer (A : Set H) := by
    rw [QuotientGroup.ker_mk',←subgroupOf_normalizer_eq hAH]
    intro x hx
    exact S.original_core_normalizes_point_residual D hZ z hz hTV hTz hbound hH hn
      (mem_map_of_mem H.subtype hx)
  have hNe : N.subgroupOf H = normalizer (A : Set H) := by
    rw [←subgroupOf_normalizer_eq hAH]
    ext x
    exact and_iff_right x.property
  have hmap : (N.subgroupOf H).map q = normalizer (A.map q : Set (H ⧸ pCore 2 H)) := by
    rw [hNe]
    apply le_antisymm (A.le_normalizer_map q)
    intro x hx
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
    exact mem_map_of_mem q (Subgroup.normalizer_comap_map_le_of_pGroup_kernel q A hpA hk hnq hx)
  have hV : V ≤ N.pCoreIn 2 :=
    S.original_module_le_residualNormalizer_twoCore D hZ z hz hTV hTz hbound hns hH hn
  have hm := map_mono (f := q) (comap_mono (f := H.subtype) hV)
  change (V.subgroupOf H).map q ≤ ((N.pCoreIn 2).subgroupOf H).map q at hm
  rw [←pCoreIn_subgroupOf 2 N H inf_le_left,map_pCoreIn_of_ker_isPGroup q hk,hmap] at hm
  exact hm

/-- A normal odd core lying in the residual normalizer is centralized by V-star. -/
theorem SourceHypothesis.original_star_odd_core_centralized_of_normalizes_residual
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hnorm : pCore p (H ⧸ pCore 2 H) ≤
      normalizer (Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ : Set (H ⧸ pCore 2 H))) :
    Nonabelian.Setup.star H V ≤ centralizer (pCore p (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H)) := by
  let N := normalizer (Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ : Set (H ⧸ pCore 2 H))
  have hV := S.original_star_module_le_residualNormalizer_twoCore D hZ z hz hTV hTz hbound hns hH hn
  have hP : (pCore p (H ⧸ pCore 2 H)).subgroupOf N ≤ pCore p N :=
    le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
  intro v hv x hx
  obtain ⟨v0,hv0,rfl⟩ := hV hv
  exact congrArg Subtype.val (pCore_commute_of_ne p 2 hp ⟨x,hnorm hx⟩ (hP hx) v0 hv0)


/-- The original point residual has order prime to five. -/
theorem SourceHypothesis.original_point_residual_five_coprime
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G)) :
    Nat.Coprime (Nat.card (D.fullSetup hZ T z).L₁) 5 := by
  obtain ⟨_,_,_,e,_,_⟩ := S.original_point_residual_quotient D hZ z hz hTz
  have hc : Nat.card ((D.fullSetup hZ T z).L₁ ⧸ pCore 2 (D.fullSetup hZ T z).L₁) = 9 :=
    (Nat.card_congr e.toEquiv).trans BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9_card
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := (D.fullSetup hZ T z).L₁)).exists_card_eq
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 (D.fullSetup hZ T z).L₁),hc,hn]
  exact (by decide : Nat.Coprime 9 5).mul_left ((by decide : Nat.Coprime 2 5).pow_left n)

/-- A moved five-core has an actual E25 or extraspecial-125 supercritical subgroup.
Both V-star and the original L₁ retain nontrivial conjugation actions on it. -/
theorem SourceHypothesis.original_five_supercritical_models
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (hm : ¬ Nonabelian.Setup.star H V ≤
      centralizer (pCore 5 (H ⧸ pCore 2 H) : Set (H ⧸ pCore 2 H))) :
    let E := D.fullSetup hZ T z
    let R := pCore 5 (H ⧸ pCore 2 H)
    ∃ (Y : Subgroup R) (hY : IsSupercriticalPSubgroup 5 Y),
      letI : Y.Characteristic := hY.characteristic
      let a := (MulAut.characteristic Y).comp
        (MulAut.conjNormal : (H ⧸ pCore 2 H) →* MulAut R)
      ((Nat.card Y = 25 ∧ Nonempty (Y ≃* (Multiplicative (ZMod 5) × Multiplicative (ZMod 5)))) ∨
       (Nat.card Y = 125 ∧ IsExtraspecial 5 Y ∧ Nonempty (Y ≃* HeisenbergPrime 5))) ∧
      (Nonabelian.Setup.star H V).map a ≠ ⊥ ∧
      (Nonabelian.Setup.star H E.L₁).map a ≠ ⊥ := by
  let E := D.fullSetup hZ T z
  let R := pCore 5 (H ⧸ pCore 2 H)
  let B := Nonabelian.Setup.star H E.L₁
  have hmove : ¬ B ≤ centralizer (R : Set (H ⧸ pCore 2 H)) := by
    intro hc
    exact hm (S.original_star_odd_core_centralized_of_normalizes_residual D hZ z hz hTV hTz hbound hns hH hn
      (by decide : 5 ≠ 2) ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)))
  have hRne : R ≠ ⊥ := by
    intro he
    apply hmove
    rw [he]
    intro x _ y hy
    rw [mem_bot.mp hy]
    simp
  let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr hRne
  have hR : IsPGroup 5 R := pCore_isPGroup
  obtain ⟨Y,hY⟩ := hR.exists_supercriticalPSubgroup (by decide : 5 ≠ 2)
  let : Y.Characteristic := hY.characteristic
  let α : (H ⧸ pCore 2 H) →* MulAut R := MulAut.conjNormal
  let a := (MulAut.characteristic Y).comp α
  have hAH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  let j := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hAH)
  have hj : j.range = B := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact mem_map_of_mem _ y.property
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y.val,hy⟩,rfl⟩
  have hαj : α.comp j ≠ 1 := by
    intro he
    apply hmove
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    intro x hx
    rw [←hj] at hx
    obtain ⟨y,rfl⟩ := hx
    exact DFunLike.congr_fun he y
  have haj : a.comp j ≠ 1 := hY.coprime_action_ne_one hR (by decide) (α.comp j) hαj
    (S.original_point_residual_five_coprime D hZ z hz hTz)
  have hB : B.map a ≠ ⊥ := by
    intro he
    apply haj
    apply MonoidHom.ext
    intro x
    exact mem_bot.mp (he ▸ mem_map_of_mem a (hj ▸ (show j x ∈ j.range from ⟨x,rfl⟩)))
  have hV : (Nonabelian.Setup.star H V).map a ≠ ⊥ := by
    apply hY.two_image_ne_bot (by decide) hR α _
      ((IsElementaryAbelian.isPGroup 2 V).comap_subtype.map _) 
    intro he
    apply hm
    rw [←MulAut.conjNormal_ker_eq_centralizer]
    exact (Subgroup.map_eq_bot_iff _).mp he
  have hr : primeRank 5 R ≤ 2 := (primeRank_subgroup_le 5 R).trans
    ((S.original_star_sqtk D hZ z hz hH).stronglyQuasithin 5 (by decide) (by decide))
  have hmodels := (ChapterA.lemma_A_1_25_1 (by decide : Odd 5) hR hr Y hY).2
  refine ⟨Y,hY,?_,hV,hB⟩
  rcases hmodels with ⟨hcyc,_⟩ | hplane | hextra
  · have hAut : IsPGroup 2 (MulAut Y) := by
      let : IsCyclic Y := isCyclic_of_prime_card hcyc
      apply IsPGroup.of_card (n := 2)
      rw [IsCyclic.card_mulAut,hcyc]
      decide
    exact (haj ((isPPerfect_embedded_pResidual 2 (L ⊓ E.Gz)).hom_eq_one_of_isPGroup hAut _)).elim
  · exact Or.inl hplane
  · exact Or.inr hextra

end CFSG.Quasithin.Chapter12.Section06
