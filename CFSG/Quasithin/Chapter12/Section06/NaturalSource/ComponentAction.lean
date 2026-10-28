module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FiveCentralization
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Components.Action
public import Theory.GroupTheory.NormalTwoThreeLayer

/-!
# The original selected component and its faithful local action

The original two-perfect L₁ normalizes the selected C-component K by
1.2.1(3). If K-star centralized L₁-star, the proved placement of V-star
in O₂(N_{H-star}(L₁-star)) would put its full component commutator in a
two-group. Hence [K-star,L₁-star] = K-star.

F.9's exact centralizer preimage also shows that C_{H-star}(V-star)
normalizes L₁-star. Its actual two-core quotient is a three-group, placing
L₁-star in that centralizer's two-three core. This assertion is made in
H-star, before passage to the subsequent faithful action quotient.

Finally construct conjugation of the original X = KL₁V on K-star. The
kernel is literally C_X(K-star), K maps onto Inn(K-star), V has image of
order two, and the nontrivial image of L₁ is two-perfect with order divisible
by three. Both quotient equivalences retain their projection formulas.
The final constructor selects K and supplies this marking from the original
contrary-nonabelian hypotheses, with no assumed component-action output.

The earlier-source geometry remains explicit. Centralizer transport to
X-hat for condition (*), the component exclusions, the abelian point-span
theorem, and the universal natural reduction remain subsequent obligations.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.832.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The original residual normalizes the original C-component in H. -/
theorem SourceHypothesis.original_residual_normalizes_selectedComponent
    (hz : z ≠ 1) {H : Subgroup G}
    (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H) :
    (D.fullSetup hZ T z).L₁ ≤ normalizer (c.K : Set G) := by
  let E := D.fullSetup hZ T z
  have hAH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hp : IsPPerfect 2 (E.L₁.subgroupOf H) :=
    (isPPerfect_embedded_pResidual 2 (L ⊓ E.Gz)).of_surjective
      (subgroupOfEquivOfLe hAH).symm.toMonoidHom (subgroupOfEquivOfLe hAH).symm.surjective
  have hn := Chapter1.Section02.twoPerfect_normalizes_cComponent_source
    (S.original_star_sqtk D hZ z hz hH) c.ccomponent hp
  rw [← subgroupOf_normalizer_eq c.le_H] at hn
  intro x hx
  exact hn (show (⟨x,hAH hx⟩ : H) ∈ E.L₁.subgroupOf H from hx)

/-- The same normalization through the literal H → H/O₂(H) map. -/
theorem SourceHypothesis.original_residual_star_normalizes_selectedComponent
    (hz : z ≠ 1) {H : Subgroup G}
    (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H) :
    Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ ≤
      normalizer (Nonabelian.Setup.star H c.K : Set (H ⧸ pCore 2 H)) := by
  have hn := S.original_residual_normalizes_selectedComponent D hZ z hz hH c
  exact (map_mono ((comap_mono hn).trans (c.K.le_normalizer_comap H.subtype))).trans
    ((c.K.subgroupOf H).le_normalizer_map (QuotientGroup.mk' (pCore 2 H)))

/-- The original L₁-star moves, and hence generates by commutators, the selected component. -/
theorem SourceHypothesis.original_selectedComponent_residual_commutator
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) :
    ⁅Nonabelian.Setup.star H c.K, Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁⁆ =
      Nonabelian.Setup.star H c.K := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let A := Nonabelian.Setup.star H E.L₁
  let N := normalizer (A : Set (H ⧸ pCore 2 H))
  apply c.component.commutator_eq_self_of_normalizes
    (S.original_residual_star_normalizes_selectedComponent D hZ z hz hH c)
  intro hc
  have hBN : B ≤ N := (commutator_eq_bot_iff_le_centralizer.mp hc).trans
    (Subgroup.centralizer_le_normalizer _)
  have hV := S.original_star_module_le_residualNormalizer_twoCore D hZ z hz hTV hTz hbound hns hH hn
  have hnorm : N ≤ normalizer (N.pCoreIn 2 : Set (H ⧸ pCore 2 H)) :=
    N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  have hBcore : B ≤ N.pCoreIn 2 := by
    change Nonabelian.Setup.star H c.K ≤ _
    rw [← c.full_commutator]
    exact (commutator_mono hBN hV).trans
      (le_normalizer_iff_commutator_le_right.mp hnorm)
  have hp : IsPGroup 2 B := (isPGroup_pCoreIn 2 N).to_le hBcore
  let := c.component.2
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : Nontrivial B := (QuotientGroup.mk'_surjective (center B)).nontrivial
  let : Group.IsNilpotent B := hp.isNilpotent
  exact Group.IsPerfect.not_isSolvable B inferInstance


/-- Local uniqueness makes N_H(V) normalize the original point residual. -/
theorem SourceHypothesis.original_module_normalizer_normalizes_residual
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    H ⊓ normalizer (V : Set G) ≤ normalizer ((D.fullSetup hZ T z).L₁ : Set G) := by
  let E := D.fullSetup hZ T z
  have hNV : normalizer (V : Set G) ≤ normalizer (L : Set G) :=
    S.chosen.normal_subgroup_normalizer_le S.source.toHypothesis1221
      (S.chosen.le_sylow.trans le_sup_right) S.chosen.ne_bot
      (sup_le S.chosen.normalizes hTV)
  have hNG : H ⊓ normalizer (V : Set G) ≤ normalizer (E.Gz : Set G) :=
    inf_le_left.trans (hH.2.1.trans E.Gz.le_normalizer)
  exact ((le_inf (inf_le_right.trans hNV) hNG).trans inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image (L ⊓ E.Gz) (pResidual 2 (L ⊓ E.Gz : Subgroup G)))

/-- The full star centralizer of V-star normalizes L₁-star, using F.9’s exact preimage. -/
theorem SourceHypothesis.original_star_centralizer_normalizes_residual
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    centralizer (Nonabelian.Setup.star H V : Set (H ⧸ pCore 2 H)) ≤
      normalizer (Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ : Set (H ⧸ pCore 2 H)) := by
  let E := D.fullSetup hZ T z
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := centralizer (Nonabelian.Setup.star H V : Set (H ⧸ pCore 2 H))
  have he : C.comap q = (normalizer (V : Set G)).subgroupOf H :=
    (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.2.2.2
  have hpre : C.comap q ≤ normalizer (E.L₁.subgroupOf H : Set H) := by
    rw [he]
    intro x hx
    exact E.L₁.le_normalizer_comap H.subtype
      (S.original_module_normalizer_normalizes_residual D hZ z hTV hH ⟨x.property,hx⟩)
  have hm := (map_mono (f := q) hpre).trans ((E.L₁.subgroupOf H).le_normalizer_map q)
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)] at hm
  exact hm

/-- The actual point-residual image remains two-perfect. -/
theorem SourceHypothesis.original_point_residual_star_twoPerfect
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    IsPPerfect 2 (Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁) := by
  let E := D.fullSetup hZ T z
  have hAH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hp : IsPPerfect 2 (E.L₁.subgroupOf H) :=
    (isPPerfect_embedded_pResidual 2 (L ⊓ E.Gz)).of_surjective
      (subgroupOfEquivOfLe hAH).symm.toMonoidHom (subgroupOfEquivOfLe hAH).symm.surjective
  exact hp.of_surjective ((QuotientGroup.mk' (pCore 2 H)).subgroupMap _) (MonoidHom.subgroupMap_surjective _ _)

/-- The E₉ quotient makes the actual residual image two-by-three. -/
theorem SourceHypothesis.original_point_residual_star_twoThree
    (hz : z ≠ 1)
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    IsPGroup 3 ((Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁) ⧸
      pCore 2 (Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁)) := by
  let E := D.fullSetup hZ T z
  have hAH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  obtain ⟨_,_,_,e,_,_⟩ := S.original_point_residual_quotient D hZ z hz hTz
  have hp : IsPGroup 3 (E.L₁ ⧸ pCore 2 E.L₁) :=
    (IsElementaryAbelian.isPGroup 3 BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9).of_equiv e.symm
  let j := (subgroupOfEquivOfLe hAH).symm
  let f := ((QuotientGroup.mk' (pCore 2 H)).subgroupMap (E.L₁.subgroupOf H)).comp j.toMonoidHom
  exact quotient_twoCore_isThreeGroup_of_surjective f
    ((MonoidHom.subgroupMap_surjective _ _).comp j.surjective) hp

/-- Placement in O₂,₃(C_{H-star}(V-star)), with both cores taken intrinsically. -/
theorem SourceHypothesis.original_residual_le_star_centralizer_twoThreeCore
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    let C := centralizer (Nonabelian.Setup.star H V : Set (H ⧸ pCore 2 H))
    (Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁).subgroupOf C ≤
      (pCore 3 (C ⧸ pCore 2 C)).comap (QuotientGroup.mk' (pCore 2 C)) := by
  let A := Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁
  let C := centralizer (Nonabelian.Setup.star H V : Set (H ⧸ pCore 2 H))
  have hAC : A ≤ C := S.original_point_residual_star_centralizes D hZ z hz hTV hTz hbound hH hn
  let : (A.subgroupOf C).Normal := normal_subgroupOf_of_le_normalizer
    (S.original_star_centralizer_normalizes_residual D hZ z hz hTV hTz hbound hH hn)
  apply le_twoThreeCore_of_normal
  let e := (subgroupOfEquivOfLe hAC).symm
  exact quotient_twoCore_isThreeGroup_of_surjective e.toMonoidHom e.surjective
    (S.original_point_residual_star_twoThree D hZ z hz hTz hH)


/-- Normalization of the selected component lifts through the actual
solvable two-core kernel; the component is not merely normalized modulo it. -/
theorem SourceHypothesis.original_module_normalizes_selectedComponent
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (c : (D.fullSetup hZ T z).SelectedComponent H) :
    V ≤ normalizer (c.K : Set G) := by
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  have hv := Subgroup.map_le_iff_le_comap.mp c.normalized
  simp only [Nonabelian.Setup.star] at hv
  rw [normalizer_cComponent_quotient c.ccomponent (pCore 2 H),
    ← subgroupOf_normalizer_eq c.le_H] at hv
  have hVH : V ≤ H := S.chosen.le_sylow.trans (fun x hx => hH.1.2 (Or.inr hx))
  intro v hvV
  exact hv (show (⟨v,hVH hvV⟩ : H) ∈ V.subgroupOf H from hvV)

/-- Construct the action of the original KL₁V with its exact centralizer kernel and all three marked images. -/
theorem SourceHypothesis.original_selectedComponent_action
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) :
    Nonempty c.ActionMarking := by
  let E := D.fullSetup hZ T z
  let X := c.K ⊔ E.L₁ ⊔ V
  let B := Nonabelian.Setup.star H c.K
  let A := Nonabelian.Setup.star H E.L₁
  let U := Nonabelian.Setup.star H V
  let N := normalizer (B : Set (H ⧸ pCore 2 H))
  let q := QuotientGroup.mk' (pCore 2 H)
  have hAH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  have hVH : V ≤ H := S.chosen.le_sylow.trans (fun x hx => hH.1.2 (Or.inr hx))
  have hAX : E.L₁ ≤ X := le_sup_right.trans le_sup_left
  have hVX : V ≤ X := le_sup_right
  have hXH : X ≤ H := sup_le (sup_le c.le_H hAH) hVH
  have hAN : A ≤ N := S.original_residual_star_normalizes_selectedComponent D hZ z hz hH c
  have hUN : U ≤ N := c.normalized
  have hXN : Nonabelian.Setup.star H X ≤ N := by
    change ((c.K ⊔ E.L₁ ⊔ V).subgroupOf H).map q ≤ N
    rw [subgroupOf_sup (sup_le c.le_H hAH) hVH,
      subgroupOf_sup c.le_H hAH,Subgroup.map_sup,Subgroup.map_sup]
    exact sup_le (sup_le B.le_normalizer hAN) hUN
  let j : X →* N := (q.comp (inclusion hXH)).codRestrict N
    (fun x => hXN (mem_map_of_mem q x.property))
  let a : X →* MulAut B := B.normalizerMonoidHom.comp j
  have hmap (R : Subgroup G) (hRX : R ≤ X) :
      (R.subgroupOf X).map j = (Nonabelian.Setup.star H R).subgroupOf N := by
    ext n
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact mem_map_of_mem q hx
    · intro hn
      obtain ⟨r,hr,he⟩ := hn
      exact ⟨⟨r.val,hRX hr⟩,hr,Subtype.ext he⟩
  have ha (R : Subgroup G) (hRX : R ≤ X) :
      (R.subgroupOf X).map a = ((Nonabelian.Setup.star H R).subgroupOf N).map B.normalizerMonoidHom := by
    change (R.subgroupOf X).map (B.normalizerMonoidHom.comp j) = _
    rw [←Subgroup.map_map,hmap R hRX]
  have hzero (R : Subgroup G) (hRX : R ≤ X)
      (hRN : Nonabelian.Setup.star H R ≤ N) :
      (R.subgroupOf X).map a = ⊥ ↔
        Nonabelian.Setup.star H R ≤ centralizer (B : Set (H ⧸ pCore 2 H)) := by
    rw [ha R hRX,Subgroup.map_eq_bot_iff,normalizerMonoidHom_ker]
    constructor
    · intro hc r hr
      exact hc (show (⟨r,hRN hr⟩ : N) ∈ (Nonabelian.Setup.star H R).subgroupOf N from hr)
    · intro hc r hr
      exact hc hr
  have hUne : (V.subgroupOf X).map a ≠ ⊥ := by
    intro he
    exact c.moved (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp ((hzero V hVX hUN).mp he)))
  have hAne : (E.L₁.subgroupOf X).map a ≠ ⊥ := by
    intro he
    have hcomm := commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp ((hzero E.L₁ hAX hAN).mp he))
    rw [S.original_selectedComponent_residual_commutator D hZ z hz hTV hTz hbound hns hH hn c] at hcomm
    exact c.moved (by rw [hcomm,commutator_bot_left])
  have hcardU : Nat.card ((V.subgroupOf X).map a) = 2 := by
    have hd := card_map_dvd (U.subgroupOf N) B.normalizerMonoidHom
    rw [Nat.card_congr (subgroupOfEquivOfLe hUN).toEquiv] at hd
    have hc : Nat.card U = 2 :=
      (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.1
    rw [hc,←ha V hVX] at hd
    exact ((Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd).resolve_left
      (fun h => hUne (Subgroup.card_eq_one.mp h))
  let F := (E.L₁.subgroupOf X).map a
  let e := (subgroupOfEquivOfLe hAX).symm
  let f : E.L₁ →* F := (a.subgroupMap (E.L₁.subgroupOf X)).comp e.toMonoidHom
  have hf : Function.Surjective f := (a.subgroupMap_surjective _).comp e.surjective
  have hpF : IsPPerfect 2 F := (isPPerfect_embedded_pResidual 2 (L ⊓ E.Gz)).of_surjective f hf
  have hthree : 3 ∣ Nat.card F := by
    by_contra hnot
    have hd : Nat.card F ∣ Nat.card E.L₁ := Subgroup.card_dvd_of_surjective f hf
    obtain ⟨_,_,_,eqv,_,_⟩ := S.original_point_residual_quotient D hZ z hz hTz
    have hq : Nat.card (E.L₁ ⧸ pCore 2 E.L₁) = 9 :=
      (Nat.card_congr eqv.toEquiv).trans BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9_card
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := E.L₁)).exists_card_eq
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 E.L₁),hq,hn] at hd
    have hcop : Nat.Coprime (Nat.card F) 9 :=
      ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).mpr hnot).symm.pow_right 2
    have htwo : IsPGroup 2 F := isPGroup_iff_card_dvd_pow.mpr
      ⟨n,hcop.dvd_of_dvd_mul_left hd⟩
    have hid := hpF.hom_eq_one_of_isPGroup htwo (MonoidHom.id F)
    apply hAne
    apply bot_unique
    intro x hx
    exact congrArg Subtype.val (DFunLike.congr_fun hid ⟨x,hx⟩)
  have hcentral : F ≤ centralizer ((V.subgroupOf X).map a : Set (MulAut B)) := by
    change (E.L₁.subgroupOf X).map a ≤ _
    rw [ha E.L₁ hAX,ha V hVX]
    apply (map_mono (f := B.normalizerMonoidHom) ?_).trans (map_centralizer_le_centralizer_image _ _)
    rintro r hr u hu
    apply Subtype.ext
    exact S.original_point_residual_star_centralizes D hZ z hz hTV hTz hbound hH hn hr u.val hu
  have hKX : c.K ≤ X := le_sup_left.trans le_sup_left
  have hinner : (c.K.subgroupOf X).map a = MulAut.innerSubgroup B := by
    rw [ha c.K hKX]
    ext b
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,by ext y; rfl⟩
    · rintro ⟨x,rfl⟩
      exact ⟨⟨x.val,B.le_normalizer x.property⟩,x.property,by ext y; rfl⟩
  have hKN : (c.K.subgroupOf X).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le (sup_le c.K.le_normalizer
      (S.original_residual_normalizes_selectedComponent D hZ z hz hH c))
      (S.original_module_normalizes_selectedComponent D hZ z hH c))
  refine ⟨⟨hXH,hKN,a,fun _ _ => rfl,?_,hinner,hcardU,hAne,hpF,hthree,hcentral⟩⟩
  ext x
  change B.normalizerMonoidHom (j x) = 1 ↔ _
  rw [←MonoidHom.mem_ker,normalizerMonoidHom_ker]
  rfl


/-- Original-source application: select the actual moved component and
construct its faithful local action, discharging all action-marking fields. -/
theorem SourceHypothesis.original_selectedComponent_with_action
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H)) :
    ∃ c : (D.fullSetup hZ T z).SelectedComponent H,
      (D.fullSetup hZ T z).L₁ ≤ normalizer (c.K : Set G) ∧
      ⁅Nonabelian.Setup.star H c.K,Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁⁆ =
        Nonabelian.Setup.star H c.K ∧ Nonempty c.ActionMarking := by
  obtain ⟨c⟩ := S.original_selectedComponent D hZ z hz hTV hTz hbound hns hH hn
  exact ⟨c,S.original_residual_normalizes_selectedComponent D hZ z hz hH c,
    S.original_selectedComponent_residual_commutator D hZ z hz hTV hTz hbound hns hH hn c,
    S.original_selectedComponent_action D hZ z hz hTV hTz hbound hns hH hn c⟩
end CFSG.Quasithin.Chapter12.Section06
