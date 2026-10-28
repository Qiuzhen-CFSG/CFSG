module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentPointAction
public import Theory.SpecificGroups.AlternatingSeven.InvolutionResidual

/-!
# The original cubic image and point-core centralizer in the A₇ cover

The actual L₁ image is two-perfect and centralizes the marked V involution.
The seven-point centralizer calculation therefore identifies it with the
three-cycle on that involution’s fixed letters, using a simultaneous
relabelling of both images. The full H action retains its literal kernel,
component image, even R₁ image and original Sylow image.

Before the action quotient, L₁-star lies in K-star and its action kernel
embeds in the cubic component center. Its order is consequently at most
nine. The original Sylow E₉ gives equality and identifies all of L₁-star.
Coprime normal subgroups in the point join then commute, and normality of
the Sylow centralizer proves R₁-star = C_{T-star}(L₁-star).

These results provide the original subgroup and kernel for the remaining
four-group identification and component-normalizer lower bound. They do
not yet exclude the cubic A₇ cover or supply the abelian point span.
Source: Aschbacher–Smith, proof of 12.6.26, printed p.832.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)

/-- The full original seven-letter action can be simultaneously marked so that
L₁ has image the tail cubic and V has image the double transposition. -/
theorem SourceHypothesis.original_alternatingSevenCover_marked_cubic
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7)
    (e : (Nonabelian.Setup.star H c.K ⧸ center (Nonabelian.Setup.star H c.K)) ≃*
      alternatingGroup (Fin 7)) :
    ∃ f : H →* Equiv.Perm (Fin 7),
      f.ker = (centralizer (Nonabelian.Setup.star H c.K : Set (Nonabelian.Setup.Hstar H))).comap
        (QuotientGroup.mk' (pCore 2 H)) ∧
      (c.K.subgroupOf H).map f = alternatingGroup (Fin 7) ∧
      ((D.fullSetup hZ T z).R₁.subgroupOf H).map f ≤ alternatingGroup (Fin 7) ∧
      (∀ x : c.localActor, MulAut.centralQuotientAction e (a.action x) =
        MulAut.conjNormal (f (inclusion a.local_le x))) ∧
      (∃ P : Sylow 2 f.range,
        (P : Subgroup f.range).map f.range.subtype = ((T : Subgroup G).subgroupOf H).map f) ∧
      ∃ g : Equiv.Perm (Fin 7),
        (((D.fullSetup hZ T z).L₁.subgroupOf H).map f).map (MulAut.conj g).toMonoidHom =
          zpowers (Equiv.swap 4 5 * Equiv.swap 5 6) ∧
        ((V.subgroupOf H).map f).map (MulAut.conj g).toMonoidHom =
          zpowers (Equiv.swap 0 1 * Equiv.swap 2 3) := by
  classical
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let := c.component.2
  obtain ⟨f,hker,hK,hR,hmark,hP⟩ :=
    S.original_alternatingSevenCover_full_permutation_action D hZ z hz hTz hH c a hm e
  let permAut : Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
    MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
      (by decide) (by decide))
  let d : MulAut B →* Equiv.Perm (Fin 7) :=
    permAut.symm.toMonoidHom.comp (MulAut.centralQuotientAction e)
  have hd : Function.Injective d := permAut.symm.injective.comp
    (MulAut.centralQuotientAction_injective e)
  have hext (x : c.localActor) : d (a.action x) = f (inclusion a.local_le x) := by
    apply permAut.injective
    change permAut (permAut.symm (MulAut.centralQuotientAction e (a.action x))) = _
    rw [permAut.apply_symm_apply]
    exact hmark x
  have hmap (R : Subgroup G) (hRX : R ≤ c.localActor) :
      (R.subgroupOf H).map f = ((R.subgroupOf c.localActor).map a.action).map d := by
    rw [map_map]
    ext t
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hRX hx⟩,hx,hext _⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨inclusion a.local_le x,hx,(hext x).symm⟩
  let A := (E.L₁.subgroupOf H).map f
  let U := (V.subgroupOf H).map f
  have hAm := hmap E.L₁ (le_sup_right.trans le_sup_left)
  have hUm := hmap V le_sup_right
  have hAc : IsPPerfect 2 A := by
    rw [show A = _ from hAm]
    exact a.residual_twoPerfect.of_surjective (d.subgroupMap _)
      (MonoidHom.subgroupMap_surjective _ _)
  have hAn : A ≠ ⊥ := by
    rw [show A = _ from hAm]
    exact fun hh => a.residual_ne_bot ((Subgroup.map_eq_bot_iff_of_injective _ hd).mp hh)
  have hUc : Nat.card U = 2 := by
    rw [show U = _ from hUm,card_map_of_injective hd]
    exact a.module_card
  have hUA : U ≤ alternatingGroup (Fin 7) := by
    rw [show U = _ from hUm]
    rintro _ ⟨v,hv,rfl⟩
    obtain ⟨b,hb⟩ := S.original_cubicCover_module_inner D hZ z hz hTV hTz hbound hH hn c a
      (Or.inl hm) hv
    rw [←hb]
    have he : d (MulAut.conj b) = (e (QuotientGroup.mk' (center B) b) : Equiv.Perm (Fin 7)) := by
      apply permAut.injective
      change permAut (permAut.symm (MulAut.centralQuotientAction e (MulAut.conj b))) = _
      rw [permAut.apply_symm_apply,MulAut.centralQuotientAction_conj]
      rfl
    rw [he]
    exact (e (QuotientGroup.mk' (center B) b)).property
  have hAU : A ≤ centralizer (U : Set (Equiv.Perm (Fin 7))) := by
    rw [show A = _ from hAm,show U = _ from hUm]
    exact (map_mono a.residual_centralizes).trans (map_centralizer_le_centralizer_image _ d)
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card (G := U) 2 (by rw [←Nat.card_eq_fintype_card,hUc])
  have hou : orderOf (u : Equiv.Perm (Fin 7)) = 2 := (Subgroup.orderOf_coe u).trans hu
  have hgen : U = zpowers (u : Equiv.Perm (Fin 7)) := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr u.property) ?_).symm
    rw [Nat.card_zpowers,hou,hUc]
  obtain ⟨g,hgu,hgA⟩ := AlternatingSeven.InvolutionResidual.marked_cubic A hAc hAn u
    (hUA u.property) hou (hAU.trans (centralizer_le (Set.singleton_subset_iff.mpr u.property)))
  refine ⟨f,hker,hK,hR,hmark,hP,g,hgA,?_⟩
  change U.map (MulAut.conj g).toMonoidHom = _
  rw [hgen,MonoidHom.map_zpowers]
  exact congrArg zpowers hgu

/-- The original L₁-star is exactly each original Sylow E₉ image. Its binary
core has disappeared in H/O₂(H), before the subsequent central quotient. -/
theorem SourceHypothesis.original_alternatingSevenCover_residual_star_eq_sylow
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ =
      Nonabelian.Setup.star H ((P : Subgroup (D.fullSetup hZ T z).L₁).map
        (D.fullSetup hZ T z).L₁.subtype) := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let A := Nonabelian.Setup.star H E.L₁
  let q := QuotientGroup.mk' (pCore 2 H)
  have hmcopy := hm
  obtain ⟨_,⟨ec⟩,⟨e⟩⟩ := hmcopy
  have hc : Nat.card (center B) = 3 := by rw [Nat.card_congr ec.toEquiv]; simp
  obtain ⟨f,hker,_,_,_,_,s,hs,_⟩ :=
    S.original_alternatingSevenCover_marked_cubic D hZ z hz hTV hTz hbound hH hn c a hm e
  have hfcard : Nat.card ((E.L₁.subgroupOf H).map f) = 3 := by
    rw [←card_map_of_injective (f := (MulAut.conj s).toMonoidHom) (MulAut.conj s).injective,
      hs,Nat.card_zpowers]
    exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hcore : pCore 2 H ≤ f.ker := by
    rw [hker]
    intro x hx
    change q x ∈ centralizer (B : Set (Nonabelian.Setup.Hstar H))
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  let f' : Nonabelian.Setup.Hstar H →* Equiv.Perm (Fin 7) :=
    QuotientGroup.lift (pCore 2 H) f hcore
  have hk' : f'.ker = centralizer (B : Set (Nonabelian.Setup.Hstar H)) := by
    ext x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) x
    change f y = 1 ↔ _
    change y ∈ f.ker ↔ _
    rw [hker]
    rfl
  have hAf : A.map f' = (E.L₁.subgroupOf H).map f := by
    change ((E.L₁.subgroupOf H).map q).map f' = _
    rw [map_map]
    rfl
  have hAB : A ≤ B := S.original_alternatingSevenCover_residual_star_le D hZ z hz hTz hH c a hm
  let g := f'.comp A.subtype
  have hg : g.range = A.map f' := by rw [MonoidHom.range_comp,range_subtype]
  have hmem (x : g.ker) : (inclusion hAB x.val : B) ∈ center B := by
    apply mem_center_iff.mpr
    intro b
    apply Subtype.ext
    have hx : (x.val : Nonabelian.Setup.Hstar H) ∈ f'.ker := x.property
    rw [hk'] at hx
    exact hx b.val b.property
  let k : g.ker →* center B := ((inclusion hAB).comp g.ker.subtype).codRestrict _ hmem
  have hkinj : Function.Injective k := by
    intro x y hh
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : center B => t.val.val) hh
  have hkc : Nat.card g.ker ≤ 3 := by
    simpa only [hc] using Nat.card_le_card_of_injective k hkinj
  have hAc : Nat.card A ≤ 9 := by
    have hh := g.ker.card_eq_card_quotient_mul_card_subgroup
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv,hg,hAf,hfcard] at hh
    omega
  have hPA : Nonabelian.Setup.star H ((P : Subgroup E.L₁).map E.L₁.subtype) ≤ A :=
    map_mono (comap_mono (map_subtype_le _))
  exact (eq_of_le_of_card_ge hPA (by
    rw [(S.original_point_sylow_star D hZ z hz hTz hH P).2.1]
    exact hAc)).symm

/-- In the cubic A₇ row the whole original point residual, before passage to
its component action, is elementary abelian of order nine. -/
theorem SourceHypothesis.original_alternatingSevenCover_residual_star_elementary
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7)
    : IsElementaryAbelian 3 (Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁) ∧
      Nat.card (Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁) = 9 := by
  let P : Sylow 3 (D.fullSetup hZ T z).L₁ := default
  rw [S.original_alternatingSevenCover_residual_star_eq_sylow D hZ z hz hTV hTz hbound hH hn c a hm P]
  exact ⟨(S.original_point_sylow_star D hZ z hz hTz hH P).1,
    (S.original_point_sylow_star D hZ z hz hTz hH P).2.1⟩

/-- The original point two-core centralizes this E₉ in the literal star group.
Both groups are normal in the same original point join, and their orders are coprime. -/
theorem SourceHypothesis.original_alternatingSevenCover_point_core_centralizes
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7)
    : Nonabelian.Setup.star H (D.fullSetup hZ T z).R₁ ≤
      centralizer (Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ : Set (Nonabelian.Setup.Hstar H)) := by
  let E := D.fullSetup hZ T z
  let A := Nonabelian.Setup.star H E.L₁
  let R := Nonabelian.Setup.star H E.R₁
  let J := A ⊔ Nonabelian.Setup.star H (T : Subgroup G)
  have hA := (S.original_alternatingSevenCover_residual_star_elementary D hZ z hz hTV hTz hbound hH hn c a hm).1
  let := hA
  have hR : R = J.pCoreIn 2 := S.original_point_core_star D hZ z hH
  have hAR : A ≤ normalizer (R : Set (Nonabelian.Setup.Hstar H)) := by
    rw [hR]
    exact le_sup_left.trans (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))
  have hTn : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) := by
    intro x hx
    exact S.original_module_normalizer_normalizes_residual D hZ z hTV hH
      ⟨hH.1.2 (Or.inr hx),hTV hx⟩
  have hRn : E.R₁ ≤ normalizer (E.L₁ : Set G) :=
    (pCoreIn_le 2 (E.L₁ ⊔ (T : Subgroup G))).trans (sup_le E.L₁.le_normalizer hTn)
  have hRA : R ≤ normalizer (A : Set (Nonabelian.Setup.Hstar H)) :=
    (map_mono ((comap_mono hRn).trans (E.L₁.le_normalizer_comap H.subtype))).trans
      ((E.L₁.subgroupOf H).le_normalizer_map (QuotientGroup.mk' (pCore 2 H)))
  have hd : Disjoint R A := (hR.symm ▸ isPGroup_pCoreIn 2 J).disjoint_of_coprime
    (IsElementaryAbelian.isPGroup 3 A) (by decide)
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply bot_unique
  exact (le_inf (le_normalizer_iff_commutator_le_left.mp hAR)
    (le_normalizer_iff_commutator_le_right.mp hRA)).trans hd.eq_bot.le

/-- The original R₁-star is exactly the centralizer of L₁-star in the
unchanged T-star. This retains the full kernel needed for its later normalizer lift. -/
theorem SourceHypothesis.original_alternatingSevenCover_point_core_eq_sylow_centralizer
    (hz : z ≠ 1)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
    (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
      Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hn : ¬ IsMulCommutative ((D.fullSetup hZ T z).VH H))
    (c : (D.fullSetup hZ T z).SelectedComponent H) (a : c.ActionMarking)
    (hm : Chapter1.Section02.LocalModels.IsAlternatingCover (Nonabelian.Setup.star H c.K) 7)
    : Nonabelian.Setup.star H (D.fullSetup hZ T z).R₁ =
      Nonabelian.Setup.star H (T : Subgroup G) ⊓
        centralizer (Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ : Set (Nonabelian.Setup.Hstar H)) := by
  let E := D.fullSetup hZ T z
  let A := Nonabelian.Setup.star H E.L₁
  let U := Nonabelian.Setup.star H (T : Subgroup G)
  let C := U ⊓ centralizer (A : Set (Nonabelian.Setup.Hstar H))
  let J := A ⊔ U
  have hRT : E.R₁ ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow (E.L₁ ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right])
  apply le_antisymm
  · exact le_inf (map_mono (comap_mono hRT))
      (S.original_alternatingSevenCover_point_core_centralizes D hZ z hz hTV hTz hbound hH hn c a hm)
  rw [S.original_point_core_star D hZ z hH]
  have hTn : (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) := by
    intro x hx
    exact S.original_module_normalizer_normalizes_residual D hZ z hTV hH
      ⟨hH.1.2 (Or.inr hx),hTV hx⟩
  have hUA : U ≤ normalizer (A : Set (Nonabelian.Setup.Hstar H)) :=
    (map_mono ((comap_mono hTn).trans (E.L₁.le_normalizer_comap H.subtype))).trans
      ((E.L₁.subgroupOf H).le_normalizer_map (QuotientGroup.mk' (pCore 2 H)))
  have hUC : U ≤ normalizer (C : Set (Nonabelian.Setup.Hstar H)) :=
    (le_inf U.le_normalizer (hUA.trans (normalizer_le_normalizer_centralizer A))).trans
      inf_normalizer_le_normalizer_inf
  have hAC : A ≤ normalizer (C : Set (Nonabelian.Setup.Hstar H)) :=
    (le_centralizer_iff.mp (show C ≤ centralizer (A : Set (Nonabelian.Setup.Hstar H)) from inf_le_right)).trans
      (Subgroup.centralizer_le_normalizer _)
  apply le_pCoreIn_of_normalizes ?_ (inf_le_left.trans le_sup_right) (sup_le hAC hUC)
  exact ((T.isPGroup'.comap_subtype (K := H)).map (QuotientGroup.mk' (pCore 2 H))).to_le inf_le_left

end CFSG.Quasithin.Chapter12.Section06
