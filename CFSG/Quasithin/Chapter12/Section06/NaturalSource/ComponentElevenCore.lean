module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentElevenMoved
public import Theory.SpecificGroups.PSL2.TwoPerfectInvolutionCentralizer

/-!
# The original residual two-core in the PSL₂(11) branch

The actual L₁ action centralizes the marked inner module involution.
Two-perfection and the reflected-torus centralizer make its image odd,
so the intrinsic O₂(L₁) centralizes K-star. The faithful whole Irr⁺
section U_H/V₁ kills this two-subgroup. Thus O₂(L₁) lies in O₂(H).

The literal H to H/O₂(H) map consequently induces an isomorphism
L₁/O₂(L₁) to L₁-star. It retains the original quotient coordinates and
identifies the whole residual image with E₉, including every original
Sylow image. The intrinsic core remains distinct from L₁ intersect O₂(L).

The containment of U_H in this core and the numerical bound of order 2⁹
are the next source steps; the abelian point span and the universal natural
reduction remain subsequent obligations. All original geometric assumptions and markings are retained.
Source: Aschbacher--Smith, proof of 12.6.26, printed p.833.
-/

public section
open Subgroup

set_option backward.isDefEq.respectTransparency false

private theorem two_group_eq_bot_of_faithful_irrPlus
    {J W : Type*} [Group J] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) J W)
    (hf : Function.Injective σ) {B P : Subgroup J}
    (hi : Representation.BinaryOffender.IsIrrPlus σ B ⊤)
    (hp : IsPGroup 2 P) (hc : P ≤ centralizer (B : Set J)) : P = ⊥ := by
  have hh := Representation.BinaryOffender.Homogeneous.IsIrrPlus.le_fixedSpace_of_twoGroup_centralizes
    σ hi hp hc (Representation.BinaryOffender.le_subspaceStabilizer σ ⊤ (by intros; trivial))
  apply bot_unique
  intro p hp
  apply mem_bot.mpr
  apply hf
  ext w
  simpa only [map_one,Module.End.one_apply,MonoidHom.comp_apply,Subgroup.subtype_apply] using hh Submodule.mem_top ⟨p,hp⟩

namespace CFSG.Quasithin.Chapter12.Section06
open Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
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
/-- The actual L₁ action on the selected component has odd order. -/
theorem SourceHypothesis.original_selectedComponent_residual_action_odd
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    Odd (Nat.card (((D.fullSetup hZ T z).L₁.subgroupOf c.localActor).map a.action)) := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let A := (E.L₁.subgroupOf c.localActor).map a.action
  obtain ⟨F,hfield,hfinite,hF,⟨e⟩⟩ :=
    S.original_selectedComponent_linearTwoEleven D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let := hfield
  let := hfinite
  obtain ⟨b,hb,hb2,_,_⟩ := S.original_selectedComponent_model_fixed_cubic
    D hZ z hz hTV hTz hbound hH hn c a hTI hns e
  have hb2' : orderOf b = 2 := ((MulAut.congr e).orderOf_eq b).symm.trans hb2
  obtain ⟨t,ht⟩ := S.original_linearTwo_module_inner D hZ z hz hTV hTz hbound hH hn c a
    hTI hns (p := 11) (n := 1) (by decide) (by decide) (by decide) (by simpa using hF) e b hb hb2'
  have ht2 : orderOf t = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot (GorensteinWalter.psl2_center_eq_bot F) t).symm.trans
      (ht ▸ hb2)
  let f := (MulAut.congr e).toMonoidHom.comp A.subtype
  have hf : Function.Injective f := (MulAut.congr e).injective.comp A.subtype_injective
  have ho := Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
    (p := 11) (n := 1) (by decide) (by decide) (by decide) (by simpa using hF)
  have hh := Theory.PSL2.odd_automorphism_image_of_twoPerfect_centralizing_inner_involution
    (show GorensteinWalter.IsOddPrimePower (Nat.card F) from
      ⟨11,1,by decide,by decide,by decide,by simpa using hF⟩)
    ho t ht2 a.residual_twoPerfect f (fun x => by
      rw [←ht]
      change (MulAut.congr e) x.val * (MulAut.congr e) b =
        (MulAut.congr e) b * (MulAut.congr e) x.val
      rw [←map_mul,←map_mul]
      exact congrArg (MulAut.congr e) ((a.residual_centralizes x.property) b hb).symm)
  rwa [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv] at hh

include hz hTV hTz hbound hH hn a in
/-- The intrinsic O₂(L₁) is killed by the original component action. -/
theorem SourceHypothesis.original_selectedComponent_residual_core_action
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    let E := D.fullSetup hZ T z
    let j : E.L₁ →* c.localActor := inclusion (le_sup_right.trans le_sup_left)
    pCore 2 E.L₁ ≤ (a.action.comp j).ker := by
  dsimp only
  let E := D.fullSetup hZ T z
  let A := (E.L₁.subgroupOf c.localActor).map a.action
  let j : E.L₁ →* c.localActor := inclusion (le_sup_right.trans le_sup_left)
  let f : E.L₁ →* A := (a.action.comp j).codRestrict A
    (fun x => mem_map_of_mem a.action x.property)
  have ho := S.original_selectedComponent_residual_action_odd
    D hZ z hz hTV hTz hbound hH hn c a hTI hns
  intro x hx
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := E.L₁)) ⟨x,hx⟩
  have hp : f x ^ 2^n = 1 := by
    rw [←map_pow,show x ^ 2^n = 1 from congrArg Subtype.val hn,map_one]
  have he : f x = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (ho.coprime_two_right.pow_right n)
      (orderOf_dvd_natCard (f x)) (orderOf_dvd_of_pow_eq_one hp))
  exact congrArg Subtype.val he

include hz hTV hTz hbound hH hn a in
/-- The image of the intrinsic O₂(L₁) centralizes the same selected component
in the literal H/O₂(H) quotient. -/
theorem SourceHypothesis.original_selectedComponent_residual_core_star_centralizes
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    Nonabelian.Setup.star H ((D.fullSetup hZ T z).L₁.pCoreIn 2) ≤
      centralizer (Nonabelian.Setup.star H c.K : Set (Nonabelian.Setup.Hstar H)) := by
  let E := D.fullSetup hZ T z
  let q := QuotientGroup.mk' (pCore 2 H)
  let j : E.L₁ →* c.localActor := inclusion (le_sup_right.trans le_sup_left)
  have hk := S.original_selectedComponent_residual_core_action
    D hZ z hz hTV hTz hbound hH hn c a hTI hns
  rintro _ ⟨y,hy,rfl⟩
  obtain ⟨x,hx,he⟩ := hy
  have heH : inclusion a.local_le (j x) = y := Subtype.ext he
  have ha : j x ∈ a.action.ker := hk hx
  rw [a.kernel] at ha
  change q (inclusion a.local_le (j x)) ∈
    centralizer (Nonabelian.Setup.star H c.K : Set (Nonabelian.Setup.Hstar H)) at ha
  rwa [heH] at ha

include hz hTV hTz hbound hH hn a in
/-- The faithful whole Irr⁺ section kills the intrinsic residual two-core.
This is O₂(L₁) ≤ O₂(H), in the original ambient group. -/
theorem SourceHypothesis.original_selectedComponent_residual_core_le
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    (D.fullSetup hZ T z).L₁.pCoreIn 2 ≤ H.pCoreIn 2 := by
  let E := D.fullSetup hZ T z
  let R := E.L₁.pCoreIn 2
  let P := Nonabelian.Setup.star H R
  have hP : IsPGroup 2 P := ((isPGroup_pCoreIn 2 E.L₁).comap_subtype).map _
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let _ : (E.V₁.subgroupOf (E.UH H)).Normal := h.point_normal_in_UH
  let _ : IsElementaryAbelian 2 (E.UH H ⧸ E.V₁.subgroupOf (E.UH H)) := h.point_quotient_elementary
  obtain ⟨σ,κ,hσ,_⟩ := h.faithful_point_quotient
  have hI := (S.original_selectedComponent_whole_module D hZ z hz hTV hTz hbound
    hH hn c a hTI hns (W := Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))) σ hσ κ).2.2.1
  have hzero : P = ⊥ := two_group_eq_bot_of_faithful_irrPlus
    (W := Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))) σ hσ hI hP
    (S.original_selectedComponent_residual_core_star_centralizes
      D hZ z hz hTV hTz hbound hH hn c a hTI hns)
  have hRH : R ≤ H := (pCoreIn_le 2 E.L₁).trans (fun x hx => hH.1.2 (Or.inl hx))
  intro x hx
  have hq : QuotientGroup.mk' (pCore 2 H) ⟨x,hRH hx⟩ = 1 :=
    mem_bot.mp (hzero ▸ (mem_map_of_mem (QuotientGroup.mk' (pCore 2 H)) hx :
      QuotientGroup.mk' (pCore 2 H) ⟨x,hRH hx⟩ ∈ P))
  exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp hq)


include hz hTV hTz hbound hH hn a in
/-- The actual residual projection has exactly its intrinsic two-core as
kernel, so the full L₁-star is the original E₉ quotient. -/
theorem SourceHypothesis.original_selectedComponent_residual_star_quotient
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    let E := D.fullSetup hZ T z
    ∃ e : (E.L₁ ⧸ pCore 2 E.L₁) ≃* Nonabelian.Setup.star H E.L₁,
      ∀ x : E.L₁, (e (QuotientGroup.mk' (pCore 2 E.L₁) x)).val =
        QuotientGroup.mk' (pCore 2 H) ⟨x.val,hH.1.2 (Or.inl x.property)⟩ := by
  let E := D.fullSetup hZ T z
  let A := Nonabelian.Setup.star H E.L₁
  have hAH : E.L₁ ≤ H := fun x hx => hH.1.2 (Or.inl hx)
  let q := QuotientGroup.mk' (pCore 2 H)
  let f : E.L₁ →* A := (q.comp (inclusion hAH)).codRestrict A
    (fun x => mem_map_of_mem q x.property)
  have hf : Function.Surjective f := by
    rintro ⟨y,x,hx,rfl⟩
    exact ⟨⟨x.val,hx⟩,rfl⟩
  have hker : f.ker = pCore 2 E.L₁ := by
    apply le_antisymm
    · have he : f.ker = (H.pCoreIn 2).subgroupOf E.L₁ := by
        ext x
        change f x = 1 ↔ x.val ∈ H.pCoreIn 2
        rw [←Subtype.val_inj]
        change q (inclusion hAH x) = 1 ↔ _
        change QuotientGroup.mk (inclusion hAH x) = 1 ↔ _
        rw [QuotientGroup.eq_one_iff]
        constructor
        · exact fun hx => mem_map_of_mem H.subtype hx
        · rintro ⟨y,hy,he⟩
          have hh : y = inclusion hAH x := Subtype.ext he
          rwa [hh] at hy
      exact le_sSup ⟨inferInstance,he.symm ▸ (isPGroup_pCoreIn 2 H).comap_subtype⟩
    · intro x hx
      apply Subtype.ext
      change q (inclusion hAH x) = 1
      apply (QuotientGroup.eq_one_iff _).mpr
      have hxH := S.original_selectedComponent_residual_core_le
        D hZ z hz hTV hTz hbound hH hn c a hTI hns (mem_map_of_mem E.L₁.subtype hx)
      obtain ⟨y,hy,he⟩ := hxH
      have hh : y = inclusion hAH x := Subtype.ext he
      rwa [hh] at hy
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf),fun _ => rfl⟩

include hz hTV hTz hbound hH hn a in
/-- The original L₁-star is elementary of order nine; its two-core vanishes.
This concerns the whole residual image, not just its Sylow subgroup. -/
theorem SourceHypothesis.original_selectedComponent_residual_star_elementary
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    let A := Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁
    IsElementaryAbelian 3 A ∧ Nat.card A = 9 ∧ pCore 2 A = ⊥ := by
  dsimp only
  let A := Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁
  obtain ⟨e,_⟩ := S.original_selectedComponent_residual_star_quotient
    D hZ z hz hTV hTz hbound hH hn c a hTI hns
  obtain ⟨_,_,_,d,_,_⟩ := S.original_point_residual_quotient D hZ z hz hTz
  let j := e.symm.trans d
  let : IsElementaryAbelian 3 A := IsElementaryAbelian.of_injective j.toMonoidHom j.injective
  refine ⟨inferInstance,(Nat.card_congr j.toEquiv).trans
    BinaryPermutation.TerminalOrthogonal.FourBlockResidual.E9_card,?_⟩
  have h3 := (IsElementaryAbelian.isPGroup 3 A).to_subgroup (pCore 2 A)
  have h2 : IsPGroup 2 (pCore 2 A) := pCore_isPGroup
  simpa only [inf_idem] using (h2.disjoint_of_coprime h3 (by decide)).eq_bot

include hz hTV hTz hbound hH hn a in
/-- Every original Sylow E₉ now maps onto the whole L₁-star through the
same H to H/O₂(H) projection. -/
theorem SourceHypothesis.original_selectedComponent_residual_sylow_star_eq
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    (P : Sylow 3 (D.fullSetup hZ T z).L₁) :
    Nonabelian.Setup.star H ((P : Subgroup (D.fullSetup hZ T z).L₁).map
      (D.fullSetup hZ T z).L₁.subtype) =
      Nonabelian.Setup.star H (D.fullSetup hZ T z).L₁ := by
  apply eq_of_le_of_card_ge
  · exact map_mono (comap_mono (map_subtype_le _))
  · rw [(S.original_selectedComponent_residual_star_elementary
      D hZ z hz hTV hTz hbound hH hn c a hTI hns).2.1,
      (S.original_point_sylow_star D hZ z hz hTz hH P).2.1]

end CFSG.Quasithin.Chapter12.Section06
