module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticExtensionOrder.OuterConjugacy
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.FixedEndpoint
public import Theory.SpecificGroups.Alternating.FourPairCore

/-!
# Original fixed binary symplectic amalgams and endpoint cores

The same faithful middle lift intertwines original conjugation by an outer
involution with a native flag automorphism. Restrict the given pure comparison
to centralizers on both endpoints and their whole intersection. The native
binary descent then gives a compatible Sp4(2) parabolic amalgam, in either
orientation. Its endpoint two-residuals are A4; each actual two-core is a
Klein four with no proper nontrivial normal subgroup in that residual.

These are the compatible fixed-endpoint and irreducibility steps of
Aschbacher--Smith F.4.37, printed p.293 of refs/quasithin.pdf, in the prepared
source pair of 5.3.1--3, pp.658--659. The remaining quotient obstruction must
place these residuals in the conjugate root local, prove that their cores
avoid its two-core, and inject their D8 join into PSL2(4). Neither S=T at q=4
nor the full-extension ambient order bound is asserted here.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G]

/-- Centralizers in the two pure parabolics, with their entire common centralizer. -/
def sourceFixedParabolicAmalgam (L K S : Subgroup G) (f : G) :=
  let P := ChapterF.Source.parabolic ![L,K] S
  let C := centralizer ({f} : Set G)
  RankTwoAmalgam.ofSubgroups (P 0 ⊓ C) ((P 0 ⊓ P 1) ⊓ C) (P 1 ⊓ C)
    (inf_le_inf inf_le_left le_rfl) (inf_le_inf inf_le_right le_rfl)

omit [Finite G] in
private def restrictIntersection {J : Type*} [Group J]
    {P C : Subgroup G} {Q D : Subgroup J} (e : P ≃* Q)
    (he : ∀ x, (e x).val ∈ D ↔ x.val ∈ C) : (P ⊓ C : Subgroup G) ≃* (Q ⊓ D : Subgroup J) where
  toFun x := ⟨(e ⟨x.val,x.property.1⟩).val,
    ⟨(e ⟨x.val,x.property.1⟩).property,(he _).mpr x.property.2⟩⟩
  invFun y := ⟨(e.symm ⟨y.val,y.property.1⟩).val,
    ⟨(e.symm ⟨y.val,y.property.1⟩).property,(he _).mp (by
      rw [e.apply_symm_apply]; exact y.property.2)⟩⟩
  left_inv x := Subtype.ext (congrArg (fun z : P => z.val) (e.symm_apply_apply ⟨x.val,x.property.1⟩))
  right_inv y := Subtype.ext (congrArg (fun z : Q => z.val) (e.apply_symm_apply ⟨y.val,y.property.1⟩))
  map_mul' x y := Subtype.ext (congrArg (fun z : Q => z.val)
    (e.map_mul ⟨x.val,x.property.1⟩ ⟨y.val,y.property.1⟩))

omit [Finite G] in
private def fixedPairIso {J : Type*} [Group J]
    {P B Q C : Subgroup G} {R U V D : Subgroup J}
    {hBP : B≤P} {hBQ : B≤Q} {hUR : U≤R} {hUV : U≤V}
    (e : RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P B Q hBP hBQ)
      (RankTwoAmalgam.ofSubgroups R U V hUR hUV))
    (hl : ∀ x, (e.left x).val ∈ D ↔ x.val ∈ C)
    (hr : ∀ x, (e.right x).val ∈ D ↔ x.val ∈ C) :
    RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (P⊓C) (B⊓C) (Q⊓C)
        (inf_le_inf hBP le_rfl) (inf_le_inf hBQ le_rfl))
      (RankTwoAmalgam.ofSubgroups (R⊓D) (U⊓D) (V⊓D)
        (inf_le_inf hUR le_rfl) (inf_le_inf hUV le_rfl)) where
  left := restrictIntersection e.left hl
  right := restrictIntersection e.right hr
  middle := restrictIntersection e.middle (fun x => by
    have hh := hl (inclusion hBP x)
    have he := congrArg Subtype.val (e.left_commutes x)
    change (e.left (inclusion hBP x)).val=(e.middle x).val at he
    rwa [he] at hh)
  left_commutes x := Subtype.ext (congrArg (fun z : R => z.val) (e.left_commutes ⟨x.val,x.property.1⟩))
  right_commutes x := Subtype.ext (congrArg (fun z : V => z.val) (e.right_commutes ⟨x.val,x.property.1⟩))

omit [Finite G] in
private theorem endpoint_fixed
    {F : Type*} [Field F] {Q : Subgroup G} {R : Subgroup (Sp F)}
    (e : Q ≃* R) (b : MulAut R) (a : MulAut (Sp F)) (f : G)
    (hb : ∀ y, (b y).val=a y.val)
    (hc : ∀ y, (e.symm (b y)).val=f*(e.symm y).val*f⁻¹) (x : Q) :
    a (e x).val=(e x).val ↔ x.val ∈ centralizer ({f} : Set G) := by
  have hh := hc (e x)
  rw [e.symm_apply_apply] at hh
  constructor
  · intro hx
    have he : b (e x)=e x := Subtype.ext ((hb _).trans hx)
    rw [he,e.symm_apply_apply] at hh
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hh.symm).symm
  · intro hx
    have hfx : f*x.val*f⁻¹=x.val :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hx).symm
    have he : b (e x)=e x := by
      apply e.symm.injective
      apply Subtype.ext
      rw [e.symm_apply_apply]
      exact hh.trans hfx
    exact (hb _).symm.trans (congrArg Subtype.val he)
private theorem alternatingFour_involution_conjugacy :
    ∀ x y : alternatingGroup (Fin 4), x≠1 → x*x=1 → y≠1 → y*y=1 →
      ∃ g : alternatingGroup (Fin 4), g*x*g⁻¹=y := by decide +kernel

private theorem core_structure_of_alternatingFour {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 4)) :
    IsKleinFour (pCore 2 X) ∧
      ∀ U : Subgroup X, U.Normal → U≤pCore 2 X → U=⊥ ∨ U=pCore 2 X := by
  let c : pCore 2 X ≃* alternatingGroup.kleinFour (Fin 4) :=
    (e.subgroupMap _).trans (MulEquiv.subgroupCongr
      ((pCore_map_iso 2 e).trans AlternatingFourPair.twoCore_eq_kleinFour))
  have hk := alternatingGroup.kleinFour_isKleinFour (by norm_num : Nat.card (Fin 4)=4)
  let hC : IsKleinFour (pCore 2 X) := {
    card_four := (Nat.card_congr c.toEquiv).trans hk.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv c).trans hk.exponent_two }
  refine ⟨hC,?_⟩
  intro U hU hle
  let _ := hU
  by_cases hbot : U=⊥
  · exact Or.inl hbot
  right
  obtain ⟨x,hx,hx1⟩ := (Subgroup.bot_or_exists_ne_one U).resolve_left hbot
  apply le_antisymm hle
  intro y hy
  by_cases hy1 : y=1
  · exact hy1 ▸ U.one_mem
  have hs (z : X) (hz : z ∈ pCore 2 X) : e z*e z=1 := by
    have hh := congrArg (fun a : pCore 2 X => a.val)
      (IsKleinFour.mul_self (⟨z,hz⟩ : pCore 2 X))
    change z*z=1 at hh
    simpa only [map_mul,map_one] using congrArg e hh
  obtain ⟨g,hg⟩ := alternatingFour_involution_conjugacy (e x) (e y)
    (fun hh => hx1 (e.map_eq_one_iff.mp hh)) (hs x (hle hx))
    (fun hh => hy1 (e.map_eq_one_iff.mp hh)) (hs y hy)
  have he : e.symm g*x*(e.symm g)⁻¹=y := by
    apply e.injective
    simpa only [map_mul,map_inv,e.apply_symm_apply] using hg
  rw [←he]
  exact Subgroup.Normal.conj_mem hU x hx (e.symm g)

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
include d h hH hp hm hF he


/-- An outer involution has the actual binary symplectic fixed amalgam,
with both original endpoint inclusions and the whole middle retained. -/
theorem Preparation.symplectic_outer_fixed_binary_amalgam
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ sourceS L H) :
    Nonempty (RankTwoAmalgam.Iso
      (sourceFixedParabolicAmalgam L (residual H) (sourceS L H) f.val)
      (SourceNormalizerExtension.diagram (ZMod 2))) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceFixedParabolicAmalgam L (residual H) (sourceS L H) f.val)
      (SourceNormalizerExtension.diagram (ZMod 2)).reverse) := by
  have hst : sourceS L H≠(T : Subgroup G) := fun hh => ho (hh.symm ▸ f.property)
  have hq := (d.symplectic_proper_inner_sylow_field_four h hH hp F hm hF he hst).2.2.1
  let N := normalizer (L : Set G) ⊓ normalizer (residual H : Set G)
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H)
  let C := P 0 ⊓ P 1
  have hST := sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have hTN : (T : Subgroup G)≤N :=
    le_inf h.sylow_normalizes (hH.1.1.2.trans (le_normalizer_residual H))
  let fN : N := inclusion hTN f
  have hFC := d.hypothesisF11 h hH.1.1.2
  have hs : Chapter1.IsSylowIn 2 (sourceS L H) C := by
    change Chapter1.IsSylowIn 2 (sourceS L H) (P 0 ⊓ P 1)
    rw [show P 0 ⊓ P 1=ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) from
      ChapterF.Source.lemma_F_1_3_6 hFC]
    exact hFC.sylow_commonBorel
  have hfC : f.val ∉ C := by
    intro hfc
    obtain ⟨R,hR⟩ := hs
    have hRT : (R : Subgroup C)≤(T : Subgroup G).subgroupOf C := by
      intro x hx
      exact hST (hR ▸ mem_map_of_mem C.subtype hx)
    have hTR : (T : Subgroup G).subgroupOf C=R :=
      R.is_maximal' (T.isPGroup'.comap_subtype (K := C)) hRT
    apply ho
    apply hR ▸ mem_map_of_mem C.subtype (x := (⟨f.val,hfc⟩ : C))
    rw [←hTR]
    exact f.property
  obtain ⟨_,hlift⟩ := d.symplectic_native_middle_lift h hH hp F hm hF he
  rcases hlift with ⟨a,σ,hσ,hact,_,hinner⟩ | ⟨a,σ,hσ,hact,_,hinner⟩
  all_goals
    let α : MulAut (Sp F) := (σ fN).val
    have hα : orderOf α=2 := by
      rw [Subgroup.orderOf_coe,orderOf_injective σ hσ]
      exact (Subgroup.orderOf_coe fN).symm.trans ((Subgroup.orderOf_coe f).trans hf)
    have hαout : α ∉ MulAut.innerSubgroup (Sp F) := fun hh => hfC ((hinner fN).mp hh)
  all_goals
    have hl (x) : (a.comparison.left x).val ∈ α.fixedSubgroup ↔
        x.val ∈ centralizer ({f.val} : Set G) := by
      rw [MulAut.mem_fixedSubgroup]
      apply endpoint_fixed a.comparison.left (a.action fN).left α f.val _
        (a.left_conjugation fN) x
      intro y
      exact (congrArg (fun z => (z.left y).val) (DFunLike.congr_fun hact fN)).symm
    have hr (x) : (a.comparison.right x).val ∈ α.fixedSubgroup ↔
        x.val ∈ centralizer ({f.val} : Set G) := by
      rw [MulAut.mem_fixedSubgroup]
      apply endpoint_fixed a.comparison.right (a.action fN).right α f.val _
        (a.right_conjugation fN) x
      intro y
      exact (congrArg (fun z => (z.right y).val) (DFunLike.congr_fun hact fN)).symm
    obtain ⟨eb⟩ := SourceFusionOrder.outer_fixed_binary_amalgam hq α hα (σ fN).property hαout
  · exact Or.inl ⟨(fixedPairIso (hBP := inf_le_left) (hBQ := inf_le_right)
      (hUR := inf_le_left) (hUV := inf_le_right) a.comparison hl hr).trans eb⟩
  · exact Or.inr ⟨(fixedPairIso (hBP := inf_le_left) (hBQ := inf_le_right)
      (hUR := inf_le_right) (hUV := inf_le_left) a.comparison hl hr).trans eb.reverse⟩

/-- Both original fixed pure endpoints have actual two-residual A4.
The preceding theorem retains their common binary marking. -/
theorem Preparation.symplectic_outer_fixed_endpoint_twoResidual
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ sourceS L H) (i : Fin 2) :
    Nonempty (pResidual 2 (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊓
      centralizer ({f.val} : Set G) : Subgroup G) ≃* alternatingGroup (Fin 4)) := by
  rcases d.symplectic_outer_fixed_binary_amalgam h hH hp F hm hF he f hf ho with hs | hs
  · obtain ⟨e⟩ := hs
    fin_cases i
    · exact ⟨((e.left.subgroupMap _).trans (MulEquiv.subgroupCongr
        (map_pResidual 2 e.left))).trans SourceFusionOrder.binary_point_twoResidual_equiv⟩
    · exact ⟨((e.right.subgroupMap _).trans (MulEquiv.subgroupCongr
        (map_pResidual 2 e.right))).trans SourceFusionOrder.binary_plane_twoResidual_equiv⟩
  · obtain ⟨e⟩ := hs
    fin_cases i
    · exact ⟨((e.left.subgroupMap _).trans (MulEquiv.subgroupCongr
        (map_pResidual 2 e.left))).trans SourceFusionOrder.binary_plane_twoResidual_equiv⟩
    · exact ⟨((e.right.subgroupMap _).trans (MulEquiv.subgroupCongr
        (map_pResidual 2 e.right))).trans SourceFusionOrder.binary_point_twoResidual_equiv⟩

/-- The original fixed endpoint residual has a Klein four two-core,
with no proper nontrivial subgroup normal in that residual. -/
theorem Preparation.symplectic_outer_fixed_endpoint_core
    (f : T) (hf : orderOf f=2) (ho : f.val ∉ sourceS L H) (i : Fin 2) :
    let E := pResidual 2 (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ⊓
      centralizer ({f.val} : Set G) : Subgroup G)
    IsKleinFour (pCore 2 E) ∧
      ∀ U : Subgroup E, U.Normal → U≤pCore 2 E → U=⊥ ∨ U=pCore 2 E := by
  obtain ⟨e⟩ := d.symplectic_outer_fixed_endpoint_twoResidual h hH hp F hm hF he f hf ho i
  exact core_structure_of_alternatingFour e

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
