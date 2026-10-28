module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.ComponentElevenSection
public import Theory.SpecificGroups.PSL2.ElevenInvolutionGeneration
public import Theory.GroupTheory.PerfectInnerConjugateGeneration
public import Theory.Representation.BinaryOffender.SimplePrimeMoved
public import Theory.Representation.BinaryOffender.PerfectCentralizer
public import Theory.Representation.BinaryOffender.SaturatedComponentNormality
public import Theory.GroupTheory.CComponent.QuotientLifting
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import Theory.Representation.BinaryConjugationSection.CommutatorFixedExtension
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan

/-!
# The original PSL2(11) module and component normality

Three conjugates of the original V-star actor generate over the selected
component. The rank-four displacement bounds its entire commutator space
by twelve dimensions. The prime eleven forces every noncentral section to
have dimension at least ten, so the whole commutator is Irr⁺, including
its possible central layers. Saturation then identifies the V-star
displacement on that commutator with its displacement on the full section.

A distinct conjugate component would centralize this displacement. Thus
the original T normalizes K, and the source two-conjugate orbit bound makes
K normal in H. The actual conjugate-span definition of U_H now gives
[U_H/V₁,K-star] = U_H/V₁. The literal faithful quotient coordinates and
V₅ displacement are retained throughout.

The original selected component and earlier geometric inputs remain
explicit. Its existence from five-core centralization, the upper bound
through the intrinsic O₂(L₁), the abelian span conclusion and the universal
natural reduction are not asserted here.

Source: Aschbacher--Smith, proof of 12.6.26, printed p.833, using 1.2.1(3).
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
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
/-- Three conjugates of an element of the original V-star generate over the
same selected component. All conjugators lie in that component. -/
theorem SourceHypothesis.original_selectedComponent_three_conjugates
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    ∃ u ∈ Nonabelian.Setup.star H V,
      ∃ f : Fin 3 → Nonabelian.Setup.star H c.K,
        Nonabelian.Setup.star H c.K ≤
          ⨆ i, (zpowers u).map (MulAut.conj (f i : Nonabelian.Setup.Hstar H)).toMonoidHom := by
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
  let tB := e.symm t
  have htB : orderOf tB = 2 := (e.symm.orderOf_eq t).trans ht2
  obtain ⟨f,hf⟩ := Theory.PSL2.ElevenConjugateBudget.three_involution_conjugates_of_card hF e tB htB
  obtain ⟨v,hv,he⟩ := hb
  let u := QuotientGroup.mk' (pCore 2 H) (inclusion a.local_le v)
  have hu : u ∈ Nonabelian.Setup.star H V := mem_map_of_mem _ hv
  let := c.component.2
  refine ⟨u,hu,f,perfect_le_conjugates_of_inner_action _ u tB ?_ f hf⟩
  intro k
  rw [←a.conjugation v k,he]
  apply congrArg Subtype.val
  apply e.injective
  have hh := DFunLike.congr_fun ht (e k)
  change e (b (e.symm (e k))) = t*e k*t⁻¹ at hh
  simpa only [e.symm_apply_apply,map_mul,map_inv,tB,e.apply_symm_apply] using hh

include hz hTV hTz hbound hH hn a in
/-- The entire original component commutator, including its fixed layers,
has dimension at most twelve on any marked original binary section. -/
theorem SourceHypothesis.original_selectedComponent_moved_dimension_le
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W)
    (κ : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
      ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H)))) :
    Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ (Nonabelian.Setup.star H c.K)) ≤ 12 := by
  obtain ⟨u,hu,f,hf⟩ := S.original_selectedComponent_three_conjugates D hZ z hz hTV hTz
    hbound hH hn c a hTI hns
  have hb := moved_finrank_le_mul_displacement_of_conjugates σ
    (Nonabelian.Setup.star H c.K) u (fun i => (f i).val) hf
  have hd := S.original_binary_displacement_bound D hZ z hz hTV hTz hbound hH hn σ κ u hu
  omega

include hz hTV hTz hbound hH hn a in
/-- Faithfulness on the component commutator gives the lower bound ten,
while the original involution gives the upper bound twelve on the same space. -/
theorem SourceHypothesis.original_selectedComponent_moved_dimension
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W)
    (hσ : Function.Injective σ)
    (κ : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
      ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H)))) :
    10 ≤ Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ (Nonabelian.Setup.star H c.K)) ∧
    Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ (Nonabelian.Setup.star H c.K)) ≤ 12 := by
  refine ⟨?_,S.original_selectedComponent_moved_dimension_le D hZ z hz hTV hTz hbound hH hn c a hTI hns σ κ⟩
  let B := Nonabelian.Setup.star H c.K
  let : IsSimpleGroup B := S.original_selectedComponent_simple D hZ z hz hTV hTz
    hbound hH hn c a hTI hns
  let := c.component.2
  let τ := (invariantSubspace σ B (subspaceCommutator σ ⊤ B)
    (subspaceCommutator_invariant σ ⊤ B)).toRepresentation
  have hτ : Function.Injective τ := faithful_on_moved_of_simple_perfect σ B (hσ.comp B.subtype_injective)
  obtain ⟨F,hfield,hfinite,hF,⟨e⟩⟩ :=
    S.original_selectedComponent_linearTwoEleven D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let := hfield
  let := hfinite
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
    (F := F) (hF ▸ (by decide : Odd 11))
  rw [←Nat.card_congr e.toEquiv,hF] at hc
  have hd : 11 ∣ Nat.card B := by
    have he : Nat.card B = 660 := by dsimp [B]; omega
    rw [he]
    decide
  have hh := Representation.BinaryPrimeDegree.orderOf_le_finrank τ hτ (by decide : Nat.Prime 11) (by decide) hd
  rwa [Representation.BinaryPrimeDegree.orderOf_two_mod_eleven] at hh
include hz hTV hTz hbound hH hn a in
/-- The source Irr⁺ conclusion holds on the whole literal component
commutator, without discarding its possible central layers. -/
theorem SourceHypothesis.original_selectedComponent_moved_irrPlus
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W)
    (hσ : Function.Injective σ)
    (κ : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
      ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H)))) :
    IsIrrPlus σ (Nonabelian.Setup.star H c.K)
      (subspaceCommutator σ ⊤ (Nonabelian.Setup.star H c.K)) := by
  let B := Nonabelian.Setup.star H c.K
  let : IsSimpleGroup B := S.original_selectedComponent_simple D hZ z hz hTV hTz
    hbound hH hn c a hTI hns
  let := c.component.2
  obtain ⟨F,hfield,hfinite,hF,⟨e⟩⟩ :=
    S.original_selectedComponent_linearTwoEleven D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let := hfield
  let := hfinite
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
    (F := F) (hF ▸ (by decide : Odd 11))
  rw [←Nat.card_congr e.toEquiv,hF] at hc
  have hd : 11 ∣ Nat.card B := by
    have he : Nat.card B = 660 := by dsimp [B]; omega
    rw [he]
    decide
  apply isIrrPlus_moved_of_prime_degree σ B (hσ.comp B.subtype_injective)
    (by decide : Nat.Prime 11) (by decide) hd
  rw [Representation.BinaryPrimeDegree.orderOf_two_mod_eleven]
  have hb := S.original_selectedComponent_moved_dimension_le D hZ z hz hTV hTz
    hbound hH hn c a hTI hns σ κ
  change Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ B) ≤ 12 at hb
  omega

include hz hTV hTz hbound hH hn a in
/-- Every other actual component of H-star centralizes the original selected
component's commutator space. This is the source's commuting-component step. -/
theorem SourceHypothesis.original_selectedComponent_other_component_fixes_moved
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W)
    (hσ : Function.Injective σ)
    (κ : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
      ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (J : Subgroup (Nonabelian.Setup.Hstar H))
    (hJ : IsComponent (Nonabelian.Setup.Hstar H) J)
    (hne : J ≠ Nonabelian.Setup.star H c.K) :
    subspaceCommutator σ ⊤ (Nonabelian.Setup.star H c.K) ≤ fixedSpace σ J := by
  let := hJ.2
  have hcent : J ≤ centralizer (Nonabelian.Setup.star H c.K : Set _) :=
    commutator_eq_bot_iff_le_centralizer.mp (hJ.commutator_eq_bot_of_ne c.component hne)
  have hI := S.original_selectedComponent_moved_irrPlus D hZ z hz hTV hTz hbound hH hn c a hTI hns σ hσ κ
  exact hI.le_fixedSpace_of_perfect_centralizes σ hcent
    (subspaceCommutator_invariant_normalizer σ
      (le_subspaceStabilizer σ ⊤ (by intros; trivial))
      (hcent.trans (Subgroup.centralizer_le_normalizer _)))

include hz hTV hTz hbound hH hn a in
/-- Apply the module argument to the literal U_H/V1 representation, retaining
its faithful H-star actor and actual quotient coordinates. -/
theorem SourceHypothesis.original_selectedComponent_point_quotient_moved
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    let E := D.fullSetup hZ T z
    let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
    let _ : (E.V₁.subgroupOf (E.UH H)).Normal := h.point_normal_in_UH
    let _ : IsElementaryAbelian 2 (E.UH H ⧸ E.V₁.subgroupOf (E.UH H)) := h.point_quotient_elementary
    ∃ (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H)
        (Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))))
      (κ : BinaryConjugationSection H (E.UH H) E.V₁
        (σ.comp (QuotientGroup.mk' (pCore 2 H)))),
      Function.Injective σ ∧
      (∀ u : E.UH H, (κ.coordinates u).toAdd =
        Additive.ofMul (QuotientGroup.mk' (E.V₁.subgroupOf (E.UH H)) u)) ∧
      IsIrrPlus σ (Nonabelian.Setup.star H c.K)
        (subspaceCommutator σ ⊤ (Nonabelian.Setup.star H c.K)) ∧
      10 ≤ Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ (Nonabelian.Setup.star H c.K)) ∧
      Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ (Nonabelian.Setup.star H c.K)) ≤ 12 := by
  dsimp only
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let E := D.fullSetup hZ T z
  let _ : (E.V₁.subgroupOf (E.UH H)).Normal := h.point_normal_in_UH
  let _ : IsElementaryAbelian 2 (E.UH H ⧸ E.V₁.subgroupOf (E.UH H)) := h.point_quotient_elementary
  obtain ⟨σ,κ,hσ,hcoord⟩ := h.faithful_point_quotient
  exact ⟨σ,κ,hσ,hcoord,
    S.original_selectedComponent_moved_irrPlus D hZ z hz hTV hTz hbound hH hn c a hTI hns
      (W := Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))) σ hσ κ,
    S.original_selectedComponent_moved_dimension D hZ z hz hTV hTz hbound hH hn c a hTI hns
      (W := Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))) σ hσ κ⟩

include hz hTV hTz hbound hH hn a in
/-- The actual V-star has the same displacement on the original component
commutator as on the whole section; its centralizer normalizes that component. -/
theorem SourceHypothesis.original_selectedComponent_module_normalizer
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W)
    (hσ : Function.Injective σ)
    (κ : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
      ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H)))) :
    subspaceCommutator σ (subspaceCommutator σ ⊤ (Nonabelian.Setup.star H c.K))
        (Nonabelian.Setup.star H V) =
      subspaceCommutator σ ⊤ (Nonabelian.Setup.star H V) ∧
      centralizer (Nonabelian.Setup.star H V : Set (Nonabelian.Setup.Hstar H)) ≤
        normalizer (Nonabelian.Setup.star H c.K : Set (Nonabelian.Setup.Hstar H)) := by
  let B := Nonabelian.Setup.star H c.K
  let U := Nonabelian.Setup.star H V
  let I := subspaceCommutator σ ⊤ B
  let := c.component.2
  obtain ⟨u,hu,f,hf⟩ := S.original_selectedComponent_three_conjugates
    D hZ z hz hTV hTz hbound hH hn c a hTI hns
  have hB : B ≠ ⊥ := by
    intro he
    apply c.moved
    change ⁅B,U⁆ = ⊥
    rw [he,commutator_bot_left]
  have hune : u ≠ 1 := by
    intro he
    rw [he] at hf
    rw [show zpowers (1 : Nonabelian.Setup.Hstar H) = ⊥ from zpowers_eq_bot.mpr rfl] at hf
    simp only [Subgroup.map_bot,iSup_bot] at hf
    exact hB (le_bot_iff.mp hf)
  have hcyc : zpowers u = U := by
    apply le_antisymm (zpowers_le.mpr hu)
    intro x hx
    have hn' : (⟨u,hu⟩ : U) ≠ 1 := fun hh => hune (congrArg Subtype.val hh)
    have hx' : (⟨x,hx⟩ : U) ∈ zpowers (⟨u,hu⟩ : U) :=
      mem_zpowers_of_prime_card
        (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.1 hn'
    obtain ⟨n,hn'⟩ := mem_zpowers_iff.mp hx'
    exact mem_zpowers_iff.mpr ⟨n,congrArg Subtype.val hn'⟩
  have hinv : U ≤ subspaceStabilizer σ I := subspaceCommutator_invariant_normalizer σ
    (le_subspaceStabilizer σ ⊤ (by intros; trivial)) c.normalized
  have hlow := (S.original_selectedComponent_moved_dimension D hZ z hz hTV hTz
    hbound hH hn c a hTI hns σ hσ κ).1
  change 10 ≤ Module.finrank (ZMod 2) I at hlow
  have he : subspaceCommutator σ I (zpowers u) = subspaceCommutator σ ⊤ (zpowers u) :=
    commutator_eq_of_saturated_conjugate_bound σ B I (subspaceCommutator_invariant σ ⊤ B)
      (subspaceCommutator_idempotent_of_perfect σ B) u (hinv hu) f hf
      (r := 4) (by change 3 * (4-1) < Module.finrank (ZMod 2) I; omega)
      (S.original_binary_displacement_bound D hZ z hz hTV hTz hbound hH hn σ κ u hu)
  have hm : (σ u - LinearMap.id).range ≤ I := by
    rw [←Representation.CyclicFixedRank.commutator_eq_range,←he]
    exact subspaceCommutator_le_of_invariant σ (zpowers_le.mpr (hinv hu))
  refine ⟨?_,?_⟩
  · change subspaceCommutator σ I U = subspaceCommutator σ ⊤ U
    rwa [hcyc] at he
  · have hh := component_normalized_by_centralizer_of_moved_containment σ hσ B c.component
      (S.original_selectedComponent_moved_irrPlus D hZ z hz hTV hTz hbound hH hn c a hTI hns σ hσ κ)
      u (hcyc.symm ▸ c.full_commutator) hm
    exact (centralizer_le (Set.singleton_subset_iff.mpr hu)).trans hh

include hz hTV hTz hbound hH hn a in
/-- On the faithful literal point quotient, the original V-star centralizer
normalizes the selected component. No change of ambient H is made. -/
theorem SourceHypothesis.original_selectedComponent_star_centralizer_normalizes
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    centralizer (Nonabelian.Setup.star H V : Set (Nonabelian.Setup.Hstar H)) ≤
      normalizer (Nonabelian.Setup.star H c.K : Set (Nonabelian.Setup.Hstar H)) := by
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let E := D.fullSetup hZ T z
  let _ : (E.V₁.subgroupOf (E.UH H)).Normal := h.point_normal_in_UH
  let _ : IsElementaryAbelian 2 (E.UH H ⧸ E.V₁.subgroupOf (E.UH H)) := h.point_quotient_elementary
  obtain ⟨σ,κ,hσ,_⟩ := h.faithful_point_quotient
  exact (S.original_selectedComponent_module_normalizer
    D hZ z hz hTV hTz hbound hH hn c a hTI hns
    (W := Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))) σ hσ κ).2

include hz hTV hTz hbound hH hn a in
/-- The original Sylow two-subgroup normalizes the original C-component.
The assertion is reflected through H → H/O₂(H), not merely a model isomorphism. -/
theorem SourceHypothesis.original_selectedComponent_sylow_normalizes
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    (T : Subgroup G) ≤ normalizer (c.K : Set G) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have he := (S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn).2.2.2.2
  have hnorm := S.original_selectedComponent_star_centralizer_normalizes
    D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  intro t ht
  let tH : H := ⟨t,h.T_le_H ht⟩
  have htc : q tH ∈ centralizer (Nonabelian.Setup.star H V : Set (Nonabelian.Setup.Hstar H)) := by
    change tH ∈ (centralizer (Nonabelian.Setup.star H V : Set (Nonabelian.Setup.Hstar H))).comap q
    rw [he]
    exact hTV ht
  have htn : tH ∈ normalizer (c.K.subgroupOf H : Set H) := by
    rw [←normalizer_cComponent_quotient c.ccomponent (pCore 2 H)]
    exact hnorm htc
  rwa [←subgroupOf_normalizer_eq c.le_H] at htn

include hz hTV hTz hbound hH hn a in
/-- The source subgroup generated by K, L₁ and T normalizes the original K.
This records the normality step without assuming H equals that subgroup. -/
theorem SourceHypothesis.original_selectedComponent_generated_normalizer
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    c.K ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G) ≤ normalizer (c.K : Set G) := by
  exact sup_le (sup_le c.K.le_normalizer
    (S.original_residual_normalizes_selectedComponent D hZ z hz hH c))
    (S.original_selectedComponent_sylow_normalizes D hZ z hz hTV hTz hbound hH hn c a hTI hns)

include hz hTV hTz hbound hH hn a in
/-- The original C-component is normal in H. The source two-conjugate
alternative is ruled out by the original Sylow subgroup's normalization. -/
theorem SourceHypothesis.original_selectedComponent_normal
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    (c.K.subgroupOf H).Normal ∧ (Nonabelian.Setup.star H c.K).Normal := by
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have ht := S.original_selectedComponent_sylow_normalizes
    D hZ z hz hTV hTz hbound hH hn c a hTI hns
  let TH : Sylow 2 H := T.subtype h.T_le_H
  have hS : (TH : Subgroup H) ≤ normalizer (c.K.subgroupOf H : Set H) := by
    rw [←subgroupOf_normalizer_eq c.le_H]
    intro x hx
    exact ht hx
  have hnK : (c.K.subgroupOf H).Normal := by
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source
      (S.original_star_sqtk D hZ z hz hH) c.ccomponent with hk | hi
    · exact hk
    · have hd := index_dvd_of_le hS
      rw [hi] at hd
      exact (TH.not_dvd_index hd).elim
  exact ⟨hnK,Normal.map hnK (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _)⟩

include hz hTV hTz hbound hH hn a in
/-- Normality and the original conjugate-span definition make the component
move the entire U_H/V₁ section. The original seed is exactly its V-star displacement. -/
theorem SourceHypothesis.original_selectedComponent_whole_module
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W)
    (hσ : Function.Injective σ)
    (κ : BinaryConjugationSection H ((D.fullSetup hZ T z).UH H)
      ((D.fullSetup hZ T z).V₁) (σ.comp (QuotientGroup.mk' (pCore 2 H)))) :
    κ.imageSpace (D.fullSetup hZ T z).V₅ = subspaceCommutator σ ⊤ (Nonabelian.Setup.star H V) ∧
      subspaceCommutator σ ⊤ (Nonabelian.Setup.star H c.K) = ⊤ ∧
      IsIrrPlus σ (Nonabelian.Setup.star H c.K) ⊤ ∧
      10 ≤ Module.finrank (ZMod 2) W ∧ Module.finrank (ZMod 2) W ≤ 12 := by
  let E := D.fullSetup hZ T z
  let B := Nonabelian.Setup.star H c.K
  let I := subspaceCommutator σ ⊤ B
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  have hg := S.original_nonabelian_geometry D hZ z hz hTV hTz hbound hH hn
  have hcomm : ⁅V,E.UH H⁆ ≤ E.UH H :=
    le_normalizer_iff_commutator_le_right.mp (h.V_le_H.trans κ.normalized)
  have hseed : κ.imageSpace E.V₅ = subspaceCommutator σ ⊤ (Nonabelian.Setup.star H V) := by
    rw [hg.2.2.2.1,sup_comm,commutator_comm (E.UH H) V,
      κ.imageSpace_sup_kernel _ hcomm,κ.imageSpace_commutator V (E.UH H) h.V_le_H le_rfl,
      κ.imageSpace_self,subspaceCommutator_comp_map]
    rfl
  let : B.Normal := (S.original_selectedComponent_normal D hZ z hz hTV hTz hbound hH hn c a hTI hns).2
  have hinv : (⊤ : Subgroup (Nonabelian.Setup.Hstar H)) ≤ subspaceStabilizer σ I :=
    subspaceCommutator_invariant_normalizer σ
      (le_subspaceStabilizer σ ⊤ (by intros; trivial)) le_normalizer_of_normal
  let P : Subrepresentation (σ.comp (QuotientGroup.mk' (pCore 2 H))) := {
    toSubmodule := I
    apply_mem_toSubmodule g v hv := (hinv (mem_top _) v).2 hv }
  have hVI : κ.imageSpace E.V₅ ≤ I := by
    rw [hseed,←(S.original_selectedComponent_module_normalizer
      D hZ z hz hTV hTz hbound hH hn c a hTI hns σ hσ κ).1]
    exact subspaceCommutator_le_of_invariant σ
      (subspaceCommutator_invariant_normalizer σ
        (le_subspaceStabilizer σ ⊤ (by intros; trivial)) c.normalized)
  have hfull : I = ⊤ := κ.generated_image_le E.V₅ rfl P hVI
  have hirr := S.original_selectedComponent_moved_irrPlus D hZ z hz hTV hTz hbound hH hn c a hTI hns σ hσ κ
  have hd := S.original_selectedComponent_moved_dimension D hZ z hz hTV hTz hbound hH hn c a hTI hns σ hσ κ
  change IsIrrPlus σ B I at hirr
  change 10 ≤ Module.finrank (ZMod 2) I ∧ Module.finrank (ZMod 2) I ≤ 12 at hd
  rw [hfull,finrank_top] at hd
  exact ⟨hseed,hfull,hfull ▸ hirr,hd⟩

include hz hTV hTz hbound hH hn a in
/-- The source's entire tilde U_H is Irr⁺ for the same selected component,
with its exact quotient coordinates and original V₅ displacement retained. -/
theorem SourceHypothesis.original_selectedComponent_point_quotient_whole
    (hTI : ∀ g ∈ M L, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L) :
    let E := D.fullSetup hZ T z
    let h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
    let _ : (E.V₁.subgroupOf (E.UH H)).Normal := h.point_normal_in_UH
    let _ : IsElementaryAbelian 2 (E.UH H ⧸ E.V₁.subgroupOf (E.UH H)) := h.point_quotient_elementary
    let W := Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))
    ∃ (σ : Representation (ZMod 2) (Nonabelian.Setup.Hstar H) W)
      (κ : BinaryConjugationSection H (E.UH H) E.V₁
        (σ.comp (QuotientGroup.mk' (pCore 2 H)))),
      Function.Injective σ ∧
      (∀ u : E.UH H, (κ.coordinates u).toAdd =
        Additive.ofMul (QuotientGroup.mk' (E.V₁.subgroupOf (E.UH H)) u)) ∧
      κ.imageSpace E.V₅ = subspaceCommutator σ ⊤ (Nonabelian.Setup.star H V) ∧
      subspaceCommutator σ ⊤ (Nonabelian.Setup.star H c.K) = ⊤ ∧
      IsIrrPlus σ (Nonabelian.Setup.star H c.K) ⊤ ∧
      10 ≤ Module.finrank (ZMod 2) W ∧ Module.finrank (ZMod 2) W ≤ 12 := by
  dsimp only
  let E := D.fullSetup hZ T z
  have h := S.original_f9_of_earlier_geometry D hZ z hz hTV hTz hbound hH
  let _ : (E.V₁.subgroupOf (E.UH H)).Normal := h.point_normal_in_UH
  let _ : IsElementaryAbelian 2 (E.UH H ⧸ E.V₁.subgroupOf (E.UH H)) := h.point_quotient_elementary
  obtain ⟨σ,κ,hσ,hcoord⟩ := h.faithful_point_quotient
  exact ⟨σ,κ,hσ,hcoord,S.original_selectedComponent_whole_module
    D hZ z hz hTV hTz hbound hH hn c a hTI hns
    (W := Additive (E.UH H ⧸ E.V₁.subgroupOf (E.UH H))) σ hσ κ⟩
end CFSG.Quasithin.Chapter12.Section06
