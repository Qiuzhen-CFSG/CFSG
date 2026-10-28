module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourReciprocal
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourCore

/-!
# The common field-four fixed subgroup

Two saturated elementary actors in the original Sylow have rank four and
fix four dimensions. The outer-rank bound puts both in the inner component;
uniqueness of its plane radical in a two-subgroup identifies their action
images. Equality of the literal relative centralizers follows through the
original automizer representation.

Consequently the fixed subgroup in a parameter-one selection is independent
of the selected pair and its H-star overgroup. In the zero-closure branch,
every moving whole conjugate in T fixes this same subgroup. The subgroup is
therefore exactly C_V(W₀(T,V)), has rank four and is normalized by T.

The Chapter 12 consumer uses selection to place every actual H-star subgroup
in one common normalizer in the positive branch. Zero-closure exclusion and
the remaining normalizer/centralizer argument through 8.2.13 are still open.
Source: Aschbacher--Smith E.3.13, H.4.4--5 and 8.2.5, printed pp.233,
381--382,716--717, refs/quasithin.pdf (1 March 2004 manuscript).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
variable {G : Type*} [Group G] [Finite G]
  (V : Subgroup G) [IsElementaryAbelian 2 V]
  (e : Additive V ≃ₗ[ZMod 2] Space 1)
  (j : Automizer V →* binaryNormalizer 1) (hj : Function.Injective j)
  (he : ∀ a v, e (automizerRepresentation V a v) =
    overgroupAction 1 (binaryNormalizer 1) (j a) (e v))

include hj he in
/-- Two saturated elementary actors in the original Sylow have the same
image on V and the same actual fixed subgroup. -/
theorem field_four_saturated_actors_eq
    (T : Sylow 2 G) (hT : HypothesisE322 V T)
    (A B : Subgroup G) [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B]
    (hAT : A ≤ T) (hBT : B ≤ T)
    (hAr : rank (inducedAutomizer V A) = 4)
    (hBr : rank (inducedAutomizer V B) = 4)
    (hAf : rank (V ⊓ centralizer (A : Set G)) = 4)
    (hBf : rank (V ⊓ centralizer (B : Set G)) = 4) :
    inducedAutomizer V A = inducedAutomizer V B ∧
      V ⊓ centralizer (A : Set G) = V ⊓ centralizer (B : Set G) := by
  let f := (binaryNormalizer 1).subtype.comp j
  have hf : Function.Injective f := (binaryNormalizer 1).subtype_injective.comp hj
  let P := inducedAutomizer V T
  have hp : IsPGroup 2 P := T.2.comap_subtype.map _
  have data (D : Subgroup G) [IsElementaryAbelian 2 D] (hDT : D ≤ T)
      (hr : rank (inducedAutomizer V D) = 4)
      (hd : rank (V ⊓ centralizer (D : Set G)) = 4) :
      let I := (inducedAutomizer V D).map f
      I ≤ P.map f ⊓ binaryImage 1 ∧ rank I = 4*1 ∧
        Module.finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction 1) I) = 4*1 := by
    let I := (inducedAutomizer V D).map f
    have hDN := hDT.trans hT.normalizes
    let : IsElementaryAbelian 2 (inducedAutomizer V D) := inducedAutomizer_elementary V D hDN
    let : IsElementaryAbelian 2 I := IsElementaryAbelian.map _
    have hIr : rank I = 4 := by rw [rank_map_injective f hf,hr]
    have hIN : I ≤ binaryNormalizer 1 := by
      rintro _ ⟨a,_,rfl⟩
      exact (j a).property
    have hIL := Chapter7.NormalizedSource.NonMathieuHermitian.large_elementary_le_image
      1 I hIN (by rw [hIr]; decide)
    have hdim : rank V = 9 := by
      rw [rank,show Nat.card V = Nat.card (Additive V) from rfl,
        Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
        e.finrank_eq,finrank_binary,Nat.log_pow Nat.one_lt_two]
    have hadd := offender_corank_add (W := V) (A := V ⊓ centralizer (D : Set G)) bot_le inf_le_left
    have hadd' : rank V = subgroupCorank V (V ⊓ centralizer (D : Set G)) +
        rank (V ⊓ centralizer (D : Set G)) := by
      simpa only [subgroupCorank,relIndex_bot_left,rank] using hadd
    have hc := fixedCodim_add_finrank (UnipotentRadicals.ambientAction 1) I
    rw [finrank_binary,← fixedCodim_map_equivariant (automizerRepresentation V)
      (UnipotentRadicals.ambientAction 1) f e he,
      fixedCodim_inducedAutomizer V D hDN] at hc
    refine ⟨le_inf (map_mono (map_mono (comap_mono hDT))) hIL,hIr,?_⟩
    rw [hdim,hd] at hadd'
    change Module.finrank (ZMod 2) (fixedSpace (UnipotentRadicals.ambientAction 1) I) = 4*1
    omega
  obtain ⟨ha,har,haf⟩ := data A hAT hAr hAf
  obtain ⟨hb,hbr,hbf⟩ := data B hBT hBr hBf
  let : IsElementaryAbelian 2 (inducedAutomizer V A) := inducedAutomizer_elementary V A (hAT.trans hT.normalizes)
  let : IsElementaryAbelian 2 (inducedAutomizer V B) := inducedAutomizer_elementary V B (hBT.trans hT.normalizes)
  let : IsElementaryAbelian 2 ((inducedAutomizer V A).map f) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 ((inducedAutomizer V B).map f) := IsElementaryAbelian.map _
  have hab := Subgroup.map_injective hf (UnipotentRadicals.eq_of_le_two_subgroup 1
    (P.map f ⊓ binaryImage 1) (hp.map f).to_inf_left inf_le_right _ _ ha hb har hbr haf hbf)
  refine ⟨hab,?_⟩
  ext x
  constructor
  · rintro ⟨hx,hxc⟩
    refine ⟨hx,?_⟩
    have hm := (mem_fixedSpace_inducedAutomizer V A (hAT.trans hT.normalizes)
      (Additive.ofMul ⟨x,hx⟩)).mpr hxc
    rw [hab] at hm
    exact (mem_fixedSpace_inducedAutomizer V B (hBT.trans hT.normalizes) _).mp hm
  · rintro ⟨hx,hxc⟩
    refine ⟨hx,?_⟩
    have hm := (mem_fixedSpace_inducedAutomizer V B (hBT.trans hT.normalizes)
      (Additive.ofMul ⟨x,hx⟩)).mpr hxc
    rw [←hab] at hm
    exact (mem_fixedSpace_inducedAutomizer V A (hAT.trans hT.normalizes) _).mp hm

include hj he in
/-- The fixed subgroup is independent of the parameter-one selection,
even when the selected pairs lie in different H-star subgroups. -/
theorem selected_one_fixed_subgroup_eq
    {T : Sylow 2 G} {M H₁ H₂ I₁ I₂ : Subgroup G}
    {i₁ : I₁} {i₂ : I₂} {S₁ : Sylow 2 I₁} {S₂ : Sylow 2 I₂}
    (s₁ : Selected H₁ T M V I₁ 1 i₁ S₁)
    (s₂ : Selected H₂ T M V I₂ 1 i₂ S₂) (hT : HypothesisE322 V T) :
    V ⊓ centralizer (V.map (MulAut.conj i₁.val⁻¹).toMonoidHom ⊓ I₁.pCoreIn 2 : Set G) =
      V ⊓ centralizer (V.map (MulAut.conj i₂.val⁻¹).toMonoidHom ⊓ I₂.pCoreIn 2 : Set G) := by
  obtain ⟨_,ha,har,haf,_⟩ := selected_one_fixed_subgroup s₁ hT 1 e j hj he
  obtain ⟨_,hb,hbr,hbf,_⟩ := selected_one_fixed_subgroup s₂ hT 1 e j hj he
  let : IsElementaryAbelian 2 (V.map (MulAut.conj i₁.val⁻¹).toMonoidHom) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (V.map (MulAut.conj i₂.val⁻¹).toMonoidHom) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (V.map (MulAut.conj i₁.val⁻¹).toMonoidHom ⊓ (pCore 2 I₁).map I₁.subtype : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (V.map (MulAut.conj i₂.val⁻¹).toMonoidHom ⊓ (pCore 2 I₂).map I₂.subtype : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  exact (field_four_saturated_actors_eq V e j hj he T hT _ _ ha hb har hbr haf hbf).2


include hj he in
/-- All moving whole conjugates in the original Sylow have the same fixed
subgroup. It is the rank-four centralizer of the entire zeroth weak closure. -/
theorem field_four_zero_closure_fixed
    (T : Sylow 2 G) (hT : HypothesisE322 V T)
    (hFF : ¬ IsFFModule (automizerRepresentation V))
    (hr : 3 ≤ globalR V) (hm : 3 ≤ localM V) (hw : globalW V T = 0) :
    let U := V ⊓ centralizer (indexedWeakClosure V T 0 : Set G)
    rank U = 4 ∧ (T : Subgroup G) ≤ normalizer (U : Set G) ∧
      ∀ g : G, V.map (MulAut.conj g).toMonoidHom ≤ T →
        ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) →
          V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) = U := by
  obtain ⟨_,hs,g,hg,hOff,har,_,_⟩ := field_four_zero_weak_closure V e j hj he T hT hFF hr hm hw
  let W := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hA : offenderNormalizer V g = W := inf_eq_left.mpr (hg.trans hT.normalizes)
  have hf := (offender_fixedSpaceFamily_of_lt_globalS hOff (by rw [hw,hs]; decide)).2
  rw [hw,hs,hA] at hf
  obtain ⟨hfix,hN⟩ := field_four_third_family_fixed_normal V e j hj he T hT W hg hf
  let U := V ⊓ centralizer (W : Set G)
  have hall (a : G) (ha : V.map (MulAut.conj a).toMonoidHom ≤ T)
      (hmove : ¬ V.map (MulAut.conj a).toMonoidHom ≤ centralizer (V : Set G)) :
      V ⊓ centralizer (V.map (MulAut.conj a).toMonoidHom : Set G) = U := by
    let Z := V.map (MulAut.conj a).toMonoidHom
    let : IsElementaryAbelian 2 Z := IsElementaryAbelian.map _
    have hAz : offenderNormalizer V a = Z := inf_eq_left.mpr (ha.trans hT.normalizes)
    have hoff : IsWOffenderAt V T a := by
      refine ⟨?_,?_⟩
      · intro hc
        exact hmove (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc))
      · rw [hAz,hw]
        simp [subgroupCorank,Z]
    have hfamily := (offender_fixedSpaceFamily_of_lt_globalS hoff (by rw [hw,hs]; decide)).2
    rw [hw,hs,hAz] at hfamily
    have hzr := (field_four_fixed_family_three_rank V e j hj he _ hfamily).1
    have hzf := (field_four_third_family_fixed_normal V e j hj he T hT Z ha hfamily).1
    exact (field_four_saturated_actors_eq V e j hj he T hT Z W ha hg hzr har hzf hfix).2
  have hweak : indexedWeakClosure V T 0 ≤ centralizer (U : Set G) := by
    rw [weakClosure_eq_sSup_gamma]
    apply sSup_le
    intro A hmem
    obtain ⟨a,rfl,ha⟩ := (mem_gamma_zero_iff V T A).mp hmem
    by_cases hc : V.map (MulAut.conj a).toMonoidHom ≤ centralizer (V : Set G)
    · exact hc.trans (centralizer_le (show U ≤ V from inf_le_left))
    · apply le_centralizer_iff.mpr
      rw [←hall a ha hc]
      exact inf_le_right
  have heq : V ⊓ centralizer (indexedWeakClosure V T 0 : Set G) = U := by
    apply le_antisymm
    · exact inf_le_inf_left V (centralizer_le (gamma_le_weakClosure
        ((mem_gamma_zero_iff V T W).mpr ⟨g,rfl,hg⟩)))
    · exact le_inf inf_le_left (le_centralizer_iff.mp hweak)
  dsimp only
  rw [heq]
  exact ⟨hfix,hN,hall⟩

end CFSG.Quasithin.Chapter8.Section02.HermitianSource
