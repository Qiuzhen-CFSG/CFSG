module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.CommutatorBounds

/-!
# The quintet cocode commutator and code fixed space

Under the precise cocode flag, action marking and earlier inputs, the actual
commutator `[M22Cocode,K]` equals the geometric six-dimensional term. Relative
normality, supplied by the marked quotient kernel, makes the commutator
Q-invariant. Faithfulness of the center action supplies a nonzero displacement
in V1, and chiefness forces V1 into the commutator.

A proper commutator would supplement V2 in V6 and intersect it in V1. Their
images would therefore complement each other in V6/V1. Transporting the pair
through the actual middle equivalence and taking coannihilators would split
the marked five-dimensional kernel module, contrary to indecomposability.
The coordinate pairing then identifies V4 with the code fixed space.

This is a conditional deduction from `CocodeFlag`, `CocodeActionData` and
`EarlierInputs`; construction of those data is a separate source obligation.
Source: Aschbacher--Smith, H.14.3(2), H.14.4(2--3), H.15.4(1--2), and
H.16.3(1), printed pp.397--400,403, manuscript of 1 March 2004.
-/

public section
noncomputable section
namespace MathieuCode.M22Quintet.DualAction.CommutatorProof
variable {k G E S : Type*} [Field k] [Group G]
  [AddCommGroup E] [Module k E] [FiniteDimensional k E]
  [AddCommGroup S] [Module k S]
  (ρ : Representation k G E) (σ : Representation k G S)
  (e : S ≃ₗ[k] Module.Dual k E)
  (he : ∀ g v, e (σ g v) = ρ.dual g (e v))

private def coann (U : Subrepresentation σ) : Subrepresentation ρ where
  toSubmodule := (U.toSubmodule.map e.toLinearMap).dualCoannihilator
  apply_mem_toSubmodule g v hv := by
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    rintro _ ⟨u, hu, rfl⟩
    have h := hv (e (σ g⁻¹ u)) ⟨σ g⁻¹ u, U.apply_mem_toSubmodule g⁻¹ hu, rfl⟩
    rw [he] at h
    change e u (ρ g v) = 0
    change e u (ρ (g⁻¹)⁻¹ v) = 0 at h
    simpa only [inv_inv] using h

private theorem compl_space {T : Type*} [AddCommGroup T] [Module k T]
    {τ : Representation k G T} (A B : Subrepresentation τ) :
    IsCompl A B ↔ IsCompl A.toSubmodule B.toSubmodule := by
  simp only [isCompl_iff, disjoint_iff, codisjoint_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨congrArg Subrepresentation.toSubmodule h₁,
      congrArg Subrepresentation.toSubmodule h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨Subrepresentation.toSubmodule_injective h₁,
      Subrepresentation.toSubmodule_injective h₂⟩

include e he in
private theorem indecomp_transfer
    (hρ : ∀ A B : Subrepresentation ρ, IsCompl A B → A = ⊥ ∨ B = ⊥)
    (A B : Subrepresentation σ) (h : IsCompl A B) : A = ⊥ ∨ B = ⊥ := by
  have hm := (Submodule.orderIsoMapComap e).isCompl_iff.mp ((compl_space A B).mp h)
  have hc := (Subspace.orderIsoFiniteDimensional (K := k) (V := E)).symm.isCompl_iff.mp hm.dual
  have hc' : IsCompl (coann ρ σ e he A) (coann ρ σ e he B) :=
    (compl_space _ _).mpr hc
  have top_of (U : Subrepresentation σ) (hu : coann ρ σ e he U = ⊥) : U = ⊤ := by
    have hz : (U.toSubmodule.map e.toLinearMap).dualCoannihilator = ⊥ :=
      congrArg Subrepresentation.toSubmodule hu
    have ht := congrArg Submodule.dualAnnihilator hz
    rw [Subspace.dualCoannihilator_dualAnnihilator_eq, Submodule.dualAnnihilator_bot] at ht
    exact Subrepresentation.toSubmodule_injective ((Submodule.map_eq_top_iff).mp ht)
  rcases hρ _ _ hc' with ha | hb
  · exact Or.inr (by simpa only [top_of A ha, top_inf_eq] using h.disjoint.eq_bot)
  · exact Or.inl (by simpa only [top_of B hb, inf_top_eq] using h.disjoint.eq_bot)

private theorem quotient_isCompl {T : Type*} [AddCommGroup T] [Module k T]
    (C A B : Submodule k T) (hCA : C ≤ A) (hCB : C ≤ B)
    (hi : A ⊓ B = C) (hs : A ⊔ B = ⊤) :
    IsCompl (A.map C.mkQ) (B.map C.mkQ) := by
  constructor
  · apply disjoint_iff.mpr
    apply Submodule.comap_injective_of_surjective C.mkQ_surjective
    rw [Submodule.comap_inf, Submodule.comap_map_mkQ, Submodule.comap_map_mkQ,
      sup_eq_right.mpr hCA, sup_eq_right.mpr hCB, hi,
      Submodule.comap_bot, Submodule.ker_mkQ]
  · apply codisjoint_iff.mpr
    rw [← Submodule.map_sup, hs, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr C.mkQ_surjective

end MathieuCode.M22Quintet.DualAction.CommutatorProof

set_option backward.isDefEq.respectTransparency false
namespace MathieuCode.M22Quintet.DualAction
variable {F : CocodeFlag} {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

private theorem commutator_invariant (D : CocodeActionData F E) (q : Q)
    (v : M22Cocode) (hv : v ∈ cocodeCommutator) : cocodeAction q v ∈ cocodeCommutator := by
  have hle : cocodeCommutator ≤ cocodeCommutator.comap (cocodeAction q) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨k, u⟩, rfl⟩
    have hk : D.quotientMap (kernelInclusion k) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [D.quotientMap_ker]
      exact k.property
    let c : Q := q * kernelInclusion k * q⁻¹
    have hc : c.val ∈ K := by
      have hc' : c ∈ D.quotientMap.ker := by
        simp [c, MonoidHom.mem_ker, hk]
      rw [D.quotientMap_ker] at hc'
      exact hc'
    have he : m22OuterCocodeRepresentation c.val (cocodeAction q u) =
        cocodeAction q (m22OuterCocodeRepresentation k.val u) := by
      change m22OuterCocodeRepresentation c.val (m22OuterCocodeRepresentation q.val u) = _
      rw [← Module.End.mul_apply, ← map_mul]
      have hmul : c.val * q.val = q.val * k.val := by
        simp [c, kernelInclusion, mul_assoc]
      rw [hmul, map_mul, Module.End.mul_apply]
      rfl
    change cocodeAction q (m22OuterCocodeRepresentation k.val u - u) ∈ cocodeCommutator
    rw [map_sub, ← he]
    exact Representation.Coinvariants.sub_mem_ker (⟨c.val, hc⟩ : K) (cocodeAction q u)
  exact hle hv

private def commutatorRep (D : CocodeActionData F E) : Subrepresentation cocodeAction where
  toSubmodule := cocodeCommutator
  apply_mem_toSubmodule g _ hv := commutator_invariant D g _ hv

private theorem center_le_commutator (D : CocodeActionData F E) (H : EarlierInputs D) :
    V1 ≤ cocodeCommutator := by
  obtain ⟨i, _, hi, _, _⟩ := H.involution_displacement
  have hi' : cocodeKernelAction i ≠ 1 := by
    intro he
    exact hi (D.centerAction_faithful (he.trans (map_one cocodeKernelAction).symm))
  obtain ⟨u, hu⟩ : ∃ u : V6, cocodeKernelAction i u ≠ u := by
    by_contra! hn
    exact hi' (LinearEquiv.ext hn)
  have hr : cocodeKernelAction i ∈ BinaryLinear.radical F.center.toSubmodule := by
    rw [← D.centerAction_full]
    exact ⟨i, rfl⟩
  let w : M22Cocode := m22OuterCocodeRepresentation i.val u.val - u.val
  have hw1 : w ∈ F.one := by
    change w ∈ F.one.toSubmodule
    rw [F.one_eq]
    exact hr.2 u
  have hwW : w ∈ commutatorRep D := Representation.Coinvariants.sub_mem_ker i u.val
  have hw0 : w ≠ 0 := by
    intro hz
    apply hu
    apply Subtype.ext
    exact sub_eq_zero.mp hz
  have hne : commutatorRep D ⊓ F.one ≠ ⊥ := by
    intro he
    have hm : w ∈ commutatorRep D ⊓ F.one := ⟨hwW, hw1⟩
    rw [he] at hm
    exact hw0 hm
  have he := (F.chief01.eq_or_eq bot_le inf_le_right).resolve_left hne
  rw [← F.one_eq]
  exact he ▸ (inf_le_left : commutatorRep D ⊓ F.one ≤ commutatorRep D)

private theorem commutator_sup_two (D : CocodeActionData F E) (H : EarlierInputs D) :
    commutatorRep D ⊔ F.two = V6Subrepresentation := by
  have hs : commutatorRep D ⊔ F.two ≤ V6Subrepresentation :=
    sup_le (cocode_commutator_le_six D) F.chief26.le
  rcases F.chief26.eq_or_eq le_sup_right hs with h | h
  · have hw : commutatorRep D ≤ F.two := h ▸ le_sup_left
    change cocodeCommutator ≤ F.two.toSubmodule at hw
    exact False.elim (cocode_commutator_not_le_two D H (by simpa only [F.two_eq] using hw))
  · exact h

private theorem commutator_inf_two (D : CocodeActionData F E) (H : EarlierInputs D)
    (hne : cocodeCommutator ≠ V6) : commutatorRep D ⊓ F.two = F.one := by
  have h1 : F.one ≤ commutatorRep D := by
    change F.one.toSubmodule ≤ cocodeCommutator
    rw [F.one_eq]
    exact center_le_commutator D H
  rcases F.chief12.eq_or_eq (le_inf h1 F.chief12.le) inf_le_right with h | h
  · exact h
  · have ht : F.two ≤ commutatorRep D := h ▸ inf_le_left
    have hs := commutator_sup_two D H
    rw [sup_eq_left.mpr ht] at hs
    exact False.elim (hne (congrArg Subrepresentation.toSubmodule hs))

private def inSix (U : Subrepresentation cocodeAction) :
    Subrepresentation V6Subrepresentation.toRepresentation where
  toSubmodule := U.toSubmodule.comap V6.subtype
  apply_mem_toSubmodule g _ hv := U.apply_mem_toSubmodule g hv

private def sectionImage (F : CocodeFlag) (U : Subrepresentation cocodeAction) :
    Subrepresentation F.middleAction := F.center.quotientImage (inSix U)

private theorem sectionImage_eq_bot (F : CocodeFlag) (U : Subrepresentation cocodeAction)
    (hU : U ≤ V6Subrepresentation) :
    sectionImage F U = ⊥ ↔ U.toSubmodule ≤ V1 := by
  constructor
  · intro he
    have h := (Subrepresentation.quotientImage_eq_bot_iff F.center (inSix U)).mp he
    intro u hu
    exact h (x := ⟨u, hU hu⟩) hu
  · intro h
    apply (Subrepresentation.quotientImage_eq_bot_iff F.center (inSix U)).mpr
    intro u hu
    exact h hu

private theorem sectionImage_compl (F : CocodeFlag) (U T : Subrepresentation cocodeAction)
    (hU : U ≤ V6Subrepresentation) (hT : T ≤ V6Subrepresentation)
    (hcU : V1 ≤ U.toSubmodule) (hcT : V1 ≤ T.toSubmodule)
    (hi : U ⊓ T = F.one) (hs : U ⊔ T = V6Subrepresentation) :
    IsCompl (sectionImage F U) (sectionImage F T) := by
  apply (CommutatorProof.compl_space _ _).mpr
  have hCU : F.center.toSubmodule ≤ (inSix U).toSubmodule := Submodule.comap_mono hcU
  have hCT : F.center.toSubmodule ≤ (inSix T).toSubmodule := Submodule.comap_mono hcT
  have hinf : (inSix U).toSubmodule ⊓ (inSix T).toSubmodule = F.center.toSubmodule := by
    change U.toSubmodule.comap V6.subtype ⊓ T.toSubmodule.comap V6.subtype =
      V1.comap V6.subtype
    rw [← Submodule.comap_inf, ← Subrepresentation.toSubmodule_inf, hi, F.one_eq]
  have hsup : (inSix U).toSubmodule ⊔ (inSix T).toSubmodule = ⊤ := by
    change U.toSubmodule.comap V6.subtype ⊔ T.toSubmodule.comap V6.subtype = ⊤
    rw [← Submodule.comap_sup_of_injective V6.injective_subtype
      (by rw [Submodule.range_subtype]; exact hU)
      (by rw [Submodule.range_subtype]; exact hT),
      ← Subrepresentation.toSubmodule_sup, hs]
    exact Submodule.comap_subtype_self V6
  exact CommutatorProof.quotient_isCompl F.center.toSubmodule
    (inSix U).toSubmodule (inSix T).toSubmodule hCU hCT hinf hsup

/-- Nonsplitting of the marked middle factor forces the full cocode commutator. -/
theorem cocode_commutator_eq_six (D : CocodeActionData F E) (H : EarlierInputs D) :
    cocodeCommutator = V6 := by
  by_contra hne
  have hcomp := sectionImage_compl F (commutatorRep D) F.two
    (cocode_commutator_le_six D) F.chief26.le (center_le_commutator D H)
    (by rw [F.two_eq]; exact V1_le_V2)
    (commutator_inf_two D H hne) (commutator_sup_two D H)
  have hd := CommutatorProof.indecomp_transfer D.kernelAction F.middleAction
    D.middleEquiv D.middleEquiv_equivariant H.indecomposable
    (sectionImage F (commutatorRep D)) (sectionImage F F.two) hcomp
  rcases hd with hw | ht
  · have hw1 := (sectionImage_eq_bot F (commutatorRep D)
      (cocode_commutator_le_six D)).mp hw
    exact cocode_commutator_not_le_two D H (hw1.trans V1_le_V2)
  · have ht1 := (sectionImage_eq_bot F F.two F.chief26.le).mp ht
    have ht1' : F.two ≤ F.one := by
      change F.two.toSubmodule ≤ F.one.toSubmodule
      rwa [F.one_eq]
    exact F.chief12.lt.not_ge ht1'

/-- The canonical annihilator is precisely the code fixed space of the actual K. -/
theorem V4_eq_fixedSpace (D : CocodeActionData F E) (H : EarlierInputs D) :
    V4 = Representation.BinaryOffender.fixedSpace m22OuterCodeRepresentation K :=
  V4_eq_fixedSpace_of_commutator (cocode_commutator_eq_six D H)

end MathieuCode.M22Quintet.DualAction
