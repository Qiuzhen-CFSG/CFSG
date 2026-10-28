module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportSections
public import Theory.Representation.BinaryOffender.CubicOrbitRestriction

/-!
# FF on the two homogeneous support orbits

For a normal quasisimple support X, homogeneity makes the two-subgroup
centralizing X fix the selected seed and its orbit under the half stabilizer.
The component kernel dichotomy gives the reverse inclusion. Normality of the
half stabilizer makes the exchanged orbit have exactly the same actor kernel.

Restrict the original starred actor to the sum of these disjoint orbits.
D.2.5 gives its cubic bound after the common kernel is removed. The two
fixed codimensions add, while both image ranks equal the rank on the sum.
Thus the original actor is an FF offender on one of the two actual orbits.
Conjugation gives an explicit offender inside the original Sylow half
stabilizer, and hence an FF orbit in that half, even when the actor has
a nontrivial centralizer on X. The exact offender alternative is retained
for restriction to the support extension in the next classification step.
Its literal kernel quotient on the central orbit section is also FF: the
quotient preserves the actor image rank and can only lower fixed codimension.

The literal consumer is `SeedAlternativesMovedExhaustionSupportOrbitFF`.
FF extraction on the Irr⁺ constituent, support classification, the Suzuki
pair exclusion and final Source325 assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith D.2.5 and the D.3.5 argument used in D.3.17,
printed pp.179,195--196,203; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

omit [Finite H] in
private theorem pair_fixedCodim_eq
    (ρ : Representation (ZMod 2) H E) (Y Z : Submodule (ZMod 2) E) (A : Subgroup H)
    (hY : A ≤ subspaceStabilizer ρ Y) (hZ : A ≤ subspaceStabilizer ρ Z)
    (hd : Disjoint Y Z) :
    fixedCodim (subspaceImageRepresentation ρ (Y ⊔ Z)) (restrictedSubgroup ρ (Y ⊔ Z) A) =
      fixedCodim (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y A) +
      fixedCodim (subspaceImageRepresentation ρ Z) (restrictedSubgroup ρ Z A) := by
  have hYZ := subspaceStabilizer_sup ρ hY hZ
  have hy := fixedCodim_add_finrank (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y A)
  have hz := fixedCodim_add_finrank (subspaceImageRepresentation ρ Z) (restrictedSubgroup ρ Z A)
  have hw := fixedCodim_add_finrank (subspaceImageRepresentation ρ (Y ⊔ Z))
    (restrictedSubgroup ρ (Y ⊔ Z) A)
  rw [(restrictedFixedSpaceEquiv ρ Y A hY).finrank_eq] at hy
  rw [(restrictedFixedSpaceEquiv ρ Z A hZ).finrank_eq] at hz
  rw [(restrictedFixedSpaceEquiv ρ (Y ⊔ Z) A hYZ).finrank_eq] at hw
  have he := Y.finrank_sup_add_finrank_inf_eq Z
  rw [hd.eq_bot,finrank_bot,add_zero] at he
  have hf := (Y ⊓ fixedSpace ρ A).finrank_sup_add_finrank_inf_eq (Z ⊓ fixedSpace ρ A)
  rw [(hd.mono inf_le_left inf_le_left).eq_bot,finrank_bot,add_zero,
    ←fixedSpace_inf_disjoint_sup ρ Y Z A hY hZ hd] at hf
  omega

omit [Finite H] in
/-- The pointwise kernel on a homogeneous orbit is the literal support centralizer. -/
theorem homogeneous_support_orbit_kernel
    (ρ : Representation (ZMod 2) H E) (X P A : Subgroup H)
    [X.Normal] [IsQuasisimple X] (hP : IsPGroup 2 P) (hAP : A ≤ P)
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlusWith ρ X P R) :
    subspaceKernel ρ (orbitSpan ρ P R) A = A ⊓ centralizer (X : Set H) := by
  apply le_antisymm
  · intro a ha
    exact ⟨ha.1,subspaceKernel_le_component_centralizer ρ X R hR.invariant
      (hR.isIrrPlus.not_le_fixedSpace ρ) A ⟨ha.1,fun v hv =>
        ha.2 v (le_orbitSpan ρ P R hv)⟩⟩
  · rintro a ⟨ha,hc⟩
    exact ⟨ha,fun v hv => orbitSpan_fixed_by_two_centralizer ρ hP hR hv ⟨a,hAP ha,hc⟩⟩

/-- Equal kernels on an invariant disjoint pair give an actual offender after
restriction of the original starred actor. No component-faithfulness premise is used. -/
theorem common_kernel_starred_pair_offender
    (ρ : Representation (ZMod 2) H E) (Y : Submodule (ZMod 2) E) (t : H)
    (A : Subgroup H) (hA : A ∈ CFSG.Quasithin.ChapterD.QhatStar ρ)
    (hY : A ≤ subspaceStabilizer ρ Y) (hZ : A ≤ subspaceStabilizer ρ (Y.map (ρ t)))
    (hd : Disjoint Y (Y.map (ρ t)))
    (hn : ¬ Y ≤ fixedSpace ρ A)
    (hk : subspaceKernel ρ Y A = subspaceKernel ρ (Y.map (ρ t)) A) :
    IsOffender (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y A) ∨
      IsOffender (subspaceImageRepresentation ρ (Y.map (ρ t)))
        (restrictedSubgroup ρ (Y.map (ρ t)) A) := by
  let Z := Y.map (ρ t)
  let W := Y ⊔ Z
  have hw : A ≤ subspaceStabilizer ρ W := subspaceStabilizer_sup ρ hY hZ
  have hwn : ¬ W ≤ fixedSpace ρ A := fun h => hn (le_sup_left.trans h)
  have hr := CFSG.Quasithin.ChapterD.QhatStar.mem_RPlus ρ hA
  have hb := CFSG.Quasithin.ChapterD.RPlusBound.restricted ρ
    (show A ∈ CFSG.Quasithin.ChapterD.RPlusBound ρ 2 from
      ⟨⟨hA.1.2.1,hA.1.2.2.2.le.trans hA.1.1⟩,hr⟩) W hw hwn
  have hkw : subspaceKernel ρ W A = subspaceKernel ρ Y A := by
    apply le_antisymm
    · exact fun a ha => ⟨ha.1,fun v hv => ha.2 v ((show Y ≤ W from le_sup_left) hv)⟩
    · intro a ha
      refine ⟨ha.1,?_⟩
      intro v hv
      obtain ⟨y,hy,z,hz,rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add,ha.2 y hy,(hk.le ha).2 z hz]
  let := hA.1.2.1.2
  have hp := IsElementaryAbelian.isPGroup 2 A
  have rY := rank_subspaceKernel_add_image ρ Y A hY hp
  have rZ := rank_subspaceKernel_add_image ρ Z A hZ hp
  have rW := rank_subspaceKernel_add_image ρ W A hw hp
  rw [hkw] at rW
  rw [←hk] at rZ
  have hrank : rank (restrictedSubgroup ρ Y A) = rank (restrictedSubgroup ρ Z A) := by omega
  have hbudget := (actionRatio_le_nat_iff (subspaceImageRepresentation ρ W) hb.1 2).mp hb.2
  rw [pair_fixedCodim_eq ρ Y Z A hY hZ hd] at hbudget
  have helY := hA.1.2.1.restrictedSubgroup ρ Y hY hn
  have hnZ : ¬ Z ≤ fixedSpace ρ A := by
    intro hz
    apply hn
    intro v hv a
    have ha : a.val ∈ subspaceKernel ρ Z A := ⟨a.property,fun w hw => hz hw a⟩
    exact (hk.ge ha).2 v hv
  have helZ := hA.1.2.1.restrictedSubgroup ρ Z hZ hnZ
  by_cases hy : fixedCodim (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y A) ≤
      rank (restrictedSubgroup ρ Y A)
  · exact Or.inl ⟨helY,hy⟩
  · right
    refine ⟨helZ,?_⟩
    change fixedCodim (subspaceImageRepresentation ρ Z) (restrictedSubgroup ρ Z A) ≤
      rank (restrictedSubgroup ρ Z A)
    omega

/-- Conjugation transports the offender carried by the original subgroup,
not only the existential FF property of the full stabilizer image. -/
theorem conjugate_restricted_offender
    (ρ : Representation (ZMod 2) H E) (Y : Submodule (ZMod 2) E)
    (A : Subgroup H) (hA : IsElementaryAbelian 2 A)
    (hAY : A ≤ subspaceStabilizer ρ Y) (t : H)
    (hoff : IsOffender (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y A)) :
    IsOffender (subspaceImageRepresentation ρ (Y.map (ρ t)))
      (restrictedSubgroup ρ (Y.map (ρ t)) (A.map (MulAut.conj t).toMonoidHom)) := by
  let := hA
  let D := A.map (MulAut.conj t).toMonoidHom
  let Z := Y.map (ρ t)
  let c : E ≃ₗ[ZMod 2] E :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) E (ρ.asGroupHom t)
  have hc (a : H) (v : E) : c (ρ a v) = ρ (MulAut.conj t a) (c v) := by
    change ρ t (ρ a v) = ρ (t*a*t⁻¹) (ρ t v)
    simp only [←Module.End.mul_apply,←map_mul,mul_assoc,inv_mul_cancel,mul_one]
  have hDZ : D ≤ subspaceStabilizer ρ Z := by
    rintro _ ⟨a,ha,rfl⟩
    exact (mem_subspaceStabilizer_equivariant ρ ρ (MulAut.conj t) c hc Y a).mp (hAY ha)
  have hker : (subspaceKernel ρ Y A).map (MulAut.conj t).toMonoidHom =
      subspaceKernel ρ Z D := by
    apply le_antisymm
    · rintro _ ⟨a,ha,rfl⟩
      refine ⟨mem_map_of_mem _ ha.1,?_⟩
      rintro _ ⟨v,hv,rfl⟩
      exact (hc a v).symm.trans (congrArg c (ha.2 v hv))
    · rintro x ⟨⟨a,ha,rfl⟩,hx⟩
      refine ⟨a,⟨ha,?_⟩,rfl⟩
      intro v hv
      apply c.injective
      rw [hc]
      exact hx (c v) ⟨v,hv,rfl⟩
  have rA := rank_subspaceKernel_add_image ρ Y A hAY (IsElementaryAbelian.isPGroup 2 A)
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.map _
  have rD := rank_subspaceKernel_add_image ρ Z D hDZ (IsElementaryAbelian.isPGroup 2 D)
  rw [←hker,rank_map_injective _ (MulAut.conj t).injective] at rD
  have rAD : rank D = rank A := rank_map_injective _ (MulAut.conj t).injective A
  have hr : rank (restrictedSubgroup ρ Z D) = rank (restrictedSubgroup ρ Y A) := by omega
  have hfix : (Y ⊓ fixedSpace ρ A).map (ρ t) = Z ⊓ fixedSpace ρ D := by
    rw [Submodule.map_inf _ (ρ.apply_bijective t).injective]
    exact congrArg (fun Q => Z ⊓ Q) (fixedSpace_map_equivariant ρ ρ
      (MulAut.conj t).toMonoidHom c hc A)
  have hdim := finrank_map_action ρ Y t
  have hdimfix := finrank_map_action ρ (Y ⊓ fixedSpace ρ A) t
  rw [hfix] at hdimfix
  have hy := fixedCodim_add_finrank (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y A)
  have hz := fixedCodim_add_finrank (subspaceImageRepresentation ρ Z) (restrictedSubgroup ρ Z D)
  rw [(restrictedFixedSpaceEquiv ρ Y A hAY).finrank_eq] at hy
  rw [(restrictedFixedSpaceEquiv ρ Z D hDZ).finrank_eq] at hz
  have hcod : fixedCodim (subspaceImageRepresentation ρ Z) (restrictedSubgroup ρ Z D) =
      fixedCodim (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y A) := by
    change Module.finrank (ZMod 2) Z = Module.finrank (ZMod 2) Y at hdim
    omega
  have hn : restrictedSubgroup ρ Z D ≠ ⊥ := by
    intro he
    have hp := hoff.1.rank_pos
    rw [←hr,he,Representation.BinaryOffender.rank_bot] at hp
    omega
  change IsOffender (subspaceImageRepresentation ρ Z) (restrictedSubgroup ρ Z D)
  let : IsElementaryAbelian 2 (D.subgroupOf (subspaceStabilizer ρ Z)) :=
    IsElementaryAbelian.subgroupOf hDZ
  refine ⟨⟨hn,IsElementaryAbelian.map _⟩,?_⟩
  rw [hcod,hr]
  exact hoff.2


/-- The two homogeneous half-orbits have the same centralizer kernel and
one is FF, hence so is its actual conjugate. -/
theorem homogeneous_support_pair_orbit_ff
    (ρ : Representation (ZMod 2) H E) (X S P A B : Subgroup H)
    [X.Normal] [IsQuasisimple X]
    (hS : IsPGroup 2 S) (hPS : P ≤ S) (hSP : S ≤ normalizer (P : Set H))
    (hAP : A ≤ P) (hBA : B ≤ A) (hXB : ⁅X,B⁆ = X)
    (hA : A ∈ CFSG.Quasithin.ChapterD.QhatStar ρ)
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlusWith ρ X P R)
    (t : H) (ht : t ∈ S)
    (hd : Disjoint (orbitSpan ρ P R) ((orbitSpan ρ P R).map (ρ t))) :
    subspaceKernel ρ (orbitSpan ρ P R) A = A ⊓ centralizer (X : Set H) ∧
    subspaceKernel ρ ((orbitSpan ρ P R).map (ρ t)) A = A ⊓ centralizer (X : Set H) ∧
    (IsOffender (subspaceImageRepresentation ρ (orbitSpan ρ P R))
        (restrictedSubgroup ρ (orbitSpan ρ P R) A) ∨
      IsOffender (subspaceImageRepresentation ρ ((orbitSpan ρ P R).map (ρ t)))
        (restrictedSubgroup ρ ((orbitSpan ρ P R).map (ρ t)) A)) ∧
    (∃ D : Subgroup H, D ≤ P ∧ IsElementaryAbelian 2 D ∧
      IsOffender (subspaceImageRepresentation ρ (orbitSpan ρ P R))
        (restrictedSubgroup ρ (orbitSpan ρ P R) D)) ∧
    IsFFModule (subspaceImageRepresentation ρ (orbitSpan ρ P R)) := by
  let Y := orbitSpan ρ P R
  have hY : A ≤ subspaceStabilizer ρ Y := hAP.trans (orbitSpan_invariant ρ P R)
  have hZ : A ≤ subspaceStabilizer ρ (Y.map (ρ t)) := by
    apply le_subspaceStabilizer
    rintro a ha _ ⟨v,hv,rfl⟩
    have htP : t⁻¹*a*t ∈ P := by
      simpa only [inv_inv] using
        (mem_normalizer_iff.mp (hSP (S.inv_mem ht)) a).mp (hAP ha)
    refine ⟨ρ (t⁻¹*a*t) v,((orbitSpan_invariant ρ P R htP) v).2 hv,?_⟩
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  have hn : ¬ Y ≤ fixedSpace ρ A := by
    intro hh
    apply hR.isIrrPlus.not_le_fixedSpace ρ
    rw [←hXB]
    exact le_fixedSpace_commutator_of_invariant ρ hR.invariant
      (((le_orbitSpan ρ P R).trans hh).trans (fixedSpace_antitone ρ hBA))
  have hkY := homogeneous_support_orbit_kernel ρ X P A (hS.to_le hPS) hAP R hR
  have hfR : R ≤ fixedSpace ρ (P ⊓ centralizer (X : Set H)) :=
    (le_orbitSpan ρ P R).trans (orbitSpan_fixed_by_two_centralizer ρ (hS.to_le hPS) hR)
  have hnC : S ≤ normalizer (centralizer (X : Set H) : Set H) := by
    exact (show S ≤ normalizer (X : Set H) by rw [normalizer_eq_top]; exact le_top).trans
      (normalizer_le_normalizer_centralizer X)
  have hfS := orbitSpan_le_fixedSpace_of_normalizes ρ
    ((le_inf hSP hnC).trans inf_normalizer_le_normalizer_inf) hfR
  have hZS : Y.map (ρ t) ≤ orbitSpan ρ S R := by
    rw [show Y = orbitSpan ρ P R from rfl,orbitSpan,Submodule.map_iSup]
    apply iSup_le
    intro p
    rw [←subspace_map_mul]
    exact le_iSup (fun s : S => R.map (ρ s.val)) ⟨t*p.val,S.mul_mem ht (hPS p.property)⟩
  have hkZ : subspaceKernel ρ (Y.map (ρ t)) A = A ⊓ centralizer (X : Set H) := by
    apply le_antisymm
    · intro a ha
      have hRt := hR.isIrrPlus.map_normalizer ρ (show t ∈ normalizer (X : Set H) by
        rw [normalizer_eq_top]; trivial)
      exact ⟨ha.1,subspaceKernel_le_component_centralizer ρ X (R.map (ρ t)) hRt.choose
        (hRt.not_le_fixedSpace ρ) A ⟨ha.1,fun v hv => ha.2 v
          ((Submodule.map_mono (le_orbitSpan ρ P R)) hv)⟩⟩
    · rintro a ⟨ha,hc⟩
      exact ⟨ha,fun v hv => hfS (hZS hv) ⟨a,hAP ha,hc⟩⟩
  have hoff := common_kernel_starred_pair_offender ρ Y t A hA hY hZ hd hn (hkY.trans hkZ.symm)
  have hlocal : ∃ D : Subgroup H, D ≤ P ∧ IsElementaryAbelian 2 D ∧
      IsOffender (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y D) := by
    rcases hoff with h | h
    · exact ⟨A,hAP,hA.1.2.1.2,h⟩
    · have ht' := conjugate_restricted_offender ρ (Y.map (ρ t)) A hA.1.2.1.2 hZ t⁻¹ h
      have hback : (Y.map (ρ t)).map (ρ t⁻¹) = Y := by
        rw [←subspace_map_mul,inv_mul_cancel,map_one,Module.End.one_eq_id,Submodule.map_id]
      rw [hback] at ht'
      let := hA.1.2.1.2
      refine ⟨A.map (MulAut.conj t⁻¹).toMonoidHom,?_,IsElementaryAbelian.map _,ht'⟩
      rintro _ ⟨a,ha,rfl⟩
      exact (mem_normalizer_iff.mp (hSP (S.inv_mem ht)) a).mp (hAP ha)
  refine ⟨hkY,hkZ,hoff,hlocal,?_⟩
  obtain ⟨D,_,_,hD⟩ := hlocal
  exact ⟨_,hD⟩

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
/-- The stabilizer of one of two permuted subspaces is normal in every actor. -/
theorem permuted_pair_normalizes_half_stabilizer
    (ρ : Representation (ZMod 2) H E) (I : Submodule (ZMod 2) E) (t : H)
    (hne : I ≠ I.map (ρ t))
    (hp : ∀ g : H, I.map (ρ g) = I ∨ I.map (ρ g) = I.map (ρ t))
    (S : Subgroup H) : S ≤ normalizer ((S ⊓ subspaceStabilizer ρ I : Subgroup H) : Set H) := by
  have hconj (s : H) (hs : s ∈ S) (p : H)
      (hp' : p ∈ S ⊓ subspaceStabilizer ρ I) :
      s*p*s⁻¹ ∈ S ⊓ subspaceStabilizer ρ I := by
    refine ⟨S.mul_mem (S.mul_mem hs hp'.1) (S.inv_mem hs),?_⟩
    apply (subspace_map_eq_iff ρ I _).mp
    have he := (subspace_map_eq_iff ρ I p).mpr hp'.2
    have he' := pair_second_stabilized ρ I t p hne hp he
    rw [subspace_map_mul,subspace_map_mul]
    have hh : (I.map (ρ s⁻¹)).map (ρ p) = I.map (ρ s⁻¹) := by
      rcases hp s⁻¹ with h | h
      · rw [h]; exact he
      · rw [h]; exact he'
    rw [hh,←subspace_map_mul,mul_inv_cancel,map_one,Module.End.one_eq_id,Submodule.map_id]
  intro s hs
  apply mem_normalizer_iff.mpr
  intro p
  constructor
  · exact hconj s hs p
  · intro h
    have hh := hconj s⁻¹ (S.inv_mem hs) (s*p*s⁻¹) h
    have he : s⁻¹ * (s*p*s⁻¹) * (s⁻¹)⁻¹ = p := by group
    rwa [he] at hh
/-- The actual offender on the homogeneous orbit retains its rank on the
central quotient. Thus that literal faithful quotient is also FF. -/
theorem homogeneous_support_orbit_section_offender
    (ρ : Representation (ZMod 2) H E) (X P B : Subgroup H)
    [IsQuasisimple X] (hP : IsPGroup 2 P) (hBP : B ≤ P)
    (hB : IsElementaryAbelian 2 B)
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlusWith ρ X P R)
    (hoff : IsOffender (subspaceImageRepresentation ρ (orbitSpan ρ P R))
      (restrictedSubgroup ρ (orbitSpan ρ P R) B)) :
    IsOffender (KernelQuotient.action (orbitSectionRepresentation ρ hR))
      ((B.subgroupOf (X ⊔ P)).map (KernelQuotient.projection (orbitSectionRepresentation ρ hR))) := by
  let := hB
  let J := X ⊔ P
  let Y := orbitSpan ρ P R
  let σ := orbitSectionRepresentation ρ hR
  let q := KernelQuotient.projection σ
  let B₀ := B.subgroupOf J
  let D := B₀.map q
  have hBJ : B ≤ J := hBP.trans le_sup_right
  have hBY : B ≤ subspaceStabilizer ρ Y := hBP.trans (orbitSpan_invariant ρ P R)
  have hr : rank D = rank (restrictedSubgroup ρ Y B) := orbitSection_image_rank ρ hP hR hBP
  let : IsElementaryAbelian 2 B₀ := IsElementaryAbelian.subgroupOf hBJ
  have hD : IsElementaryTwo D := by
    refine ⟨?_,IsElementaryAbelian.map q⟩
    intro hz
    have hp := hoff.1.rank_pos
    change 0 < rank (restrictedSubgroup ρ Y B) at hp
    rw [←hr,hz,Representation.BinaryOffender.rank_bot] at hp
    omega
  let τ := ρ.comp J.subtype
  let W := invariantSubspace ρ J Y (orbitSection_stable ρ hR.normalizes hR.isIrrPlus)
  let N := centralSectionFixedSubspace ρ X J Y
    (orbitSection_stable ρ hR.normalizes hR.isIrrPlus)
    (sup_le X.le_normalizer hR.normalizes)
  have hfixed : fixedSpace W.toRepresentation B₀ =
      fixedSpace (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y B) := by
    rw [fixedSpace_restrictedSubgroup ρ Y B hBY]
    ext w
    constructor
    · intro hw b
      exact congrArg Subtype.val (hw ⟨⟨b,hBJ b.property⟩,b.property⟩)
    · intro hw b
      exact Subtype.ext (hw ⟨b,b.property⟩)
  have hcost : fixedCodim W.toRepresentation B₀ =
      fixedCodim (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y B) :=
    congrArg (fun Q => Module.finrank (ZMod 2) (Y ⧸ Q)) hfixed
  have hd : fixedCodim (KernelQuotient.action σ) D ≤
      fixedCodim (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y B) := by
    have he := fixedCodim_map_equivariant σ (KernelQuotient.action σ) q
      (LinearEquiv.refl _ _) (fun _ _ => rfl) B₀
    rw [←he,←hcost]
    exact (Nat.le_add_right _ _).trans
      (fixedCodim_quotient_add_subrepresentation_le W.toRepresentation N B₀)
  exact ⟨hD,hr.symm ▸ hd.trans hoff.2⟩


end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
