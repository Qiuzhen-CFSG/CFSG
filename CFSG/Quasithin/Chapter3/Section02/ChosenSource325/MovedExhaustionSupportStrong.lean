module
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSupportNatural
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedSylowSieveStability
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.SpecificGroups.SL3.PerfectCentralCover
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.NumberTheory.BinaryTorusParity
public import Theory.Representation.SL3OddNaturalNormalizer

/-!
# Strong offending and the natural SL₃ support section

The selected support seed is stable under the Sylow half stabilizer. The
sum of it and its exchanged copy cannot supplement the starred actor's fixed
space: full support movement would put the commuting perfect component's
strictly larger seed orbit inside that sum and inside the original half,
forcing it back into the seed. D.2.7 therefore gives a strict two-rank budget.
Both seed actions have the same literal centralizer kernel, so one carries
a strong offender. Conjugation and the original central quotient preserve
its rank and give a strong offender on the actual support section.

Strong replacement passes to the offender-generated subgroup. The complete
rank-one B.5.1 classification then excludes its ratio-one SL₂, alternating-five
and repeated-natural rows. The remaining section is marked odd-degree
natural SL₃. The inherited trivial two-core makes the original central
covering map injective. Odd field degree puts the half-stabilizer image
inside this natural SL₃ image; the marked projection lifts its action to
inner conjugation on the original support. The corresponding application is `SeedAlternativesMovedExhaustionSupportStrong`.

This proves the central-section model exclusion in D.3.17. Removing the
original seed's fixed vectors, full component movement, multiplicity, Suzuki-pair exclusion, U = W and Source325 assembly
remain with qt-baumann-fsu.
Source: Aschbacher--Smith D.2.7--8 and D.3.17, printed pp.179--180,203;
B.5.1, pp.99--103; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
open ChapterB.QuasisimpleSource
open ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
variable {H E : Type*} [Group H] [Finite H] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

omit [Finite H] in
/-- The exchanged support seeds cannot supplement the original actor's fixed space. -/
theorem support_pair_not_supplement
    (ρ : Representation (ZMod 2) H E) (X K A B : Subgroup H) [Group.IsPerfect K]
    (hK : fixedSpace ρ K = ⊥) (hc : K ≤ centralizer (X : Set H))
    (hBA : B ≤ A) (hXB : ⁅X,B⁆ = X)
    (I R Q : Submodule (ZMod 2) E)
    (hKI : K ≤ subspaceStabilizer ρ I) (hRI : R ≤ I) (hd : Disjoint I Q)
    (hR : IsIrrPlus ρ X R) (hXQ : X ≤ subspaceStabilizer ρ Q)
    (hAR : A ≤ subspaceStabilizer ρ R) (hAQ : A ≤ subspaceStabilizer ρ Q) :
    R ⊔ Q ⊔ fixedSpace ρ A ≠ ⊤ := by
  intro hs
  let W := R ⊔ Q
  have hXW := subspaceStabilizer_sup ρ hR.choose hXQ
  have hAW := subspaceStabilizer_sup ρ hAR hAQ
  have hm : subspaceCommutator ρ ⊤ X ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,hx,v,_,rfl⟩
    obtain ⟨w,hw,c,hc',rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ W ⊔ fixedSpace ρ A by rw [hs]; trivial)
    have hf := differences_mem_of_invariant_mod_fixed ρ hXW (hBA.trans hAW)
      (show X ≤ subspaceStabilizer ρ (fixedSpace ρ A ⊔ W) by
        rw [sup_comm,hs]; exact le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      (fixedSpace_antitone ρ hBA) hXB c hc' x hx
    have he : ρ x (w+c) - (w+c) = (ρ x w-w)+(ρ x c-c) := by rw [map_add]; abel
    rw [he]
    exact W.add_mem (W.sub_mem ((hXW hx w).2 hw) hw) hf
  obtain ⟨hlt,hOI,_,hmove,_⟩ := support_seed_commuting_orbit ρ X K hK hc I R hKI hRI hR
  have hOW : orbitSpan ρ K R ≤ W := by
    rw [←hmove]
    exact (subspaceCommutator_mono_left ρ le_top X).trans hm
  have hOR : orbitSpan ρ K R ≤ R := by
    intro v hv
    obtain ⟨r,hr,q,hq,he⟩ := Submodule.mem_sup.mp (hOW hv)
    have hqI : q ∈ I := by
      have hh := I.sub_mem (hOI hv) (hRI hr)
      rw [←he] at hh
      simpa using hh
    have hz := Submodule.disjoint_def.mp hd q hqI hq
    rw [hz,add_zero] at he
    exact he ▸ hr
  exact (not_le_of_gt hlt) hOR

/-- Equal kernels and failure of a fixed-space supplement make the original
starred actor a strong offender on one of the two disjoint seeds. -/
theorem common_kernel_starred_pair_strong_offender
    (ρ : Representation (ZMod 2) H E) (Y : Submodule (ZMod 2) E) (t : H)
    (A : Subgroup H) (hA : A ∈ CFSG.Quasithin.ChapterD.QhatStar ρ)
    (hY : A ≤ subspaceStabilizer ρ Y) (hZ : A ≤ subspaceStabilizer ρ (Y.map (ρ t)))
    (hd : Disjoint Y (Y.map (ρ t)))
    (hn : ¬ Y ≤ fixedSpace ρ A)
    (hk : subspaceKernel ρ Y A = subspaceKernel ρ (Y.map (ρ t)) A)
    (hs : Y ⊔ Y.map (ρ t) ⊔ fixedSpace ρ A ≠ ⊤) :
    IsStrongOffender (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y A) ∨
      IsStrongOffender (subspaceImageRepresentation ρ (Y.map (ρ t)))
        (restrictedSubgroup ρ (Y.map (ρ t)) A) := by
  let Z := Y.map (ρ t)
  let W := Y ⊔ Z
  have hw : A ≤ subspaceStabilizer ρ W := subspaceStabilizer_sup ρ hY hZ
  have hwn : ¬ W ≤ fixedSpace ρ A := fun h => hn (le_sup_left.trans h)
  have hb := (CFSG.Quasithin.ChapterD.QhatStar.restriction_alternatives
    ρ hA W hw hwn).2.2.resolve_right (fun h => hs h.2)
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
  have hbudget : fixedCodim (subspaceImageRepresentation ρ W)
      (restrictedSubgroup ρ W A) < 2 * rank (restrictedSubgroup ρ W A) := by
    have hlt := hb.2.trans_le hA.1.1
    have hp := hb.1.1.rank_pos
    change (fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) : ℝ≥0∞) /
      (rank (restrictedSubgroup ρ W A) : ℝ≥0∞) < 2 at hlt
    have hh := (ENNReal.div_lt_iff (Or.inl (by exact_mod_cast (Nat.ne_of_gt hp))) (Or.inl (by simp))).mp hlt
    exact_mod_cast hh
  rw [common_actor_fixedCodim_sup ρ Y Z A hY hZ hd] at hbudget
  have helY := hA.1.2.1.restrictedSubgroup ρ Y hY hn
  have hnZ : ¬ Z ≤ fixedSpace ρ A := by
    intro hz
    apply hn
    intro v hv a
    have ha : a.val ∈ subspaceKernel ρ Z A := ⟨a.property,fun w hw => hz hw a⟩
    exact (hk.ge ha).2 v hv
  have helZ := hA.1.2.1.restrictedSubgroup ρ Z hZ hnZ
  by_cases hy : fixedCodim (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y A) <
      rank (restrictedSubgroup ρ Y A)
  · exact Or.inl ⟨helY,hy⟩
  · right
    refine ⟨helZ,?_⟩
    change fixedCodim (subspaceImageRepresentation ρ Z) (restrictedSubgroup ρ Z A) <
      rank (restrictedSubgroup ρ Z A)
    omega

/-- Conjugation transports the offender carried by the original subgroup,
not only the existential FF property of the full stabilizer image. -/
theorem conjugate_restricted_strong_offender
    (ρ : Representation (ZMod 2) H E) (Y : Submodule (ZMod 2) E)
    (A : Subgroup H) (hA : IsElementaryAbelian 2 A)
    (hAY : A ≤ subspaceStabilizer ρ Y) (t : H)
    (hoff : IsStrongOffender (subspaceImageRepresentation ρ Y) (restrictedSubgroup ρ Y A)) :
    IsStrongOffender (subspaceImageRepresentation ρ (Y.map (ρ t)))
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
  change IsStrongOffender (subspaceImageRepresentation ρ Z) (restrictedSubgroup ρ Z D)
  let : IsElementaryAbelian 2 (D.subgroupOf (subspaceStabilizer ρ Z)) :=
    IsElementaryAbelian.subgroupOf hDZ
  refine ⟨⟨hn,IsElementaryAbelian.map _⟩,?_⟩
  rw [hcod,hr]
  exact hoff.2


/-- The strong offender retains its rank on the literal central orbit
quotient, whose fixed codimension can only decrease. -/
theorem homogeneous_support_orbit_section_strong_offender
    (ρ : Representation (ZMod 2) H E) (X P B : Subgroup H)
    [IsQuasisimple X] (hP : IsPGroup 2 P) (hBP : B ≤ P)
    (hB : IsElementaryAbelian 2 B)
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlusWith ρ X P R)
    (hoff : IsStrongOffender (subspaceImageRepresentation ρ (orbitSpan ρ P R))
      (restrictedSubgroup ρ (orbitSpan ρ P R) B)) :
    IsStrongOffender (KernelQuotient.action (orbitSectionRepresentation ρ hR))
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
  exact ⟨hD,hr.symm ▸ hd.trans_lt hoff.2⟩

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
/-- An explicit strong offender in the original half stabilizer, on both
its selected seed and the literal central orbit section. -/
@[expose] def SupportStrongSection
    (ρ : Representation (ZMod 2) H E) {X P : Subgroup H}
    {R : Submodule (ZMod 2) E} (hR : IsIrrPlusWith ρ X P R) : Prop :=
  ∃ D : Subgroup H, D ≤ P ∧ IsElementaryAbelian 2 D ∧
    IsStrongOffender (subspaceImageRepresentation ρ R) (restrictedSubgroup ρ R D) ∧
    IsStrongOffender (KernelQuotient.action (orbitSectionRepresentation ρ hR))
      ((D.subgroupOf (X ⊔ P)).map (KernelQuotient.projection (orbitSectionRepresentation ρ hR)))

/-- The original starred actor yields a strong offender on a homogeneous support
seed (or its actual conjugate), and hence on its literal central quotient. -/
theorem homogeneous_support_section_strong
    (ρ : Representation (ZMod 2) H E) (X K S P A B : Subgroup H)
    [X.Normal] [IsQuasisimple X] [Group.IsPerfect K]
    (hK : fixedSpace ρ K = ⊥) (hc : K ≤ centralizer (X : Set H))
    (hS : IsPGroup 2 S) (hPS : P ≤ S) (hSP : S ≤ normalizer (P : Set H))
    (hAP : A ≤ P) (hBA : B ≤ A) (hXB : ⁅X,B⁆ = X)
    (hA : A ∈ CFSG.Quasithin.ChapterD.QhatStar ρ)
    (I R : Submodule (ZMod 2) E) (hKI : K ≤ subspaceStabilizer ρ I)
    (hRI : R ≤ I) (hR : IsIrrPlusWith ρ X P R) (he : orbitSpan ρ P R = R)
    (t : H) (ht : t ∈ S) (hd : Disjoint I (I.map (ρ t))) :
    SupportStrongSection ρ hR := by
  have hAR : A ≤ subspaceStabilizer ρ R := by
    rw [←he]
    exact hAP.trans (orbitSpan_invariant ρ P R)
  have hAQ : A ≤ subspaceStabilizer ρ (R.map (ρ t)) := by
    apply le_subspaceStabilizer
    rintro a ha _ ⟨v,hv,rfl⟩
    have htP : t⁻¹*a*t ∈ P := by
      simpa only [inv_inv] using
        (mem_normalizer_iff.mp (hSP (S.inv_mem ht)) a).mp (hAP ha)
    have hPR : P ≤ subspaceStabilizer ρ R := by
      rw [←he]; exact orbitSpan_invariant ρ P R
    refine ⟨ρ (t⁻¹*a*t) v,((hPR htP) v).2 hv,?_⟩
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  have hRt := hR.isIrrPlus.map_normalizer ρ
    (show t ∈ normalizer (X : Set H) by rw [normalizer_eq_top]; trivial)
  have hnot := support_pair_not_supplement ρ X K A B hK hc hBA hXB
    I R (R.map (ρ t)) hKI hRI (hd.mono_right (Submodule.map_mono hRI))
    hR.isIrrPlus hRt.choose hAR hAQ
  have hdR := hd.mono hRI (Submodule.map_mono hRI)
  have hpair := homogeneous_support_pair_orbit_ff ρ X S P A B hS hPS hSP hAP hBA hXB hA
    R hR t ht (by simpa only [he] using hdR)
  have hk : subspaceKernel ρ R A = subspaceKernel ρ (R.map (ρ t)) A := by
    simpa only [he] using hpair.1.trans hpair.2.1.symm
  have hn : ¬ R ≤ fixedSpace ρ A := by
    intro hh
    apply hR.isIrrPlus.not_le_fixedSpace ρ
    rw [←hXB]
    exact le_fixedSpace_commutator_of_invariant ρ hR.invariant
      (hh.trans (fixedSpace_antitone ρ hBA))
  have hlocal : ∃ D : Subgroup H, D ≤ P ∧ IsElementaryAbelian 2 D ∧
      IsStrongOffender (subspaceImageRepresentation ρ R) (restrictedSubgroup ρ R D) := by
    rcases common_kernel_starred_pair_strong_offender ρ R t A hA hAR hAQ hdR hn hk hnot with h | h
    · exact ⟨A,hAP,hA.1.2.1.2,h⟩
    · have hh := conjugate_restricted_strong_offender ρ (R.map (ρ t)) A hA.1.2.1.2 hAQ t⁻¹ h
      have hback : (R.map (ρ t)).map (ρ t⁻¹) = R := by
        rw [←subspace_map_mul,inv_mul_cancel,map_one,Module.End.one_eq_id,Submodule.map_id]
      rw [hback] at hh
      let := hA.1.2.1.2
      refine ⟨A.map (MulAut.conj t⁻¹).toMonoidHom,?_,IsElementaryAbelian.map _,hh⟩
      rintro _ ⟨a,ha,rfl⟩
      exact (mem_normalizer_iff.mp (hSP (S.inv_mem ht)) a).mp (hAP ha)
  obtain ⟨D,hDP,hD,hoff⟩ := hlocal
  refine ⟨D,hDP,hD,hoff,?_⟩
  exact homogeneous_support_orbit_section_strong_offender ρ X P D (hS.to_le hPS) hDP hD R hR
    (by rw [he]; exact hoff)


omit [Finite H] [FiniteDimensional (ZMod 2) E] in
private def strongFullMovedSpaceEquiv
    (ρ : Representation (ZMod 2) H E) (X : Subgroup H) (s : MovedSection ρ X)
    (hm : moved ρ X = ⊤) :
    ActionEquiv (s.space.toRepresentation.comp X.subtype) (ρ.comp X.subtype) :=
  ⟨MulEquiv.refl _, LinearEquiv.ofBijective s.space.toSubmodule.subtype
    ⟨Subtype.val_injective,fun v => ⟨⟨v,s.space_eq.symm ▸ hm.symm ▸ Submodule.mem_top⟩,rfl⟩⟩,
    fun _ _ => rfl⟩

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
private def strongFullMovedSectionEquiv
    (ρ : Representation (ZMod 2) H E) (X : Subgroup H) (s : MovedSection ρ X)
    (hm : moved ρ X = ⊤) (hz : fixedSpace ρ X = ⊥) :
    ActionEquiv (s.action.comp X.subtype) (ρ.comp X.subtype) := by
  let e := strongFullMovedSpaceEquiv ρ X s hm
  have hf : Representation.invariants (s.space.toRepresentation.comp X.subtype) = ⊥ :=
    ExtensionConsequences.invariants_of_equiv e hz
  let q := ExtensionConsequences.movedQuotientEquiv s hf
  exact ⟨q.groupEquiv.trans e.groupEquiv,q.linearEquiv.trans e.linearEquiv,
    fun g v => (congrArg e.linearEquiv (q.intertwines g v)).trans
      (e.intertwines (q.groupEquiv g) (q.linearEquiv v))⟩


omit [Finite H] in
private theorem strong_on_full_moved_section
    (ρ : Representation (ZMod 2) H E) (X : Subgroup H) (s : MovedSection ρ X)
    (hm : moved ρ X = ⊤) (hs : IsStrongFFModule ρ) : IsStrongFFModule s.action := by
  obtain ⟨A,hA,hlt⟩ := hs
  let e : s.space.toSubmodule ≃ₗ[ZMod 2] E :=
    (strongFullMovedSpaceEquiv ρ X s hm).linearEquiv
  have he : fixedCodim s.space.toRepresentation A = fixedCodim ρ A := by
    have hh := fixedCodim_map_equivariant s.space.toRepresentation ρ
      (MonoidHom.id H) e (fun _ _ => rfl) A
    simpa only [Subgroup.map_id] using hh
  have hb := fixedCodim_quotient_add_subrepresentation_le s.space.toRepresentation s.central A
  refine ⟨A,hA,?_⟩
  change fixedCodim s.action A + _ ≤ _ at hb
  rw [he] at hb
  omega

private theorem rankOne_strong_linearThree
    (ρ : Representation (ZMod 2) H E) (X : Subgroup H)
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ X)
    (hr : primeRank 3 X = 1) (hm : moved ρ X = ⊤) (hz : fixedSpace ρ X = ⊥)
    (hs : IsStrongFFModule ρ) :
    ∃ F : BinaryField, Odd F.degree ∧ IsLinearNatural (ρ.comp X.subtype) F 3 := by
  let s := c.sectionData
  have hsec := strong_on_full_moved_section ρ X s hm hs
  have hq := (isStrongFFModule_iff_quadraticRatio_lt_one s.action).mp hsec
  have hqρ := (isStrongFFModule_iff_quadraticRatio_lt_one ρ).mp hs
  cases rankOneAction_of_source ρ hr c.clause_one with
  | irreducible _ _ _ h _ =>
    cases h with
    | linearTwo _ _ _ _ hratio =>
      rw [hratio] at hq
      exact (lt_irrefl _ hq).elim
    | symmetricFive _ _ hratio =>
      rw [hratio] at hq
      exact (lt_irrefl _ hq).elim
    | linearThree F ho _ a _ =>
      let e := ExtensionConsequences.actionSymm (strongFullMovedSectionEquiv ρ X s hm hz)
      exact ⟨F,ho,⟨⟨e.groupEquiv.trans a.groupEquiv,e.linearEquiv.trans a.linearEquiv,
        fun g v => (congrArg a.linearEquiv (e.intertwines g v)).trans
          (a.intertwines (e.groupEquiv g) (e.linearEquiv v))⟩⟩⟩
  | doubleThree _ _ _ _ _ hratio =>
    rw [hratio] at hqρ
    exact (lt_irrefl _ hqρ).elim

/-- Strong offending removes the SL₂, alternating-five and repeated-natural
rows of B.5.1 on the literal central support section. -/
theorem support_section_odd_linearThree_of_strong
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [IsQuasisimple X]
    (hr : primeRank 3 X = 1) (R : Submodule (ZMod 2) E)
    (hR : IsIrrPlusWith ρ X P R) (hclass : SupportSectionClassification ρ hR)
    (hs : IsStrongFFModule (KernelQuotient.action (orbitSectionRepresentation ρ hR))) :
    let σ := orbitSectionRepresentation ρ hR
    let D := (X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection σ)
    ∃ F : BinaryField, Odd F.degree ∧
      IsLinearNatural ((KernelQuotient.action σ).comp D.subtype) F 3 := by
  let σ := orbitSectionRepresentation ρ hR
  let δ := KernelQuotient.action σ
  let D := (X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection σ)
  obtain ⟨_,hDJ,⟨c⟩⟩ := hclass
  let J := offenderSubgroup δ
  let C := D.subgroupOf J
  let α := δ.comp J.subtype
  have hm : moved α C = ⊤ := by
    change subspaceCommutator α ⊤ C = ⊤
    rw [subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hDJ]
    exact support_section_moved ρ X P R hR
  have hz : fixedSpace α C = ⊥ := by
    rw [fixedSpace_comp_map,map_subgroupOf_eq_of_le hDJ]
    exact support_section_fixed ρ X P R hR
  have hrC : primeRank 3 C = 1 := by
    rw [primeRank_congr 3 (subgroupOfEquivOfLe hDJ)]
    exact support_section_component_rank ρ X P hr R hR
  have hstrong : IsStrongFFModule α := by
    by_contra hn
    exact not_strong_of_offenderSubgroup δ hn hs
  obtain ⟨F,ho,⟨a⟩⟩ := rankOne_strong_linearThree α C c hrC hm hz hstrong
  let e : ActionEquiv (δ.comp D.subtype) (α.comp C.subtype) :=
    ⟨(subgroupOfEquivOfLe hDJ).symm,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  exact ⟨F,ho,⟨⟨e.groupEquiv.trans a.groupEquiv,e.linearEquiv.trans a.linearEquiv,
    fun g v => (congrArg a.linearEquiv (e.intertwines g v)).trans
      (a.intertwines (e.groupEquiv g) (e.linearEquiv v))⟩⟩⟩

omit [FiniteDimensional (ZMod 2) E] in
/-- The original central covering map becomes injective once the actual
normal support has its inherited trivial two-core and an SL₃ section. -/
theorem support_section_cover_injective_of_linearThree
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [X.Normal] [IsQuasisimple X]
    (hcore : pCore 2 H = ⊥) (R : Submodule (ZMod 2) E)
    (hR : IsIrrPlusWith ρ X P R) (F : BinaryField)
    (a : ActionEquiv ((KernelQuotient.action (orbitSectionRepresentation ρ hR)).comp
      ((X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection
        (orbitSectionRepresentation ρ hR))).subtype) (linearNatural F 3)) :
    Function.Injective (supportSectionComponentCover ρ X P R hR).toMonoidHom := by
  have hXcore : pCore 2 X = ⊥ := by
    apply bot_unique
    intro x hx
    apply Subtype.ext
    exact hcore.le (pCoreIn_le_of_subnormal 2 (inferInstance : X.Normal).isSubnormal
      (mem_map_of_mem X.subtype hx))
  let c₀ := supportSectionComponentCover ρ X P R hR
  let c : PerfectCentralCovering.Cover X (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) := {
    toMonoidHom := a.groupEquiv.toMonoidHom.comp c₀.toMonoidHom
    surjective := a.groupEquiv.surjective.comp c₀.surjective
    isPerfect := inferInstance
    ker_le_center := by
      rw [MonoidHom.ker_comp_of_injective _ _ a.groupEquiv.injective]
      exact c₀.ker_le_center }
  have hi := Matrix.SL3.centralCover_injective c hXcore
  exact fun x y hxy => hi (congrArg a.groupEquiv hxy)

omit [FiniteDimensional (ZMod 2) E] in
/-- Recognition uses the original support map and the same section coordinates;
it proves the central kernel trivial instead of silently discarding it. -/
theorem support_section_marked_linearThree
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [X.Normal] [IsQuasisimple X]
    (hcore : pCore 2 H = ⊥) (R : Submodule (ZMod 2) E)
    (hR : IsIrrPlusWith ρ X P R) (F : BinaryField) (ho : Odd F.degree)
    (a : ActionEquiv ((KernelQuotient.action (orbitSectionRepresentation ρ hR)).comp
      ((X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection
        (orbitSectionRepresentation ρ hR))).subtype) (linearNatural F 3)) :
    center X = ⊥ ∧
    ∃ e : X ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier,
      (∀ x : X, e x = a.groupEquiv ((supportSectionComponentCover ρ X P R hR).toMonoidHom x)) ∧
      ∀ (x : X) (v : centralQuotient ρ X (orbitSpan ρ P R)),
        a.linearEquiv (centralQuotientRepresentation ρ X (orbitSpan ρ P R)
          (orbitSpan_component_invariant ρ hR.normalizes hR.isIrrPlus) x v) =
          linearNatural F 3 (e x) (a.linearEquiv v) := by
  let c := supportSectionComponentCover ρ X P R hR
  let e₀ := MulEquiv.ofBijective c.toMonoidHom
    ⟨support_section_cover_injective_of_linearThree ρ X P hcore R hR F a,c.surjective⟩
  let e := e₀.trans a.groupEquiv
  have he (x : X) : e x = a.groupEquiv (c.toMonoidHom x) := rfl
  have hz : center (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) = ⊥ := by
    apply (Matrix.SL3.center_eq_bot_iff_card_mod_three F.Carrier).mpr
    rw [F.card_eq,Nat.BinaryTorusParity.two_pow_mod_three,Nat.odd_iff.mp ho]
    decide
  refine ⟨?_,e,he,?_⟩
  · apply bot_unique
    intro x hx
    have hh := ((centerCongr e) ⟨x,hx⟩).property
    exact e.injective ((hz.le hh).trans e.map_one.symm)
  · intro x v
    have hh := a.intertwines (c.toMonoidHom x) v
    have hact : KernelQuotient.action (orbitSectionRepresentation ρ hR)
        (c.toMonoidHom x) v =
        centralQuotientRepresentation ρ X (orbitSpan ρ P R)
          (orbitSpan_component_invariant ρ hR.normalizes hR.isIrrPlus) x v := by
      rw [supportSectionComponentCover_apply,KernelQuotient.action_projection]
      rfl
    exact (congrArg a.linearEquiv hact.symm).trans hh

omit [Finite H] [FiniteDimensional (ZMod 2) E] in
/-- The original support is SL₃, with its model marking compatible with the
literal central-section projection and with no residual central kernel. -/
@[expose] def SupportMarkedLinearThreeSection
    (ρ : Representation (ZMod 2) H E) {X P : Subgroup H}
    {R : Submodule (ZMod 2) E} (hR : IsIrrPlusWith ρ X P R) : Prop :=
  let σ := orbitSectionRepresentation ρ hR
  let D := (X.subgroupOf (X ⊔ P)).map (KernelQuotient.projection σ)
  center X = ⊥ ∧
  ∃ F : BinaryField, Odd F.degree ∧
    ∃ (a : ActionEquiv ((KernelQuotient.action σ).comp D.subtype) (linearNatural F 3))
      (e : X ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier),
      ∀ x : X, KernelQuotient.projection σ (inclusion (show X ≤ X ⊔ P from le_sup_left) x) =
        (a.groupEquiv.symm (e x) : D)

/-- Strong offending constructs the marked SL₃ support from the original
rank bound and classification; trivial ambient two-core discharges its cover. -/
theorem support_marked_linearThree_section
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H) [X.Normal] [IsQuasisimple X]
    (hcore : pCore 2 H = ⊥) (hr : primeRank 3 X = 1)
    (R : Submodule (ZMod 2) E) (hR : IsIrrPlusWith ρ X P R)
    (hclass : SupportSectionClassification ρ hR)
    (hs : IsStrongFFModule (KernelQuotient.action (orbitSectionRepresentation ρ hR))) :
    SupportMarkedLinearThreeSection ρ hR := by
  obtain ⟨F,ho,⟨a⟩⟩ := support_section_odd_linearThree_of_strong ρ X P hr R hR hclass hs
  obtain ⟨hz,e,he,_⟩ := support_section_marked_linearThree ρ X P hcore R hR F ho a
  refine ⟨hz,F,ho,a,e,?_⟩
  intro x
  rw [he x,a.groupEquiv.symm_apply_apply]
  exact (supportSectionComponentCover_apply ρ X P R hR x).symm


omit [Finite H] [FiniteDimensional (ZMod 2) E] in
/-- Odd field degree puts every two-element of the original half stabilizer
in the natural component image. The marked projection lifts this to inner
conjugation on the original support. -/
theorem support_marked_section_inducesInner
    (ρ : Representation (ZMod 2) H E) (X P : Subgroup H)
    (hP : IsPGroup 2 P) (R : Submodule (ZMod 2) E)
    (hR : IsIrrPlusWith ρ X P R) (hm : SupportMarkedLinearThreeSection ρ hR) :
    ChapterB.SourceInduction.ComponentReduction.InducesInner P X := by
  let J := X ⊔ P
  let X₀ := X.subgroupOf J
  let σ := orbitSectionRepresentation ρ hR
  let q := KernelQuotient.projection σ
  let D := X₀.map q
  let δ := KernelQuotient.action σ
  let i := inclusion (show X ≤ J from le_sup_left)
  obtain ⟨_,F,ho,a,e,hmark⟩ := hm
  let : X₀.Normal := (normal_subgroupOf_iff_le_normalizer
    (show X ≤ J from le_sup_left)).mpr (sup_le X.le_normalizer hR.normalizes)
  let : D.Normal := (inferInstance : X₀.Normal).map q (KernelQuotient.projection_surjective σ)
  let τ := a.linearEquiv.conjRingEquiv.toMonoidHom.comp δ
  have hf : Function.Injective τ := a.linearEquiv.conjRingEquiv.injective.comp
    (KernelQuotient.faithful σ)
  have hnat (d : D) (v : Fin 3 → F.Carrier) :
      τ d v = Matrix.mulVec (a.groupEquiv d).val v := by
    change a.linearEquiv (δ d (a.linearEquiv.symm v)) = _
    exact (a.intertwines d (a.linearEquiv.symm v)).trans
      (congrArg (linearNatural F 3 (a.groupEquiv d)) (a.linearEquiv.apply_symm_apply v))
  have hle : (P.subgroupOf J).map q ≤ D :=
    SL3OddNaturalNormalizer.two_subgroup_le_of_natural F.degree_pos ho F.card_eq
      D a.groupEquiv τ hf hnat _ (hP.comap_subtype.map q)
  have hi : Function.Injective (q.comp i) := by
    intro x y hxy
    apply e.injective
    apply a.groupEquiv.symm.injective
    apply Subtype.val_injective
    rw [←hmark x,←hmark y]
    exact hxy
  intro p hp
  let p₀ : J := ⟨p,(show P ≤ J from le_sup_right) hp⟩
  obtain ⟨x₀,hx₀,hx⟩ := hle (mem_map_of_mem q (show p₀ ∈ P.subgroupOf J from hp))
  let x : X := ⟨x₀.val,hx₀⟩
  refine ⟨x.val,x.property,?_⟩
  intro y hy
  let y₀ : X := ⟨y,hy⟩
  let u : X := ⟨p*y*p⁻¹,(mem_normalizer_iff.mp (hR.normalizes hp) y).mp hy⟩
  let v : X := x*y₀*x⁻¹
  have heq : u = v := by
    apply hi
    change q (p₀*i y₀*p₀⁻¹) = q (i x*i y₀*(i x)⁻¹)
    simp only [map_mul,map_inv]
    change q p₀ * q (i y₀) * (q p₀)⁻¹ = q x₀ * q (i y₀) * (q x₀)⁻¹
    rw [hx]
  exact congrArg Subtype.val heq


/-- The classified rank-one support has an explicit strong offender and an
actual SL₃ marking, with the central covering kernel discharged. -/
theorem homogeneous_support_strong_marked_linearThree
    (ρ : Representation (ZMod 2) H E) (X K S P A B : Subgroup H)
    [X.Normal] [IsQuasisimple X] [Group.IsPerfect K]
    (hcore : pCore 2 H = ⊥) (hr : primeRank 3 X = 1)
    (hK : fixedSpace ρ K = ⊥) (hc : K ≤ centralizer (X : Set H))
    (hS : IsPGroup 2 S) (hPS : P ≤ S) (hSP : S ≤ normalizer (P : Set H))
    (hAP : A ≤ P) (hBA : B ≤ A) (hXB : ⁅X,B⁆ = X)
    (hA : A ∈ CFSG.Quasithin.ChapterD.QhatStar ρ)
    (I R : Submodule (ZMod 2) E) (hKI : K ≤ subspaceStabilizer ρ I)
    (hRI : R ≤ I) (hR : IsIrrPlusWith ρ X P R) (hclass : SupportSectionClassification ρ hR)
    (t : H) (ht : t ∈ S) (hd : Disjoint I (I.map (ρ t))) :
    SupportStrongSection ρ hR ∧ SupportMarkedLinearThreeSection ρ hR ∧
      ChapterB.SourceInduction.ComponentReduction.InducesInner P X := by
  have hs := homogeneous_support_section_strong ρ X K S P A B hK hc hS hPS hSP hAP hBA hXB hA
    I R hKI hRI hR (support_orbit_eq_seed ρ X P hr R hR hclass) t ht hd
  have hm : SupportMarkedLinearThreeSection ρ hR := by
    obtain ⟨D,_,_,_,hsec⟩ := hs
    exact support_marked_linearThree_section ρ X P hcore hr R hR hclass ⟨_,hsec⟩
  exact ⟨hs,hm,support_marked_section_inducesInner ρ X P (hS.to_le hPS) R hR hm⟩

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
