module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SuzukiCentralizer
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorModels
public import Theory.Representation.BinaryOffender.PerfectIrreducibleCentralizer
public import Theory.Representation.BinaryOffender.NormalRestriction
public import Theory.Representation.Suzuki.BinaryDegree

/-!
# Suzuki pairs commuting with reduced offender actions

The original orbit may have separated Suzuki supports. Only the common
fixed space of the pair is assumed zero. Each factor acts trivially on a
commuting doubled natural three-space, so their join fixes it. Natural
irreducibles are fixed by the perfect join. This preserves both source
supports instead of replacing them by a fully moving individual component.

Source: Aschbacher--Smith B.5.1, B.5.6 and 10.2.9.
-/

public noncomputable section
open scoped MonoidAlgebra
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter10.PointControl.Constrained.SuzukiCentralizer
open ChapterB.SourceInduction
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.ExtensionConsequences BenderSuzuki.MatrixGroups Theory.GroupTheory

variable {Q D V : Type*} [Group Q] [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private def fixedImageEquiv (σ : Representation (ZMod 2) D V)
    (hz : σ.invariants = ⊥) (A : Subgroup D) (U : Subrepresentation σ) :
    ActionEquiv (U.toRepresentation.comp A.subtype)
      (((fixed σ).quotientImage U).toRepresentation.comp A.subtype) where
  groupEquiv := MulEquiv.refl A
  linearEquiv := Submodule.equivMapOfInjective σ.invariants.mkQ
    (by apply LinearMap.ker_eq_bot.mp; rw [Submodule.ker_mkQ,hz]) U.toSubmodule
  intertwines _ _ := rfl

private def fixedImageMarking (σ : Representation (ZMod 2) D V)
    (hz : σ.invariants = ⊥) (A : Subgroup D) (U : Subrepresentation σ)
    {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
    {τ : Representation (ZMod 2) H W}
    (e : ActionEquiv (((fixed σ).quotientImage U).toRepresentation.comp A.subtype) τ) :
    ActionEquiv (U.toRepresentation.comp A.subtype) τ where
  groupEquiv := e.groupEquiv
  linearEquiv := (fixedImageEquiv σ hz A U).linearEquiv.trans e.linearEquiv
  intertwines a v :=
    (congrArg e.linearEquiv ((fixedImageEquiv σ hz A U).intertwines a v)).trans
      (e.intertwines a _)

private theorem no_irreducible_moved
    (ρ : Representation (ZMod 2) Q V) (S : Subgroup Q) [Group.IsPerfect S]
    (hfix : fixedSpace ρ S = ⊥)
    (f : D →* Q) (hc : f.range ≤ centralizer (S : Set Q))
    (A : Subgroup D) (U : Subrepresentation (ρ.comp f))
    (hu : U.toSubmodule = moved (ρ.comp f) A)
    (hi : IsIrreducible (U.toRepresentation.comp A.subtype)) : False := by
  let W := U.toSubmodule
  have hs : S ≤ subspaceStabilizer ρ W := by
    dsimp only [W]
    rw [hu]
    change S ≤ subspaceStabilizer ρ (subspaceCommutator (ρ.comp f) ⊤ A)
    rw [subspaceCommutator_comp_map]
    exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      ((le_centralizer_iff.mp ((map_le_range f A).trans hc)).trans (Subgroup.centralizer_le_normalizer _))
  let τ := (stabilizerRepresentation ρ W).comp (inclusion hs)
  let α := U.toRepresentation.comp A.subtype
  let := hi
  have ht := perfect_commuting_irreducible α τ (by
    intro a s
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    change ρ s (ρ (f a) v) = ρ (f a) (ρ s v)
    rw [← Module.End.mul_apply,←map_mul,← Module.End.mul_apply,←map_mul]
    exact LinearMap.congr_fun (congrArg ρ (hc (MonoidHom.mem_range.mpr ⟨a,rfl⟩) s s.property)) v)
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial α
  obtain ⟨v,hv⟩ := exists_ne (0:W)
  apply hv
  apply Subtype.ext
  apply hfix.le
  intro s
  exact congrArg Subtype.val (ht s v)

omit [FiniteDimensional (ZMod 2) V] in
private theorem doubled_moved_fixed
    (ρ : Representation (ZMod 2) Q V) (S : Subgroup Q)
    {m : ℕ} (hm : 0<m) (eS : S ≃* SuzukiMatrixGroup m)
    (f : D →* Q) (hc : f.range ≤ centralizer (S : Set Q))
    (A : Subgroup D) (U : Subrepresentation (ρ.comp f))
    (hu : U.toSubmodule = moved (ρ.comp f) A)
    (F : BinaryField)
    (e : ActionEquiv (U.toRepresentation.comp A.subtype) (repeated (linearNatural F 3) 2)) : U.toSubmodule ≤ fixedSpace ρ S := by
  let W := U.toSubmodule
  have hs : S ≤ subspaceStabilizer ρ W := by
    dsimp only [W]
    rw [hu]
    change S ≤ subspaceStabilizer ρ (subspaceCommutator (ρ.comp f) ⊤ A)
    rw [subspaceCommutator_comp_map]
    exact subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      ((le_centralizer_iff.mp ((map_le_range f A).trans hc)).trans (Subgroup.centralizer_le_normalizer _))
  let τ := ((stabilizerRepresentation ρ W).comp (inclusion hs)).comp eS.symm.toMonoidHom
  let α := (U.toRepresentation.comp A.subtype).comp e.groupEquiv.symm.toMonoidHom
  have hcomm (a : SuzukiMatrixGroup m) (b : Matrix.SpecialLinearGroup (Fin 3) F.Carrier)
      (v : W) : τ a (α b v) = α b (τ a v) := by
    apply Subtype.ext
    change ρ (eS.symm a) (ρ (f (e.groupEquiv.symm b)) v) =
      ρ (f (e.groupEquiv.symm b)) (ρ (eS.symm a) v)
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    exact LinearMap.congr_fun (congrArg ρ
      (hc (MonoidHom.mem_range.mpr ⟨(e.groupEquiv.symm b : D),rfl⟩)
        (eS.symm a) (eS.symm a).property)) v
  have he (b : Matrix.SpecialLinearGroup (Fin 3) F.Carrier) (v : W) :
      e.linearEquiv (α b v) = SL3DoubledNaturalOffenders.representation F.Carrier b (e.linearEquiv v) := by
    have hh := e.intertwines (e.groupEquiv.symm b) v
    rw [e.groupEquiv.apply_symm_apply] at hh
    exact hh
  have ht := Suzuki.doubled_natural_commuting_trivial_of_coordinates hm τ α hcomm e.linearEquiv he
  intro v hv s
  have hh := congrArg Subtype.val (ht (eS s) (⟨v,hv⟩ : W))
  change ρ (eS.symm (eS s)) v = v at hh
  rwa [eS.symm_apply_apply] at hh

omit [FiniteDimensional (ZMod 2) V] in
private theorem no_doubled_pair
    (ρ : Representation (ZMod 2) Q V) (S K : Subgroup Q)
    {m : ℕ} (hm : 0<m) (eS : S ≃* SuzukiMatrixGroup m) (eK : K ≃* SuzukiMatrixGroup m)
    (hfix : fixedSpace ρ (S ⊔ K) = ⊥)
    (f : D →* Q) (hc : f.range ≤ centralizer ((S ⊔ K : Subgroup Q) : Set Q))
    (A : Subgroup D) (U : Subrepresentation (ρ.comp f))
    (hu : U.toSubmodule = moved (ρ.comp f) A)
    (F : BinaryField)
    (e : ActionEquiv (U.toRepresentation.comp A.subtype) (repeated (linearNatural F 3) 2)) : False := by
  have hS := doubled_moved_fixed ρ S hm eS f (hc.trans (centralizer_le (show S ≤ S ⊔ K from le_sup_left))) A U hu F e
  have hK := doubled_moved_fixed ρ K hm eK f (hc.trans (centralizer_le (show K ≤ S ⊔ K from le_sup_right))) A U hu F e
  have hz : U.toSubmodule = ⊥ := by
    apply bot_unique
    have h := le_inf hS hK
    have hs : fixedSpace ρ (S ⊔ K) = fixedSpace ρ S ⊓ fixedSpace ρ K := ρ.invariants_comp_sup S K
    rw [←hs,hfix] at h
    exact h
  let : Nontrivial U.toSubmodule := e.linearEquiv.toEquiv.nontrivial
  exact (Submodule.nontrivial_iff_ne_bot.mp inferInstance) hz

/-- The literal B.5 two-factor quotient is impossible for a commuting Suzuki
component when the offender action has no fixed vectors and large moved spaces. -/
private theorem not_twoFactors_of_commuting_suzuki_pair
    (ρ : Representation (ZMod 2) Q V) (S K : Subgroup Q) [Group.IsPerfect (S ⊔ K : Subgroup Q)]
    {m : ℕ} (hm : 0<m) (eS : S ≃* SuzukiMatrixGroup m) (eK : K ≃* SuzukiMatrixGroup m)
    (hfix : fixedSpace ρ (S ⊔ K) = ⊥)
    (f : D →* Q) (hc : f.range ≤ centralizer ((S ⊔ K : Subgroup Q) : Set Q))
    (hz : Representation.invariants (ρ.comp f) = ⊥)
    (hdegree : ∀ A : Subgroup D, A ≠ ⊥ →
      12 ≤ Module.finrank (ZMod 2) (moved (ρ.comp f) A))
    (c : SourceTwoFactorCase (ρ.comp f)) : False := by
  let σ := ρ.comp f
  let A := c.first
  let U := c.firstSpace
  let E := (fixed σ).quotientImage U
  let eU := fixedImageEquiv σ hz A U
  have hdU := eU.linearEquiv.finrank_eq
  let : Nontrivial A := c.firstCase.nontrivial
  have hA : A ≠ ⊥ := (nontrivial_iff_ne_bot A).mp inferInstance
  have hd := hdegree A hA
  have hle : moved σ A ≤ U.toSubmodule := by
    cases c.firstCase with
    | natural he _ => exact he.ge
    | doubleNatural _ _ he _ => exact he.ge
    | exceptional he _ => exact he
  have hdim : 12 ≤ Module.finrank (ZMod 2) U.toSubmodule :=
    hd.trans (Submodule.finrank_mono hle)
  have hdimE : 12 ≤ Module.finrank (ZMod 2) E.toSubmodule := by
    rwa [← hdU]
  cases c.firstCase with
  | natural hu hn =>
    cases hn with
    | linearTwo F hn =>
      obtain ⟨e⟩ := hn
      exact no_irreducible_moved ρ (S ⊔ K) hfix f hc A U hu
        (irreducible_of_equiv (fixedImageMarking σ hz A U e) (linearNatural_irreducible F (by decide : 2 ≤ 2)))
    | linearThree F ho hn =>
      obtain ⟨e⟩ := hn
      exact no_irreducible_moved ρ (S ⊔ K) hfix f hc A U hu
        (irreducible_of_equiv (fixedImageMarking σ hz A U e) (linearNatural_irreducible F (by decide : 2 ≤ 3)))
    | symmetricFive hn =>
      obtain ⟨e⟩ := hn
      have he := e.linearEquiv.finrank_eq
      change Module.finrank (ZMod 2) E.toSubmodule =
        Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 5)) at he
      rw [BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)] at he
      simp only [Fintype.card_fin] at he
      omega
  | doubleNatural F ho hu hn =>
    obtain ⟨e⟩ := hn
    exact no_doubled_pair ρ S K hm eS eK hfix f hc A U hu F (fixedImageMarking σ hz A U e)
  | exceptional hu d =>
    have he := d.dimension
    change Module.finrank (ZMod 2) E.toSubmodule = 4 at he
    omega


private theorem normal_characteristic_image
    {H P : Type*} [Group H] [Group P]
    (f : H →* P) (hf : Function.Injective f) [f.range.Normal]
    (K : Subgroup H) [K.Characteristic] : (K.map f).Normal := by
  let e : H ≃* f.range := MulEquiv.ofBijective f.rangeRestrict
    ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  refine ⟨?_⟩
  rintro _ ⟨k,hk,rfl⟩ g
  let α : MulAut H := (e.trans (MulAut.conjNormal g)).trans e.symm
  refine ⟨α k,characteristic_iff_le_comap.mp inferInstance α hk,?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ((MulAut.conjNormal g) (e k)))

variable [Finite D]

/-- Normality in the full irreducible actor makes the quasisimple moved
space the whole original space. Degree twelve suffices on smaller sections. -/
private theorem ff_rows_of_normal_commuting_perfect
    (ρ : Representation (ZMod 2) Q V) (hρ : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (X : Subgroup Q) [Group.IsPerfect X]
    (hfix : fixedSpace ρ X = ⊥)
    (hdegree : ∀ U : Subrepresentation (ρ.comp X.subtype), U ≠ ⊥ →
      12 ≤ Module.finrank (ZMod 2) U.toSubmodule)
    (hfull : 24 ≤ Module.finrank (ZMod 2) V)
    (f : D →* Q) (hf : Function.Injective f) [f.range.Normal]
    (hc : f.range ≤ centralizer (X : Set Q))
    (hcore : pCore 2 D = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple D)
    (hgen : offenderSubgroup (ρ.comp f) = ⊤)
    (hff : IsFFModule (ρ.comp f)) : LargeSectionFFCases (ρ.comp f) := by
  let σ := ρ.comp f
  have hfaith : Function.Injective σ := hρ.comp hf
  have hno (K : Subgroup D) : ¬ IsIrrPlus σ K (subspaceCommutator σ ⊤ K) := by
    intro h
    have hh : IsIrrPlus ρ (K.map f) (subspaceCommutator σ ⊤ K) :=
      h.of_intertwining σ ρ (f.subgroupMap K) (f.subgroupMap_surjective K)
        LinearMap.id Function.injective_id (fun _ _ => rfl) (Submodule.map_id _)
    rw [subspaceCommutator_comp_map] at hh
    exact not_irrPlus_moved_of_commuting_perfect ρ X (K.map f) hfix
      (le_centralizer_iff.mp ((map_le_range f K).trans hc)) hh
  have hkernel (K : Subgroup D) (hK : K ≠ ⊥) : ¬ K.map f ≤ ρ.ker := by
    intro h
    apply hK
    apply bot_unique
    intro k hk
    apply hf
    apply hρ
    exact (h (mem_map_of_mem f hk)).trans (by simp)
  have hdim (K : Subgroup D) (hK : K ≠ ⊥) :
      12 ≤ Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ K) := by
    rw [subspaceCommutator_comp_map]
    exact degree_le_moved_finrank_of_commuting ρ X (K.map f) hdegree
      (hkernel K hK) ((map_le_range f K).trans hc)
  have hcard : 2^12 ≤ Nat.card D := by
    obtain ⟨A,hA⟩ := hff
    have hd := degree_le_fixedCodim_of_commuting ρ X (A.map f) hdegree
      (hkernel A hA.1.1) ((map_le_range f A).trans hc)
    have he := fixedCodim_map_equivariant σ ρ f (LinearEquiv.refl (ZMod 2) V)
      (fun _ _ => rfl) A
    have ha : fixedCodim σ A ≤ rank A := hA.2
    have hr : 12 ≤ rank A := by omega
    exact (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hr).trans
      (hA.1.card_eq_two_pow_rank ▸ Nat.card_le_card_of_injective A.subtype A.subtype_injective)
  have hclass := (adequateAlternative_knownSimple σ
    ⟨inferInstance,hfaith,hcore,hgen,⟨cover⟩⟩).of_ff σ hff
  cases hclass with
  | quasisimple hq c =>
    let K := generalizedFitting D
    let : IsQuasisimple K := hq
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    have hK : K ≠ ⊥ := (nontrivial_iff_ne_bot _).mp inferInstance
    let : (K.map f).Normal := normal_characteristic_image f hf K
    have hneq : K.map f ≠ ⊥ := fun he => hK ((map_eq_bot_iff_of_injective _ hf).mp he)
    have htop : subspaceCommutator σ ⊤ K = ⊤ := by
      rw [subspaceCommutator_comp_map]
      exact subspaceCommutator_top_eq_top_of_normal_faithful_irreducible ρ hρ hi (K.map f) hneq
    have hd : 24 ≤ Module.finrank (ZMod 2) (subspaceCommutator σ ⊤ K) := by
      rw [htop,finrank_top]
      exact hfull
    obtain ⟨F,hF,he⟩ := quasisimple_double_of_large_moved_sections σ _ c (hno _) hd
    exact Or.inr ⟨c,F,hF,he⟩
  | symmetricThree c =>
    rw [Nat.card_congr c.equiv.toEquiv] at hcard
    norm_num [Nat.card_eq_fintype_card,Fintype.card_perm] at hcard
  | twoFactors c => exact Or.inl ⟨c⟩
  | outerSixThree c =>
    have hi : (c.first ⊔ c.second).index ≤ 2 :=
      Nat.le_of_dvd (by decide) (c.factors_index_dvd_two σ hgen)
    have hp : Nat.card (c.first ⊔ c.second : Subgroup D) = 1080 := by
      rw [←Nat.card_congr c.product.toEquiv,Nat.card_prod,
        Nat.card_congr c.firstEquiv.toEquiv,Nat.card_congr c.secondEquiv.toEquiv]
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hb := (c.first ⊔ c.second).index_mul_card
    rw [hp] at hb
    omega
  | hyperplane c =>
    have hK : c.first ≠ ⊥ := by
      intro he
      have hh := c.firstDimension
      have hz : moved σ c.first = ⊥ := by
        apply (subspaceCommutator_eq_bot_iff σ ⊤ c.first).mpr
        intro v _ a
        have ha : (a : D) = 1 := he.le a.property
        change σ (a : D) v = v
        rw [ha,map_one,Module.End.one_apply]
      rw [hz,finrank_bot] at hh
      omega
    have hh := hdim c.first hK
    change 12 ≤ Module.finrank (ZMod 2) (moved σ c.first) at hh
    rw [c.firstDimension] at hh
    omega

/-- Both source FF alternatives are impossible when the commuting pair
consists of actual Suzuki groups and only their common fixed space vanishes. -/
theorem no_ff_of_normal_commuting_suzuki_pair
    (ρ : Representation (ZMod 2) Q V) (hρ : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (S K : Subgroup Q) [Group.IsPerfect (S ⊔ K : Subgroup Q)]
    {m : ℕ} (hm : 0<m) (eS : S ≃* SuzukiMatrixGroup m) (eK : K ≃* SuzukiMatrixGroup m)
    (hfix : fixedSpace ρ (S ⊔ K) = ⊥)
    (hdegree : ∀ U : Subrepresentation (ρ.comp (S ⊔ K).subtype), U ≠ ⊥ →
      12 ≤ Module.finrank (ZMod 2) U.toSubmodule)
    (hfull : 24 ≤ Module.finrank (ZMod 2) V)
    (f : D →* Q) (hf : Function.Injective f) [f.range.Normal]
    (hc : f.range ≤ centralizer ((S ⊔ K : Subgroup Q) : Set Q))
    (hcore : pCore 2 D = ⊥)
    (cover : SQTKQuotient KnownSimple.IsKnownSimple D)
    (hgen : offenderSubgroup (ρ.comp f) = ⊤)
    (hz : Representation.invariants (ρ.comp f) = ⊥) : ¬ IsFFModule (ρ.comp f) := by
  intro hff
  rcases ff_rows_of_normal_commuting_perfect ρ hρ hi (S ⊔ K) hfix hdegree hfull
      f hf hc hcore cover hgen hff with h | ⟨c,F,_,⟨e⟩⟩
  · obtain ⟨c⟩ := h
    apply not_twoFactors_of_commuting_suzuki_pair ρ S K hm eS eK hfix f hc hz ?_ c
    intro B hB
    change 12 ≤ Module.finrank (ZMod 2) (subspaceCommutator (ρ.comp f) ⊤ B)
    rw [subspaceCommutator_comp_map]
    apply degree_le_moved_finrank_of_commuting ρ (S ⊔ K) (B.map f) hdegree ?_
      ((map_le_range f B).trans hc)
    intro h
    apply hB
    apply bot_unique
    intro b hb
    apply hf
    apply hρ
    exact (h (mem_map_of_mem f hb)).trans (by simp)
  · exact no_doubled_pair ρ S K hm eS eK hfix f hc _ c.sectionData.space
      c.sectionData.space_eq F e

omit [Finite D] in
private theorem small_suzuki_trivial
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    {m : ℕ} (hm : 0 < m) (τ : Representation (ZMod 2) (SuzukiMatrixGroup m) W)
    (hd : Module.finrank (ZMod 2) W < 12) : ∀ a, τ a = 1 := by
  let : Fact (0 < m) := ⟨hm⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal τ.ker inferInstance with h | h
  · have hb := Suzuki.finrank_ge (by omega : 1 ≤ m) τ ((MonoidHom.ker_eq_bot_iff τ).mp h)
    omega
  · exact fun a => h.ge (mem_top a)

omit [Finite D] in
/-- Every nonzero section of a Suzuki pair with zero common fixed space
has degree at least twelve, even when each component has a fixed summand. -/
theorem pair_submodule_degree
    (ρ : Representation (ZMod 2) Q V) (S K : Subgroup Q)
    {m : ℕ} (hm : 0<m) (eS : S ≃* SuzukiMatrixGroup m) (eK : K ≃* SuzukiMatrixGroup m)
    (hfix : fixedSpace ρ (S ⊔ K) = ⊥)
    (U : Subrepresentation (ρ.comp (S ⊔ K).subtype)) (hU : U ≠ ⊥) :
    12 ≤ Module.finrank (ZMod 2) U.toSubmodule := by
  by_contra! hd
  have ht (A : Subgroup Q) (hA : A ≤ S ⊔ K) (e : A ≃* SuzukiMatrixGroup m) :
      U.toSubmodule ≤ fixedSpace ρ A := by
    let τ := U.toRepresentation.comp ((inclusion hA).comp e.symm.toMonoidHom)
    have hz := small_suzuki_trivial hm τ hd
    intro v hv a
    have hh := LinearMap.congr_fun (hz (e a)) (⟨v,hv⟩ : U.toSubmodule)
    have he := congrArg Subtype.val hh
    change ρ (e.symm (e a)) v = v at he
    rwa [e.symm_apply_apply] at he
  have hz : U.toSubmodule ≤ fixedSpace ρ (S ⊔ K) := by
    have hs : fixedSpace ρ (S ⊔ K) = fixedSpace ρ S ⊓ fixedSpace ρ K := ρ.invariants_comp_sup S K
    rw [hs]
    exact le_inf (ht S le_sup_left eS) (ht K le_sup_right eK)
  exact hU (Subrepresentation.toSubmodule_injective (bot_unique (hz.trans_eq hfix)))

end CFSG.Quasithin.Chapter10.PointControl.Constrained.SuzukiCentralizer
