module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalLineExclusion
public import Theory.Representation.PSL3Two.IrreducibleCatalogue
public import Theory.Representation.BinaryNormalExtension
public import Theory.Representation.BinaryOffender.CentralizerField
public import Theory.Representation.Quotient

/-!
# The binary linear-three exclusion in the original field-plane action

The checked binary PSL₃(2) irreducible catalogue has trivial invertible
commutant. Faithful descent through the fixed subspace therefore gives the
same conclusion on an Irr⁺ component moved space, including central extensions.
The original residual cubic fixes this space because it centralizes the component.

Minimality puts all offender displacement in that moved space. An operator
fixing it and normalizing the original action commutes with the offender:
the difference fixes both this space and its quotient, so lies in the
trivial two-core of the normal offender subgroup. The original cubic
noncentrality witness now gives a contradiction on the literal quotient.
No offender-containment assumption or later LocalAnalysis result is used.

The Chapter 12 companion removes PSL₃(2) from the actual component list.
The A5 and SL₃(4) branches and the subsequent graph argument remain.
Source: Aschbacher--Smith 6.2.7, printed pp.682--684; H.6.1, p.386.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction

private theorem centralizer_transfer
    {D W X : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) D W} {τ : Representation (ZMod 2) D X}
    (e : σ.Equiv τ)
    (ht : ∀ f : X ≃ₗ[ZMod 2] X, (∀ g x, f (τ g x) = τ g (f x)) → f = 1)
    (f : W ≃ₗ[ZMod 2] W) (hf : ∀ g w, f (σ g w) = σ g (f w)) : f = 1 := by
  let l := e.toLinearEquiv
  have he (g : D) (w : W) : l (σ g w) = τ g (l w) :=
    LinearMap.congr_fun (e.isIntertwining' g) w
  have hi (g : D) (x : X) : l.symm (τ g x) = σ g (l.symm x) := by
    apply l.injective
    rw [l.apply_symm_apply,he,l.apply_symm_apply]
  have hconj : (l.symm.trans f).trans l = 1 := ht _ (by
    intro g x
    change l (f (l.symm (τ g x))) = τ g (l (f (l.symm x)))
    rw [hi,hf,he])
  ext w
  apply l.injective
  have hh := LinearEquiv.congr_fun hconj (l w)
  change l (f (l.symm (l w))) = l w at hh
  change l (f w) = l w
  simpa only [l.symm_apply_apply] using hh

private theorem binary_irreducible_centralizer
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (σ : Representation (ZMod 2) D W) [IsIrreducible σ]
    (e : D ≃* PSL(3,ZMod 2))
    (f : W ≃ₗ[ZMod 2] W) (hf : ∀ g w, f (σ g w) = σ g (f w)) : f = 1 := by
  let mark := e.trans Matrix.PSL3Two.equiv.symm
  let τ := σ.comp mark.symm.toMonoidHom
  let : IsIrreducible τ := (irreducible_comp_surjective_iff mark.symm.toMonoidHom
    mark.symm.surjective σ).mpr inferInstance
  have hc (g : BinaryLinearThree.Group) (w : W) : f (τ g w) = τ g (f w) := hf (mark.symm g) w
  rcases BinaryLinearThree.IrreducibleCatalogue.classify τ with ht | hn | hd | hs
  · obtain ⟨a⟩ := ht
    exact centralizer_transfer a (fun b _ => by
      ext v
      fin_cases v
      · exact b.map_zero
      · have hb : b 1 ≠ 0 := fun hz => one_ne_zero (b.injective (hz.trans b.map_zero.symm))
        have hcases : b 1 = 0 ∨ b 1 = 1 := by
          generalize b 1 = x
          fin_cases x
          · exact Or.inl rfl
          · exact Or.inr rfl
        exact hcases.resolve_left hb) f hc
  · obtain ⟨a⟩ := hn
    let := BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
    let := BinaryLinearThree.IrreducibleCatalogue.natural_absolute
    exact centralizer_transfer a
      (BinaryNormalExtension.centralizer_eq_one_of_absolutelyIrreducible _) f hc
  · obtain ⟨a⟩ := hd
    let := BinaryLinearThree.IrreducibleCatalogue.dual_irreducible
    let := BinaryLinearThree.IrreducibleCatalogue.dual_absolute
    exact centralizer_transfer a
      (BinaryNormalExtension.centralizer_eq_one_of_absolutelyIrreducible _) f hc
  · obtain ⟨a⟩ := hs
    let := BinaryLinearThree.IrreducibleCatalogue.steinberg_irreducible
    let := BinaryLinearThree.IrreducibleCatalogue.steinberg_absolute
    let : Nontrivial BinaryLinearThree.Steinberg :=
      Subrepresentation.irreducible_module_nontrivial BinaryLinearThree.S
    exact centralizer_transfer a
      (BinaryNormalExtension.centralizer_eq_one_of_absolutelyIrreducible _) f hc

private theorem binary_irrPlus_centralizer
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) D W) (K : Subgroup D)
    (hI : IsIrrPlus ρ K (moved ρ K)) (e : K ≃* PSL(3,ZMod 2))
    (f : W ≃ₗ[ZMod 2] W) (hf : ∀ k : K, ∀ w, f (ρ k w) = ρ k (f w)) :
    ∀ w ∈ moved ρ K, f w = w := by
  let I := moved ρ K
  let σ := (invariantSubspace ρ K I hI.choose).toRepresentation
  let τ := centralQuotientRepresentation ρ K I hI.choose
  have hmaple : I.map f.toLinearMap ≤ I := by
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨k,hk,w,_,rfl⟩
    change f (ρ k w - w) ∈ I
    rw [map_sub,hf ⟨k,hk⟩]
    exact Submodule.subset_span ⟨k,hk,f w,Submodule.mem_top,rfl⟩
  have hmap : I.map f.toLinearMap = I := Submodule.eq_of_le_of_finrank_eq hmaple
    (LinearEquiv.finrank_map_eq f I)
  let fI := f.ofSubmodules I I hmap
  let u := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).symm fI
  have hu : u ∈ Representation.CentralizerField.linearCentralizer σ := by
    apply (Representation.CentralizerField.mem_linearCentralizer_iff σ u).mpr
    intro k w
    exact Subtype.ext (hf k w)
  let a : Representation.CentralizerField.linearCentralizer σ := ⟨u,hu⟩
  let b := CentralizerField.centralizerQuotientHom ρ K I hI.choose a
  let := hI.choose_spec.2
  have hb : b = 1 := by
    apply Subtype.ext
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) _).injective
    apply binary_irreducible_centralizer τ e
    exact (Representation.CentralizerField.mem_linearCentralizer_iff τ b.val).mp b.property
  have ha : a = 1 := CentralizerField.centralizerQuotientHom_injective ρ K I hI.choose
    hI.choose_spec.1 (hb.trans (map_one _).symm)
  intro w hw
  exact congrArg (fun c : Representation.CentralizerField.linearCentralizer σ =>
    (c.val.val ⟨w,hw⟩ : W)) ha

private theorem fixed_support_commutes
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥) (I : Subgroup D) (hI : IsBestOffender ρ I)
    (U : Submodule (ZMod 2) W)
    (hNU : offenderSubgroup ρ ≤ subspaceStabilizer ρ U)
    (hIU : moved ρ I ≤ U)
    (a : D ≃* D) (f : W ≃ₗ[ZMod 2] W)
    (he : ∀ g w, f (ρ g w) = ρ (a g) (f w))
    (hfix : ∀ w ∈ U, f w = w) : ∀ i ∈ I, a i = i := by
  let N := offenderSubgroup ρ
  let σ := ρ.comp N.subtype
  let S : Subrepresentation σ := ⟨U,fun g w hw => (hNU g.property w).2 hw⟩
  have hIN : I ≤ N := hI.le_offenderSubgroup ρ
  have haN : I.map a.toMonoidHom ≤ N :=
    (hI.map_equivariant ρ ρ a f he).le_offenderSubgroup ρ
  have hker : S.toRepresentation.ker ⊓ S.quotientRepresentation.ker = ⊥ := by
    apply le_bot_iff.mp
    exact (ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.section_kernel_le_twoCore
      σ (hf.comp N.subtype_injective) S).trans_eq
        (ChapterB.SourceInduction.offenderSubgroup_twoCore ρ hcore)
  intro i hi
  have hiaN : a i ∈ N := haN (mem_map_of_mem a.toMonoidHom hi)
  let k : N := ⟨a i * i⁻¹,N.mul_mem hiaN (N.inv_mem (hIN hi))⟩
  have hsame (w : W) (hw : w ∈ U) : ρ (a i) w = ρ i w := by
    have hh := he i w
    rw [hfix w hw,hfix _ ((hNU (hIN hi) w).2 hw)] at hh
    exact hh.symm
  have hmove (w : W) : ρ (a i) w - w ∈ U := by
    have hv : ρ i (f.symm w) - f.symm w ∈ U :=
      hIU (Submodule.subset_span ⟨i,hi,f.symm w,Submodule.mem_top,rfl⟩)
    have hh := hfix _ hv
    rw [map_sub,he,f.apply_symm_apply] at hh
    exact hh.symm ▸ hv
  have hk1 : k ∈ S.toRepresentation.ker := by
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    change ρ (a i * i⁻¹) w = w
    rw [map_mul,Module.End.mul_apply,hsame _ ((hNU (N.inv_mem (hIN hi)) w).2 w.property)]
    rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one]
    rfl
  have hk2 : k ∈ S.quotientRepresentation.ker := by
    apply MonoidHom.mem_ker.mpr
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ w =>
      apply (Submodule.Quotient.eq U).mpr
      change ρ (a i * i⁻¹) w - w ∈ U
      rw [map_mul,Module.End.mul_apply]
      have hh := U.add_mem (hmove (ρ i⁻¹ w))
        (hIU (Submodule.subset_span ⟨i⁻¹,I.inv_mem hi,w,Submodule.mem_top,rfl⟩))
      simpa only [sub_add_sub_cancel] using hh
  have hk : k = 1 := hker.le ⟨hk1,hk2⟩
  exact mul_inv_eq_one.mp (congrArg Subtype.val hk)

private theorem normalizer_equivariant
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (f : (Module.End (ZMod 2) W)ˣ)
    (hn : f ∈ normalizer (ρ.asGroupHom.range : Set (Module.End (ZMod 2) W)ˣ)) :
    ∃ a : D ≃* D, ∀ g w, f.val (ρ g w) = ρ (a g) (f.val w) := by
  let S := ρ.asGroupHom.range
  let e : D ≃* S := MonoidHom.ofInjective (show Function.Injective ρ.asGroupHom from
    fun x y h => hf (congrArg Units.val h))
  let b := S.normalizerMonoidHom ⟨f,hn⟩
  let a := MulAut.congr e.symm b
  refine ⟨a,?_⟩
  intro g w
  have hb : e (a g) = b (e g) := by simp [a]
  have hh : ρ.asGroupHom (a g) = f * ρ.asGroupHom g * f⁻¹ := congrArg Subtype.val hb
  have hc : f * ρ.asGroupHom g = ρ.asGroupHom (a g) * f :=
    (mul_inv_eq_iff_eq_mul.mp hh.symm)
  exact congrArg (fun u : (Module.End (ZMod 2) W)ˣ => u.val w) hc

private theorem fixed_component_commutes_offender
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (hcore : pCore 2 D = ⊥) (I K : Subgroup D)
    (hI : IsMinimalBestOffender ρ I) (hK : IsComponent D K) (hKI : ⁅K,I⁆ = K)
    (hdim : Module.finrank (ZMod 2) (moved ρ I) ≤ 2)
    (f : (Module.End (ZMod 2) W)ˣ)
    (hn : f ∈ normalizer (ρ.asGroupHom.range : Set (Module.End (ZMod 2) W)ˣ))
    (hfix : ∀ w ∈ moved ρ K, f.val w = w) :
    (∀ i : I, Commute f (ρ.asGroupHom i)) ∧ ∀ w ∈ moved ρ I, f.val w = w := by
  let : IsQuasisimple K := hK.2
  have hKne : K ≠ ⊥ := by
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact (Subgroup.nontrivial_iff_ne_bot _).mp inferInstance
  have hm := hI.moved_le_moved_perfect ρ hf hKne hdim hKI
  have hNU : offenderSubgroup ρ ≤ subspaceStabilizer ρ (moved ρ K) :=
    subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by simp))
      (ChapterB.offenderSubgroup_le_normalizer_component ρ hf hK)
  obtain ⟨a,ha⟩ := normalizer_equivariant ρ hf f hn
  have he := fixed_support_commutes ρ hf hcore I hI.1 (moved ρ K) hNU hm a
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W f) ha hfix
  refine ⟨?_,fun w hw => hfix w (hm hw)⟩
  intro i
  apply Units.ext
  ext w
  change f.val (ρ i w) = ρ i (f.val w)
  rw [ha,he i i.property]

private theorem section_offender_contradiction
    {G D W : Type*} [Group G] [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    {H J U P A : Subgroup G} (hHP : H ≤ P) (hAH : A ≤ H)
    (π : H →* D) (hπ : Function.Surjective π)
    (ρ : Representation (ZMod 2) D W)
    (c : BinaryConjugationSection H J U (ρ.comp π))
    (η : Representation (ZMod 2) P W) (c' : BinaryConjugationSection P J U η)
    (hcoords : c'.coordinates = c.coordinates)
    (hr : ∀ a : H, η (inclusion hHP a) = ρ (π a))
    (d : P) (K : Subgroup D) (hAK : (A.subgroupOf H).map π ≤ K)
    (hc : ∀ k : K, Commute (η.asGroupHom d) (ρ.asGroupHom k))
    (hf : ∀ w ∈ moved ρ K, η d w = w)
    (hclaim : ∀ Q : Subgroup G, A ≤ Q → Q ≤ H →
      (⁅Q,zpowers (d : G)⁆.subgroupOf P).map η.asGroupHom = ⊥ →
      c'.imageSpace ⁅⁅J,Q⁆,zpowers (d : G)⁆ ≠ ⊥) : False := by
  let K0 := K.comap π
  let Q := K0.map H.subtype
  have hQH : Q ≤ H := map_subtype_le _
  have hQP : Q ≤ P := hQH.trans hHP
  have hAQ : A ≤ Q := by
    intro a ha
    exact ⟨⟨a,hAH ha⟩,hAK (mem_map_of_mem π ha),rfl⟩
  have hQsub : Q.subgroupOf H = K0 := by
    change (K0.map H.subtype).comap H.subtype = K0
    rw [comap_map_eq_self_of_injective H.subtype_injective]
  have hKmap : K0.map π = K := by
    exact map_comap_eq_self_of_surjective hπ K
  have hQsubP : Q.subgroupOf P = K0.map (inclusion hHP) := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le hQP,map_map]
    rfl
  have hQimage : (Q.subgroupOf P).map η.asGroupHom = K.map ρ.asGroupHom := by
    rw [hQsubP,map_map]
    have he : η.asGroupHom.comp (inclusion hHP) = ρ.asGroupHom.comp π := by
      apply MonoidHom.ext
      intro a
      exact Units.ext (hr a)
    rw [he,←map_map,hKmap]
  have hDsub : (zpowers (d : G)).subgroupOf P = zpowers d := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le (zpowers_le.mpr d.property),MonoidHom.map_zpowers]
    rfl
  have hcommSub : ⁅Q,zpowers (d : G)⁆.subgroupOf P =
      ⁅Q.subgroupOf P,zpowers d⁆ := by
    apply map_injective P.subtype_injective
    rw [map_subgroupOf_eq_of_le (Subgroup.commutator_le_sup Q _ |>.trans
      (sup_le hQP (zpowers_le.mpr d.property))),map_commutator,
      map_subgroupOf_eq_of_le hQP,MonoidHom.map_zpowers]
    rfl
  have hcomm : (⁅Q,zpowers (d : G)⁆.subgroupOf P).map η.asGroupHom = ⊥ := by
    rw [hcommSub,map_commutator,hQimage,MonoidHom.map_zpowers,commutator_comm]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply zpowers_le.mpr
    rintro _ ⟨k,hk,rfl⟩
    exact (hc ⟨k,hk⟩).eq.symm
  have hself : c.imageSpace J = ⊤ := by
    apply top_unique
    intro w _
    obtain ⟨j,hj⟩ := c.onto (Multiplicative.ofAdd w)
    exact (c.mem_imageSpace_iff _ _).mpr ⟨j,j.property,congrArg Multiplicative.toAdd hj⟩
  have hm : c'.imageSpace ⁅J,Q⁆ = moved ρ K := by
    have he : c'.imageSpace ⁅J,Q⁆ = c.imageSpace ⁅J,Q⁆ := by
      simp only [BinaryConjugationSection.imageSpace,hcoords]
    rw [he,commutator_comm J Q,c.imageSpace_commutator Q J hQH le_rfl,
      hself,subspaceCommutator_comp_map,hQsub,hKmap]
  apply hclaim Q hAQ hQH hcomm
  rw [commutator_comm ⁅J,Q⁆ _,c'.imageSpace_commutator _ _
    (zpowers_le.mpr d.property)
    (le_normalizer_iff_commutator_le_left.mp (hQP.trans c'.normalized)),hm,hDsub]
  apply (subspaceCommutator_eq_bot_iff η _ _).mpr
  intro w hw
  exact (mem_fixedSpace_zpowers_iff η d w).mpr (hf w hw)

private theorem section_cubic_normalizes
    {G D W : Type*} [Group G] [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {H P : Subgroup G} (hHP : H ≤ P)
    (π : H →* D) (hπ : Function.Surjective π)
    (ρ : Representation (ZMod 2) D W) (η : Representation (ZMod 2) P W)
    (hr : ∀ a : H, η (inclusion hHP a) = ρ (π a))
    (d : P) (hd : (d : G) ∈ normalizer (H : Set G)) :
    η.asGroupHom d ∈ normalizer (ρ.asGroupHom.range : Set (Module.End (ZMod 2) W)ˣ) := by
  let f := η.asGroupHom d
  let S := ρ.asGroupHom.range
  let : Finite S := Finite.of_surjective ρ.asGroupHom.rangeRestrict
    ρ.asGroupHom.rangeRestrict_surjective
  have hru (a : H) : η.asGroupHom (inclusion hHP a) = ρ.asGroupHom (π a) :=
    Units.ext (hr a)
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨_,⟨k,rfl⟩,rfl⟩
    obtain ⟨a,rfl⟩ := hπ k
    let b : H := ⟨d * (a : G) * (d : G)⁻¹,(mem_normalizer_iff.mp hd _).mp a.property⟩
    refine ⟨π b,?_⟩
    have he : inclusion hHP b = d * inclusion hHP a * d⁻¹ := Subtype.ext rfl
    change ρ.asGroupHom (π b) = f * ρ.asGroupHom (π a) * f⁻¹
    rw [←hru b,he,map_mul,map_mul,map_inv,hru]
  · rw [card_map_of_injective (MulAut.conj (η.asGroupHom d)).injective]

/-- In the original one-sided configuration, no component moved by the plane
can be PSL₃(2). The original cubic, quotient coordinates and noncentrality
witness are used; containment of the offender in the component is not assumed. -/
theorem one_sided_binary_component_excluded
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hfactor : CentralLineNormalizerFactorization M (ZS (T : Subgroup G) L R))
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N → N = M)
    (g : G)
    (hBA : layer L R ≤ normalizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (layer L R).map (MulAut.conj g).toMonoidHom ≤ centralizer (layer L R : Set G))
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (ρ : Representation (ZMod 2) (action (layer L R)
      (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))).range W)
    (c : BinaryConjugationSection
      (Centralizer (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G)))
      (conjugateSpanBy (layer L R)
        (Centralizer (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))))
      (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))
      (ρ.comp (action (layer L R)
        (layer L R ⊓ centralizer ((layer L R).map (MulAut.conj g).toMonoidHom : Set G))).rangeRestrict))
    (hf : Function.Injective ρ) :
    let B := layer L R
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    let I := (A.subgroupOf (Centralizer U)).map (action B U).rangeRestrict
    IsMinimalBestOffender ρ I →
    ∀ K, IsComponent (action B U).range K → ⁅K,I⁆ = K →
      IsIrrPlus ρ K (moved ρ K) → ¬ Nonempty (K ≃* PSL(3,ZMod 2)) := by
  let B := layer L R
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let H := Centralizer U
  let J := conjugateSpanBy B H
  let P := H ⊔ fieldLocalResidual L U
  let π := (action B U).rangeRestrict
  let I := (A.subgroupOf H).map π
  dsimp only
  intro hI K hK hKI hIrr ⟨eK⟩
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  obtain ⟨hUc,hfield,hout⟩ := local_one_sided_field_plane h hnatural hE hfactor g hBA hnon
  let : IsElementaryAbelian 2 J :=
    local_plane_closure_elementary h hnatural hE hfactor inf_le_left hUc.ge
  obtain ⟨d,hd,ho,hBD,η,c',hcoords,hrestrict,_⟩ := field_plane_cubic_section_action hnat hfield hUc c
  let dP : P := ⟨d,mem_sup_right hd⟩
  let δ := η.asGroupHom dP
  have hcomm := binary_component_cubic_commutes h hnatural hE hfactor hu hfield hUc hout
    K hK eK ρ η hrestrict d hd (ho ▸ pow_orderOf_eq_one d)
  have hfix : ∀ w ∈ moved ρ K, δ.val w = w :=
    binary_irrPlus_centralizer ρ K hIrr eK
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) W δ) (by
        intro k w
        exact congrArg (fun a : (Module.End (ZMod 2) W)ˣ => a.val w) (hcomm k).eq)
  have hnorm : δ ∈ normalizer (ρ.asGroupHom.range : Set (Module.End (ZMod 2) W)ˣ) :=
    section_cubic_normalizes (show H ≤ P from le_sup_left) π (action B U).rangeRestrict_surjective
      ρ η hrestrict dP
      (normalizer_le_normalizer_centralizer U ((map_subtype_le _ hd).2))
  have hdim := (section_plane_geometry h hnatural hE hfactor g hBA hnon ρ c).2.2.1
  obtain ⟨hcI,hfI⟩ := fixed_component_commutes_offender ρ hf
    (action_range_core h hnatural hE hfactor hfield hUc.ge) I K hI hK hKI hdim δ hnorm hfix
  exact section_offender_contradiction (show H ≤ P from le_sup_left)
    (show A ≤ H from le_centralizer_iff.mpr inf_le_right) π (action B U).rangeRestrict_surjective
    ρ c η c' hcoords hrestrict dP I le_rfl hcI hfI
    (local_one_sided_cubic_section_noncentral h hnatural hE hfactor g hBA hnon η c' d hd hBD)

/-- The original marked plane section after excluding the binary linear-three component. -/
@[expose] def PlaneTwoModelSection {G : Type*} [Group G] [Finite G]
    (B A U : Subgroup G) [IsElementaryAbelian 2 (LocalFieldQuotientAction.space B U)] : Prop :=
    let H := LocalFieldQuotientAction.Centralizer U
    let J := conjugateSpanBy B H
    let π := (LocalFieldQuotientAction.action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ (ρ : Representation (ZMod 2) (LocalFieldQuotientAction.action B U).range
        (Additive (LocalFieldQuotientAction.space B U)))
      (c : BinaryConjugationSection H J U (ρ.comp π)),
      Function.Injective ρ ∧ IsOffender ρ I ∧ IsQuadratic ρ I ∧ Nat.card I = 4 ∧
      moved ρ I = c.imageSpace ⁅A,B⁆ ∧ Module.finrank (ZMod 2) (moved ρ I) = 2 ∧
      fixedCodim ρ I = 2 ∧ I ∈ ChapterE.fixedSpaceFamily ρ 2 ∧
      IsMinimalBestOffender ρ I ∧
      (∀ K, IsComponent (LocalFieldQuotientAction.action B U).range K → ⁅K,I⁆ = K →
        IsIrrPlus ρ K (moved ρ K) ∧
          (Nonempty (K ≃* alternatingGroup (Fin 5)) ∨
            Nonempty (K ≃* SL(3,BinaryField.four.Carrier)))) ∧
      ∀ j : J, ∃ hj : (j : G) ∈ H, LocalFieldQuotientAction.projection U ⟨j,hj⟩ =
        ((c.coordinates j).toAdd.toMul : LocalFieldQuotientAction.Ambient U)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.LocalFieldQuotientAction
