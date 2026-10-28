module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearFixedFree
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.LinearFixedLine
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FixedLineOrbits
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FixedLineOrbitsAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ComponentFixedFreeAt

/-!
# Guarded full movement of the original linear omega module

The fixed line gives the literal parabolic permutation quotient. Its
whole fixed-free action is dual natural or the Fano core, hence fully
moved. Apply both orientations and the proved orbit sum to obtain full
movement of the original omega module by its actual linear component.
Source: Aschbacher--Smith 13.4.7(1ii),(2), printed pp.901--902.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open BinaryLinearThree.FanoDecomposition Representation.BinaryOffender
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The second fixed line supplies an actual moved generator and the literal
coset permutation quotient of its orbit module. The opposite orientation
follows by interchanging the two original vertices. -/
theorem original_pair_fixed_line_permutation_quotient_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (L : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂) :
    let X := A ⊔ B
    let F := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)
    let U := conjugateSpanBy F X
    ∃ he : IsElementaryAbelian 2 U,
      let := he
      let actor := U.normalizerMonoidHom.comp
        (inclusion (le_normalizer_conjugateSpanBy F X))
      let ρ := Representation.elementaryRepresentation (p := 2) actor
      1 < Module.finrank (ZMod 2) (Additive U) ∧
      Module.finrank (ZMod 2) (Additive U) ≤ B.relIndex X ∧
      ∃ v : F, v ≠ 1 ∧ v.val ∉ centralizer (A : Set G) ∧
      ∃ f : ((X ⧸ B.subgroupOf X) →₀ ZMod 2) →ₗ[ZMod 2] Additive U,
        Function.Surjective f ∧
        (∀ g : X, f (Finsupp.single (QuotientGroup.mk g) 1) =
          ρ g (Additive.ofMul (inclusion (le_conjugateSpanBy F X) v))) ∧
        (∀ (g : X) x, f (Finsupp.lmapDomain (ZMod 2) (ZMod 2)
          (fun q : X ⧸ B.subgroupOf X => g • q) x) = ρ g (f x)) := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let F := Z ⊓ centralizer (B : Set G)
  let W := conjugateSpanBy Z X
  let U := conjugateSpanBy F X
  have hd := pair_fixed_subgroups_ne hTA hTB eA eB hne hres
  obtain ⟨_,_,hF,hi,_,_⟩ := original_pair_fixed_lines_at h structural D m hout
    hindexL hindexA hindexB hd
  have hWX : W ≤ X := conjugateSpanBy_le (fun z hz =>
    (hTA.trans le_sup_left) ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hr := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  let : IsElementaryAbelian 2 (W.subgroupOf X) := hr.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hWX).symm.toMonoidHom (subgroupOfEquivOfLe hWX).symm.injective
  let he : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (inclusion (conjugateSpanBy_mono (show F ≤ Z from inf_le_left) le_rfl))
    (inclusion_injective _)
  obtain ⟨v,hv,_⟩ := (Nat.card_eq_two_iff' (1 : F)).mp hF
  have hmove : v.val ∉ centralizer (A : Set G) := by
    intro hc
    have hvb : v.val ∈ (⊥ : Subgroup G) := hi ▸ ⟨⟨v.property.1,hc⟩,v.property⟩
    exact hv (Subtype.ext hvb)
  let := he
  have hlower := Representation.one_lt_finrank_conjugateLine F X hF (by
    intro hh
    exact hmove (centralizer_le (show A ≤ X from le_sup_left) (hh v.property)))
  obtain ⟨f,hf,hm,heq⟩ :=
    Representation.exists_conjugateLine_coset_map F X B inf_le_right hF v hv
  have hupper : Module.finrank (ZMod 2) (Additive U) ≤ B.relIndex X := by
    let := Fintype.ofFinite (X ⧸ B.subgroupOf X)
    have hh := LinearMap.finrank_le_finrank_of_surjective hf
    simpa only [Module.finrank_finsupp_self,relIndex,index_eq_card,Nat.card_eq_fintype_card] using hh
  exact ⟨he,hlower,hupper,v,hv,hmove,f,hf,hm,heq⟩

/-- In the linear component case, the original second fixed line has a
faithful Fano permutation quotient and a dual-natural head. -/
theorem original_pair_linear_fixed_line_quotient_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL) :
    let C := K.map (A ⊔ B).subtype
    let F := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)
    let U := conjugateSpanBy F C
    ∃ he : IsElementaryAbelian 2 U, let := he
      let ρ := Representation.elementaryRepresentation (p := 2)
        (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F C)))
      (Module.finrank (ZMod 2) (Additive U) = 3 ∨
        Module.finrank (ZMod 2) (Additive U) = 4 ∨
        Module.finrank (ZMod 2) (Additive U) = 6 ∨
        Module.finrank (ZMod 2) (Additive U) = 7) ∧
      C ⊓ centralizer (U : Set G) = C.pCoreIn 2 ∧
      ∃ e : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group,
        let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
        (B.subgroupOf C).map f = Matrix.PSL3Two.lineParabolicSL ∧
        ((T : Subgroup G).subgroupOf C).map f = Matrix.PSL3Two.borelSL ∧
        (∃ q : Representation.IntertwiningMap
          (BinaryLinearThree.FanoLineQuotients.lineRepresentation.comp f) ρ,
          Function.Surjective q ∧
          (BinaryLinearThree.FanoLineMoved.coreMap f ρ q).range.toSubmodule =
            Representation.BinaryOffender.subspaceCommutator ρ ⊤ ⊤ ∧
          (Nonempty (Representation.Equiv (BinaryLinearThree.W.dual.comp f)
              (BinaryLinearThree.FanoLineMoved.coreMap f ρ q).range.toRepresentation) ∨
            Nonempty (Representation.Equiv (lineCoreRepresentation.comp f)
              (BinaryLinearThree.FanoLineMoved.coreMap f ρ q).range.toRepresentation))) ∧
        (∃ r : ρ.IntertwiningMap (BinaryLinearThree.W.dual.comp f), Function.Surjective r) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let F := Z ⊓ centralizer (B : Set G)
  let U := conjugateSpanBy F C
  obtain ⟨heX,_,_,v,hv,hm,_,_,_,_⟩ := original_pair_fixed_line_permutation_quotient_at
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
  let := heX
  let he : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (inclusion (conjugateSpanBy_mono le_rfl (map_subtype_le K))) (inclusion_injective _)
  let := he
  have hd := pair_fixed_subgroups_ne hTA hTB eA eB hne hres
  have hF : Nat.card F = 2 := (original_pair_fixed_lines_at h structural D m hout
    hindexL hindexA hindexB hd).2.2.1
  have hgen := (original_pair_component_is_residual h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).2
  have hmove : ¬ F ≤ centralizer (C : Set G) := by
    intro hh
    have hCX : X ≤ centralizer ({v.val} : Set G) := by
      change A ⊔ B ≤ _
      rw [hgen]
      refine sup_le (fun c hc => mem_centralizer_singleton_iff.mpr (hh v.property c hc)) ?_
      intro t ht
      exact mem_centralizer_singleton_iff.mpr
        (((mem_omegaOneCenterAmbient_iff _ _).mp v.property.1).2.2 t ht)
    exact hm (fun a ha => mem_centralizer_singleton_iff.mp (hCX ((show A ≤ X from le_sup_left) ha)))
  have hlower := Representation.one_lt_finrank_conjugateLine F C hF hmove
  obtain ⟨S,hS,hi⟩ := original_pair_linear_parabolic h₀ D m h1332 hTA hTB eA eB hne
    hindexA hindexB K hK eK
  let actor := U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F C))
  let ρ := Representation.elementaryRepresentation (p := 2) actor
  let w := inclusion (le_conjugateSpanBy F C) v
  have hw (a : B.subgroupOf C) : ρ a (Additive.ofMul w) = Additive.ofMul w := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (v.property.2 a.val.val a.property)
  have hs : Submodule.span (ZMod 2) (Set.range (fun c : C => ρ c (Additive.ofMul w))) = ⊤ := by
    apply Representation.conjugateSpan_binary_orbit_span F C U (le_conjugateSpanBy F C) rfl
      (MonoidHom.id U) Function.surjective_id actor
    · intro c x hx
      rfl
    · intro a
      obtain ⟨b,hb,huniq⟩ := (Nat.card_eq_two_iff' (1 : F)).mp hF
      by_cases ha : a = 1
      · exact Or.inl (by simp [ha])
      · exact Or.inr (congrArg (inclusion (le_conjugateSpanBy F C))
          ((huniq a ha).trans (huniq v hv).symm))
  obtain ⟨hd,hker,e,hP,hSb,hq,hr⟩ := BinaryLinearThree.FixedParabolicQuotient.quotient_and_head
    eK S (B.subgroupOf C) (by rw [hS]; exact fun _ ht => hTB ht) hi ρ
    (Additive.ofMul w) hw hs hlower
  rw [hS] at hSb
  have hkerC : ρ.ker = (centralizer (U : Set G)).subgroupOf C := by
    ext c
    change ρ c = 1 ↔ c.val ∈ centralizer (U : Set G)
    constructor
    · intro hc u hu
      have hh := congrArg (fun x : Additive U => x.toMul.val)
        (LinearMap.congr_fun hc (Additive.ofMul ⟨u,hu⟩))
      change c.val * u * c.val⁻¹ = u at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hc
      apply LinearMap.ext
      intro u
      apply Additive.toMul.injective
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hc u.toMul u.toMul.property).symm
  have hcentral := congrArg (Subgroup.map C.subtype) (hkerC.symm.trans hker)
  rw [subgroupOf_map_subtype,inf_comm] at hcentral
  exact ⟨he,hd,hcentral,e,hP,hSb,hq,hr⟩

/-- The original fixed-line orbit is fully moved, and its whole action is
actually dual natural or the Fano core under the same parabolic/Sylow marking. -/
theorem original_pair_linear_fixed_line_models_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL) :
    let C := K.map (A ⊔ B).subtype
    let F := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)
    let U := conjugateSpanBy F C
    ⁅U,C⁆ = U ∧ ∃ he : IsElementaryAbelian 2 U, let := he
      let ρ := Representation.elementaryRepresentation (p := 2)
        (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F C)))
      (Module.finrank (ZMod 2) (Additive U) = 3 ∨
        Module.finrank (ZMod 2) (Additive U) = 6) ∧
      ∃ e : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group,
        let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
        (A.subgroupOf C).map f = Matrix.PSL3Two.pointParabolicSL ∧
        (B.subgroupOf C).map f = Matrix.PSL3Two.lineParabolicSL ∧
        ((T : Subgroup G).subgroupOf C).map f = Matrix.PSL3Two.borelSL ∧
        (Nonempty (Representation.Equiv (BinaryLinearThree.W.dual.comp f) ρ) ∨
          Nonempty (Representation.Equiv (lineCoreRepresentation.comp f) ρ)) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let F := Z ⊓ centralizer (B : Set G)
  let U := conjugateSpanBy F C
  obtain ⟨he,hd,_,e,hP,hS,⟨q,hq,_,_⟩,_⟩ := original_pair_linear_fixed_line_quotient_at
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK
  let := he
  let ρ := Representation.elementaryRepresentation (p := 2)
    (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F C)))
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hfree := original_pair_component_fixed_free_at h₀ h structural D m
    hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK
  have hUW : U ≤ conjugateSpanBy Z X :=
    conjugateSpanBy_mono inf_le_left (map_subtype_le K)
  have hfixed (v : Additive U) (hv : ∀ c : C, ρ c v = v) : v = 0 := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply hfree.le
    refine ⟨hUW v.toMul.property,?_⟩
    intro c hc
    have hh := congrArg (fun x : Additive U => x.toMul.val) (hv ⟨c,hc⟩)
    change c * v.toMul.val * c⁻¹ = v.toMul.val at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  change Module.finrank (ZMod 2) (Additive U) = 3 ∨
    Module.finrank (ZMod 2) (Additive U) = 4 ∨
    Module.finrank (ZMod 2) (Additive U) = 6 ∨
    Module.finrank (ZMod 2) (Additive U) = 7 at hd
  obtain ⟨_,hm,hmodels,hdim⟩ := BinaryLinearThree.FanoFixedFreeQuotient.whole_models
    f hf ρ q hq (by rcases hd with hd | hd | hd | hd <;> omega) hfixed
  have hA := original_pair_linear_companion_image h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK eK e hP hS
  exact ⟨group_commutator_eq_of_elementary_moved U C
    (le_normalizer_conjugateSpanBy F C) hm,he,hdim,e,hA,hP,hS,hmodels⟩
/-- The complete original omega module is its commutator with the actual linear component. -/
theorem original_pair_linear_whole_moved_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL) :
    let C := K.map (A ⊔ B).subtype
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B)
    ⁅U,C⁆ = U := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let F₁ := Z ⊓ centralizer (A : Set G)
  let F₂ := Z ⊓ centralizer (B : Set G)
  let U₁ := conjugateSpanBy F₁ C
  let U₂ := conjugateSpanBy F₂ C
  let U := conjugateSpanBy Z X
  have hm₂ : ⁅U₂,C⁆ = U₂ := (original_pair_linear_fixed_line_models_at h₀ h structural
    D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK eK).1
  have hm₁ : ⁅U₁,C⁆ = U₁ := by
    have aux := fun (J : Subgroup (B ⊔ A : Subgroup G)) (hJ : J.IsCComponent)
      (eJ : ((J.map (B ⊔ A).subtype) ⧸ pCore 2 (J.map (B ⊔ A).subtype)) ≃*
        Matrix.PSL3Two.PSL) =>
      (original_pair_linear_fixed_line_models_at h₀ h structural D m hTB hTA eB eA hne.symm
        (by simpa only [sup_comm B A] using hout) hindexL hindexB hindexA
        (by dsimp only; rw [sup_comm B A]; exact Or.symm hres) h1332 J hJ eJ).1
    have aux' : ∀ (J : Subgroup (A ⊔ B : Subgroup G)) (hJ : J.IsCComponent)
      (eJ : ((J.map (A ⊔ B).subtype) ⧸ pCore 2 (J.map (A ⊔ B).subtype)) ≃*
        Matrix.PSL3Two.PSL),
      ⁅conjugateSpanBy F₁ (J.map (A ⊔ B).subtype),J.map (A ⊔ B).subtype⁆ =
        conjugateSpanBy F₁ (J.map (A ⊔ B).subtype) := by
      rw [sup_comm B A] at aux
      exact aux
    exact aux' K hK eK
  have hs : U = U₁ ⊔ U₂ := original_pair_component_fixed_line_spans_at h₀ h structural
    D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 K hK
  change ⁅U,C⁆ = U
  apply le_antisymm
  · exact le_normalizer_iff_commutator_le_left.mp
      ((map_subtype_le K).trans (le_normalizer_conjugateSpanBy Z X))
  · rw [hs]
    apply sup_le
    · calc
        U₁ = ⁅U₁,C⁆ := hm₁.symm
        _ ≤ ⁅U₁ ⊔ U₂,C⁆ := commutator_mono le_sup_left le_rfl
    · calc
        U₂ = ⁅U₂,C⁆ := hm₂.symm
        _ ≤ ⁅U₁ ⊔ U₂,C⁆ := commutator_mono le_sup_right le_rfl

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
