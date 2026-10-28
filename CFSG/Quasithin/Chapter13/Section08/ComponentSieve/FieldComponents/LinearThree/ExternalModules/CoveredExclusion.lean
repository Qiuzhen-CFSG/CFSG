module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.SeedTensor
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.TensorReduction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.SaturatedPair
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Excluding the covered-A₆ external component

The actual generating seed supplies a natural tensor chief section under the
same point-parabolic marking as the source geometry. Its faithful action has
no transvections, so 13.8.18(4) makes the marked V-actor fill the point radical.

For a proper U-actor the tensor section has fixed codimension two. The source
critical comparison forces the actual D_H denominator to have index two, and
the order-two actor cannot have all its displacements in the critical line.
This proves the centralizer-lifting premises used to exclude the proper pair.
For a saturated actor the checked reversal argument supplies the contradiction.
Inner conjugation transports the section and both actors together; no graph
twist changes the distinguished point parabolic.

Both exclusions retain the actual U_H/V₁ action and the relative source
normalizers. Group-geometric identifications and exact earlier source clauses
are explicit inputs. This is the covered branch of the representation argument,
not the full containment theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.21(1),
printed p.957, using 13.7.3(7), 13.8.4(5), 13.8.8(2), 13.8.18(4), and F.9.13–16.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter13.Section08
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve
open FieldComponents.LinearThree FieldComponents.LinearThree.ExternalModules
open FieldComponents.LinearThree.ExternalModules.MarkedCritical
open AlternatingAndLinear.FourStructure.CriticalTransfer

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.CoveredExclusion

variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    {H U Z : Subgroup G} {ρ : Representation (ZMod 2) (Source.Hstar H) W}

omit [Finite G] [FiniteDimensional (ZMod 2) W] in
private theorem image_sup_line (s : ConjugationSection H U Z ρ)
    (A : Subgroup G) (hAH : A ≤ H) : s.image (A ⊔ Z) = s.image A := by
  have hZH : Z ≤ H := s.line_le.trans s.le
  let : (Z.subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hZH).mpr
      (s.centralizes.trans (Subgroup.centralizer_le_normalizer _))
  apply le_antisymm _ (s.image_mono le_sup_left)
  rintro v ⟨u, hu, rfl⟩
  have hu' : (⟨u.val, s.le u.property⟩ : H) ∈ A.subgroupOf H ⊔ Z.subgroupOf H := by
    rw [← subgroupOf_sup hAH hZH]
    exact hu
  obtain ⟨a, ha, z, hz, he⟩ := mem_sup_of_normal_right.mp hu'
  have hau : (a : G) ∈ U := by
    have he' : (a : G) = (u : G) * (z : G)⁻¹ := by
      have := congrArg Subtype.val he
      exact eq_mul_inv_of_mul_eq this
    rw [he']
    exact U.mul_mem u.property (U.inv_mem (s.line_le hz))
  refine ⟨⟨a, hau⟩, ha, ?_⟩
  have he' : u = (⟨a, hau⟩ : U) * ⟨z, s.line_le hz⟩ :=
    Subtype.ext (congrArg Subtype.val he).symm
  rw [he', map_mul]
  have hz' : s.quotient ⟨z, s.line_le hz⟩ = 1 := by
    change (⟨z, s.line_le hz⟩ : U) ∈ s.quotient.ker
    rw [s.kernel]
    exact hz
  rw [hz', mul_one]
  rfl

private theorem cyclic_of_card_two {J : Type*} [Group J] [Finite J]
    (A : Subgroup J) (hA : Nat.card A = 2) : ∃ a, A = zpowers a := by
  have hn : A ≠ ⊥ := by intro he; simp [he] at hA
  have hex : ∃ a ∈ A, a ≠ 1 := by
    by_contra! hh
    exact hn (bot_unique (fun a ha => hh a ha))
  obtain ⟨a, ha, ha1⟩ := hex
  refine ⟨a, (eq_of_le_of_card_ge (zpowers_le.mpr ha) ?_).symm⟩
  have hz : zpowers a ≠ ⊥ := by simpa using ha1
  have hc := (zpowers a).one_lt_card_iff_ne_bot.mpr hz
  omega

private theorem cyclic_codim_le_one (s : ConjugationSection H U Z ρ)
    (A B : Subgroup G) (hBH : B ≤ H) (hB : Nat.card B = 2)
    (hA : Nat.card (Source.starImage H A) = 2)
    (hc : ⁅U,A⁆ ≤ B ⊔ Z) : fixedCodim ρ (Source.starImage H A) ≤ 1 := by
  obtain ⟨a, ha⟩ := cyclic_of_card_two (Source.starImage H A) hA
  have haA : a ∈ Source.starImage H A := ha ▸ mem_zpowers a
  have hr : LinearMap.range (ρ a - LinearMap.id) ≤ s.image B := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨u, hu⟩ := s.surjective (Multiplicative.ofAdd v)
    have hv : v ∈ s.image U := ⟨u, u.property, congrArg Multiplicative.toAdd hu⟩
    have hd := s.displacement_mem U A (B ⊔ Z) (by rwa [commutator_comm]) a haA v hv
    rwa [image_sup_line s B hBH] at hd
  rw [ha, fixedCodim_zpowers_eq_displacement_rank]
  have hd := s.image_finrank_le B
  rw [hB] at hd
  exact (Submodule.finrank_mono hr).trans (by simpa only [show Nat.log 2 2 = 1 from by decide] using hd)

omit [Finite G] in
private theorem index_eq_pow (s : ConjugationSection H U Z ρ)
    (D : Subgroup G) (hZD : Z ≤ D) :
    D.relIndex U = 2 ^ Module.finrank (ZMod 2) (W ⧸ s.image D) := by
  let q : U →* Multiplicative (W ⧸ s.image D) :=
    (s.image D).mkQ.toAddMonoidHom.toMultiplicative.comp s.quotient
  have hq : Function.Surjective q := by
    intro u
    obtain ⟨v, hv⟩ := (s.image D).mkQ_surjective u.toAdd
    obtain ⟨x, hx⟩ := s.surjective (Multiplicative.ofAdd v)
    exact ⟨x, by change (s.image D).mkQ (s.quotient x).toAdd = u.toAdd; rw [hx]; exact hv⟩
  have hk : q.ker = D.subgroupOf U := by
    ext x
    change (s.image D).mkQ (s.quotient x).toAdd = 0 ↔ (x : G) ∈ D
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact s.quotient_mem_image_iff D hZD x
  have hc : D.relIndex U = Nat.card (W ⧸ s.image D) := by
    change (D.subgroupOf U).index = _
    rw [← hk, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hq,
      Nat.card_congr (Subgroup.topEquiv).toEquiv]
    rfl
  rw [hc, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]


private theorem faithful_of_natural_section
    {J E : Type*} [Group J] [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) J E) (L N : Subrepresentation σ)
    (eJ : J ≃* TensorGroup)
    (e : (sectionRepresentation σ L N).Equiv (naturalTensor.comp eJ.toMonoidHom)) :
    Function.Injective σ := by
  intro a b hab
  apply eJ.injective
  apply TensorFacts.naturalTensor_faithful
  apply LinearMap.ext
  intro w
  obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
  have he (c : J) (v) : e.toLinearEquiv (sectionRepresentation σ L N c v) =
      naturalTensor (eJ c) (e.toLinearEquiv v) :=
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap c v
  rw [← he a v, ← he b v]
  congr 1
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change sectionRepresentation σ L N a ((sectionLower σ L N).toSubmodule.mkQ v) =
      sectionRepresentation σ L N b ((sectionLower σ L N).toSubmodule.mkQ v)
    rw [sectionRepresentation_mk, sectionRepresentation_mk]
    apply congrArg (sectionLower σ L N).toSubmodule.mkQ
    exact Subtype.ext (LinearMap.congr_fun hab v.val)

private theorem natural_section_inner_marking
    {J E : Type*} [Group J] [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) J E) (eJ : J ≃* TensorGroup)
    (L N : Subrepresentation ρ) (hc : IsNaturalTensorChiefSection ρ eJ L N) (h : J) :
    IsNaturalTensorChiefSection ρ ((MulAut.conj h).trans eJ) L N := by
  obtain ⟨hLN, ⟨e⟩⟩ := hc
  let σ := sectionRepresentation ρ L N
  let f : _ ≃ₗ[ZMod 2] _ :=
    { toLinearMap := σ h
      invFun := σ h⁻¹
      left_inv := fun v => by
        change σ h⁻¹ (σ h v) = v
        simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
          Module.End.one_apply]
      right_inv := fun v => by
        change σ h (σ h⁻¹ v) = v
        simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply] }
  refine ⟨hLN, ⟨{ toLinearEquiv := f.trans e.toLinearEquiv, isIntertwining' := ?_ }⟩⟩
  intro a
  apply LinearMap.ext
  intro v
  change e (σ h (σ a v)) = naturalTensor (eJ (h * a * h⁻¹)) (e (σ h v))
  have he (b : J) (w) : e (σ b w) = naturalTensor (eJ b) (e w) :=
    Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap b w
  rw [← he]
  simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]

variable (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsMulCommutative (Source.Utilde H V₃ V₁)]
    [Module (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]

private def sourceSection (act : SourceAction H V₃ V₁)
    (hc : H ≤ centralizer (V₁ : Set G)) :
    ConjugationSection H (Source.UH H V₃) V₁ act.representation where
  le := conjugateSpanBy_le_self act.seed_le
  normalizes := le_normalizer_conjugateSpanBy V₃ H
  centralizes := hc
  line_le := act.line_le
  quotient := quotientMap H V₃ V₁
  surjective := QuotientGroup.mk'_surjective _
  kernel := QuotientGroup.ker_mk' _
  conjugates := act.conjugation

/-- The proper marked pair is excluded from the actual critical index
comparison and offender bound. Its index-two denominator and the non-line-valued
moved space are proved here; neither is an additional source hypothesis. -/
theorem source_proper_pair_false_of_indices
    [FiniteDimensional (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    (act : SourceAction H V₃ V₁) (eH : Source.Hstar H ≃* TensorGroup)
    (L N : Subrepresentation act.representation)
    (hchief : IsNaturalTensorChiefSection act.representation eH L N)
    (hc : H ≤ centralizer (V₁ : Set G))
    (A B Z : Subgroup G) (hAH : A ≤ H) (hZH : Z ≤ H)
    (hnZ : Source.UH H V₃ ≤ normalizer (Z : Set G))
    (hdis : Disjoint V₁ Z) (hZ : Nat.card Z = 2)
    (hA0 : Source.starImage H A ≠ ⊥)
    (hproper : (Source.starImage H A).map eH.toMonoidHom < tensorPointRadical)
    (hBmark : (Source.starImage H B).map eH.toMonoidHom = tensorPointRadical)
    (hsmall : fixedCodim act.representation (Source.starImage H A) ≤
      2 * rank (Source.starImage H A))
    (hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃) A Z).relIndex (Source.UH H V₃)) ≤
      Nat.log 2 ((Source.Dgamma A (Source.UH H V₃) V₁).relIndex A))
    (hbound : ⁅Source.UH H V₃ ⊓ centralizer (A : Set G), B⁆ ≤ Z) : False := by
  obtain ⟨e⟩ := hchief.2
  let s := sourceSection H V₃ V₁ act hc
  let R := (Source.starImage H A).map eH.toMonoidHom
  have hR0 : R ≠ ⊥ := fun he => hA0
    ((Subgroup.map_eq_bot_iff_of_injective _ eH.injective).mp he)
  have hcard : Nat.card (Source.starImage H A) = 2 := by
    rw [← Subgroup.card_map_of_injective (f := eH.toMonoidHom) eH.injective]
    exact TensorFacts.card_proper_radical R hproper hR0
  have hrank : rank (Source.starImage H A) = 1 := by
    change Nat.log 2 (Nat.card (Source.starImage H A)) = 1
    rw [hcard]
    decide
  have hsection : fixedCodim (sectionRepresentation act.representation L N)
      (Source.starImage H A) = 2 := by
    rw [fixedCodim_map_equivariant _ naturalTensor eH.toMonoidHom
      e.toLinearEquiv e.toIntertwiningMap.isIntertwining]
    exact TensorFacts.fixedCodim_proper_radical R hproper hR0
  have hlower : 2 ≤ fixedCodim act.representation (Source.starImage H A) :=
    hsection.symm.le.trans (fixedCodim_section_le act.representation L N _)
  have hmoved : ¬ ⁅Source.UH H V₃,A⁆ ≤ Z ⊔ V₁ := by
    intro hh
    have hu := cyclic_codim_le_one s A Z hZH hZ hcard hh
    omega
  have hdim := s.critical_bound A Z hAH
    (faithful_of_natural_section act.representation L N eH e) hcritical
  rw [hrank] at hdim
  have hp := index_eq_pow s (Source.DH (Source.UH H V₃) A Z) (s.line_le_DH A Z hAH)
  have hdim0 : Module.finrank (ZMod 2)
      (Additive (Source.Utilde H V₃ V₁) ⧸ s.image (Source.DH (Source.UH H V₃) A Z)) ≠ 0 := by
    intro hz
    rw [hz, pow_zero] at hp
    apply hmoved
    exact ((commutator_mono (relIndex_eq_one.mp hp) le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hnZ)).trans le_sup_left
  have hdim1 : Module.finrank (ZMod 2)
      (Additive (Source.Utilde H V₃ V₁) ⧸ s.image (Source.DH (Source.UH H V₃) A Z)) = 1 := by omega
  have hindex : (Source.DH (Source.UH H V₃) A Z).relIndex (Source.UH H V₃) = 2 := by
    rw [hp, hdim1, pow_one]
  exact source_proper_pair_false H V₃ V₁ act eH L N hchief A B Z R hAH hindex
    hnZ (s.le.trans (hc.trans (Subgroup.centralizer_le_normalizer _)))
    hmoved hdis (by simpa only [hrank, mul_one] using hsmall) hbound hZ rfl hproper hR0 hBmark


/-- The covered-A₆ external-component configuration is impossible. The actual
generating seed constructs a natural tensor chief section in the supplied
point marking. The model discharges the no-transvection premise of 13.8.18(4),
so the marked V-actor fills the point radical. The proper and saturated U-actor
cases are then both excluded using the actual critical pair.

The compatible product and parabolic images are geometric inputs. The other
premises are the source seed clauses, 13.7.3(7), 13.8.4(5), the critical actor
and index comparison from 13.8.8(2), F.9.13, and the exact implication 13.8.18(4).
No tensor section, rank-one conclusion, faithfulness or contradiction is assumed.
This conditional representation exclusion is not the full L₁-containment theorem. -/
theorem source_covered_configuration_exclusion
    [FiniteDimensional (ZMod 2) (Additive (Source.Utilde H V₃ V₁))]
    (act : SourceAction H V₃ V₁)
    (K L₀ X L₁ T V : Subgroup G) (g : G) (h : H)
    (eH : Source.Hstar H ≃* TensorGroup)
    (hV : V ≤ H) (hflag : V₃ ≤ V) (hflag_index : V₃.relIndex V = 2)
    (hline : V₁ ≤ V₃) (hcard : Nat.card V₁ = 2)
    (hcentral : H ≤ centralizer (V₁ : Set G))
    (hL₀ : L₀ ≤ L₁) (hX : X ≤ L₁)
    (hL₀mark : (Source.starImage H L₀).map eH.toMonoidHom ≤
      (⊤ : Subgroup BinaryLinearThree.Group).prod ⊥)
    (hXmark : (Source.starImage H X).map eH.toMonoidHom ≤
      (⊥ : Subgroup BinaryLinearThree.Group).prod ⊤)
    (hL₀seed : ⁅L₀,V₃⁆ ≤ V₁) (hXseed : V₃ ≤ ⁅X,V₃⁆ ⊔ V₁)
    (hPH : L₁ ⊔ T ≤ H) (hH : H = K ⊔ (L₁ ⊔ T))
    (hK : (K.subgroupOf H).Normal) (hres : pResidual 2 (K.subgroupOf H) = ⊤)
    (hqs : Theory.GroupTheory.IsQuasisimple (Source.starImage H K))
    (hseed : ⁅L₁ ⊔ T,V⁆ ≤ Source.UH H V₃)
    (hnoncentral : ¬ ⁅Source.VH H V,H⁆ ≤ Source.UH H V₃)
    (hforward : (Source.VH H V).map (MulAut.conj g).toMonoidHom ≤ H)
    (hback : Source.VH H V ≤ ((L₁ ⊔ T).pCoreIn 2).map (MulAut.conj g).toMonoidHom)
    (hplace : ((Source.VH H V).map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj (h:G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2)
    (hcentralizer : ⁅Source.HC H V₃,Source.VH H V⁆ ≤ V₁)
    (hdisjoint : Disjoint V₁ (V₁.map (MulAut.conj g).toMonoidHom))
    (hseed_noncentral : ¬ ⁅(Source.UH H V₃).map (MulAut.conj g).toMonoidHom,V⁆ ≤
      V₁.map (MulAut.conj g).toMonoidHom)
    (hcommute : ⁅Source.DH (Source.UH H V₃)
        ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
        (V₁.map (MulAut.conj g).toMonoidHom),
      Source.Dgamma ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
        (Source.UH H V₃) V₁⁆ = ⊥)
    (hparabolic_group : (Source.starImage H (L₁ ⊔ T)).map eH.toMonoidHom =
      Matrix.PSL3Two.pointParabolicSL.prod ⊤)
    (hline_commutators :
      ⁅(Source.UH H V₃).map (MulAut.conj g).toMonoidHom,
        Source.EH (Source.VH H V) ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
          (V₁.map (MulAut.conj g).toMonoidHom)⁆ ≤ V₁.map (MulAut.conj g).toMonoidHom ∧
      ⁅Source.UH H V₃, Source.Egamma ((Source.VH H V).map (MulAut.conj g).toMonoidHom)
        (Source.UH H V₃) V₁⁆ ≤ V₁)
    (hparabolic : (Source.starImage H ((L₁ ⊔ T).pCoreIn 2)).map
      eH.toMonoidHom = tensorPointRadical)
    (hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃)
        ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
        (V₁.map (MulAut.conj g).toMonoidHom)).relIndex (Source.UH H V₃)) ≤
      Nat.log 2 ((Source.Dgamma ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)
        (Source.UH H V₃) V₁).relIndex ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)))
    (hKmark : (Source.starImage H K).map eH.toMonoidHom =
      (⊤ : Subgroup BinaryLinearThree.Group).prod ⊥)
    (hn : ∃ k : Source.starImage H K, ∃ v, act.representation k v ≠ v)
    (hP : L₁ ⊔ T ≤ normalizer (V₃ : Set G))
    (hXcubic : tensorCubic.map eH.symm.toMonoidHom = Source.starImage H X)
    (hd : Module.finrank (ZMod 2) (Geometry.seedSpace H V₃ V₁) = 2)
    (hactor : IsElementaryTwo
        (Source.starImage H ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)) ∧
      IsQuadratic act.representation
        (Source.starImage H ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)) ∧
      fixedCodim act.representation
          (Source.starImage H ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)) ≤
        2 * rank (Source.starImage H ((Source.UH H V₃).map (MulAut.conj g).toMonoidHom)))
    (hlarge : (∀ a : Source.Hstar H,
        fixedCodim act.representation (zpowers a) ≠ 1) →
      1 < rank (Source.starImage H ((Source.VH H V).map (MulAut.conj g).toMonoidHom))) :
    False := by
  obtain ⟨L, N, hchief⟩ := source_natural_tensor_chief_section H V₃ V₁ act eH
    K L₁ T L₀ X hKmark hn hP ((hX.trans le_sup_left).trans hPH)
    (hX.trans le_sup_left) hparabolic_group hXcubic hd hL₀seed hXseed
  let U := Source.UH H V₃
  let Ug := U.map (MulAut.conj g).toMonoidHom
  let Vg := (Source.VH H V).map (MulAut.conj g).toMonoidHom
  let A₁ := V₁.map (MulAut.conj g).toMonoidHom
  let Vα := Vg.map (MulAut.conj (h : G)).toMonoidHom
  have hUV : U ≤ Source.VH H V := conjugateSpanBy_mono hflag le_rfl
  have hUgVg : Ug ≤ Vg := map_mono hUV
  have hUgH : Ug ≤ H := hUgVg.trans hforward
  have hreverse : U ≤ H.map (MulAut.conj g).toMonoidHom :=
    hUV.trans (hback.trans (map_mono ((pCoreIn_le 2 (L₁ ⊔ T)).trans hPH)))
  have hVαle : (Source.starImage H Vα).map eH.toMonoidHom ≤ tensorPointRadical := by
    rw [← hparabolic]
    exact map_mono (map_mono (comap_mono hplace))
  have hVαmark : (Source.starImage H Vα).map eH.toMonoidHom = tensorPointRadical := by
    apply source_natural_tensor_critical_image_eq_radical H V₃ V₁ act eH L N hchief Vα hVαle
    intro ht
    change 1 < rank (Source.starImage H (Vg.map (MulAut.conj (h : G)).toMonoidHom))
    rw [Seven.LocalGeometry.starImage_conjugate H Vg hforward h, rank_map_conj]
    exact hlarge ht
  by_cases hsat : Source.starImage H Ug = Source.starImage H Vg
  · exact SaturatedPair.source_saturated_pair_false H V₃ V₁ act K L₀ X L₁ T V g h eH
      L N hchief TensorFacts.naturalTensor_faithful TensorFacts.fixedCodim_radical
      hV hflag hflag_index hline hcard hcentral hL₀ hX hL₀mark hXmark hL₀seed hXseed
      hPH hH hK hres hqs hseed hnoncentral hforward hback hplace hcentralizer
      hdisjoint hseed_noncentral hcommute hparabolic_group hline_commutators
      hparabolic hcritical hVαmark hsat
  · let eA := (MulAut.conj (QuotientGroup.mk' (pCore 2 H) h)).trans eH
    have hBmark : (Source.starImage H Vg).map eA.toMonoidHom = tensorPointRadical := by
      change (Source.starImage H Vg).map
        (eH.toMonoidHom.comp (MulAut.conj _).toMonoidHom) = _
      rw [← Subgroup.map_map, ← Seven.LocalGeometry.starImage_conjugate H Vg hforward h]
      exact hVαmark
    have hproper : (Source.starImage H Ug).map eA.toMonoidHom < tensorPointRadical := by
      apply lt_of_le_of_ne
      · rw [← hBmark]
        exact map_mono (map_mono (comap_mono hUgVg))
      · intro he
        apply hsat
        exact Subgroup.map_injective eA.injective (he.trans hBmark.symm)
    let s := sourceSection H V₃ V₁ act hcentral
    apply source_proper_pair_false_of_indices H V₃ V₁ act eA L N
      (natural_section_inner_marking act.representation eH L N hchief _) hcentral
      Ug Vg A₁ hUgH ((map_mono act.line_le).trans hUgH)
      (hreverse.trans ((s.centralizes_conjugate_line g).trans
        (Subgroup.centralizer_le_normalizer _))) hdisjoint
      (by rw [card_map_of_injective (MulAut.conj g).injective, hcard])
      hactor.1.1 hproper hBmark hactor.2.2 hcritical
    exact conjugate_centralizer_bound H V₃ V₁ V g hreverse hcentralizer

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.CoveredExclusion
