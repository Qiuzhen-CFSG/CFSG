module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.ConstituentRecognition

/-!
# Natural constituents with the original MS quotient marking

For C_Q(K)=1, the natural faithful image of every Irr⁺ central-omega
constituent lifts to coordinates on the entire constituent. The original
covering kernel is a normal two-group, so it acts trivially on the
irreducible central quotient. The resulting epimorphism of the supplied
full SL₃ with itself is an automorphism. This retains the complete marking
and identifies the constituent kernel exactly, including at field four.

Each constituent is then realized as a literal subgroup U of Ω₁(Z(Q)).
It has a HasSectionModel for the reframed original K/O₂(K) quotient,
order |F|³, and C_K(U)=O₂(K). The existence result constructs such a U;
NonblockConstituentSections applies it to the original 4.3.8--10 input.
The automorphism may depend on the constituent. Alignment of markings,
exhaustion of the whole center and Frattini sections, and elimination of
the covering kernel on the whole action remain required for C.1.34.

Source: Aschbacher--Smith B.1.5, K.3.2 and C.1.34,
printed pp.69--70,454--456,136--137.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.ConstituentSections
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterB.QuasisimpleSource
private theorem kernel_of_coordinates
    {X W : Type*} [Group X] [AddCommGroup W] [Module (ZMod 2) W]
    {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (ρ : Representation (ZMod 2) X W) (p : X →* SL(3,F))
    (α : SL(3,F) ≃* SL(3,F)) (l : W ≃ₗ[ZMod 2] (Fin 3 → F))
    (hl : ∀ b v, l (ρ b v) = specialLinearNatural 3 (α (p b)) (l v)) :
    ρ.ker = p.ker := by
  ext b
  constructor
  · intro hb
    have hz : α (p b) = 1 := by
      apply specialLinearNatural_injective 3
      apply LinearMap.ext
      intro v
      obtain ⟨w,rfl⟩ := l.surjective v
      have hh := hl b w
      rw [show ρ b = 1 from hb] at hh
      simpa only [map_one, Module.End.one_apply, toAdd_ofAdd] using hh.symm
    exact α.map_eq_one_iff.mp hz
  · intro hb
    apply LinearMap.ext
    intro v
    apply l.injective
    change l (ρ b v) = l v
    rw [hl,show p b = 1 from hb,map_one,map_one]
    rfl

private theorem centralizer_of_natural_model
    {G : Type*} [Group G] {K U : Subgroup G} {F : Type*} [Field F]
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (hm : HasSectionModel K U ⊥ (linearThreeActor e) (specialLinearNatural 3)) :
    (centralizer (U : Set G)).subgroupOf K = pCore 2 K := by
  rw [HasSectionModel,bot_subgroupOf] at hm
  obtain ⟨_,hn,_,_,d,hd⟩ := hm
  let a := QuotientGroup.quotientBot.symm.trans d
  have he (k : K) (u : U) :
      (a (U.normalizerMonoidHom ⟨k,hn k.property⟩ u)).toAdd =
        specialLinearNatural 3 (linearThreeActor e k) (a u).toAdd :=
    hd k u _ (normalizerMonoidHom_apply_apply_coe _ _ _)
  ext k
  constructor
  · intro hk
    have hg : linearThreeActor e k = 1 := by
      apply specialLinearNatural_injective 3
      apply LinearMap.ext
      intro v
      obtain ⟨u,hu⟩ := a.surjective (Multiplicative.ofAdd v)
      have hx : U.normalizerMonoidHom ⟨k,hn k.property⟩ u = u := by
        apply Subtype.ext
        change (k:G) * (u:G) * (k:G)⁻¹ = u
        have hc : (u:G) * (k:G) = (k:G) * (u:G) := hk u u.property
        rw [←hc,mul_inv_cancel_right]
      have hh := he k u
      rw [hx,hu] at hh
      simpa only [map_one, Module.End.one_apply, toAdd_ofAdd] using hh.symm
    exact (QuotientGroup.eq_one_iff k).mp (e.map_eq_one_iff.mp hg)
  · intro hk u hu
    have hg : linearThreeActor e k = 1 := by
      change e (QuotientGroup.mk' _ k) = 1
      have hz : QuotientGroup.mk' (pCore 2 K) k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
      rw [hz,map_one]
    have hh := he k ⟨u,hu⟩
    rw [hg,map_one] at hh
    have hx : U.normalizerMonoidHom ⟨k,hn k.property⟩ ⟨u,hu⟩ = ⟨u,hu⟩ :=
      a.injective (Multiplicative.toAdd.injective hh)
    have hv := congrArg Subtype.val hx
    exact (mul_inv_eq_iff_eq_mul.mp hv).symm

private theorem coordinates_of_natural_section
    {X W : Type*} [Group X] [Finite X] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) X W) (B D : Subgroup X)
    (I : Submodule (ZMod 2) W) (hI : IsIrrPlus ρ B I)
    (F : BinaryField) (p : PerfectCentralCovering.Cover B SL(3,F.Carrier))
    (hpk : IsPGroup 2 p.toMonoidHom.ker) (hfix : fixedSpace ρ B = ⊥)
    (hnat : ConstituentRecognition.HasNaturalCentralSection ρ B D I F) :
    ∃ (α : SL(3,F.Carrier) ≃* SL(3,F.Carrier))
      (l : I ≃ₗ[ZMod 2] (Fin 3 → F.Carrier)),
      ∀ (b : B) (v : I),
        l ((invariantSubspace ρ B I hI.choose).toRepresentation b v) =
          specialLinearNatural 3 (α (p.toMonoidHom b)) (l v) := by
  obtain ⟨hDI,hDN,⟨a⟩⟩ := hnat
  let U := B ⊔ D
  let C := B.subgroupOf U
  let c : C ≃* B := subgroupOfEquivOfLe (show B ≤ U from le_sup_left)
  let τ := centralSectionRepresentation ρ B U I hDI hDN
  let π := KernelQuotient.projection τ
  let σ := centralQuotientRepresentation ρ B I hI.choose
  let f : B →* SL(3,F.Carrier) := a.groupEquiv.toMonoidHom.comp
    ((π.subgroupMap C).comp c.symm.toMonoidHom)
  have hfs : Function.Surjective f := a.groupEquiv.surjective.comp
    ((π.subgroupMap_surjective C).comp c.symm.surjective)
  have he (b : B) (v : centralQuotient ρ B I) :
      a.linearEquiv (σ b v) = specialLinearNatural 3 (f b) (a.linearEquiv v) := by
    exact a.intertwines ((π.subgroupMap C) (c.symm b)) v
  let : IsIrreducible σ := hI.choose_spec.2
  have hkσ : p.toMonoidHom.ker ≤ σ.ker := normal_p_subgroup_le_ker σ _ hpk
  have hk : p.toMonoidHom.ker ≤ f.ker := by
    intro b hb
    apply specialLinearNatural_injective 3
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := a.linearEquiv.surjective v
    have hh := he b w
    rw [show σ b = 1 from hkσ hb] at hh
    simpa only [map_one, Module.End.one_apply, toAdd_ofAdd] using hh.symm
  let α₀ : SL(3,F.Carrier) →* SL(3,F.Carrier) := p.toMonoidHom.liftOfSurjective p.surjective ⟨f,hk⟩
  have hα (b : B) : α₀ (p.toMonoidHom b) = f b :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ b
  have hαs : Function.Surjective α₀ := by
    intro x
    obtain ⟨b,rfl⟩ := hfs x
    exact ⟨p.toMonoidHom b,hα b⟩
  let α : SL(3,F.Carrier) ≃* SL(3,F.Carrier) := MulEquiv.ofBijective α₀
    ⟨Finite.injective_iff_surjective.mpr hαs,hαs⟩
  have hd : Disjoint I (fixedSpace ρ B) := by
    rw [hfix]
    exact disjoint_bot_right
  let l := (centralSectionEquiv ρ B I hd).trans a.linearEquiv
  refine ⟨α,l,fun b v => ?_⟩
  change a.linearEquiv (σ b (centralSectionEquiv ρ B I hd v)) =
    specialLinearNatural 3 (α₀ (p.toMonoidHom b)) (l v)
  rw [hα]
  exact he b _


variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local instance binaryAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
local notation "J" => (K ⊔ R : Subgroup G)
local notation "L" => K.subgroupOf (K ⊔ R)
local notation "E" => CentralSections.coreOmegaLayer (K := K) (R := R)
variable [hEN : Subgroup.Normal (CentralSections.coreOmegaLayer (K := K) (R := R))]
local instance omega_elementary : IsElementaryAbelian 2 E :=
  CentralSections.coreOmegaLayer_elementary
local notation "H" => (J ⧸ centralizer (E : Set J))
local notation "q" => (QuotientGroup.mk' (centralizer (E : Set J)) : J →* H)
local notation "B" => MonoidHom.range ((MonoidHom.comp q (Subgroup.subtype L)) : L →* H)
local notation "rho" => CentralSections.coreOmegaRepresentation h hn

include h hn

/-- Natural coordinates on the entire constituent factor through the supplied
full SL₃ quotient, up to an explicit automorphism of that same group. -/
theorem irrPlus_marked_coordinates
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (I : Submodule (ZMod 2) (Additive E)) (hI : IsIrrPlus rho B I) :
    ∃ (α : SL(3,F) ≃* SL(3,F)) (l : I ≃ₗ[ZMod 2] (Fin 3 → F)),
      ∀ (b : B) (v : I),
        l ((invariantSubspace rho B I hI.choose).toRepresentation b v) =
          specialLinearNatural 3 (α ((KernelOffenders.omegaCover h hn e).toMonoidHom b)) (l v) := by
  obtain ⟨A,_,D,_,_,hs⟩ :=
    ConstituentRecognition.irrPlus_local_natural h hn hfixed e (R.subgroupOf J) le_rfl
  have hp : IsPGroup 2 (KernelOffenders.omegaCover h hn e).toMonoidHom.ker := by
    rw [KernelOffenders.omegaCover_kernel]
    exact pCore_isPGroup.map _
  exact coordinates_of_natural_section rho B D I hI (ConstituentRecognition.coefficientField h hn)
    (KernelOffenders.omegaCover h hn e) hp
    (KernelOffenders.omega_fixedSpace_eq_bot h hn hfixed) (hs I hI)

/-- Every constituent has exactly the marked covering kernel, including at
field four. This is an equality of kernels on that constituent only. -/
theorem irrPlus_kernel
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (I : Submodule (ZMod 2) (Additive E)) (hI : IsIrrPlus rho B I) :
    ((invariantSubspace rho B I hI.choose).toRepresentation).ker =
      (KernelOffenders.omegaCover h hn e).toMonoidHom.ker := by
  obtain ⟨α,l,hl⟩ := irrPlus_marked_coordinates h hn hfixed e I hI
  exact kernel_of_coordinates _ (KernelOffenders.omegaCover h hn e).toMonoidHom α l hl

omit h hn hEN [Finite G] [Field F] [Finite F] [CharP F 2] in
/-- The embedding retains the original ambient group, rather than only the
faithful component image used by constituent recognition. -/
@[expose] def embedding (I : Submodule (ZMod 2) (Additive E)) : Multiplicative I →* G where
  toFun v := v.toAdd.val.toMul.val.val
  map_one' := rfl
  map_mul' _ _ := rfl

omit h hn hEN [Finite G] [Field F] [Finite F] [CharP F 2] in
/-- The constituent embedding into the original ambient group is injective. -/
theorem embedding_injective (I : Submodule (ZMod 2) (Additive E)) :
    Function.Injective (embedding I) := by
  intro v w hvw
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  apply Additive.toMul.injective
  exact Subtype.ext (Subtype.ext hvw)

/-- The actual ambient subgroup underlying a central-omega subspace. -/
@[expose] def subgroup (I : Submodule (ZMod 2) (Additive E)) : Subgroup G :=
  (embedding I).range

omit h hn hEN [Finite G] [Field F] [Finite F] [CharP F 2] in
/-- The constituent lies in the whole central omega of the original MS core. -/
theorem subgroup_le_omegaCenter (I : Submodule (ZMod 2) (Additive E)) :
    subgroup I ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn (msQ K R) := by
  rintro _ ⟨v,rfl⟩
  exact (CentralSections.coreOmegaLayer_eq (K := K) (R := R)).le v.toAdd.val.toMul.property

private def componentElement (k : K) : B :=
  ((q).comp (L).subtype).rangeRestrict ⟨⟨k,mem_sup_left k.property⟩,k.property⟩

omit [CharP F 2] in
private theorem embedding_conjugate
    (I : Submodule (ZMod 2) (Additive E)) (hI : IsIrrPlus rho B I)
    (k : K) (v : I) :
    embedding I (Multiplicative.ofAdd
      ((invariantSubspace rho B I hI.choose).toRepresentation (componentElement k) v)) =
      k * embedding I (Multiplicative.ofAdd v) * (k : G)⁻¹ := by
  have hh := NormalElementaryQuotient.representation_apply E q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    ⟨k,mem_sup_left k.property⟩ v.val
  change (((rho ((q) ⟨k,mem_sup_left k.property⟩) v.val).toMul : J) : G) = _
  rw [CentralSections.coreOmegaRepresentation_eq]
  exact congrArg (J).subtype hh

omit [CharP F 2] in
/-- Component invariance is literal normalization by the original K. -/
theorem subgroup_normalized
    (I : Submodule (ZMod 2) (Additive E)) (hI : IsIrrPlus rho B I) :
    K ≤ normalizer (subgroup I : Set G) := by
  apply le_normalizer_iff.mpr
  rintro k hk _ ⟨v,rfl⟩
  exact ⟨Multiplicative.ofAdd
    ((invariantSubspace rho B I hI.choose).toRepresentation (componentElement ⟨k,hk⟩) v.toAdd),
    embedding_conjugate h hn I hI ⟨k,hk⟩ v.toAdd⟩

/-- An actual natural section of the original K, with no remaining quotient
kernel in its numerator and with the supplied marking explicitly reframed. -/
theorem irrPlus_section_model
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (I : Submodule (ZMod 2) (Additive E)) (hI : IsIrrPlus rho B I) :
    ∃ α : SL(3,F) ≃* SL(3,F),
      HasSectionModel K (subgroup I) ⊥ (linearThreeActor (e.trans α))
        (specialLinearNatural 3) := by
  obtain ⟨α,l,hl⟩ := irrPlus_marked_coordinates h hn hfixed e I hI
  let c : Multiplicative I ≃* subgroup I := MonoidHom.ofInjective (embedding_injective I)
  let d := c.symm.trans l.toAddEquiv.toMultiplicative
  refine ⟨α,?_⟩
  rw [HasSectionModel,bot_subgroupOf]
  refine ⟨bot_le,subgroup_normalized h hn I hI,le_normalizer_of_normal,
    inferInstance,QuotientGroup.quotientBot.trans d,?_⟩
  intro k x y hxy
  have hcoord : (c.symm y).toAdd =
      (invariantSubspace rho B I hI.choose).toRepresentation (componentElement k)
        (c.symm x).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply embedding_injective I
    have hx : embedding I (c.symm x) = (x : G) := congrArg Subtype.val (c.apply_symm_apply x)
    have hy : embedding I (c.symm y) = (y : G) := congrArg Subtype.val (c.apply_symm_apply y)
    rw [embedding_conjugate h hn I hI]
    change embedding I (c.symm y) = (k:G) * embedding I (c.symm x) * (k:G)⁻¹
    rw [hx,hy]
    exact hxy
  change l (c.symm y).toAdd =
    specialLinearNatural 3 (linearThreeActor (e.trans α) k) (l (c.symm x).toAdd)
  rw [hcoord,hl]
  apply congrArg (fun g => specialLinearNatural 3 g (l (c.symm x).toAdd))
  exact congrArg α (KernelOffenders.omegaCover_apply h hn e
    ⟨⟨k,mem_sup_left k.property⟩,k.property⟩)

/-- The centralizer in the original K of each actual constituent is precisely
O₂(K), not merely a subgroup with the same order or projective quotient. -/
theorem subgroup_centralizer
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (I : Submodule (ZMod 2) (Additive E)) (hI : IsIrrPlus rho B I) :
    (centralizer (subgroup I : Set G)).subgroupOf K = pCore 2 K := by
  obtain ⟨α,hm⟩ := irrPlus_section_model h hn hfixed e I hI
  exact centralizer_of_natural_model (e.trans α) hm

/-- Each actual constituent has the natural order in the original group. -/
theorem subgroup_card
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F))
    (I : Submodule (ZMod 2) (Additive E)) (hI : IsIrrPlus rho B I) :
    Nat.card (subgroup I) = Nat.card F ^ 3 := by
  change Nat.card (embedding I).range = _
  rw [←Nat.card_congr (MonoidHom.ofInjective (embedding_injective I)).toEquiv]
  exact (ConstituentRecognition.irrPlus_card_finrank h hn hfixed e I hI).1

/-- There is an actual natural subgroup in the entire central omega. Its
marking factors the supplied K/O₂(K) marking through a displayed automorphism. -/
theorem exists_natural_subgroup
    (hfixed : msQ K R ⊓ centralizer (K : Set G) = ⊥)
    (e : (K ⧸ pCore 2 K) ≃* SL(3,F)) :
    ∃ U : Subgroup G, U ≤ Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.omegaCenterIn
        (msQ K R) ∧
      Nat.card U = Nat.card F ^ 3 ∧
      (centralizer (U : Set G)).subgroupOf K = pCore 2 K ∧
      ∃ α : SL(3,F) ≃* SL(3,F),
        HasSectionModel K U ⊥ (linearThreeActor (e.trans α)) (specialLinearNatural 3) := by
  obtain ⟨I,hI⟩ := ConstituentRecognition.exists_irrPlus h hn
  exact ⟨subgroup I,subgroup_le_omegaCenter I,
    subgroup_card h hn hfixed e I hI,subgroup_centralizer h hn hfixed e I hI,
    irrPlus_section_model h hn hfixed e I hI⟩

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.ConstituentSections
