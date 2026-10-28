module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalDecomposition
public import Theory.Representation.SL2.NaturalHomogeneous
public import Theory.Representation.BinaryOffender.Homogeneous.DoubleCoordinates


/-!
# Bounded natural constituents recover the original seed

The full component stabilizer acts irreducibly on the literal moved subgroup
by original full-module minimality. A natural constituent has invariant type
under this entire stabilizer, so Clifford generation makes W homogeneous.
If its degree is at most two natural degrees, a proper constituent would give
two actual natural copies, excluded by the original odd-rank argument.
Thus W is L-minimal, and the checked reconstruction recovers both orientations
of the unchanged seed and applies to the literal Hall exponent. In the source
Galois-field row, its whole-W natural coordinates give a direct contradiction
to the proved natural Hall exclusion.

The earlier source separation, natural constituent recognition and degree
bound remain with qt-d-10-nona5-central-hall-orders; this does not assert
SeedAnalysisAt or the unconditional Hall theorem.
Source: Aschbacher--Smith D.3.9(1), D.3.21(3), 3.2.6 and 10.2.3,
printed pp.199--207,581,745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 Representation.BinaryOffender Representation.BinaryOffender.Homogeneous
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance naturalBoundedElementary : IsElementaryAbelian 2 (⁅D.fullModule,L⁆ : Subgroup G) :=
  source_original_full_moved_elementary D

private theorem stabilizer_normalizes_moved :
    D.maximalLocal ⊓ normalizer (L : Set G) ≤
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  intro n hn
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hn.1),
    mem_normalizer_iff_map_conj_eq.mp hn.2]

/-- The actual full component stabilizer acts on W before full/local equality. -/
@[expose] def movedStabilizerAction :
    Representation (ZMod 2) ↥(D.maximalLocal ⊓ normalizer (L : Set G))
      (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
  Representation.elementaryRepresentation
    ((⁅D.fullModule,L⁆ : Subgroup G).normalizerMonoidHom.comp
      (inclusion (by exact stabilizer_normalizes_moved D)))

/-- The original component, as a subgroup of its full stabilizer. -/
abbrev movedStabilizerComponent :=
  L.subgroupOf (D.maximalLocal ⊓ normalizer (L : Set G))

private theorem component_le_stabilizer : L ≤ D.maximalLocal ⊓ normalizer (L : Set G) :=
  le_inf ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer) L.le_normalizer

local instance movedStabilizerComponentNormal : (movedStabilizerComponent D).Normal :=
  (normal_subgroupOf_iff_le_normalizer (component_le_stabilizer D)).mpr inf_le_right

/-- Original minimality gives irreducibility for the full stabilizer action,
without asserting irreducibility for L. -/
theorem movedStabilizerAction_irreducible
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)) :
    (movedStabilizerAction D).IsIrreducible := by
  let W := ⁅D.fullModule,L⁆
  let : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr (source_full_moved_ne_bot D)
  refine ⟨?_⟩
  intro I
  let J := I.toSubmodule.toAddSubgroup.toSubgroup.map W.subtype
  have hJW : J ≤ W := by rintro _ ⟨w,_,rfl⟩; exact w.property
  have hNJ : D.maximalLocal ⊓ normalizer (L : Set G) ≤ normalizer (J : Set G) := by
    apply le_normalizer_iff.mpr
    rintro n hn _ ⟨w,hw,rfl⟩
    refine ⟨(movedStabilizerAction D ⟨n,hn⟩ (Additive.ofMul w)).toMul,
      I.apply_mem_toSubmodule ⟨n,hn⟩ hw,rfl⟩
  rcases moved_minimal_under_component_stabilizer_of_seed_separated D c ht htn hsep J hJW hNJ with he | he
  · right
    apply Subrepresentation.toSubmodule_injective
    apply top_unique
    intro w _
    have hwJ : (w.toMul : G) ∈ J := by rw [he]; exact w.toMul.property
    obtain ⟨v,hv,hvw⟩ := hwJ
    have hvw' : v = w.toMul := Subtype.ext hvw
    change Additive.ofMul v ∈ I.toSubmodule at hv
    rw [hvw'] at hv
    exact hv
  · left
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro w hw
    have hz : (w.toMul : G) ∈ J := ⟨w.toMul,hw,rfl⟩
    rw [he,mem_bot] at hz
    exact (show w = 0 from Subtype.ext hz)

local instance naturalBoundedFiniteDimensional :
    FiniteDimensional (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) :=
  Module.Finite.of_finite

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra _ 2

/-- A natural constituent fills W if W has degree at most two natural copies.
Its homogeneity and full-normalizer invariance are conclusions, not inputs. -/
theorem natural_constituent_eq_top_of_degree_le
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (hd : Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) ≤
      2 * Module.finrank (ZMod 2) (Fin 2 → F)) : I = ⊤ := by
  let N := D.maximalLocal ⊓ normalizer (L : Set G)
  let K := movedStabilizerComponent D
  let ρ := movedStabilizerAction D
  let := movedStabilizerAction_irreducible D c ht htn hsep
  let q : K →* SL(2,F) := e.toMonoidHom.comp
    ((QuotientGroup.mk' (pCore 2 L)).comp (subgroupOfEquivOfLe (component_le_stabilizer D)).toMonoidHom)
  let α : N →* MulAut (SL(2,F)) := (MulAut.congr e).toMonoidHom.comp
    ((normalizerPCoreQuotientAction L).comp (inclusion inf_le_right))
  have hα (n : N) (l : K) : q (MulAut.conjNormal n l) = α n (q l) := by
    change e (QuotientGroup.mk' (pCore 2 L) _) =
      e (normalizerPCoreQuotientAction L (inclusion inf_le_right n)
        (e.symm (e (QuotientGroup.mk' (pCore 2 L) _))))
    rw [e.symm_apply_apply]
    change _ = e (quotientAut (pCore 2 L) _ _)
    rw [quotientAut_apply_mk]
    rfl
  have hE' (l : K) v : E ((q l).val.mulVec v) = I.toRepresentation l (E v) := by
    rw [←hE]
    congr 1
    exact (SL2AutomorphismNatural.action_conj _ _).symm
  have hh := SL2AutomorphismNatural.homogeneous_natural_of_irreducible ρ K q α hα I hI E hE'
  by_contra hproper
  have hp : I.toSubmodule ≠ ⊤ := fun he => hproper (Subrepresentation.toSubmodule_injective he)
  have hdim : Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) ≤
      2 * Module.finrank (ZMod 2) I.toSubmodule := by rwa [←E.finrank_eq]
  obtain ⟨a⟩ := double_coordinates_of_degree_le I hI hh hp hdim
  let f := ((LinearEquiv.finTwoArrow (ZMod 2) (Fin 2 → F)).trans
    (E.prodCongr E)).trans a.toLinearEquiv.symm
  apply no_two_natural_copies_on_moved D c ht htn hsep e f
  intro l x
  let lK : K := (subgroupOfEquivOfLe (component_le_stabilizer D)).symm l
  have he := LinearMap.congr_fun (a.symm.isIntertwining' lK) (E (x 0),E (x 1))
  have hpair : (E (naturalComponent e l (x 0)),E (naturalComponent e l (x 1))) =
      (I.toRepresentation lK (E (x 0)),I.toRepresentation lK (E (x 1))) := by
    rw [←hE,←hE]
    rfl
  change ((a.toLinearEquiv.symm
    (E (naturalComponent e l (x 0)),E (naturalComponent e l (x 1)))).toMul : G) = _
  rw [hpair]
  exact congrArg (fun w : Additive (⁅D.fullModule,L⁆ : Subgroup G) => (w.toMul : G)) he

/-- The bounded natural constituent upgrades original stabilizer minimality
to the L-minimality required by moved-module recognition. -/
theorem movedMinimal_of_bounded_natural_constituent
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (hd : Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) ≤
      2 * Module.finrank (ZMod 2) (Fin 2 → F)) : MovedMinimal D := by
  have he := natural_constituent_eq_top_of_degree_le D c ht htn hsep e I hI E hE hd
  have hatom := (Subrepresentation.irreducible_iff_isAtom I).mp hI
  rw [he] at hatom
  let σ := (movedStabilizerAction D).comp (movedStabilizerComponent D).subtype
  let : Representation.IsIrreducible σ := isSimpleOrder_iff_isAtom_top.mpr hatom
  intro J hJW hLJ
  let W := ⁅D.fullModule,L⁆
  let P : Subrepresentation σ := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 (J.subgroupOf W).toAddSubgroup
    apply_mem_toSubmodule l w hw := by
      exact (mem_normalizer_iff.mp (hLJ l.property) w.toMul.val).mp hw }
  rcases eq_bot_or_eq_top P with hbot | htop
  · right
    intro w hw
    have hp : Additive.ofMul (⟨w,hJW hw⟩ : W) ∈ P.toSubmodule := hw
    rw [hbot] at hp
    have hz : w = 1 := congrArg (fun v : Additive W => (v.toMul : G))
      (show Additive.ofMul (⟨w,hJW hw⟩ : W) = 0 from hp)
    exact hz ▸ (centralizer (L : Set G)).one_mem
  · left
    apply le_antisymm hJW
    intro w hw
    have hp : Additive.ofMul (⟨w,hw⟩ : W) ∈ P.toSubmodule := by rw [htop]; trivial
    exact hp

/-- The bounded natural decomposition reconstructs the unchanged original seed
in either orientation, including full/local equality and Sylow stability. -/
theorem separatedSeed_of_bounded_natural_constituent
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (hd : Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) ≤
      2 * Module.finrank (ZMod 2) (Fin 2 → F)) : SeparatedSeed D t :=
  separatedSeed_of_separated_and_movedMinimal D
    (movedMinimal_of_bounded_natural_constituent D c ht htn hsep e I hI E hE hd) ht htn hsep

/-- The literal Hall consumer after constructing homogeneity and eliminating
repeated natural copies. Earlier separation, natural-type recognition and its
degree bound remain with qt-d-10-nona5-central-hall-orders. -/
theorem hall_exponent_of_bounded_natural_constituent
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → F) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (hd : Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) ≤
      2 * Module.finrank (ZMod 2) (Fin 2 → F)) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1 :=
  hall_exponent_of_moved_minimal_and_crossed T D c hnot ht htn
    (movedMinimal_of_bounded_natural_constituent D c ht htn hsep e I hI E hE hd)
    (full_moved_centralizes_opposite_of_seed_separated D ht htn hsep)

local instance naturalBoundedGaloisAlgebra (n : ℕ) :
    Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2

/-- In the original central Hall context, the bounded natural alternative is
impossible. The constructed whole-W coordinates feed the literal natural Hall
exclusion, so no non-linear-three hypothesis or recognition callback is needed. -/
theorem no_bounded_natural_constituent
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))
    (n : ℕ) (hn : 1 < n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    (I : Subrepresentation ((movedStabilizerAction D).comp (movedStabilizerComponent D).subtype))
    (hI : I.toRepresentation.IsIrreducible)
    (E : (Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] I.toSubmodule)
    (hE : ∀ (l : movedStabilizerComponent D) v,
      E (naturalComponent e ⟨l.val.val,l.property⟩ v) = I.toRepresentation l (E v))
    (hd : Module.finrank (ZMod 2) (Additive (⁅D.fullModule,L⁆ : Subgroup G)) ≤
      2 * Module.finrank (ZMod 2) (Fin 2 → GaloisField 2 n)) : False := by
  have hs := separatedSeed_of_bounded_natural_constituent D c ht htn hsep e I hI E hE hd
  obtain ⟨geometry,_⟩ := geometry_and_minimality_of_separatedSeed D ht htn hs
  have he := natural_constituent_eq_top_of_degree_le D c ht htn hsep e I hI E hE hd
  subst I
  let W := ⁅D.fullModule,L⁆
  let f : (Fin 2 → GaloisField 2 n) ≃ₗ[ZMod 2] Additive W := E.trans Submodule.topEquiv
  have hf (l : L) v : ((f (naturalComponent e l v)).toMul : G) =
      (l : G) * ((f v).toMul : G) * (l : G)⁻¹ := by
    let lK : movedStabilizerComponent D :=
      (subgroupOfEquivOfLe (component_le_stabilizer D)).symm l
    exact congrArg (fun w : (⊤ : Submodule (ZMod 2) (Additive W)) => (w.val.toMul : G))
      (hE lK v)
  let C : BinaryConjugationSection L W ⊥
      (SL2.BinarySmall.natural.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) := {
    section_le := source_full_moved_le_component D
    kernel_le := bot_le
    normalized := (component_le_stabilizer D).trans (stabilizer_normalizes_moved D)
    coordinates := {
      toFun w := Multiplicative.ofAdd (f.symm (Additive.ofMul w))
      map_one' := congrArg Multiplicative.ofAdd f.symm.map_zero
      map_mul' a b := congrArg Multiplicative.ofAdd
        (f.symm.map_add (Additive.ofMul a) (Additive.ofMul b)) }
    onto := fun v => ⟨(f v.toAdd).toMul,
      congrArg Multiplicative.ofAdd (f.symm_apply_apply v.toAdd)⟩
    kernel_eq := by
      ext w
      change f.symm (Additive.ofMul w) = 0 ↔ (w : G) = 1
      constructor
      · intro hz
        have hz' : Additive.ofMul w = 0 :=
          f.symm.injective (hz.trans f.symm.map_zero.symm)
        exact congrArg (fun v : Additive W => (v.toMul : G)) hz'
      · intro hz
        have hz' : w = 1 := Subtype.ext hz
        rw [hz']
        exact f.symm.map_zero
    equivariant := by
      intro l w
      apply f.injective
      change f (f.symm (Additive.ofMul _)) =
        f (SL2.BinarySmall.natural (e (QuotientGroup.mk' (pCore 2 L) l))
          (f.symm (Additive.ofMul w)))
      rw [f.apply_symm_apply]
      apply Additive.toMul.injective
      apply Subtype.ext
      have hh := hf l (f.symm (Additive.ofMul w))
      rw [f.apply_symm_apply] at hh
      rw [show naturalComponent e l (f.symm (Additive.ofMul w)) =
          (SL2.BinarySmall.natural (e (QuotientGroup.mk' (pCore 2 L) l)))
            (f.symm (Additive.ofMul w)) from SL2AutomorphismNatural.action_conj _ _] at hh
      exact hh.symm }
  let C' : NaturalSection D n e := C.replaceKernel _
    (movedFixed_eq_bot_of_seed_separated D c ht htn hsep).symm
  exact (HallGeometry.source_hallGeometryAt T L D H B c geometry).natural_excluded n hn e C'

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
