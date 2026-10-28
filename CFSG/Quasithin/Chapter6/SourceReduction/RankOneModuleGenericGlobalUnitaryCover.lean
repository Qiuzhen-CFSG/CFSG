module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryLinear
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.AbsoluteExhaustion
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition.FieldDescent
public import Theory.SpecificGroups.PSL3.BinaryOddCenterCover
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow

/-!
# The full linear quotient and its natural Frattini section

In the proper-intersection branch of 5.2.8, write R = O₂(J) and q = 2^m.
The preceding comparison identifies the central quotient of J/R with PSL₃(q).
Its trivial two-core removes the exceptional two-primary covering kernels,
including q = 4, and gives an actual surjection SL₃(q) → J/R.

Characteristic two makes the literal action of J/R on R/Φ(R) faithful. Its
binary dimension is at most 3m+1. Perfectness supplies a nontrivial simple
section. The proved tensor-word classification and scalar descent identify
the inflated section as natural or dual: the half-field tensor has degree
9m/2, and all other nontrivial rows have degree at least 8m. The natural and
dual actions are faithful, so the scalar-cover map is injective. Thus the
FULL quotient is SL₃(q), and the original Frattini action has a faithful
natural section of order q³. In particular |Φ(R)| ≤ 2.

A nontrivial Frattini kernel makes the section exhaust the whole Frattini
quotient and forces irreducibility. A quotient of order at most q³ similarly
upgrades the section to the whole natural or dual action. These deductions
feed the elementary-core proof in `RankOneModuleGenericGlobalUnitaryMoved`.

The source theorem applies this construction to the original prepared pair;
the Chapter12 companion retains all preceding quotient and Sylow markings.
Identification of the whole moved core and the second-parabolic contradiction
remain required. A natural section alone does not prove those assertions.

Source: Aschbacher–Smith 5.2.8, printed pp.652–653 (`refs/quasithin.pdf`),
using the scalar-cover results A.2.18/I.1.3 and the proved SL₃ representation
classification, GLS III 2.8.6, 2.8.8 and 2.8.10(c).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryCover
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition

private theorem natural_injective {F : Type*} [Field F] [CharP F 2]
    [Algebra (ZMod 2) F] : Function.Injective (naturalBinary F) := by
  intro a b hab
  apply Subtype.ext
  ext i j
  have he := congrArg (fun f : Module.End (ZMod 2) (Fin 3 → F) => f (Pi.single j 1) i) hab
  change (a.val.mulVec (Pi.single j 1)) i = (b.val.mulVec (Pi.single j 1)) i at he
  simpa using he

private theorem dual_injective {F : Type*} [Field F] [CharP F 2]
    [Algebra (ZMod 2) F] : Function.Injective (dualBinary F) := by
  intro a b hab
  have he := natural_injective hab
  have hi : a⁻¹ = b⁻¹ := Subtype.ext (Matrix.transpose_injective (congrArg Subtype.val he))
  exact inv_injective hi

private theorem equiv_injective {A V W : Type*} [Group A]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) A V} {σ : Representation (ZMod 2) A W}
    (e : ρ.Equiv σ) (hi : Function.Injective σ) : Function.Injective ρ := by
  intro a b hab
  apply hi
  ext w
  obtain ⟨v,rfl⟩ := e.toLinearEquiv.surjective w
  exact (IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap a v).symm.trans
    ((congrArg (fun f : Module.End (ZMod 2) V => e (f v)) hab).trans
      (IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap b v))

private theorem small_simple_natural {F V : Type*} [Field F] [Finite F] [CharP F 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(3,F) V) [ρ.IsIrreducible]
    {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2^m)
    (hn : ∃ g, ρ g ≠ 1) (hd : Module.finrank (ZMod 2) V ≤ 3*m+1) :
    let := ZMod.algebra F 2
    Function.Injective ρ ∧ Module.finrank (ZMod 2) V = 3*m ∧
      (Nonempty (ρ.Equiv (naturalBinary F)) ∨ Nonempty (ρ.Equiv (dualBinary F))) := by
  let := ZMod.algebra F 2
  obtain ⟨hs,ha | ht | hg⟩ := AbsoluteExhaustion.absolute_model_trichotomy ρ hn m (by omega) hF
  · obtain ⟨hs,hdim,hmodel⟩ := ha
    have he := descend_absolute_natural ρ m hF hs hmodel
    refine ⟨?_,hdim,he⟩
    rcases he with he | he
    all_goals obtain ⟨e⟩ := he
    · exact equiv_injective e natural_injective
    · exact equiv_injective e dual_injective
  · obtain ⟨hn,he,_⟩ := ht
    omega
  · omega

variable {G : Type*} [Group G] [Finite G]

/-- The actual elementary Frattini quotient of the overcomponent's two-core. -/
abbrev CoreSpace (G : Type*) [Group G] := Additive ((pCore 2 G) ⧸ frattini (pCore 2 G))

instance core_pGroup : Fact (IsPGroup 2 (pCore 2 G)) := ⟨pCore_isPGroup⟩
instance core_frattini_elementary : IsElementaryAbelian 2 ((pCore 2 G) ⧸ frattini (pCore 2 G)) :=
  isElementaryAbelian_quotient_frattini

/-- Conjugation on the literal Frattini quotient, factored through the actual two-core. -/
def frattiniAction (h : HasCharacteristicTwo G) :
    Representation (ZMod 2) (G ⧸ pCore 2 G) (CoreSpace G) := by
  let E := (pCore 2 G) ⧸ frattini (pCore 2 G)
  let a := (quotientAut (frattini (pCore 2 G))).comp
    (MulAut.conjNormal : G →* MulAut (pCore 2 G))
  let f := QuotientGroup.lift (pCore 2 G) a (pCore_frattini_action_kernel 2 h).ge
  let b : MulAut E →* Module.End (ZMod 2) (Additive E) := {
    toFun z := { z.toAdditive.toAddMonoidHom with map_smul' := ZMod.map_smul z.toAdditive }
    map_one' := by ext; rfl
    map_mul' := by intros; ext; rfl }
  exact b.comp f

/-- The action is the original conjugation map on representatives. -/
theorem frattiniAction_apply (h : HasCharacteristicTwo G) (g : G)
    (x : (pCore 2 G) ⧸ frattini (pCore 2 G)) :
    frattiniAction h (QuotientGroup.mk' (pCore 2 G) g) (Additive.ofMul x) =
      Additive.ofMul (quotientAut (frattini (pCore 2 G)) (MulAut.conjNormal g) x) := by
  unfold frattiniAction
  rfl

/-- Characteristic two makes this literal quotient action faithful. -/
theorem frattiniAction_injective (h : HasCharacteristicTwo G) :
    Function.Injective (frattiniAction h) := by
  let a := (quotientAut (frattini (pCore 2 G))).comp
    (MulAut.conjNormal : G →* MulAut (pCore 2 G))
  have hi : Function.Injective (QuotientGroup.lift (pCore 2 G) a
      (pCore_frattini_action_kernel 2 h).ge) :=
    (QuotientGroup.injective_lift_iff _ _ _).mpr (pCore_frattini_action_kernel 2 h).symm
  intro x y hxy
  apply hi
  ext z
  exact congrArg (fun f : Module.End (ZMod 2) (CoreSpace G) =>
    (f (Additive.ofMul z)).toMul) hxy

private theorem coreSpace_dimension {m : ℕ}
    (hc : Nat.card (pCore 2 G) ≤ 2*(2^m)^3) :
    Module.finrank (ZMod 2) (CoreSpace G) ≤ 3*m+1 := by
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := CoreSpace G)
  rw [Nat.card_zmod] at hcard
  rw [←hcard]
  have hb := Nat.card_le_card_of_surjective (QuotientGroup.mk' (frattini (pCore 2 G)))
    (QuotientGroup.mk'_surjective _)
  change Nat.card ((pCore 2 G) ⧸ frattini (pCore 2 G)) ≤ _
  calc
    _ ≤ Nat.card (pCore 2 G) := hb
    _ ≤ 2*(2^m)^3 := hc
    _ = 2^(3*m+1) := by rw [←pow_mul,Nat.mul_comm m 3,pow_succ]; omega

private theorem scalar_lift {F : Type*} [Field F] [Finite F]
    [IsQuasisimple G] (hcore : pCore 2 G = ⊥)
    (e : (G ⧸ center G) ≃* PSL(3,F))
    {m : ℕ} (hm : 1 < m) (hF : Nat.card F = 2^m) :
    ∃ k : SL(3,F) →* G, Function.Surjective k ∧
      (e.toMonoidHom.comp (QuotientGroup.mk' (center G))).comp k = Matrix.PSL3.projection F := by
  have h2 : Nat.card F ≠ 2 := by
    have hh : 4 ≤ 2^m := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hm
    omega
  by_cases h4 : Nat.card F = 4
  · have ho : Odd (Nat.card (center G)) := Nat.not_even_iff_odd.mp (by
      simpa only [even_iff_two_dvd] using
        PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot hcore (center G) le_rfl)
    exact Matrix.PSL3.BinaryOddCenterCover.exists_scalar_lift_four h4 e ho
  · exact Matrix.PSL3.OrdinaryCenterRecognition.exists_scalar_lift h2 h4 e

/-- A full special-linear quotient together with a faithful natural or dual
section of the literal core action. This does not identify the whole core. -/
def NaturalCoreSection (h : HasCharacteristicTwo G) (m : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2^m ∧ ∃ e : (G ⧸ pCore 2 G) ≃* SL(3,F),
      ∃ U : Subrepresentation (frattiniAction h),
      ∃ N : Subrepresentation U.toRepresentation,
      N.quotientRepresentation.IsIrreducible ∧
      Function.Injective N.quotientRepresentation ∧
      Module.finrank (ZMod 2) (U.toSubmodule ⧸ N.toSubmodule) = 3*m ∧
      (let := ZMod.algebra F 2
       Nonempty (Representation.Equiv (N.quotientRepresentation.comp e.symm.toMonoidHom) (naturalBinary F)) ∨
       Nonempty (Representation.Equiv (N.quotientRepresentation.comp e.symm.toMonoidHom) (dualBinary F)))

/-- Recover the marked simple section of the actual core action, for subsequent
extension and moved-space arguments. -/
theorem NaturalCoreSection.exists_section {h : HasCharacteristicTwo G} {m : ℕ}
    (d : NaturalCoreSection h m) :
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2^m ∧ ∃ e : (G ⧸ pCore 2 G) ≃* SL(3,F),
      ∃ U : Subrepresentation (frattiniAction h),
      ∃ N : Subrepresentation U.toRepresentation,
      N.quotientRepresentation.IsIrreducible ∧
      Function.Injective N.quotientRepresentation ∧
      Module.finrank (ZMod 2) (U.toSubmodule ⧸ N.toSubmodule) = 3*m ∧
      (let := ZMod.algebra F 2
       Nonempty (Representation.Equiv (N.quotientRepresentation.comp e.symm.toMonoidHom) (naturalBinary F)) ∨
       Nonempty (Representation.Equiv (N.quotientRepresentation.comp e.symm.toMonoidHom) (dualBinary F))) := d

/-- The bounded original Frattini action recognizes the full quotient and
an actual natural or dual simple section of the original action. -/
theorem full_linear_quotient (h : HasCharacteristicTwo G)
    [IsQuasisimple (G ⧸ pCore 2 G)] {m : ℕ} (hm : 1 < m)
    (hc : Nat.card (pCore 2 G) ≤ 2*(2^m)^3)
    (hlin : ClassicalGroup.IsPSL
      ((G ⧸ pCore 2 G) ⧸ center (G ⧸ pCore 2 G)) 3 (2^m)) :
    NaturalCoreSection h m := by
  unfold NaturalCoreSection
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hlin
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨k,hk,_⟩ := scalar_lift (pCore_quotient_pCore_eq_bot 2) a hm hF
  let X := G ⧸ pCore 2 G
  let : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
  let : Nontrivial X := (QuotientGroup.mk'_surjective (center X)).nontrivial
  let : Group.IsPerfect (⊤ : Subgroup X) :=
    Group.IsPerfect.ofSurjective (f := (topEquiv (G := X)).symm.toMonoidHom)
      (topEquiv (G := X)).symm.surjective
  have hn : ¬ (⊤ : Subgroup X) ≤ (frattiniAction h).ker := by
    intro hh
    have hz := (MonoidHom.ker_eq_bot_iff _).mpr (frattiniAction_injective h)
    exact top_ne_bot ((top_unique hh).symm.trans hz)
  obtain ⟨U,N,hi,hn⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (⊤ : Subgroup X) hn
  let τ := N.quotientRepresentation
  let σ : Representation (ZMod 2) SL(3,F) (U.toSubmodule ⧸ N.toSubmodule) := τ.comp k
  let : τ.IsIrreducible := hi
  let : σ.IsIrreducible := (irreducible_comp_surjective_iff k hk τ).mpr hi
  have hact : ∃ g, σ g ≠ 1 := by
    by_contra! he
    apply hn
    intro x _
    obtain ⟨g,rfl⟩ := hk x
    exact he g
  have hd : Module.finrank (ZMod 2) (U.toSubmodule ⧸ N.toSubmodule) ≤ 3*m+1 :=
    (Submodule.finrank_quotient_le N.toSubmodule).trans
      ((Submodule.finrank_le U.toSubmodule).trans (coreSpace_dimension hc))
  obtain ⟨hs,hdim,hmodel⟩ := small_simple_natural σ hm hF hact hd
  have hki : Function.Injective k := fun x y he => hs (congrArg τ he)
  let e := (MulEquiv.ofBijective k ⟨hki,hk⟩).symm
  have hτ : Function.Injective τ := by
    intro x y he
    obtain ⟨u,rfl⟩ := hk x
    obtain ⟨v,rfl⟩ := hk y
    exact congrArg k (hs he)
  exact ⟨F,inferInstance,inferInstance,inferInstance,hF,e,U,N,hi,hτ,hdim,hmodel⟩


/-- The recognized section identifies the full quotient, including its center. -/
theorem NaturalCoreSection.isSL {h : HasCharacteristicTwo G} {m : ℕ}
    (d : NaturalCoreSection h m) : Chapter1.Section02.LocalModels.IsSL (G ⧸ pCore 2 G) 3 (2^m) := by
  obtain ⟨F,_,_,_,hF,e,_⟩ := d
  exact ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩

/-- The natural section occupies at least q³ elements of the literal Frattini
quotient, leaving at most a central involution in its Frattini kernel. -/
theorem NaturalCoreSection.frattini_card_le_two {h : HasCharacteristicTwo G} {m : ℕ}
    (d : NaturalCoreSection h m) (hc : Nat.card (pCore 2 G) ≤ 2*(2^m)^3) :
    Nat.card (frattini (pCore 2 G)) ≤ 2 := by
  obtain ⟨F,_,_,_,hF,e,U,N,hi,hfaith,hdegree,hmodel⟩ := d
  have hd : 3*m ≤ Module.finrank (ZMod 2) (CoreSpace G) := by
    rw [←hdegree]
    exact (Submodule.finrank_quotient_le N.toSubmodule).trans (Submodule.finrank_le U.toSubmodule)
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := CoreSpace G)
  rw [Nat.card_zmod] at hcard
  have hb : (2^m)^3 ≤ Nat.card ((pCore 2 G) ⧸ frattini (pCore 2 G)) := by
    change (2^m)^3 ≤ Nat.card (CoreSpace G)
    rw [hcard,←pow_mul,Nat.mul_comm m 3]
    exact Nat.pow_le_pow_right (by decide) hd
  have hh := card_eq_card_quotient_mul_card_subgroup (frattini (pCore 2 G))
  have hp : 0 < (2^m)^3 := pow_pos (pow_pos (by decide) _) _
  nlinarith

private theorem whole_section {A V : Type*} [Group A]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) (U : Subrepresentation ρ)
    (N : Subrepresentation U.toRepresentation)
    (hd : Module.finrank (ZMod 2) V ≤ Module.finrank (ZMod 2) (U.toSubmodule ⧸ N.toSubmodule)) :
    Nonempty (ρ.Equiv N.quotientRepresentation) := by
  have hdim := N.toSubmodule.finrank_quotient_add_finrank
  have hU := Submodule.finrank_le U.toSubmodule
  have hNt : N.toSubmodule = ⊥ := Submodule.finrank_eq_zero.mp (by omega)
  have hUt : U.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq (by omega)
  let i : U.toRepresentation.IntertwiningMap ρ :=
    .mk U.toSubmodule.subtype (by intro g; ext v; rfl)
  let q : U.toRepresentation.IntertwiningMap N.quotientRepresentation :=
    .mk N.toSubmodule.mkQ (by intro g; ext v; rfl)
  have hi : Function.Bijective i := ⟨Subtype.val_injective,by
    intro v; exact ⟨⟨v,hUt ▸ Submodule.mem_top⟩,rfl⟩⟩
  have hq : Function.Bijective q := ⟨?_,N.toSubmodule.mkQ_surjective⟩
  · exact ⟨(i.ofBijective hi).symm.trans (q.ofBijective hq)⟩
  · apply (injective_iff_map_eq_zero q).mpr
    intro v hv
    have hv' := (Submodule.Quotient.mk_eq_zero N.toSubmodule).mp hv
    simpa only [hNt,Submodule.mem_bot] using hv'


/-- A nontrivial Frattini kernel leaves exactly the natural section in the
Frattini quotient, so the original quotient action is irreducible. -/
theorem NaturalCoreSection.irreducible_of_frattini_ne_bot
    {h : HasCharacteristicTwo G} {m : ℕ}
    (d : UnitaryCover.NaturalCoreSection h m)
    (hc : Nat.card (pCore 2 G) ≤ 2*(2^m)^3)
    (hne : frattini (pCore 2 G) ≠ ⊥) :
    (UnitaryCover.frattiniAction h).IsIrreducible := by
  have hphi : 2 ≤ Nat.card (frattini (pCore 2 G)) := by
    let : Nontrivial (frattini (pCore 2 G)) := (nontrivial_iff_ne_bot _).mpr hne
    exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have hprod := card_eq_card_quotient_mul_card_subgroup (frattini (pCore 2 G))
  have hE : Nat.card (UnitaryCover.CoreSpace G) ≤ (2^m)^3 := by
    change Nat.card ((pCore 2 G) ⧸ frattini (pCore 2 G)) ≤ _
    nlinarith
  obtain ⟨F,_,_,_,hF,e,U,N,hi,hfaith,hdegree,hmodel⟩ := d
  have hd : Module.finrank (ZMod 2) (UnitaryCover.CoreSpace G) ≤ 3*m := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := UnitaryCover.CoreSpace G)
    rw [Nat.card_zmod] at he
    rw [←he]
    simpa only [←pow_mul,Nat.mul_comm m 3] using hE
  obtain ⟨a⟩ := whole_section (UnitaryCover.frattiniAction h) U N (by omega)
  exact (RepEquiv.ofRepresentationEquiv a).irreducible_of_euqiv hi


/-- The whole literal Frattini action, with the actual quotient isomorphism
and either natural orientation retained. -/
def NaturalCoreAction (h : HasCharacteristicTwo G) (m : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    Nat.card F = 2^m ∧ ∃ e : (G ⧸ pCore 2 G) ≃* SL(3,F),
    (let := ZMod.algebra F 2
     Nonempty (Representation.Equiv ((frattiniAction h).comp e.symm.toMonoidHom) (naturalBinary F)) ∨
     Nonempty (Representation.Equiv ((frattiniAction h).comp e.symm.toMonoidHom) (dualBinary F)))

/-- Recover the field, quotient marking and intertwiner of the whole core
without exposing the predicate's implementation across modules. -/
theorem NaturalCoreAction.exists_coordinates {h : HasCharacteristicTwo G} {m : ℕ}
    (d : NaturalCoreAction h m) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2^m ∧ ∃ e : (G ⧸ pCore 2 G) ≃* SL(3,F),
      (let := ZMod.algebra F 2
       Nonempty (Representation.Equiv ((frattiniAction h).comp e.symm.toMonoidHom) (naturalBinary F)) ∨
       Nonempty (Representation.Equiv ((frattiniAction h).comp e.symm.toMonoidHom) (dualBinary F))) := d

/-- A section of order q³ is the whole action whenever the Frattini
quotient has at most q³ elements. Both natural orientations remain explicit. -/
theorem NaturalCoreSection.whole_of_card_le {h : HasCharacteristicTwo G} {m : ℕ}
    (d : NaturalCoreSection h m) (hc : Nat.card (CoreSpace G) ≤ (2^m)^3) :
    NaturalCoreAction h m := by
  have hd : Module.finrank (ZMod 2) (CoreSpace G) ≤ 3*m := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := CoreSpace G)
    rw [Nat.card_zmod] at he
    rw [←he]
    simpa only [←pow_mul,Nat.mul_comm m 3] using hc
  obtain ⟨F,_,_,_,hF,e,U,N,hi,hfaith,hdegree,hmodel⟩ := d
  obtain ⟨a⟩ := whole_section (frattiniAction h) U N (by omega)
  let b : Representation.Equiv ((frattiniAction h).comp e.symm.toMonoidHom)
      (N.quotientRepresentation.comp e.symm.toMonoidHom) :=
    .mk a.toLinearEquiv (fun g => a.isIntertwining' (e.symm g))
  refine ⟨F,inferInstance,inferInstance,inferInstance,hF,e,?_⟩
  let := ZMod.algebra F 2
  rcases hmodel with hn | hd
  · obtain ⟨c⟩ := hn
    exact .inl ⟨b.trans c⟩
  · obtain ⟨c⟩ := hd
    exact .inr ⟨b.trans c⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryCover

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- The proper unitary overcomponent has full quotient SL₃ over the original
field, and a faithful natural section in its actual Frattini action. -/
theorem Preparation.unitary_overcomponent_full_linear_action
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J)
    (hQR : ¬ (residual H).pCoreIn 2 ≤ J.pCoreIn 2) :
    Chapter1.Section02.LocalModels.IsSL (J ⧸ pCore 2 J) 3 (2^m) ∧
      Nat.card (frattini (pCore 2 J)) ≤ 2 ∧
      ∃ hc : HasCharacteristicTwo J, UnitaryCover.NaturalCoreSection hc m := by
  have hlin := d.unitary_overcomponent_central_quotient_linear h hH hp m hm he hJ hKJ hQR
  have hq := (d.unitary_overcomponent_central_quotient_models h hH hp m hm he hJ hKJ hQR).1
  let := hq
  have hb := (d.unitary_overcomponent_proper_image_block h hH hp m hm he hJ hKJ.le hQR).1
  have hR := (d.unitary_overcomponent_proper_quotient_core h hH hp m hm he hJ hKJ.le hQR).2
  have hR' : Nat.card (pCore 2 J) ≤ 2*(2^m)^3 := by
    rw [Nat.card_congr ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).toEquiv]
    exact hR
  have hc := Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo
    T (h.qtke.evenCharacteristic T) hJ
  have hn := UnitaryCover.full_linear_quotient hc hb.1 hR' hlin
  exact ⟨hn.isSL,hn.frattini_card_le_two hR',hc,hn⟩

end Unitary
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
