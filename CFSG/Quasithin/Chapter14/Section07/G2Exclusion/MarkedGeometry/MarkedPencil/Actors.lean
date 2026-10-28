module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil
public import Theory.AtlasPort.LinearGroups.G2.BinaryNaturalPlane
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Restriction
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# The actual binary G₂ pencil centralizers

An octonion automorphism fixing the first three basis vectors is determined
by its image on the opposite vector. Preservation of the polar norm, trace
and norm restricts that image to eight possibilities. These are exactly the
three commuting root coordinates in `BinaryCore.elementary`. The existing
quotient character cuts out its elementary four in the actual derived group.

The published singular maps reflect pointwise fixation of the pencil plane,
so this calculation applies to both the natural six-dimensional quotient and
the trace-zero Weyl module. Equivariance and point transitivity transport the
calculation to every singular point. The final applications use the literal
quotient U/(V₁ ∩ U), an actual actor equivalence and an equivariance equation.

This proves the centralizer identifications in Aschbacher–Smith 14.7.55(4),
printed p.1066, PDF p.1083, combined manuscript of 1 March 2004. The fixed and
moved spaces and the family equality in (8) are separate remaining branches.
In particular the elementary eight is in the full actor; the proved
`fullCentralizer_not_le_derived` prevents identifying it with a subgroup of
an H* equal to the derived actor.

Root conventions use the existing licensed ATLAS port; see LICENSES/ATLAS.txt.
No additional ATLAS source is copied here.
-/

@[expose] public noncomputable section
open Atlas.G2 Atlas.SplitOctonion Atlas.G2.Natural Atlas.G2.Explicit
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Actors

/-- The three commuting root coordinates fixing the base pencil. -/
def rootActor (a b c : ZMod 2) : Model (ZMod 2) :=
  BinaryCore.embedding ⟨a,b,c,0,0⟩

/-- The action on all eight octonion coordinates, before taking trace or quotient. -/
theorem rootActor_apply (a b c : ZMod 2) (x : Carrier (ZMod 2)) :
    (rootActor a b c).val x =
    ![x 0 + a*x 6 + b*x 5 + c*(x 3+x 4) + c*x 7,
      x 1 + c*x 5 + a*x 7, x 2 + c*x 6 + b*x 7,
      x 3+c*x 7,x 4+c*x 7,x 5,x 6,x 7] := by
  have hneg : ∀ a : ZMod 2, -a = a := by decide
  have hsq : ∀ a : ZMod 2, a^2 = a := by decide
  ext i
  fin_cases i <;>
    simp [rootActor, BinaryCore.embedding, BinaryCore.parameters, unipotentProduct,
      rootA, rootB, rootC, rootD, rootE, rootF, rootAEquiv, rootBEquiv, rootCEquiv,
      rootDEquiv, rootEEquiv, rootFEquiv, rootALinear, rootBLinear, rootCLinear,
      rootDLinear, rootELinear, rootFLinear, rootAApply, rootBApply, rootCApply,
      rootDApply, rootEApply, rootFApply, sub_eq_add_neg, hneg, hsq]
  ring

private theorem ext_four (g h : Model (ZMod 2))
    (h0 : g.val (basisVector 0) = h.val (basisVector 0))
    (h1 : g.val (basisVector 1) = h.val (basisVector 1))
    (h2 : g.val (basisVector 2) = h.val (basisVector 2))
    (h7 : g.val (basisVector 7) = h.val (basisVector 7)) : g = h := by
  have product (i j k : Fin 8) (hi : g.val (basisVector i) = h.val (basisVector i))
      (hj : g.val (basisVector j) = h.val (basisVector j))
      (hp : Atlas.SplitOctonion.mul (basisVector (F := ZMod 2) i) (basisVector j) = basisVector k) :
      g.val (basisVector k) = h.val (basisVector k) := by
    rw [← hp, automorphism_mul, automorphism_mul, hi, hj]
  have h3 := product 0 7 3 h0 h7 (by decide)
  have h4 := product 7 0 4 h7 h0 (by decide)
  have h5 := product 1 7 5 h1 h7 (by decide)
  have h6 := product 2 7 6 h2 h7 (by decide)
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun (ZMod 2) (Fin 8)).ext
  intro i
  change g.val ((Pi.basisFun (ZMod 2) (Fin 8)) i) = h.val ((Pi.basisFun (ZMod 2) (Fin 8)) i)
  simp only [Pi.basisFun_apply]
  change g.val (basisVector i) = h.val (basisVector i)
  fin_cases i <;> assumption

/-- Exhaustiveness of the root-coordinate centralizer, derived from the norm. -/
theorem fixes_three_iff (g : Model (ZMod 2)) :
    (g.val (basisVector 0) = basisVector 0 ∧
      g.val (basisVector 1) = basisVector 1 ∧ g.val (basisVector 2) = basisVector 2) ↔
    g ∈ BinaryCore.elementary := by
  constructor
  · rintro ⟨h0,h1,h2⟩
    let y := g.val (basisVector 7)
    have h7 : y 7 = 1 := by
      have hp := automorphism_normPolar g (basisVector 0) (basisVector 7)
      rw [h0] at hp
      simpa [normPolar, basisVector, y] using hp
    have h6 : y 6 = 0 := by
      have hp := automorphism_normPolar g (basisVector 1) (basisVector 7)
      rw [h1] at hp
      simpa [normPolar, basisVector, y] using hp
    have h5 : y 5 = 0 := by
      have hp := automorphism_normPolar g (basisVector 2) (basisVector 7)
      rw [h2] at hp
      simpa [normPolar, basisVector, y] using hp
    have ht : y 3 + y 4 = 0 := by
      simpa [trace, basisVector, y] using automorphism_trace g (basisVector 7)
    have hn : y 0 * y 7 + y 1 * y 6 + y 2 * y 5 + y 3 * y 4 = 0 := by
      simpa [Atlas.SplitOctonion.norm, basisVector, y] using automorphism_norm g (basisVector 7)
    have h34 : y 4 = y 3 := by
      have : ∀ a b : ZMod 2, a+b=0 → b=a := by decide
      exact this _ _ ht
    have h03 : y 0 = y 3 := by
      rw [h7,h6,h5,h34] at hn
      have hh : ∀ a b : ZMod 2, a + b*b = 0 → a=b := by decide
      exact hh _ _ (by simpa using hn)
    have he : g = rootActor (y 1) (y 2) (y 3) := by
      apply ext_four
      · rw [h0, rootActor_apply]; ext i; fin_cases i <;> simp [basisVector]
      · rw [h1, rootActor_apply]; ext i; fin_cases i <;> simp [basisVector]
      · rw [h2, rootActor_apply]; ext i; fin_cases i <;> simp [basisVector]
      · rw [rootActor_apply]
        change y = _
        ext i
        fin_cases i <;> simp [basisVector, h7,h6,h5,h34,h03]
    exact ⟨⟨y 1,y 2,y 3,0,0⟩, ⟨rfl,rfl⟩, he.symm⟩
  · rintro ⟨x,⟨hd,he⟩,rfl⟩
    have hx : x = ⟨x.a,x.b,x.c,0,0⟩ := by cases x; simp_all
    rw [hx]
    change (rootActor x.a x.b x.c).val _ = _ ∧
      (rootActor x.a x.b x.c).val _ = _ ∧ (rootActor x.a x.b x.c).val _ = _
    simp only [rootActor_apply]
    constructor
    · ext i; fin_cases i <;> simp [basisVector]
    constructor <;> ext i <;> fin_cases i <;> simp [basisVector]


/-- The third root coordinate detects the index-two derived subgroup. -/
theorem rootActor_mem_derived (a b c : ZMod 2) :
    rootActor a b c ∈ commutator (Model (ZMod 2)) ↔ c = 0 := by
  exact BinaryParabolicPair.embedding_mem_derived_iff ⟨a,b,c,0,0⟩

/-- The elementary eight meets the genuine commutator group in the root four. -/
theorem elementary_inf_derived :
    BinaryCore.elementary ⊓ commutator (Model (ZMod 2)) = BinaryCore.natural := by
  ext g
  constructor
  · rintro ⟨⟨x,⟨hd,he⟩,rfl⟩,hg⟩
    have hx : x = ⟨x.a,x.b,x.c,0,0⟩ := by cases x; simp_all
    rw [hx] at hg
    have hc := (rootActor_mem_derived x.a x.b x.c).mp hg
    exact ⟨x,⟨hc,hd,he⟩,rfl⟩
  · rintro ⟨x,⟨hc,hd,he⟩,rfl⟩
    refine ⟨⟨x,⟨hd,he⟩,rfl⟩,?_⟩
    have hx : x = ⟨x.a,x.b,0,0,0⟩ := by cases x; simp_all
    rw [hx]
    exact (rootActor_mem_derived x.a x.b 0).mpr rfl

open Representation.BinaryOffender
open scoped IsMulCommutative
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- A* is the pointwise centralizer of the pencil span in the full actor. -/
def fullCentralizer (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (p : SingularPoints (ZMod 2)) : Subgroup (Model (ZMod 2)) :=
  subspaceKernel ρ (pencilSpan f p) ⊤

/-- B* is the same pointwise centralizer intersected with the actual derived actor. -/
def derivedCentralizer (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (p : SingularPoints (ZMod 2)) : Subgroup (Model (ZMod 2)) :=
  fullCentralizer f ρ p ⊓ commutator (Model (ZMod 2))

@[simp] theorem mem_fullCentralizer (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (p : SingularPoints (ZMod 2)) (g : Model (ZMod 2)) :
    g ∈ fullCentralizer f ρ p ↔ ∀ w ∈ pencilSpan f p, ρ g w = w := by
  simp [fullCentralizer]

private def lowerBasis (i : Fin 3) : TraceZero (ZMod 2) :=
  ⟨basisVector (Fin.castLE (by decide) i), by fin_cases i <;> simp [trace,basisVector]⟩

private theorem lowerBasis_norm (i : Fin 3) :
    Atlas.SplitOctonion.norm (lowerBasis i).val = 0 := by
  fin_cases i <;> simp [lowerBasis, Atlas.SplitOctonion.norm,basisVector]

private theorem lowerBasis_mem (i : Fin 3) :
    (lowerBasis i).val ∈ distinguishedPlane :=
  basis_mem_distinguishedPlane _ i.isLt

theorem fullCentralizer_firstPoint (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ) :
    fullCentralizer f ρ firstPoint = BinaryCore.elementary := by
  ext g
  rw [mem_fullCentralizer, pencilSpan_firstPoint]
  constructor
  · intro h
    have he (i : Fin 3) : g.val (lowerBasis i).val = (lowerBasis i).val := by
      have hfix := h (f.linear (lowerBasis i)) ⟨lowerBasis i,lowerBasis_mem i,rfl⟩
      rw [hf] at hfix
      have he := f.separates (traceZeroAction (ZMod 2) g (lowerBasis i)) (lowerBasis i)
        ((automorphism_norm g _).trans (lowerBasis_norm i)) (lowerBasis_norm i) hfix
      exact congrArg Subtype.val he
    exact (fixes_three_iff g).mp ⟨he 0,he 1,he 2⟩
  · rintro ⟨x,⟨hd,he⟩,rfl⟩ w ⟨v,hv,rfl⟩
    have hx : x = ⟨x.a,x.b,x.c,0,0⟩ := by cases x; simp_all
    rw [hf]
    apply congrArg f.linear
    apply Subtype.ext
    change (BinaryCore.embedding x).val v.val = v.val
    rw [hx]
    change (rootActor x.a x.b x.c).val v.val = v.val
    change v.val ∈ distinguishedPlane at hv
    rw [rootActor_apply, distinguishedPlane_coordinates hv]
    ext i
    fin_cases i <;> simp

theorem derivedCentralizer_firstPoint (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ) :
    derivedCentralizer f ρ firstPoint = BinaryCore.natural := by
  rw [derivedCentralizer, fullCentralizer_firstPoint f ρ hf, elementary_inf_derived]


theorem fullCentralizer_conjugate (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (g : Model (ZMod 2)) (p : SingularPoints (ZMod 2)) :
    (fullCentralizer f ρ p).map (MulAut.conj g).toMonoidHom =
      fullCentralizer f ρ (g • p) := by
  ext a
  rw [mem_fullCentralizer, ← pencilSpan_equivariant f ρ hf g p]
  constructor
  · rintro ⟨b,hb,rfl⟩ w ⟨v,hv,rfl⟩
    change ρ (g*b*g⁻¹) (ρ g v) = ρ g v
    simp only [map_mul, Module.End.mul_apply, ρ.inv_self_apply,
      (mem_fullCentralizer f ρ p b).mp hb v hv]
  · intro h
    refine ⟨g⁻¹*a*g, (mem_fullCentralizer f ρ p _).mpr ?_, ?_⟩
    · intro v hv
      have he := h (ρ g v) (Submodule.mem_map_of_mem hv)
      change ρ (g⁻¹*a*g) v = v
      simp only [map_mul, Module.End.mul_apply, he, ρ.inv_self_apply]
    · change g*(g⁻¹*a*g)*g⁻¹ = a
      group

theorem derivedCentralizer_conjugate (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (g : Model (ZMod 2)) (p : SingularPoints (ZMod 2)) :
    (derivedCentralizer f ρ p).map (MulAut.conj g).toMonoidHom =
      derivedCentralizer f ρ (g • p) := by
  rw [derivedCentralizer, Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
    fullCentralizer_conjugate f ρ hf]
  change fullCentralizer f ρ (g • p) ⊓ _ = fullCentralizer f ρ (g • p) ⊓ _
  exact congrArg (fullCentralizer f ρ (g • p) ⊓ ·)
    (Subgroup.Normal.map_conj_eq (commutator (Model (ZMod 2))) g)

private theorem natural_elementary : IsElementaryAbelian 2 BinaryCore.natural := by
  let i := Subgroup.inclusion BinaryCore.natural_le_elementary
  refine { is_comm := ⟨?_⟩, exponent_dvd_p := ?_ }
  · intro x y
    apply Subtype.ext
    exact congrArg (fun z : BinaryCore.elementary => (z : Model (ZMod 2))) (mul_comm (i x) (i y))
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian x.val
      (BinaryCore.natural_le_elementary x.property)

theorem fullCentralizer_structure (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (p : SingularPoints (ZMod 2)) :
    IsElementaryAbelian 2 (fullCentralizer f ρ p) ∧
      Nat.card (fullCentralizer f ρ p) = 8 := by
  obtain ⟨g,hg⟩ := exists_smul_firstPoint p
  have hp : g⁻¹ • firstPoint = p := by rw [← hg, inv_smul_smul]
  rw [← hp, ← fullCentralizer_conjugate f ρ hf,
    fullCentralizer_firstPoint f ρ hf]
  exact ⟨IsElementaryAbelian.map _,
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).trans BinaryCore.card_elementary⟩

theorem derivedCentralizer_structure (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (p : SingularPoints (ZMod 2)) :
    IsElementaryAbelian 2 (derivedCentralizer f ρ p) ∧
      Nat.card (derivedCentralizer f ρ p) = 4 := by
  obtain ⟨g,hg⟩ := exists_smul_firstPoint p
  have hp : g⁻¹ • firstPoint = p := by rw [← hg, inv_smul_smul]
  rw [← hp, ← derivedCentralizer_conjugate f ρ hf,
    derivedCentralizer_firstPoint f ρ hf]
  let := natural_elementary
  exact ⟨IsElementaryAbelian.map _,
    (Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective).trans BinaryCore.card_natural⟩

theorem derivedCentralizer_le (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (p : SingularPoints (ZMod 2)) :
    derivedCentralizer f ρ p ≤ commutator (Model (ZMod 2)) := inf_le_right

theorem derivedCentralizer_actor (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (p : SingularPoints (ZMod 2)) :
    subspaceKernel (ρ.comp (commutator (Model (ZMod 2))).subtype) (pencilSpan f p) ⊤ =
      (derivedCentralizer f ρ p).subgroupOf (commutator (Model (ZMod 2))) := by
  ext g
  change (True ∧ ∀ w ∈ pencilSpan f p, ρ g.val w = w) ↔
    (True ∧ ∀ w ∈ pencilSpan f p, ρ g.val w = w) ∧ g.val ∈ commutator (Model (ZMod 2))
  simp [g.property]


theorem derivedActorCentralizer_structure (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (p : SingularPoints (ZMod 2)) :
    IsElementaryAbelian 2 (subspaceKernel (ρ.comp (commutator (Model (ZMod 2))).subtype)
      (pencilSpan f p) ⊤) ∧
    Nat.card (subspaceKernel (ρ.comp (commutator (Model (ZMod 2))).subtype)
      (pencilSpan f p) ⊤) = 4 := by
  rw [derivedCentralizer_actor]
  obtain ⟨he,hc⟩ := derivedCentralizer_structure f ρ hf p
  let := he
  exact ⟨IsElementaryAbelian.subgroupOf (derivedCentralizer_le f ρ p),
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (derivedCentralizer_le f ρ p)).toEquiv).trans hc⟩

theorem fullCentralizer_not_le_derived (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (p : SingularPoints (ZMod 2)) :
    ¬ fullCentralizer f ρ p ≤ commutator (Model (ZMod 2)) := by
  intro h
  have he : derivedCentralizer f ρ p = fullCentralizer f ρ p := inf_eq_left.mpr h
  have hc := (derivedCentralizer_structure f ρ hf p).2
  rw [he, (fullCentralizer_structure f ρ hf p).2] at hc
  contradiction

/-- The marked polar hyperplane, formed in the trace-zero octonions and then
mapped into the chosen natural or Weyl module. -/
def perpendicular (f : SingularMap W) (p : SingularPoints (ZMod 2)) :
    Submodule (ZMod 2) W := f.image (LinearMap.ker (normPolar p.val.rep))

variable {H Q : Type*} [Group H] [Group Q] [MulAction H Q]

private theorem fixingSubgroup_transport {D : Type*} [Group D]
    (ρ : Representation (ZMod 2) D W) (P : Submodule (ZMod 2) W)
    (e : Multiplicative W ≃* Q) (α : D ≃* H)
    (he : ∀ g w, α g • e (Multiplicative.ofAdd w) = e (Multiplicative.ofAdd (ρ g w))) :
    _root_.fixingSubgroup H (P.toAddSubgroup.toSubgroup.map e.toMonoidHom : Set Q) =
      (subspaceKernel ρ P ⊤).map α.toMonoidHom := by
  ext a
  constructor
  · intro ha
    obtain ⟨g,rfl⟩ := α.surjective a
    refine ⟨g,⟨Subgroup.mem_top _,?_⟩,rfl⟩
    intro w hw
    apply Multiplicative.ofAdd.injective
    apply e.injective
    rw [← he]
    exact (_root_.mem_fixingSubgroup_iff H).mp ha _ ⟨Multiplicative.ofAdd w,hw,rfl⟩
  · rintro ⟨g,⟨_,hg⟩,rfl⟩
    apply (_root_.mem_fixingSubgroup_iff H).mpr
    rintro _ ⟨w,hw,rfl⟩
    change α g • e (Multiplicative.ofAdd w.toAdd) = e (Multiplicative.ofAdd w.toAdd)
    rw [he, hg w.toAdd hw]

theorem quotient_fullCentralizer_eq (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (e : Multiplicative W ≃* Q) (α : Model (ZMod 2) ≃* H)
    (he : ∀ g w, α g • e (Multiplicative.ofAdd w) = e (Multiplicative.ofAdd (ρ g w)))
    (p : SingularPoints (ZMod 2)) :
    _root_.fixingSubgroup H
      (quotientPencilSpan (transportGeometry f.geometry e)
        ((transportGeometry f.geometry e).point p) : Set Q) =
      (fullCentralizer f ρ p).map α.toMonoidHom := by
  rw [quotientPencilSpan_eq]
  exact fixingSubgroup_transport ρ (pencilSpan f p) e α he

theorem quotient_derivedCentralizer_eq (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (e : Multiplicative W ≃* Q) (α : commutator (Model (ZMod 2)) ≃* H)
    (he : ∀ g w, α g • e (Multiplicative.ofAdd w) = e (Multiplicative.ofAdd (ρ g.val w)))
    (p : SingularPoints (ZMod 2)) :
    _root_.fixingSubgroup H
      (quotientPencilSpan (transportGeometry f.geometry e)
        ((transportGeometry f.geometry e).point p) : Set Q) =
      ((derivedCentralizer f ρ p).subgroupOf (commutator (Model (ZMod 2)))).map α.toMonoidHom := by
  rw [quotientPencilSpan_eq, ← derivedCentralizer_actor]
  exact fixingSubgroup_transport (ρ.comp (commutator (Model (ZMod 2))).subtype)
    (pencilSpan f p) e α he

theorem quotient_fullCentralizer_structure (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (e : Multiplicative W ≃* Q) (α : Model (ZMod 2) ≃* H)
    (he : ∀ g w, α g • e (Multiplicative.ofAdd w) = e (Multiplicative.ofAdd (ρ g w)))
    (p : SingularPoints (ZMod 2)) :
    IsElementaryAbelian 2 (_root_.fixingSubgroup H
      (quotientPencilSpan (transportGeometry f.geometry e)
        ((transportGeometry f.geometry e).point p) : Set Q)) ∧
    Nat.card (_root_.fixingSubgroup H
      (quotientPencilSpan (transportGeometry f.geometry e)
        ((transportGeometry f.geometry e).point p) : Set Q)) = 8 := by
  rw [quotient_fullCentralizer_eq f ρ e α he p]
  obtain ⟨hA,hcard⟩ := fullCentralizer_structure f ρ hf p
  let := hA
  exact ⟨IsElementaryAbelian.map _,
    (Subgroup.card_map_of_injective α.injective).trans hcard⟩

theorem quotient_derivedCentralizer_structure (f : SingularMap W)
    (ρ : Representation (ZMod 2) (Model (ZMod 2)) W) (hf : f.Equivariant ρ)
    (e : Multiplicative W ≃* Q) (α : commutator (Model (ZMod 2)) ≃* H)
    (he : ∀ g w, α g • e (Multiplicative.ofAdd w) = e (Multiplicative.ofAdd (ρ g.val w)))
    (p : SingularPoints (ZMod 2)) :
    IsElementaryAbelian 2 (_root_.fixingSubgroup H
      (quotientPencilSpan (transportGeometry f.geometry e)
        ((transportGeometry f.geometry e).point p) : Set Q)) ∧
    Nat.card (_root_.fixingSubgroup H
      (quotientPencilSpan (transportGeometry f.geometry e)
        ((transportGeometry f.geometry e).point p) : Set Q)) = 4 := by
  rw [quotient_derivedCentralizer_eq f ρ e α he p, ← derivedCentralizer_actor]
  obtain ⟨hB,hcard⟩ := derivedActorCentralizer_structure f ρ hf p
  let := hB
  exact ⟨IsElementaryAbelian.map _,
    (Subgroup.card_map_of_injective α.injective).trans hcard⟩


/-- Both source centralizers in the actual natural representation, at an
arbitrary geometric singular point. -/
theorem natural_centralizers (p : SingularPoints (ZMod 2)) :
    (IsElementaryAbelian 2 (fullCentralizer naturalMap (action (ZMod 2)) p) ∧
      Nat.card (fullCentralizer naturalMap (action (ZMod 2)) p) = 8) ∧
    (IsElementaryAbelian 2 (derivedCentralizer naturalMap (action (ZMod 2)) p) ∧
      Nat.card (derivedCentralizer naturalMap (action (ZMod 2)) p) = 4) :=
  ⟨fullCentralizer_structure naturalMap (action (ZMod 2)) naturalMap_equivariant p,
    derivedCentralizer_structure naturalMap (action (ZMod 2)) naturalMap_equivariant p⟩

/-- The same centralizers in the actual trace-zero Weyl representation. -/
theorem weyl_centralizers (p : SingularPoints (ZMod 2)) :
    (IsElementaryAbelian 2 (fullCentralizer weylMap (traceZeroAction (ZMod 2)) p) ∧
      Nat.card (fullCentralizer weylMap (traceZeroAction (ZMod 2)) p) = 8) ∧
    (IsElementaryAbelian 2 (derivedCentralizer weylMap (traceZeroAction (ZMod 2)) p) ∧
      Nat.card (derivedCentralizer weylMap (traceZeroAction (ZMod 2)) p) = 4) :=
  ⟨fullCentralizer_structure weylMap (traceZeroAction (ZMod 2)) weylMap_equivariant p,
    derivedCentralizer_structure weylMap (traceZeroAction (ZMod 2)) weylMap_equivariant p⟩

variable {G : Type*} [Group G]

/-- The full-actor centralizer is an elementary eight on the literal source
quotient, provided with its actual equivariant model and singular-point marking.
In the full case of 14.7.55(4), take this actor to be H*. -/
theorem source_fullCentralizer_structure (U V₁ V₂ : Subgroup G)
    [(V₁.subgroupOf U).Normal] [MulAction H (U ⧸ V₁.subgroupOf U)]
    (f : SingularMap W) (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (hf : f.Equivariant ρ) (e : Multiplicative W ≃* U ⧸ V₁.subgroupOf U)
    (α : Model (ZMod 2) ≃* H)
    (he : ∀ g w, α g • e (Multiplicative.ofAdd w) = e (Multiplicative.ofAdd (ρ g w)))
    (p : SingularPoints (ZMod 2))
    (hmark : (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
      (transportGeometry f.geometry e).point p) :
    IsElementaryAbelian 2 (_root_.fixingSubgroup H
      (quotientPencilSpan (transportGeometry f.geometry e)
        ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) :
        Set (U ⧸ V₁.subgroupOf U))) ∧
    Nat.card (_root_.fixingSubgroup H
      (quotientPencilSpan (transportGeometry f.geometry e)
        ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) :
        Set (U ⧸ V₁.subgroupOf U))) = 8 := by
  rw [hmark]
  exact quotient_fullCentralizer_structure f ρ hf e α he p

/-- The derived-actor centralizer is an elementary four on the literal source
quotient. This uses an equivalence with the actual commutator subgroup and
therefore also applies when H*=K*, without inserting an elementary eight into H*. -/
theorem source_derivedCentralizer_structure (U V₁ V₂ : Subgroup G)
    [(V₁.subgroupOf U).Normal] [MulAction H (U ⧸ V₁.subgroupOf U)]
    (f : SingularMap W) (ρ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (hf : f.Equivariant ρ) (e : Multiplicative W ≃* U ⧸ V₁.subgroupOf U)
    (α : commutator (Model (ZMod 2)) ≃* H)
    (he : ∀ g w, α g • e (Multiplicative.ofAdd w) = e (Multiplicative.ofAdd (ρ g.val w)))
    (p : SingularPoints (ZMod 2))
    (hmark : (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
      (transportGeometry f.geometry e).point p) :
    IsElementaryAbelian 2 (_root_.fixingSubgroup H
      (quotientPencilSpan (transportGeometry f.geometry e)
        ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) :
        Set (U ⧸ V₁.subgroupOf U))) ∧
    Nat.card (_root_.fixingSubgroup H
      (quotientPencilSpan (transportGeometry f.geometry e)
        ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) :
        Set (U ⧸ V₁.subgroupOf U))) = 4 := by
  rw [hmark]
  exact quotient_derivedCentralizer_structure f ρ hf e α he p

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.Actors
