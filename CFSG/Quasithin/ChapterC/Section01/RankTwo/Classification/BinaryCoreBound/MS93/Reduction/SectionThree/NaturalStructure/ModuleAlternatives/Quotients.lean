module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.Actions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.Homogeneous

/-!
# Actual natural coordinates modulo the fixed part of U

The faithful, full-commutator FF-action on the literal moving subgroup U
satisfies the hypotheses of the checked binary recognition theorem. Its
linear quotient coordinates give a surjective group homomorphism with
kernel precisely C ∩ U, where C is the residual-fixed subgroup of X. The
same automorphism of the specified quotient marks every natural summand.

This does not split a central extension or classify the remaining part of X.
Those obligations distinguish the four binary cases of MS93 (3.2).
Source: Meierfrankenfeld–Stellmacher (1993), printed p.863; the recognition
input is the binary specialization of Aschbacher–Smith B.5.1, pp.99–103.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- C in the printed alternatives: the residual-fixed subgroup of X. -/
noncomputable def fixedPart (R : Subgroup M) : Subgroup (FreeAmalgam R) :=
  X R (alpha R) ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R))

/-- Actual homogeneous quotient coordinates, retaining the central kernel.
One marking acts on every copy; in particular two copies have the same orientation. -/
structure MovingQuotient (source : LocalSource L R) (m : ℕ) where
  marking : SL ≃* SL
  projection : U R (alpha R) →* Multiplicative (Fin m → Fin 3 → ZMod 2)
  onto : Function.Surjective projection
  kernel : projection.ker = (fixedPart R).subgroupOf (U R (alpha R))
  action : ∀ (g : M) (u v : U R (alpha R)),
    (v : FreeAmalgam R) = embedM R g * (u : FreeAmalgam R) * (embedM R g)⁻¹ →
    ∀ i : Fin m, (projection v).toAdd i =
      (marking (source.projection g)).val.mulVec ((projection u).toAdd i)

variable [Finite M]

/-- Recognition applies to the actual moving layer, with every action premise
proved. The quotient kernel is C ∩ U, not an assumed trivial subgroup. -/
theorem exists_movingQuotient (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) :
    ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ Nonempty (MovingQuotient source m) := by
  let := geometry.U_elementary hb (alpha R) rfl
  let := finite_Z R (alpha R)
  let : Finite (U R (alpha R)) :=
    Finite.of_injective (inclusion (U_le_Z (R := R) (alpha R))) (inclusion_injective _)
  let ρ : Representation (ZMod 2) SL (Additive (U R (alpha R))) :=
    Offenders.linearize (uAction source)
  have hf := uAction_injective source geometry hb
  have hfull := uAction_full source geometry hb
  have hFF := uAction_isFFModule source geometry hb
  have hq : ∃ m : ℕ, (m = 1 ∨ m = 2) ∧
      Nonempty (AbelianCore.QuotientRecognition.ModuleQuotient ρ m) :=
    AbelianCore.QuotientRecognition.ExtensionControl.exists_moduleQuotient ρ hf hfull hFF
  obtain ⟨m, hm, ⟨q⟩⟩ := hq
  let p : U R (alpha R) →* Multiplicative (Fin m → Fin 3 → ZMod 2) := {
    toFun := fun u => Multiplicative.ofAdd (q.projection (Additive.ofMul u))
    map_one' := q.projection.map_zero
    map_mul' := fun u v => q.projection.map_add (Additive.ofMul u) (Additive.ofMul v) }
  refine ⟨m, hm, ⟨{ marking := q.marking, projection := p, onto := ?_, kernel := ?_, action := ?_ }⟩⟩
  · intro v
    obtain ⟨u, hu⟩ := q.surjective v.toAdd
    exact ⟨u.toMul, hu⟩
  · ext u
    change q.projection (Additive.ofMul u) = 0 ↔ (u : FreeAmalgam R) ∈ fixedPart R
    change Additive.ofMul u ∈ q.projection.ker ↔ _
    rw [q.kernel]
    have hf := layerAction_fixed_iff source (U R (alpha R)) (U_normalized (alpha R))
      (Q_centralizes_U (alpha R) rfl) u
    constructor
    · intro hu
      refine ⟨(U_le_Z (alpha R)).trans
        (geometry.omega_bound (alpha R) rfl hb) u.property, hf.mp ?_⟩
      intro g
      exact congrArg Additive.toMul (hu ⟨g, mem_top g⟩)
    · intro hu g
      exact congrArg Additive.ofMul ((hf.mpr hu.2) g.val)
  · intro g u v hv i
    have hact : uAction source (source.projection g) u = v := by
      apply Subtype.ext
      rw [uAction, layerAction_apply, hv]
    have he := q.equivariant (source.projection g) (Additive.ofMul u) i
    change q.projection (Additive.ofMul (uAction source (source.projection g) u)) i = _ at he
    rw [hact] at he
    exact he

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
