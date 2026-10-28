module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.Basic
public import Theory.GroupAction.SubgroupQuotientCommutatorBound

/-!
# Source 3.3 quotient action control

For a critical pair `(a,a')` and an adjacent vertex `t`, the endpoint layer
`X a'` is normalized by `Q t`.  The auxiliary layer
`[X a, X a']` is relatively normal in `X a'`; this is proved from the
critical intersection and the elementary-abelian endpoint layer.  The native
quotient-conjugation transfer therefore turns an explicit displacement
calculation in `X a'/[X a,X a']` into the literal source-3.3 containment.

`CriticalQuotientActionData` is the source-faithful interface for the remaining
model calculation.  Its action is an actual action on the subgroup quotient,
and its displacement field has exactly the image of
`X a ∩ Q a'` against `Y`.  No model carrier, common-image assertion, offender
uniqueness, or later source (3.8) input is folded into this interface.

Source: Meierfrankenfeld–Stellmacher (1993), (3.3), p.866; the quotient
transfer is the checked subgroup-conjugation lemma in
`Theory.GroupAction.SubgroupQuotientCommutatorBound`.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-! The three marked source branches have the same action interface once the
coordinate map is viewed as a homomorphism. Keeping this interface separate
from `CriticalQuotientActionData` lets the source-three consumer transport a
branch action before doing its local displacement calculation. -/

structure MarkedUAction (source : LocalSource L R) (m : ℕ) where
  marking : SL ≃* SL
  coordinate : U R (alpha R) →* Multiplicative (Fin m → Fin 3 → ZMod 2)
  action : ∀ (g : M) (u v : U R (alpha R)),
    (v : FreeAmalgam R) = embedM R g * (u : FreeAmalgam R) * (embedM R g)⁻¹ →
    ∀ i : Fin m, (coordinate v).toAdd i =
      (marking (source.projection g)).val.mulVec ((coordinate u).toAdd i)

noncomputable def MovingCopies.marked {source : LocalSource L R} {m : ℕ}
    (model : MovingCopies source m) : MarkedUAction source m where
  marking := model.marking
  coordinate := model.equiv.toMonoidHom
  action := model.action

noncomputable def MovingQuotient.marked {source : LocalSource L R} {m : ℕ}
    (model : MovingQuotient source m) : MarkedUAction source m where
  marking := model.marking
  coordinate := model.projection
  action := model.action

noncomputable def NaturalU.marked {source : LocalSource L R}
    (model : NaturalU R source.projection) : MarkedUAction source 1 where
  marking := model.marking
  coordinate := {
    toFun := fun u => Multiplicative.ofAdd (fun _ : Fin 1 => (model.equiv u).toAdd)
    map_one' := by
      ext i j
      simp
    map_mul' := by
      intro u v
      ext i j
      simp }
  action := by
    intro g u v hv i
    have h := model.action g u v hv
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change (model.equiv v).toAdd =
      (model.marking (source.projection g)).val.mulVec ((model.equiv u).toAdd)
    exact h

/-! Conjugation gives the actual moving-layer carrier at every transported
vertex. This is the common carrier equivalence used by all three marked
models. -/

noncomputable def uTransport (f : FreeAmalgam R) :
    U R (alpha R) ≃* U R (act R f (alpha R)) := by
  exact (MulAut.conj f⁻¹).subgroupMap (U R (alpha R)) |>.trans
    (MulEquiv.subgroupCongr (U_act R f (alpha R)).symm)

omit [Finite M] in
@[simp] theorem uTransport_val (f : FreeAmalgam R) (u : U R (alpha R)) :
    ((uTransport (R := R) f u : U R (act R f (alpha R))) : FreeAmalgam R) =
      f⁻¹ * (u : FreeAmalgam R) * f := by
  change (MulAut.conj f⁻¹) (u : FreeAmalgam R) = _
  simp [MulAut.conj]

omit [Finite M] in
noncomputable def movedCoordinate {m : ℕ} {source : LocalSource L R}
    (model : MarkedUAction source m) (f : FreeAmalgam R) :
    U R (act R f (alpha R)) →* Multiplicative (Fin m → Fin 3 → ZMod 2) :=
  model.coordinate.comp (uTransport (R := R) f).symm.toMonoidHom

omit [Finite M] in
theorem movedCoordinate_action {m : ℕ} {source : LocalSource L R}
    (model : MarkedUAction source m) (f : FreeAmalgam R) (g : M)
    (u v : U R (alpha R))
    (hv : (uTransport (R := R) f v : FreeAmalgam R) =
      (f⁻¹ * embedM R g * f) * (uTransport (R := R) f u : FreeAmalgam R) *
        (f⁻¹ * embedM R g * f)⁻¹) :
    ∀ i : Fin m, (movedCoordinate model f (uTransport f v)).toAdd i =
      (model.marking (source.projection g)).val.mulVec
        ((movedCoordinate model f (uTransport f u)).toAdd i) := by
  have hv' : (v : FreeAmalgam R) = embedM R g * (u : FreeAmalgam R) *
      (embedM R g)⁻¹ := by
    have h := hv
    rw [uTransport_val, uTransport_val] at h
    simpa [mul_assoc] using congrArg (fun z => f * z * f⁻¹) h
  have h := model.action g u v hv'
  intro i
  simpa [movedCoordinate] using h i

omit [Finite M] in
/-- Every bad branch supplies one of the common marked action carriers.  This
projection records the branch transport without identifying the carriers or
discarding the central kernel of the one-copy quotient. -/
theorem badCase_marked_action (source : LocalSource L R) (h : BadCase source) :
    Nonempty (MarkedUAction source 2) ∨ Nonempty (MarkedUAction source 1) := by
  rcases h with h | h | h
  · obtain ⟨model⟩ := h.1
    exact Or.inl ⟨model.marked⟩
  · obtain ⟨model⟩ := h.1
    exact Or.inr ⟨model.marked⟩
  · obtain ⟨model⟩ := h.1
    exact Or.inr ⟨CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives.NaturalU.marked model⟩

omit [Finite M] in
/-- The endpoint layer is normalized by the adjacent edge kernel. -/
theorem critical_endpoint_X_normalizer (a' t : Vertex R)
    (hat : Adjacent R a' t) :
    Q R t ≤ normalizer (X R a' : Set (FreeAmalgam R)) := by
  intro x hx
  have hQt : Q R t ≤ stabilizer R a' := by
    intro z hz
    exact hz.2 a' (adjacent_symm R hat)
  exact (X_normalized R a') (hQt hx)

theorem critical_commutator_quotient_normal (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) :
    (⁅X R a, X R a'⁆).subgroupOf (X R a') |>.Normal := by
  let _ := X_elementary R a'
  apply Subgroup.normal_subgroupOf_of_le_normalizer (H := X R a') (N := ⁅X R a, X R a'⁆)
  apply (le_centralizer_iff.mpr ?_).trans (Subgroup.centralizer_le_normalizer _)
  intro x hx y hy
  have hxX : x ∈ X R a' :=
    (critical_commutator_le_intersection source geometry hb a ha a' hc).trans inf_le_right hx
  change x ∈ omegaCenter (Q R a') at hxX
  change y ∈ omegaCenter (Q R a') at hy
  exact (mem_omegaCenter_iff.mp hxX).2.2 y (omegaCenter_le _ hy)

/-- The exact action and displacement data consumed by source 3.3.

The `letI` installs the relative normality proved above before elaborating the
literal subgroup quotient.  The endpoint conjugation proof is explicit, so a
consumer can use this record without any hidden normality or quotient
convention.
-/
def CriticalQuotientActionData (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false)
    (a' : Vertex R) (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a' t)
    (Y : Subgroup (FreeAmalgam R)) : Prop :=
  letI : (⁅X R a, X R a'⁆).subgroupOf (X R a') |>.Normal :=
    critical_commutator_quotient_normal source geometry hb a ha a' hc
  ∃ action : Q R t →* MulAut (X R a' ⧸ (⁅X R a, X R a'⁆).subgroupOf (X R a')),
    (∀ actor : Q R t, ∀ point : X R a',
      action actor (QuotientGroup.mk' ((⁅X R a, X R a'⁆).subgroupOf (X R a')) point) =
        QuotientGroup.mk' ((⁅X R a, X R a'⁆).subgroupOf (X R a'))
          ⟨(actor : FreeAmalgam R) * (point : FreeAmalgam R) * (actor : FreeAmalgam R)⁻¹,
            (mem_normalizer_iff.mp
              (critical_endpoint_X_normalizer a' t hat actor.property) point).mp point.property⟩) ∧
    (∀ actor : Q R t, (actor : FreeAmalgam R) ∈ Y → ∀ point : X R a',
      (point : FreeAmalgam R) ∈ Z R a' →
      (QuotientGroup.mk' ((⁅X R a, X R a'⁆).subgroupOf (X R a')) point)⁻¹ *
          action actor (QuotientGroup.mk' ((⁅X R a, X R a'⁆).subgroupOf (X R a')) point) ∈
        (⁅X R a ⊓ Q R a', Y⁆.subgroupOf (X R a')).map
          (QuotientGroup.mk' ((⁅X R a, X R a'⁆).subgroupOf (X R a'))))

/-- The quotient displacement datum gives the source-3.3 bound with the
literal orientation `[Z a',Y]` and `[X a ∩ Q a',Y]`. -/
theorem source33_of_critical_action (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (t : Vertex R) (hat : Adjacent R a' t)
    (ht : (cosetGraph R).dist a t + 1 = (cosetGraph R).dist a a')
    (Y : Subgroup (FreeAmalgam R)) (hY : Y ≤ Q R t)
    (hdata : CriticalQuotientActionData source geometry hb a ha a' hc t hat Y) :
    ⁅Z R a', Y⁆ ≤ ⁅X R a, X R a'⁆ ⊔ ⁅X R a ⊓ Q R a', Y⁆ := by
  let _ := ht
  let hD := critical_commutator_quotient_normal source geometry hb a ha a' hc
  rcases hdata with ⟨action, hformula, hcontrol⟩
  have hPQ : Q R t ≤ normalizer (X R a' : Set (FreeAmalgam R)) :=
    critical_endpoint_X_normalizer a' t hat
  have hCQ : Z R a' ≤ X R a' :=
    (critical_endpoint_choice source geometry hb a ha a' hc).1
  have h := @Subgroup.quotient_conjugation_commutator_le_sup _ _
    (Q R t) (X R a') (⁅X R a, X R a'⁆) (Z R a') Y (⁅X R a ⊓ Q R a', Y⁆)
    hPQ hY hCQ hD action hformula hcontrol
  rw [commutator_comm]
  simpa only [sup_comm] using h

/-- A branch-independent package of the model calculations needed to make the
source-3.3 bound unconditional.  The three `BadCase` branches supply this
field by transporting their marked `MovingCopies`, `MovingQuotient`, or
`NaturalU` action to each critical endpoint. -/
structure Source33ActionControl (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) : Prop where
  control : ∀ (a : Vertex R), ∀ (ha : color R a = false), ∀ (a' : Vertex R),
    (hc : CriticalPair R a a' (geometry.exists_critical a ha)) → ∀ (t : Vertex R),
    (hat : Adjacent R a' t) →
    (ht : (cosetGraph R).dist a t + 1 = (cosetGraph R).dist a a') →
    ∀ Y : Subgroup (FreeAmalgam R), Y ≤ Q R t →
    CriticalQuotientActionData source geometry hb a ha a' hc t hat Y

/-- Assemble the source-3.3 predicate from the branch action calculations. -/
theorem source33Bound_of_action_control (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (hcontrol : Source33ActionControl source geometry hb) :
    Source33Bound R geometry := by
  intro a ha a' hc t hat ht Y hY
  have hdata := hcontrol.control a ha a' hc t hat ht Y (hY.trans inf_le_left)
  exact source33_of_critical_action source geometry hb a ha a' hc t hat ht Y (hY.trans inf_le_left) hdata

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
