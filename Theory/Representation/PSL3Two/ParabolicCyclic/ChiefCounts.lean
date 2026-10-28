module

public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Products
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Reindex
public import Theory.Representation.PSL3Two.ParabolicCyclic
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Natural
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.DualCore
public import Theory.Representation.PSL3Two.ParabolicCyclic.ChiefCounts.Steinberg

/-!
# Chief counts and recognition for the parabolic cyclic alternatives

The actor is the embedded intrinsic two-residual of the marked line parabolic.
The actual natural, core and Steinberg flags have respectively one, two and
three noncentral sections. Concatenating product flags gives four for natural
plus Steinberg and five for core plus Steinberg. The dual natural module also
has one noncentral section, as needed for the original natural section after
switching the point/line marking.

These counts exclude every competing H.6.5 alternative for a cyclic module
with three noncentral chief factors. Count independence compares the supplied
complete flag with each model flag through the actual representation
equivalence. `recognition_of_three_noncentral_sections` discharges all model
count premises. Its source parent supplies the Borel-fixed cyclic seed, the
two-dimensional parabolic span and the quotient's three-factor flag; transport
from the original actor and subtraction of its natural section remain there.

Source: Aschbacher–Smith 14.7.22(2), 14.7.72, and H.6.5.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Representation
namespace BinaryLinearThree.ParabolicCyclic.ChiefCounts

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

/-- The natural-plus-Steinberg alternative has four noncentral chief sections
for the literal embedded line-parabolic two-residual. -/
theorem natural_prod_steinberg_count :
    HasCount (G := actor) (M := Vector × Steinberg) ((W.prod S).comp actor.subtype) 4 :=
  natural_count.prod steinberg_count

/-- The core-plus-Steinberg alternative has five noncentral chief sections
for the literal embedded line-parabolic two-residual. -/
theorem core_prod_steinberg_count :
    HasCount (G := actor) (M := Core × Steinberg) ((U₂.prod S).comp actor.subtype) 5 :=
  core_count.prod steinberg_count

/-- Recognition reduction retaining the core and Steinberg counts as explicit
inputs. The final recognition theorem below supplies their concrete proofs. -/
theorem recognition_of_core_steinberg_counts
    (hU : HasCount (U₂.comp actor.subtype) 2)
    (hS : HasCount (S.comp actor.subtype) 3)
    (ρ : Representation (ZMod 2) Group M) (m : M)
    (hfixed : ∀ g ∈ Matrix.PSL3Two.borelSL, ρ g m = m)
    (hgen : orbitSpan ρ ⊤ m = ⊤)
    (hdim : Module.finrank (ZMod 2) (orbitSpan ρ Matrix.PSL3Two.lineParabolicSL m) = 2)
    (s : Series (ρ.comp actor.subtype)) (h0 : s.head = ⊥) (h1 : s.last = ⊤)
    (hcount : s.count = 3) : Nonempty (ρ.Equiv S) := by
  have hW := natural_count
  have hρ : HasCount (ρ.comp actor.subtype) 3 := ⟨s, h0, h1, hcount⟩
  have hWS : HasCount (G := actor) (M := Vector × Steinberg)
      ((W.prod S).comp actor.subtype) 4 := by
    exact hW.prod hS
  have hUS : HasCount (G := actor) (M := Core × Steinberg)
      ((U₂.prod S).comp actor.subtype) 5 := by
    exact hU.prod hS
  have ha := parabolic_seed_alternatives ρ m hfixed hgen hdim
  change Nonempty (ρ.Equiv W) ∨ Nonempty (ρ.Equiv U₂) ∨ Nonempty (ρ.Equiv S) ∨
    Nonempty (ρ.Equiv (W.prod S)) ∨ Nonempty (ρ.Equiv (U₂.prod S)) at ha
  rcases ha with h | h | h | h | h
  · obtain ⟨e⟩ := h
    have hh := (hρ.mapEquiv (restrictEquiv e actor.subtype)).unique hW
    omega
  · obtain ⟨e⟩ := h
    have hh := (hρ.mapEquiv (restrictEquiv e actor.subtype)).unique hU
    omega
  · exact h
  · obtain ⟨e⟩ := h
    have hh := (hρ.mapEquiv (restrictEquiv e actor.subtype)).unique hWS
    omega
  · obtain ⟨e⟩ := h
    have hh := (hρ.mapEquiv (restrictEquiv e actor.subtype)).unique hUS
    omega

/-- A Borel-fixed cyclic seed whose line-parabolic orbit spans a plane, together
with an actual complete residual chief flag having three noncentral sections,
recognizes the Steinberg module. All five alternative counts are proved; only
the seed and source flag remain inputs to this conditional source application. -/
theorem recognition_of_three_noncentral_sections
    (ρ : Representation (ZMod 2) Group M) (m : M)
    (hfixed : ∀ g ∈ Matrix.PSL3Two.borelSL, ρ g m = m)
    (hgen : orbitSpan ρ ⊤ m = ⊤)
    (hdim : Module.finrank (ZMod 2) (orbitSpan ρ Matrix.PSL3Two.lineParabolicSL m) = 2)
    (s : Series (ρ.comp actor.subtype)) (h0 : s.head = ⊥) (h1 : s.last = ⊤)
    (hcount : s.count = 3) : Nonempty (ρ.Equiv S) :=
  recognition_of_core_steinberg_counts core_count steinberg_count
    ρ m hfixed hgen hdim s h0 h1 hcount

end BinaryLinearThree.ParabolicCyclic.ChiefCounts
