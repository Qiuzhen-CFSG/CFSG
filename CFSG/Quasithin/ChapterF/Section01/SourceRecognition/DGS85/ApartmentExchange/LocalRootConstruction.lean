module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.MarkedTitsSystem
public import Theory.GroupTheory.WeakBNPair.RegularTree.LocalRootAction

/-!
# The literal DGS root-action application

At both endpoints of the original edge in the universal amalgam tree, use the
chosen reflection and the genuine root orbit on the other neighbors. The
local-action theorems prove the two-cell decomposition, thickness, reflection
square, Borel factorization, and triple-stabilizer conjugation. They supply the
local algebra needed by the marked Tits-system construction.

The original Cartan normality/generation, the root signs in the apartment
quotient, its Borel-normalizer intersection, and short-distance separation
remain explicit. They are still obligations of the Chapter 14/(3.6) geometry
proof, not assumptions hidden in a model or classification callback.

Source: DGS, *Groups and Graphs* (1985), Part II, (3.7), pp.79–80, using
the regular root actions and reflection choices of Chapter 14.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.GroupTheory
open Theory.GroupTheory.WeakBNPair.RegularTree
open Subgroup.CosetGeometry
open RankTwoAmalgam
universe u
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable (α : RankTwoAmalgam L B R) (T : Set (SourceVertex α)) (n : ℕ)
variable (hL : Function.Injective α.left) (hR : Function.Injective α.right)
variable (d : Bool → LocalRootAction (X := α.Universal) (sourceGraph α))
variable (ha : ∀ i, (d i).a = base (Universal.cosetFamily α) i)
variable (hb : ∀ i, (d i).b = base (Universal.cosetFamily α) (!i))

include ha in
/-- The local endpoint is the literal original endpoint in the universal tree. -/
theorem localRoot_endpoint (i : Bool) :
    (d i).endpoint = Universal.cosetFamily α i := by
  change MulAction.stabilizer α.Universal (d i).a = _
  rw [ha i, stabilizer_base]

include hL hR ha hb in
/-- Its Borel is the whole original middle image, at either orientation. -/
theorem localRoot_borel (i : Bool) : (d i).borel = originalMiddle α := by
  change (d i).endpoint ⊓ MulAction.stabilizer α.Universal (d i).b = _
  rw [localRoot_endpoint α d ha i, hb i, stabilizer_base]
  cases i
  · exact Universal.overlap_eq α hL hR
  · rw [inf_comm]
    exact Universal.overlap_eq α hL hR

variable (N : Subgroup α.Universal)
variable (hlift : ∀ i, (d i).reflection ∈ N)
variable (hnormal : ((originalMiddle α ⊓ N).subgroupOf N).Normal)
variable (hgen : N ≤ Subgroup.closure
  ((originalMiddle α ⊓ N : Subgroup α.Universal) ∪ Set.range fun i => (d i).reflection))
variable (hsign : ∀ i x, x ∈ N →
  (∀ r ∈ (d i).root, quotientMap α T n (x⁻¹ * r * x) ∈
    (originalMiddle α).map (quotientMap α T n)) ∨
  (∀ r ∈ (d i).root, quotientMap α T n
    (((d i).reflection * x)⁻¹ * r * ((d i).reflection * x)) ∈
      (originalMiddle α).map (quotientMap α T n)))

/-- All rank-one algebraic premises are discharged from the actual local
root actions; only the Cartan and global geometric premises remain. -/
def localRootQuotientData : RootQuotientData (quotientMap α T n) where
  B := originalMiddle α
  N := N
  endpoint := Universal.cosetFamily α
  lift i := ⟨(d i).reflection, hlift i⟩
  root i := (d i).root
  fixed i := (d i).fixed
  borel_le i := by
    rw [← localRoot_borel α hL hR d ha hb i, ← localRoot_endpoint α d ha i]
    exact inf_le_left
  lift_mem i := by
    rw [← localRoot_endpoint α d ha i]
    exact (d i).reflection_mem
  lift_not_mem i := by
    rw [← localRoot_borel α hL hR d ha hb i]
    exact (d i).reflection_not_mem
  generated := Universal.generated α
  cells := by
    intro i x hx
    rw [← localRoot_borel α hL hR d ha hb i]
    exact (d i).cells (source_action α) x (by rwa [localRoot_endpoint α d ha i])
  thick i := by
    rw [← localRoot_endpoint α d ha i, ← localRoot_borel α hL hR d ha hb i]
    exact (d i).third_coset
  square i := by
    rw [← localRoot_borel α hL hR d ha hb i]
    exact (d i).reflection_square
  normal := hnormal
  normalizer_generated := hgen
  factor := by
    intro i b hmem
    exact (d i).factor (source_action α) b (by rwa [localRoot_borel α hL hR d ha hb i])
  conjugate_fixed := by
    intro i b hmem
    rw [← localRoot_borel α hL hR d ha hb i]
    exact ((d i).conjugate_fixed b hmem).1
  root_sign := hsign

variable (hsep : Separated (sourceRelation α T n) (sourceGraph α) (2 * n))
variable (hn : 1 < n)
variable (hcore : ((Universal.left α).range ⊓ (Universal.right α).range).normalCore = ⊥)
variable (hBN : (originalMiddle α).map (quotientMap α T n) ⊓ N.map (quotientMap α T n) =
  (originalMiddle α ⊓ N).map (quotientMap α T n))

/-- A Tits system on the already constructed apartment quotient, from the
actual original local root actions. -/
abbrev localActionTitsSystem :=
  sourceTitsSystem α T n hL hR hsep hn hcore
    (localRootQuotientData α T n hL hR d ha hb N hlift hnormal hgen hsign) rfl (fun _ => rfl) hBN

/-- Both original maps are retained when the endpoints are identified with
the standard parabolics of `localActionTitsSystem`. -/
noncomputable abbrev localActionMarkedIso :=
  markedStandardIso α T n hL hR hsep hn hcore
    (localRootQuotientData α T n hL hR d ha hb N hlift hnormal hgen hsign) rfl (fun _ => rfl) hBN

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
