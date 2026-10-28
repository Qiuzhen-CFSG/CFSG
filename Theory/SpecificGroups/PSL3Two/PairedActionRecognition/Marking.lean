module
public import Theory.SpecificGroups.PSL3Two.PairedActionRecognition
public import Theory.SpecificGroups.PSL3Two.PairedSylowRecognition
public import Theory.SpecificGroups.PSL3Two.Parabolics.CompatibleMarking
/-!
# Retaining the source Sylow and central involution marks

An existing PSL₃(2) isomorphism can be chosen to send a specified Sylow to
the Borel. Its specified nonidentity central element is then forced to the
highest-root involution. In the recognized pair, a source Sylow containing
the Borel product equals the standard paired subgroup, giving an explicit
multiplicative equivalence compatible with the full model isomorphism.

These are the marking steps in Aschbacher--Smith 2.4.34, printed p.548 of
the 1 March 2004 manuscript. They retain both original component marks.
-/

public section
namespace Matrix.PSL3Two.PairedActionRecognition
open Subgroup PairedSylowRecognition
variable {H:Type*} [Group H]
/-- Mark a prescribed source Sylow and its nontrivial central involution at once. -/
theorem exists_sylow_center_marking [Finite H] (e₀:H≃*PSL) (S:Sylow 2 H)
    (z:S) (hz:z∈center S) (hne:z≠1) :
    ∃ e:H≃*SL, (S:Subgroup H).map e.toMonoidHom=borelSL ∧
      e (z:H)=PairedGraphInputs.highestRoot := by
  obtain ⟨e,he⟩ := exists_sylow_marking e₀ S
  let eS : S≃*borelSL := (e.subgroupMap S).trans (MulEquiv.subgroupCongr he)
  have hcenter : eS z∈center borelSL := by
    rw [mem_center_iff]
    intro y
    obtain ⟨w,rfl⟩ := eS.surjective y
    simpa only [←map_mul] using congrArg eS (mem_center_iff.mp hz w)
  have hnontriv : eS z≠1 := fun h=>hne (eS.injective (h.trans eS.map_one.symm))
  have hm := highestRoot_eq_of_center_ne_one (eS z) hcenter hnontriv
  exact ⟨e,he,hm⟩

/-- The recognized standard paired subgroup is the actual selected source Sylow. -/
noncomputable def sylowEquiv (e:H≃*StandardModel) (S:Sylow 2 H)
    (hbase : standardBase ≤ (S:Subgroup H).map e.toMonoidHom) : standardPaired ≃* S := by
  have : Finite H := Finite.of_equiv StandardModel e.symm.toEquiv
  have hm : (S:Subgroup H).map e.toMonoidHom=standardPaired :=
    sylow_eq_standard_of_base_le (S.mapSurjective (f:=e.toMonoidHom) e.surjective) hbase
  exact ((e.subgroupMap S).trans (MulEquiv.subgroupCongr hm)).symm

theorem sylowEquiv_apply (e:H≃*StandardModel) (S:Sylow 2 H)
    (hbase : standardBase ≤ (S:Subgroup H).map e.toMonoidHom) (u:standardPaired) :
    ((sylowEquiv e S hbase u:S):H)=e.symm u.val := by
  rfl
end Matrix.PSL3Two.PairedActionRecognition
