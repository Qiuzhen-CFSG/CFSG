module
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondPackedMaps
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.SecondCubicCentralizer

/-!
# Excluding the twisted reflected extension

Compose the native reflection action with the central twist. A packed finite
certificate checks every one of the 2,048 core elements and proves that
`a * badActor(a) * root7 = 1` has no solution. A source extension with this
action and lift square root7 therefore has no involution in that coset.
Matching the source extension with this alternative remains a separate step.

Source: the extension alternatives in the binary Ree F.1.12 calculation,
Aschbacher–Smith J.4.5, pp.441–442. No endpoint model is assumed.
-/

@[expose] public section
noncomputable section

namespace ReeTwo.SylowModel.CubicAction
open Tits.AmalgamRigidity.FullRee.SecondExtension

def reflectionImage (i:Fin 10):A := ⟨weylImage i,by
  rw [mem_firstParabolicCore_iff]
  exact (by decide +kernel : ∀i:Fin 10,(weylImage i).left.b0=0) i⟩

theorem inverter_generator (i:Fin 10) : inverter (generator i)=reflectionImage i := by
  apply A.subtype_injective
  change (inverter (generator i):SylowModel)=(reflectionImage i:SylowModel)
  apply Tits.AmalgamRigidity.FullRee.SecondExtension.inclusion_injective
  change inclusion (action reflection (generator i):SylowModel)=inclusion (reflectionImage i:SylowModel)
  rw [action_inclusion]
  exact weyl_relations.conjugate i

def badActor : MulAut A := twist*inverter

def badImage (i:Fin 10):A := twist (reflectionImage i)

theorem badActor_generator (i:Fin 10) : badActor (generator i)=badImage i := by
  change twist (inverter (generator i))=twist (reflectionImage i)
  rw [inverter_generator]

end ReeTwo.SylowModel.CubicAction

namespace ReeTwo.SylowModel.CollectedBitVectors
open CubicAction
variable {n:ℕ}

def badPacked (x:PackedElement n):PackedElement n :=
  packedMap (fun i=>(badImage i:SylowModel)) x

theorem read_badPacked (x:PackedElement n) (k:Fin n) (a:A) (ha:read x k=(a:SylowModel)) :
    read (badPacked x) k=(badActor a:SylowModel) := by
  exact read_packedMap_hom (fun i=>(badImage i:SylowModel)) badActor.toMonoidHom
    (fun i=>congrArg Subtype.val (badActor_generator i).symm) x k a ha

def badSquareMask : BitVec 2048 := equal
  (product (product coreEnumeration (badPacked coreEnumeration)) (pack (generator 7))) (pack 1)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1000000 in
private theorem badSquareMask_zero : badSquareMask=0 := by decide +kernel

/-- The twisted reflected coset has no possible involution square. -/
theorem bad_coset_square_ne_one (a:A) : a*badActor a*generator 7≠1 := by
  obtain ⟨k,rfl⟩:=coreEnumerationEquiv.surjective a
  intro h
  have hb:badSquareMask.getLsbD k.val=true := by
    rw [badSquareMask,equal_spec,read_product,read_product,read_pack,read_pack,
      read_coreEnumeration,read_badPacked coreEnumeration k (coreEnumerationEquiv k) (read_coreEnumeration k)]
    exact congrArg Subtype.val h
  rw [badSquareMask_zero] at hb
  simp at hb

end ReeTwo.SylowModel.CollectedBitVectors
