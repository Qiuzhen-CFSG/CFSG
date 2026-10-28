module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.BorelReduction.Quotients
public import BenderSuzuki.Converse.PSL2
public import Theory.SpecificGroups.Suzuki.StandardSubgroups

/-!
# Split tori in the linear and Suzuki Borel models

The diagonal matrices in SL₂, their faithful projective images in
characteristic two, and the existing Suzuki split torus give injections of
field units into the respective concrete Borel subgroups. These are model
calculations, independent of recognition of a local component as a model.
`Quotients.lift_component_borel_torus` transports them after recognition.

The Suzuki matrix carrier has field exponent `2 * m + 1`; the positivity
restriction is the standard nondegenerate parameter. Neither a field exponent
nor its parity is identified with the generation parameter in this module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.2.2,
printed pp.215–216, and 15.3.65, printed p.1152. The reused Suzuki torus
calculation is Huppert–Blackburn, Finite Groups III, XI.3.1 and XI.3.3.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
open Subgroup BenderSuzuki.Converse BenderSuzuki.MatrixGroups

variable {F : Type*} [Field F]

/-- The usual diagonal split torus inside the actual triangular Borel. -/
def sl2Torus : Fˣ →* Borel F :=
  (torHom F).codRestrict _ (fun a => Torus_le_Borel (Torus_eq_range (F := F) ▸ ⟨a, rfl⟩))

theorem sl2Torus_injective : Function.Injective (sl2Torus (F := F)) := by
  intro a b h
  exact torHom_injective (congrArg Subtype.val h)

/-- The image of the diagonal torus in the actual projective Borel. -/
def psl2Torus : Fˣ →* PBorel F :=
  ((pi F).comp (torHom F)).codRestrict _ (by
    intro a
    rw [PBorel_eq_map]
    exact mem_map_of_mem _ (sl2Torus a).property)

theorem psl2Torus_injective [CharP F 2] : Function.Injective (psl2Torus (F := F)) := by
  intro a b h
  exact torHom_injective (pi_injective (congrArg Subtype.val h))

/-- The matrix Suzuki split torus, included in its standard Borel. -/
noncomputable def suzukiTorus (m : ℕ) (hm : 0 < m) :
    (BenderSuzuki.PFAppendixIII.BinaryGaloisField (2 * m + 1))ˣ →* SuzukiBorelSubgroup m :=
  (inclusion (suzukiBorelSubgroup_eq_sup m ▸ le_sup_right)).comp
    (suzukiSplitTorus_equiv_units m hm).some.toMonoidHom

theorem suzukiTorus_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (suzukiTorus m hm) := by
  exact (inclusion_injective (suzukiBorelSubgroup_eq_sup m ▸ le_sup_right)).comp
    (suzukiSplitTorus_equiv_units m hm).some.injective

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.BorelReduction
