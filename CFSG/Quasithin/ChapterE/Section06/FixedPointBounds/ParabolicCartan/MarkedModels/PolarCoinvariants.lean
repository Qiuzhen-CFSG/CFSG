module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.OrbitDegree
public import Theory.Representation.OddPolarOrbitCoinvariants

/-!
# Displacement from the actual marked Borel orbit

The marked quotient and its literal stabilizer supply the spanning orbit.
Its odd cardinality and nondegenerate invariant polar then give full
coinvariant generation by the original component. This is the local
module input to original 14.2.16, printed pp.985–986.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open Subgroup
variable {G P Ω W : Type*} [Group G] [Group P] [MulAction P Ω]
variable [AddCommGroup W] [Module (ZMod 2) W]
theorem ModelBorelPair.orbit_polar_coinvariants [Finite Ω]
    (M K S : Subgroup G) [K.Normal] (hgen : K ⊔ S = ⊤) (hSM : S ≤ M)
    (o : Ω) (hm : ModelBorelPair M K (MulAction.stabilizer P o))
    (htwo : MulAction.IsMultiplyPretransitive P Ω 2)
    (ρ : Representation (ZMod 2) G W) (v : W)
    (hfix : ∀ g ∈ M, ρ g v = v)
    (hspan : Submodule.span (ZMod 2) (Set.range (fun g : G => ρ g v)) = ⊤)
    (B : LinearMap.BilinForm (ZMod 2) W) (hB : B.IsAlt) (hne : B ≠ 0)
    (hinv : ∀ g x y, B (ρ g x) (ρ g y) = B x y)
    (hker : B.ker = ⊥) (hodd : Odd (Nat.card Ω)) :
    Representation.Coinvariants.ker (ρ.comp K.subtype) = ⊤ := by
  let : MulAction.IsMultiplyPretransitive P Ω 2 := htwo
  let : MulAction.IsPretransitive P Ω := MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨π,b,hπ,_,hb,hsp⟩ := hm.spanning_orbit M K S hgen hSM o
    (fun x => MulAction.exists_smul_eq P o x) ρ v hfix hspan
  exact BinaryBorelOrbit.odd_polar_coinvariants π hπ (ρ.comp K.subtype) htwo b hb
    hsp B hB hne (fun k => hinv k.val) hker hodd
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
