module

public import Theory.AtlasPort.LinearGroups.G2.BinarySylowCoreReduction
public import Theory.AtlasPort.LinearGroups.G2.BinaryNinePointReduction
public import Theory.AtlasPort.LinearGroups.G2.BinaryProperSylowCore
public import Theory.AtlasPort.LinearGroups.G2.SylowOvergroupCharacteristic

/-!
# The binary derived G₂ branch of the proper Sylow-overgroup bound

For the literal commutator subgroup of G₂(2), the numerical reduction and
the C₄ × C₄ obstruction in A₉ prove nontriviality of the two-core in every
proper Sylow two-overgroup. The geometric recognition and the two actual
derived-parabolic calculations then give the intrinsic characteristic-two
bound. The final two theorems discharge all additional model and permutation
premises; the earlier conditional interfaces are retained.

Source: Aschbacher--Smith, proof of B.1.13, printed p.74 (PDF p.85), and
GLS III, §2.6, with the small-derived convention for G₂(2)′.
-/

public section

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.TwistedExceptional.BinaryG2
open Subgroup Atlas.G2

/-- The numerical part of the binary branch, keeping the index-nine gap visible. -/
theorem twoCore_ne_bot_of_index_ne_nine
    [IsSimpleGroup (commutator (Model (ZMod 2)))]
    (Q : Sylow 2 (commutator (Model (ZMod 2))))
    (H : Subgroup (commutator (Model (ZMod 2)))) (hH : H ≠ ⊤)
    (hQH : (Q : Subgroup (commutator (Model (ZMod 2)))) ≤ H)
    (h9 : H.index ≠ 9) : pCore 2 H ≠ ⊥ :=
  BinarySylowCoreReduction.twoCore_ne_bot_of_index_ne_nine Q H hH hQH h9

/-- Apply the actual derived-parabolic characteristic-two theorem to the
nontrivial core supplied by the order reduction. -/
theorem centralizer_twoCore_le_of_index_ne_nine
    [IsSimpleGroup (commutator (Model (ZMod 2)))]
    (Q : Sylow 2 (commutator (Model (ZMod 2))))
    (H : Subgroup (commutator (Model (ZMod 2)))) (hH : H ≠ ⊤)
    (hQH : (Q : Subgroup (commutator (Model (ZMod 2)))) ≤ H)
    (h9 : H.index ≠ 9) : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
  SylowOvergroupCharacteristic.binary_derived Q H hQH
    (twoCore_ne_bot_of_index_ne_nine Q H hH hQH h9)

/-- All numerical and model-embedding steps are discharged; the remaining
premise is the elementary obstruction in the alternating group on nine letters. -/
theorem twoCore_ne_bot_of_cyclicFourSquare_obstruction
    [IsSimpleGroup (commutator (Model (ZMod 2)))]
    [Group.IsPerfect (commutator (Model (ZMod 2)))]
    (hA : ∀ f : ExceptionalLocalQuotients.C4Square →* alternatingGroup (Fin 9),
      ¬ Function.Injective f)
    (Q : Sylow 2 (commutator (Model (ZMod 2))))
    (H : Subgroup (commutator (Model (ZMod 2)))) (hH : H ≠ ⊤)
    (hQH : (Q : Subgroup (commutator (Model (ZMod 2)))) ≤ H) : pCore 2 H ≠ ⊥ :=
  twoCore_ne_bot_of_index_ne_nine Q H hH hQH
    (BinaryNinePointReduction.index_ne_nine_of_cyclicFourSquare_obstruction hA H)

/-- The same explicit A₉ premise gives intrinsic characteristic two via the
literal derived-parabolic theorem consumed by B.1.13. -/
theorem centralizer_twoCore_le_of_cyclicFourSquare_obstruction
    [IsSimpleGroup (commutator (Model (ZMod 2)))]
    [Group.IsPerfect (commutator (Model (ZMod 2)))]
    (hA : ∀ f : ExceptionalLocalQuotients.C4Square →* alternatingGroup (Fin 9),
      ¬ Function.Injective f)
    (Q : Sylow 2 (commutator (Model (ZMod 2))))
    (H : Subgroup (commutator (Model (ZMod 2)))) (hH : H ≠ ⊤)
    (hQH : (Q : Subgroup (commutator (Model (ZMod 2)))) ≤ H) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
  SylowOvergroupCharacteristic.binary_derived Q H hQH
    (twoCore_ne_bot_of_cyclicFourSquare_obstruction hA Q H hH hQH)

/-- The nontrivial-core premise for every proper Sylow two-overgroup in the
binary derived branch, with simplicity and the A₉ obstruction discharged. -/
theorem twoCore_ne_bot
    (Q : Sylow 2 (commutator (Model (ZMod 2))))
    (H : Subgroup (commutator (Model (ZMod 2)))) (hH : H ≠ ⊤)
    (hQH : (Q : Subgroup (commutator (Model (ZMod 2)))) ≤ H) :
    pCore 2 H ≠ ⊥ :=
  BinaryProperSylowCore.twoCore_ne_bot Q H hH hQH

/-- Intrinsic characteristic two for every proper Sylow two-overgroup in
the literal G₂(2)′ carrier, as needed in the Lie-type branch of B.1.13. -/
theorem centralizer_twoCore_le
    (Q : Sylow 2 (commutator (Model (ZMod 2))))
    (H : Subgroup (commutator (Model (ZMod 2)))) (hH : H ≠ ⊤)
    (hQH : (Q : Subgroup (commutator (Model (ZMod 2)))) ≤ H) :
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
  SylowOvergroupCharacteristic.binary_derived Q H hQH
    (twoCore_ne_bot Q H hH hQH)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.TwistedExceptional.BinaryG2
