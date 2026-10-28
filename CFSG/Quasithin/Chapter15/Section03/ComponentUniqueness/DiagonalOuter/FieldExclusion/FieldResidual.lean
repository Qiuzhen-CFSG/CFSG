module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Layer
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary

/-!
# Applying the odd-core bound to the actual field residual

`fieldResidual L f` is O²(C_L(f)) embedded in C_G(f), with its ambient
inclusion proved explicitly. The actual PSL₃(2) isomorphism makes it perfect.
The E₉ odd-core embedding supplied by fusion then lets `Layer` convert the
I.3.2 two-layer inclusion into ordinary-layer containment.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, proof of
15.3.38, printed p.1137. The genuine balance inclusion remains an earlier
input; neither ordinary-layer containment nor a chosen component is assumed.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
variable {G : Type*} [Group G]

/-- O²(C_L(f)), embedded in the actual element centralizer C_G(f). -/
@[expose] def fieldResidual (L : Subgroup G) (f : G) :
    Subgroup (centralizer ({f} : Set G)) :=
  (pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G)).map
    (inclusion inf_le_right)

/-- The two inclusions recover the residual embedded directly in G. -/
theorem map_fieldResidual (L : Subgroup G) (f : G) :
    (fieldResidual L f).map (centralizer ({f} : Set G)).subtype =
      (pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G)).map
        (L ⊓ centralizer ({f} : Set G)).subtype := by
  rw [fieldResidual, map_map]
  rfl

/-- The concrete PSL₃(2) model supplies perfectness. -/
theorem fieldResidual_perfect (L : Subgroup G) (f : G)
    (e : pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    Group.IsPerfect (fieldResidual L f) := by
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.psl_perfect 3 (by decide)
  let : Group.IsPerfect (pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.IsPerfect.map (inclusion inf_le_right)

/-- The balance embedding and small odd core put the field residual in E(G_f). -/
theorem fieldResidual_le_layer [Finite G] (L : Subgroup G) (f : G)
    (e : pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (ι : pPrimeCore 2 (centralizer ({f} : Set G)) →* ElementaryNine)
    (hι : Function.Injective ι)
    (hbalance : fieldResidual L f ≤
      oddExtendedTwoComponentLayer (centralizer ({f} : Set G))) :
    fieldResidual L f ≤ componentLayer (centralizer ({f} : Set G)) := by
  let := fieldResidual_perfect L f e
  exact le_layer_of_balance_embedding (fieldResidual L f) ι hι hbalance

/-- Fusion supplies the odd-core bound needed for ordinary-layer containment. -/
theorem fieldResidual_le_layer_of_fusion [Finite G]
    (V I L : Subgroup G) [IsKleinFour V]
    (hV : CFSG.Quasithin.ChapterI.Section06To08.IsTISubgroup V)
    (hI : I = normalizer (V : Set G)) {w f : G}
    (hw : w ∈ centralizer (V : Set G)) (hfusion : IsConj w f)
    (eO : pPrimeCore 2 (I ⊓ centralizer ({w} : Set G) : Subgroup G) ≃* ElementaryNine)
    (eF : pResidual 2 (L ⊓ centralizer ({f} : Set G) : Subgroup G) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (hbalance : fieldResidual L f ≤
      oddExtendedTwoComponentLayer (centralizer ({f} : Set G))) :
    fieldResidual L f ≤ componentLayer (centralizer ({f} : Set G)) := by
  obtain ⟨ι, hι⟩ := centralizer_oddCore_embeds_of_fusion V I hV hI hw hfusion eO
  exact fieldResidual_le_layer L f eF ι hι hbalance

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion
