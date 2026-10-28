module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.SylowGeometry
public import Theory.GroupTheory.ElementarySwappedFixed

/-!
# The actual fixed subgroup and its Sylow kernel in the decomposable row

The original Thompson fixed subgroup is the direct product of its two
marked four-groups. When the first support action has no factor of four,
the support stabilizer centralizes both markings, so it is exactly the
kernel of the original Sylow action on the whole fixed subgroup. In the
prime-three row the existing source support calculation supplies this
hypothesis. No residual assertion from 15.1.14 is used.

Source: Aschbacher--Smith 15.1.13--14, printed pp.1090--1091.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
open ChapterD ChapterD.UniqueFactor ChapterD.RatioDecomposition
open Stellmacher Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Both marked four-groups are literal subgroups of the same chosen module. -/
theorem ThompsonPair.fixed_card
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    {hn : M ≤ normalizer (V : Set G)}
    {U : Submodule (ZMod 2) (Additive V)}
    {c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U}
    {d : Decomposition c.representation} (s : ThompsonPair (T := T) hn c d) :
    Nat.card (thompsonFixed T V) = 16 := by
  let A := thompsonPlane T V (c.ambientFactor d s.first).space
  let B := thompsonPlane T V (c.ambientFactor d s.second).space
  have hAV : A ≤ V := inf_le_right.trans inf_le_left
  have hBV : B ≤ V := inf_le_right.trans inf_le_left
  have hBA : B ≤ centralizer (A : Set G) := by
    intro b hb a ha
    exact congrArg Subtype.val (isMulCommutative_iff.mp
      (inferInstance : IsMulCommutative V) ⟨a,hAV ha⟩ ⟨b,hBV hb⟩)
  rw [s.thompson_split,card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (hBA.trans (Subgroup.centralizer_le_normalizer _))
    (disjoint_iff.mpr s.thompson_disjoint),s.thompson_card,s.thompson_card]

/-- Centralizing one marking is equivalent to centralizing the whole fixed
subgroup; the original support stabilizer has index two in the Sylow group. -/
theorem ThompsonPair.fixed_sylow_kernel_of_support_four_not_dvd
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (hfour : ¬ 4 ∣ Nat.card (subspaceActionImage (imageRepresentation M V hn)
      (c.ambientFactor d s.first).space)) :
    (T : Subgroup G) ⊓ centralizer (thompsonFixed T V : Set G) =
        (T : Subgroup G) ⊓ centralizer
          (thompsonPlane T V (c.ambientFactor d s.first).space : Set G) ∧
      ((T : Subgroup G) ⊓ centralizer (thompsonFixed T V : Set G)).relIndex
        (T : Subgroup G) = 2 := by
  let A := thompsonPlane T V (c.ambientFactor d s.first).space
  let B := thompsonPlane T V (c.ambientFactor d s.second).space
  let S := (T : Subgroup G) ⊓ centralizer (A : Set G)
  obtain ⟨he,hi,hnS,_,_,_,_⟩ :=
    s.sylow_geometry_of_support_four_not_dvd hTM hn c d hfour
  have hST : S ≤ (T : Subgroup G) := inf_le_left
  have hTN : (T : Subgroup G) ≤ normalizer (S : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hST).mp hnS
  have hSne : S ≠ (T : Subgroup G) := by
    intro hh
    change S.relIndex (T : Subgroup G) = 2 at hi
    rw [hh,relIndex_self] at hi
    omega
  obtain ⟨t,ht,htS⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hST hSne)
  have htout : t ∉ normalizer (plane V (c.ambientFactor d s.first).space : Set G) := by
    intro hh
    apply htS
    change t ∈ (T : Subgroup G) ⊓ centralizer
      (thompsonPlane T V (c.ambientFactor d s.first).space : Set G)
    rw [he]
    exact ⟨ht,hh⟩
  have hAB : A.map (MulAut.conj t).toMonoidHom = B :=
    (s.thompson_exchanges t ht htout).1
  have hSB : S ≤ centralizer (B : Set G) := by
    have hmap := map_mono (f := (MulAut.conj t).toMonoidHom)
      (show S ≤ centralizer (A : Set G) from inf_le_right)
    have hSmap : S.map (MulAut.conj t).toMonoidHom = S :=
      mem_normalizer_iff_map_conj_eq.mp (hTN ht)
    rw [hSmap] at hmap
    exact hmap.trans (by
      simpa only [←Subgroup.coe_map,hAB] using
        map_centralizer_le_centralizer_image (A : Set G) (MulAut.conj t).toMonoidHom)
  have hSE : S ≤ centralizer (thompsonFixed T V : Set G) := by
    apply le_centralizer_iff.mpr
    rw [s.thompson_split]
    exact sup_le (le_centralizer_iff.mp (show S ≤ centralizer (A : Set G) from inf_le_right))
      (le_centralizer_iff.mp hSB)
  have hk : (T : Subgroup G) ⊓ centralizer (thompsonFixed T V : Set G) = S :=
    le_antisymm (inf_le_inf_left _ (centralizer_le inf_le_right)) (le_inf hST hSE)
  exact ⟨hk,hk ▸ hi⟩

end CFSG.Quasithin.Chapter15.Section01.DecomposableMarker
