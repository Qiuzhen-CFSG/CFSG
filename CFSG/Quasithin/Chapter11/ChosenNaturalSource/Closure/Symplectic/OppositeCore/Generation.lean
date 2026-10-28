module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Pair
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Multiplier
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.SolvableResidual
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Lifting the three opposite-pair generators to the original core

The three source pairs centralize O₂(L) modulo C=O₂(L)∩O₂(G₁). They
therefore normalize C, as does O₂(LT). Their join H with O₂(LT) normalizes
both O₂(L) and C. The kernel of its action on O₂(L)/C contains all three
pairs, so its quotient is a two-group. Perfectness of the original L forces
L into this kernel. The genuine symplectic multiplier identity then puts
all of O₂(L) in O₂(G₁).

The generation input is the literal inclusion of L in the join of the
three pairs and O₂(LT), not a substituted equality of abstract images.
The geometric construction must lift its marked action-image generation
to this inclusion. The natural-quotient branch must supply Q≤O₂(G₁).
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

private theorem perfect_centralizes_modulo_of_two_supplement
    {G : Type*} [Group G] [Finite G]
    (H J S R C L : Subgroup G) [Group.IsPerfect L]
    (hH : H = J ⊔ S) (hLH : L ≤ H) (hS : IsPGroup 2 S)
    (hHR : H ≤ normalizer (R : Set G)) (hHC : H ≤ normalizer (C : Set G))
    (hJR : ⁅J,R⁆ ≤ C) : ⁅L,R⁆ ≤ C := by
  let N := commutatorPreimage H R C
  have hNH : N ≤ H := commutatorPreimage_le H R C
  have hHN : H ≤ normalizer (N : Set G) :=
    commutatorPreimage_normalized H R C H hHC H.le_normalizer hHR hHC
  have hJN : J ≤ N := le_commutatorPreimage (by rw [hH]; exact le_sup_left) hJR
  have hSH : S ≤ H := by rw [hH]; exact le_sup_right
  let N' := N.subgroupOf H
  let S' := S.subgroupOf H
  let : N'.Normal := (normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  have hsup : N' ⊔ S' = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hNH, map_subgroupOf_eq_of_le hSH,
      ← MonoidHom.range_eq_map, range_subtype]
    exact le_antisymm (sup_le hNH hSH) (by rw [hH]; exact sup_le_sup_right hJN S)
  have hquot := isPGroup_quotient_of_sup_eq_top N' S' hS.comap_subtype hsup
  let : Group.IsNilpotent (H ⧸ N') := hquot.isNilpotent
  let : Group.IsPerfect (L.subgroupOf H) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLH).symm.toMonoidHom) (subgroupOfEquivOfLe hLH).symm.surjective
  have hLN' : L.subgroupOf H ≤ N' :=
    (le_solvableResidual_of_isPerfect _).trans (solvableResidual_le_of_solvable_quotient N')
  have hLN : L ≤ N := by
    have hm := map_mono (f := H.subtype) hLN'
    change (L.subgroupOf H).map H.subtype ≤ (N.subgroupOf H).map H.subtype at hm
    simpa only [map_subgroupOf_eq_of_le hLH, map_subgroupOf_eq_of_le hNH] using hm
  exact (commutator_mono hLN le_rfl).trans
    (commutator_commutatorPreimage_le H R C hHC)

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Assemble the actual three-conjugate generation, opposite-core bound,
and the unconditional multiplier step. The chosen y, its core-image bound,
the natural-quotient containment, and the lifted generation remain explicit
outputs of the separate source constructions. -/
theorem core_le_point_core_of_three_opposites (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hQ : corePair (auxiliaryW E) y ≤ E.G₁.pCoreIn 2)
    (l : Fin 3 → G) (hl : ∀ i, l i ∈ E.L₁)
    (hgen : L ≤ (⨆ i, (oppositeJoin (auxiliaryW E) y).map (MulAut.conj (l i)).toMonoidHom) ⊔
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    L.pCoreIn 2 ≤ E.G₁.pCoreIn 2 := by
  let R := L.pCoreIn 2
  let S := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let C := R ⊓ E.G₁.pCoreIn 2
  let I := oppositeJoin (auxiliaryW E) y
  let A : Fin 3 → Subgroup G := fun i => I.map (MulAut.conj (l i)).toMonoidHom
  let J := ⨆ i, A i
  let H := J ⊔ S
  have hT : E.G₁.pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le m.sylow_le_point_normalizer] using
      pCoreIn_le_sylow E.G₁ (T.subtype m.sylow_le_point_normalizer)
  have hST : S ≤ T := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hWL : auxiliaryW E ≤ L ⊔ (T : Subgroup G) :=
    ((auxiliaryW_le_W E).trans hW).trans (hT.trans le_sup_right)
  have hIL : I ≤ L ⊔ (T : Subgroup G) := by
    apply sup_le hWL
    have he : (L ⊔ (T : Subgroup G)).map (MulAut.conj y).toMonoidHom =
        L ⊔ (T : Subgroup G) := mem_normalizer_iff_map_conj_eq.mp
      ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_left hy))
    exact (map_mono hWL).trans_eq he
  have hAL (i : Fin 3) : A i ≤ L ⊔ (T : Subgroup G) := by
    have he : (L ⊔ (T : Subgroup G)).map (MulAut.conj (l i)).toMonoidHom =
        L ⊔ (T : Subgroup G) := mem_normalizer_iff_map_conj_eq.mp
      ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_left (E.L₁_le (hl i))))
    exact (map_mono hIL).trans_eq he
  have hHR : H ≤ normalizer (R : Set G) :=
    ((sup_le (iSup_le hAL) (pCoreIn_le 2 _)).trans
      (sup_le L.le_normalizer D.sylow_normalizes_component)).trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hAH (i : Fin 3) : A i ≤ H := (le_iSup A i).trans le_sup_left
  have hcomm (i : Fin 3) : ⁅R, A i⁆ ≤ C := le_inf
    (le_normalizer_iff_commutator_le_left.mp ((hAH i).trans hHR))
    (original_core_conjugate_commutator E m hy hW hcore hQ (hl i))
  have hAC (i : Fin 3) : A i ≤ normalizer (C : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono inf_le_left le_rfl).trans (hcomm i))
  have hSC : S ≤ normalizer (C : Set G) :=
    (le_inf (le_sup_right.trans hHR)
      ((hST.trans m.sylow_le_point_normalizer).trans
        (E.G₁.le_normalizer.trans (normalizer_le_normalizer_characteristic_image E.G₁
          (pCore 2 E.G₁))))).trans inf_normalizer_le_normalizer_inf
  have hHC : H ≤ normalizer (C : Set G) := sup_le (iSup_le hAC) hSC
  have hJR : ⁅J,R⁆ ≤ C := commutator_iSup_le_of_relative_normal H R C A hHC hAH
    (fun i => by rw [commutator_comm]; exact hcomm i)
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect E.input.source.maximal_faithful.1.1
  have hLR : ⁅L,R⁆ ≤ C := perfect_centralizes_modulo_of_two_supplement H J S R C L
    rfl hgen (isPGroup_pCoreIn 2 _) hHR hHC hJR
  rw [commutator_comm] at hLR
  exact (core_eq_commutator E m).le.trans (hLR.trans inf_le_right)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
