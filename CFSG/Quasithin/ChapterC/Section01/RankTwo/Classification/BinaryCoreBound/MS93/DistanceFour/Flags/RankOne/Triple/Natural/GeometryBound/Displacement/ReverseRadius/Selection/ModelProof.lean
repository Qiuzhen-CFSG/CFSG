module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.ReverseRadius.Selection.Model
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
public import Theory.GroupTheory.NormalizedSupCard
/-!
# The same-type parabolic join in binary SL₃

For distinct conjugate parabolics P and Q of the same type, the join of
O₂(P) ∩ Q with O₂(Q) has index three in Q. Bruhat decomposition reduces
point parabolics to the pair fixing e₀ and e₁. For this pair the translation
cores are disjoint, their relevant intersection has order two, and intrinsic
core normality gives a join of order eight in a parabolic of order twenty-four.
The actual diagram automorphism gives the line case, and automorphism transport
retains the arbitrary common conjugation of the marked flag.

Only the six permutation representatives and two single-matrix predicates
are checked by kernel reduction; no enumeration of subgroup joins is used.

This is the finite quotient calculation used in Meierfrankenfeld--Stellmacher,
*Pushing up weak BN-pairs of rank two* (1993), (4.6.8), claim (1), printed p.905.
The source-group selection and quotient lifting are assembled separately.
-/

open Subgroup Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.ReverseSelection

private noncomputable def joinIndex (P Q : Subgroup SL) : ℕ :=
  ((P.pCoreIn 2 ⊓ Q) ⊔ Q.pCoreIn 2).relIndex Q

private theorem joinIndex_map (e : MulAut SL) (P Q : Subgroup SL) :
    joinIndex (P.map e.toMonoidHom) (Q.map e.toMonoidHom) = joinIndex P Q := by
  unfold joinIndex
  rw [← map_pCoreIn_of_injective 2 P e.toMonoidHom e.injective,
    ← map_pCoreIn_of_injective 2 Q e.toMonoidHom e.injective,
    ← map_inf _ _ _ e.injective, ← Subgroup.map_sup,
    relIndex_map_map_of_injective _ _ e.injective]

private def conjugate (P : Subgroup SL) (g : SL) : Subgroup SL :=
  P.map (MulAut.conj g).toMonoidHom

private theorem conjugate_mul (P : Subgroup SL) (a b : SL) :
    conjugate P (a * b) = conjugate (conjugate P b) a := by
  unfold conjugate
  rw [map_map]
  apply congrArg (fun f : SL →* SL => P.map f)
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private theorem conjugate_eq_self (P : Subgroup SL) {g : SL} (hg : g ∈ P) :
    conjugate P g = P :=
  mem_normalizer_iff_map_conj_eq.mp (P.le_normalizer hg)

private theorem conjugate_map (P : Subgroup SL) (e : MulAut SL) (g : SL) :
    conjugate (P.map e.toMonoidHom) (e g) = (conjugate P g).map e.toMonoidHom := by
  unfold conjugate
  rw [map_map, map_map]
  apply congrArg (fun f : SL →* SL => P.map f)
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

private def SameTypeJoin (P : Subgroup SL) : Prop :=
  ∀ g : SL, conjugate P g ≠ P → joinIndex P (conjugate P g) = 3

private theorem sameTypeJoin_map (P : Subgroup SL) (e : MulAut SL)
    (h : SameTypeJoin P) : SameTypeJoin (P.map e.toMonoidHom) := by
  intro g hn
  obtain ⟨a, rfl⟩ := e.surjective g
  rw [conjugate_map] at hn ⊢
  rw [joinIndex_map]
  apply h a
  intro he
  exact hn (congrArg (fun H : Subgroup SL => H.map e.toMonoidHom) he)

private theorem core_normalized (P : Subgroup SL) :
    P ≤ normalizer (P.pCoreIn 2 : Set SL) := by
  simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
    (pCore 2 P).le_normalizer_map P.subtype

private theorem reflection_symm :
    (MulAut.conj (Bruhat.perm 2)).symm = MulAut.conj (Bruhat.perm 2) := by
  have hw : (Bruhat.perm 2)⁻¹ = Bruhat.perm 2 := by decide +kernel
  apply MulEquiv.ext
  intro x
  change (Bruhat.perm 2)⁻¹ * x * Bruhat.perm 2 =
    Bruhat.perm 2 * x * (Bruhat.perm 2)⁻¹
  rw [hw]

private theorem reflection_map (P : Subgroup SL) :
    conjugate P (Bruhat.perm 2) =
      P.comap (MulAut.conj (Bruhat.perm 2)).toMonoidHom := by
  unfold conjugate
  rw [map_equiv_eq_comap_symm', reflection_symm]

set_option maxRecDepth 100000 in
/-- The two double cosets of the point parabolic, obtained from the six Weyl representatives. -/
private theorem permutation_cells (j : Fin 6) :
    Bruhat.perm j ∈ pointParabolicSL ∨
    ∃ a b : Fin 2, Bruhat.perm j =
      Bruhat.perm (a.castLE (by decide)) * Bruhat.perm 2 *
        Bruhat.perm (b.castLE (by decide)) := by
  revert j
  decide +kernel

private theorem small_permutation_mem (a : Fin 2) :
    Bruhat.perm (a.castLE (by decide)) ∈ pointParabolicSL := by
  revert a
  decide +kernel

set_option maxRecDepth 100000 in
/-- The translations fixing the second coordinate point form a group of order two. -/
private theorem reflection_intersection_card :
    Nat.card (pointV ⊓ conjugate pointParabolicSL (Bruhat.perm 2) : Subgroup SL) = 2 := by
  rw [reflection_map]
  change Nat.card {g : SL // g ∈ pointV ∧
    (MulAut.conj (Bruhat.perm 2)) g ∈ pointParabolicSL} = 2
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 100000 in
/-- A translation with both distinct coordinate centers is the identity. -/
private theorem reflection_cores_disjoint :
    Disjoint pointV (conjugate pointV (Bruhat.perm 2)) := by
  rw [reflection_map, Subgroup.disjoint_def]
  have h : ∀ g : SL, g ∈ pointV →
      (MulAut.conj (Bruhat.perm 2)) g ∈ pointV → g = 1 := by
    decide +kernel
  exact fun {g} hg hg' => h g hg hg'

private theorem reflection_join :
    joinIndex pointParabolicSL (conjugate pointParabolicSL (Bruhat.perm 2)) = 3 := by
  let Q := conjugate pointParabolicSL (Bruhat.perm 2)
  have hc : Q.pCoreIn 2 = conjugate pointV (Bruhat.perm 2) := by
    dsimp [Q, conjugate]
    rw [← map_pCoreIn_of_injective 2 _ _ (MulAut.conj (Bruhat.perm 2)).injective,
      MarkedProduct.pointParabolic_core]
  have hc4 : Nat.card (Q.pCoreIn 2) = 4 := by
    rw [hc]
    exact (Nat.card_congr ((MulAut.conj (Bruhat.perm 2)).subgroupMap pointV).toEquiv).symm.trans
      card_pointV
  have hQ24 : Nat.card Q = 24 :=
    (Nat.card_congr ((MulAut.conj (Bruhat.perm 2)).subgroupMap pointParabolicSL).toEquiv).symm.trans
      card_pointParabolicSL
  have hd : Disjoint (Q.pCoreIn 2) (pointV ⊓ Q) := by
    rw [hc]
    exact reflection_cores_disjoint.symm.mono_right inf_le_left
  have hj8 : Nat.card ((pointV ⊓ Q) ⊔ Q.pCoreIn 2 : Subgroup SL) = 8 := by
    rw [sup_comm, card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (inf_le_right.trans (core_normalized Q)) hd, hc4, reflection_intersection_card]
  have hle : (pointV ⊓ Q) ⊔ Q.pCoreIn 2 ≤ Q :=
    sup_le inf_le_right (pCoreIn_le 2 Q)
  have hidx := relIndex_mul_relIndex (⊥ : Subgroup SL)
    ((pointV ⊓ Q) ⊔ Q.pCoreIn 2) Q bot_le hle
  rw [relIndex_bot_left, relIndex_bot_left, hj8, hQ24] at hidx
  unfold joinIndex
  rw [MarkedProduct.pointParabolic_core]
  change ((pointV ⊓ Q) ⊔ Q.pCoreIn 2).relIndex Q = 3
  omega

private theorem point_sameTypeJoin : SameTypeJoin pointParabolicSL := by
  intro g hn
  obtain ⟨i, j, k, hg⟩ := Bruhat.decomposition g
  rcases permutation_cells j with hj | ⟨a, b, hj⟩
  · have hmem : g ∈ pointParabolicSL := by
      rw [hg]
      exact pointParabolicSL.mul_mem
        (pointParabolicSL.mul_mem (Bruhat.upper_mem i).1 hj) (Bruhat.upper_mem k).1
    exact (hn (conjugate_eq_self _ hmem)).elim
  · let u := Bruhat.upper i * Bruhat.perm (a.castLE (by decide))
    let v := Bruhat.perm (b.castLE (by decide)) * Bruhat.upper k
    have hu : u ∈ pointParabolicSL :=
      pointParabolicSL.mul_mem (Bruhat.upper_mem i).1 (small_permutation_mem a)
    have hv : v ∈ pointParabolicSL :=
      pointParabolicSL.mul_mem (small_permutation_mem b) (Bruhat.upper_mem k).1
    have hguv : g = u * (Bruhat.perm 2 * v) := by
      rw [hg, hj]
      dsimp [u, v]
      group
    rw [hguv, conjugate_mul _ u (Bruhat.perm 2 * v),
      conjugate_mul _ (Bruhat.perm 2) v, conjugate_eq_self _ hv]
    have hm := joinIndex_map (MulAut.conj u) pointParabolicSL
      (conjugate pointParabolicSL (Bruhat.perm 2))
    change joinIndex (conjugate pointParabolicSL u)
      (conjugate (conjugate pointParabolicSL (Bruhat.perm 2)) u) = _ at hm
    rw [conjugate_eq_self _ hu] at hm
    exact hm.trans reflection_join

/-- Distinct conjugates of either marked parabolic satisfy the intrinsic index-three join. -/
public theorem modelJoin (t : SL) (i : Bool) : ModelJoin t i := by
  change SameTypeJoin (modelParabolic t i)
  unfold modelParabolic
  apply sameTypeJoin_map
  cases i
  · exact point_sameTypeJoin
  · exact pointParabolic_map_diagram ▸ sameTypeJoin_map pointParabolicSL diagram point_sameTypeJoin

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.ReverseSelection
