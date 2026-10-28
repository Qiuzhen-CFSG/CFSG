module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage.Factors.Local
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# The selected linear factor is the actual local residual

After the E.2.3 decomposition has one factor, its actor isomorphism identifies
all of the image of global J(H) with SL₂ over the factor's coefficient field.
The field of order two is excluded: its actor is S₃, which cannot contain the
nontrivial perfect ambient residual. For larger binary fields the matrix
commutator calculation makes the whole Thompson image perfect, hence
2-perfect, and residual functoriality gives the reverse containment to
E.2.3(1).

In the actual application H=KT_v, the block's field has order at least four.
The literal `localResidualEquiv` supplies perfectness, and the existing
simplicity argument selects one factor. The final image equalities use the
actual local quotient maps and global J(KT_v); no identification with J(H*)
is made. A caller may split `d.modules` at `localSelectedIndex` and apply this
module to its genuine linear witness. The symmetric alternative and final
case assembly remain with the factor-comparison owner.

Source: Aschbacher–Smith, E.2.3(1)–(2), printed pp.216–217, and its application
in 13.6.18, printed p.931 (combined manuscript of 1 March 2004).
-/

@[expose] public section

open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative

private theorem sl2_perfect_of_four_le_card {F : Type*} [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F) : Group.IsPerfect SL(2,F) := by
  obtain ⟨x, hx⟩ : IsCyclic Fˣ := inferInstance
  have hsq : (x : F) ^ 2 ≠ 1 := by
    intro h
    grw [Nat.card_eq_card_units_add_one F, ← orderOf_eq_card_of_forall_mem_zpowers hx,
      orderOf_le_of_pow_eq_one zero_lt_two (Units.ext (by simpa using h))] at hF
    omega
  exact ⟨Matrix.SL2.commutator_eq_top (Units.ne_zero x) hsq⟩

private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro H hH hq
  let : H.Normal := hH
  by_contra hne
  let : Nontrivial (A ⧸ H) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsNilpotent (A ⧸ H) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (A ⧸ H) inferInstance

private theorem symmetricThree_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceFactors
variable {H A W : Type*} [Group H] [Finite H] [Group A]
  [AddCommGroup W] [Module (ZMod 2) W]
variable {q : H →* A} {T : Subgroup H} {ρ : Representation (ZMod 2) A W}

/-- For a singleton linear decomposition, a nontrivial perfect ambient
residual forces the whole global Thompson image to be that residual.
In particular this proves, rather than assumes, exclusion of the field of
order two. The local application below supplies both residual hypotheses. -/
theorem Decomposition.globalImage_eq_residual_of_linear (d : Decomposition q T ρ) (hq : Function.Surjective q)
    [Nontrivial (pResidual 2 A)] [Group.IsPerfect (pResidual 2 A)]
    (hsize : d.factors.size = 1) (i : Fin d.factors.size)
    (m : LinearFactor (ρ.comp (globalImage q).subtype)
      ((pResidual 2 A).subgroupOf (globalImage q)) (d.factors.factor i)) :
    globalImage q = pResidual 2 A := by
  let : Finite A := Finite.of_surjective q hq
  let e : globalImage q ≃* SL(2,m.field.Carrier) :=
    ((MulEquiv.subgroupCongr (unique_factor_top d.factors hsize i)).trans
      Subgroup.topEquiv).symm.trans m.actor
  have hfield : 4 ≤ Nat.card m.field.Carrier := by
    by_contra hfour
    have hdegree : m.field.degree = 1 := by
      have hpow : 2 ^ m.field.degree < 2 ^ 2 := by simpa [m.field.card_eq] using hfour
      have := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hpow
      have := m.field.degree_pos
      omega
    have htwo : Nat.card m.field.Carrier = 2 := by rw [m.field.card_eq, hdegree]; rfl
    obtain ⟨e₂⟩ := BenderSuzuki.External.huppert_II_6_14_a_psl2_card_two htwo
    let e₃ := (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL).trans e₂
    let f := e₃.toMonoidHom.comp (inclusion (d.residual_le_image hq))
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := symmetricThree_solvable
    exact Group.IsPerfect.not_isSolvable (pResidual 2 A)
      (Group.isSolvable_of_isSolvable_injective (f := f)
        (e₃.injective.comp (inclusion_injective (d.residual_le_image hq))))
  let : Group.IsPerfect SL(2,m.field.Carrier) := sl2_perfect_of_four_le_card hfield
  let : Group.IsPerfect (globalImage q) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact le_antisymm (le_pResidual_of_isPPerfect _ perfect_twoPerfect)
    (d.residual_le_image hq)

section Local
open Stellmacher
open ComponentSelection
open Matrix.SpecialLinearGroup.RankOneResidual
variable {G : Type*} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
variable (hL : Tv T v ≤ normalizer (Lv L v : Set G))
variable (hz : Tv T v ≤ centralizer ({z} : Set G))
variable (hK : K ∈ Yz L T z v) (hnorm : Tv T v ≤ normalizer (K : Set G))
variable [IsElementaryAbelian 2 (WK K L T z v)]
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
variable {n : ℕ} (hF : Nat.card F = 2 ^ n) (hb : ChapterC.IsL2EvenBlock K n)
variable (s : NaturalSection (F := F) (componentRepresentation K L T z v hL hz)
  (movingSpace K L T z v))

include hK hnorm hF hb s

omit [CharP F 2] in
/-- The actual local residual is perfect through its marked SL₂ model.
The block's degree bound discharges the necessary field-size condition. -/
theorem localResidual_perfect :
    Group.IsPerfect (pResidual 2 (localMap K L T z v hL hz).range) := by
  have hfour : 4 ≤ Nat.card F := by
    rw [hF]
    change 2 ^ 2 ≤ 2 ^ n
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (by have := hb.1; omega)
  let : Group.IsPerfect SL(2,F) := sl2_perfect_of_four_le_card hfour
  let e := localResidualEquiv K L T z v hL hz hK hnorm hb s
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- A literal factor index selected using the proved singleton result.
The caller can split the actual `d.modules` at this index. -/
def localSelectedIndex
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (d : Decomposition (localProjection K L T z v hL hz)
      ((Tv T v).subgroupOf (K ⊔ Tv T v))
      (localRepresentation K L T z v hL hz hW)) : Fin d.factors.size :=
  ⟨0, by rw [localDecomposition_size_eq_one K L T z v hL hz hK hnorm hF hb s hW d]; decide⟩

/-- The linear branch of the local E.2.3 comparison. The field and action in
`m` are precisely those of a genuine factor of the specified decomposition;
no extra simplicity, perfectness, or large-field premise remains. -/
theorem local_linear_globalImage_eq_residual
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (d : Decomposition (localProjection K L T z v hL hz)
      ((Tv T v).subgroupOf (K ⊔ Tv T v))
      (localRepresentation K L T z v hL hz hW)) (i : Fin d.factors.size)
    (m : LinearFactor
      ((localRepresentation K L T z v hL hz hW).comp
        (globalImage (localProjection K L T z v hL hz)).subtype)
      ((pResidual 2 (localMap K L T z v hL hz).range).subgroupOf
        (globalImage (localProjection K L T z v hL hz))) (d.factors.factor i)) :
    globalImage (localProjection K L T z v hL hz) =
      pResidual 2 (localMap K L T z v hL hz).range := by
  let := localResidual_simple K L T z v hL hz hK hnorm hF hb s
  let := localResidual_perfect K L T z v hL hz hK hnorm hF hb s
  exact d.globalImage_eq_residual_of_linear (localMap K L T z v hL hz).rangeRestrict_surjective
    (localDecomposition_size_eq_one K L T z v hL hz hK hnorm hF hb s hW d) i m

/-- Mapping the intrinsic equality into the actual plus quotient gives K⁺.
The domain Thompson subgroup is global J(KT_v), expressed internally. -/
theorem local_linear_thompson_image
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (d : Decomposition (localProjection K L T z v hL hz)
      ((Tv T v).subgroupOf (K ⊔ Tv T v))
      (localRepresentation K L T z v hL hz hW)) (i : Fin d.factors.size)
    (m : LinearFactor
      ((localRepresentation K L T z v hL hz hW).comp
        (globalImage (localProjection K L T z v hL hz)).subtype)
      ((pResidual 2 (localMap K L T z v hL hz).range).subgroupOf
        (globalImage (localProjection K L T z v hL hz))) (d.factors.factor i)) :
    (elementaryAbelianMaxJ (⊤ : Subgroup (K ⊔ Tv T v : Subgroup G))).map
      (localMap K L T z v hL hz) = plusImage K L T z v hL hz K := by
  have he := congrArg (fun U : Subgroup (localMap K L T z v hL hz).range =>
    U.map (localMap K L T z v hL hz).range.subtype)
    (local_linear_globalImage_eq_residual K L T z v hL hz hK hnorm hF hb s hW d i m)
  rw [localRange_residual_image K L T z v hL hz hK hnorm hb, globalImage, Subgroup.map_map] at he
  exact he

/-- The same conclusion with global J(KT_v) expressed as an ambient subgroup
of G and then restricted along the literal domain of `localMap`. -/
theorem local_linear_ambient_thompson_image
    (hW : WK K L T z v ≤ K ⊔ Tv T v)
    (d : Decomposition (localProjection K L T z v hL hz)
      ((Tv T v).subgroupOf (K ⊔ Tv T v))
      (localRepresentation K L T z v hL hz hW)) (i : Fin d.factors.size)
    (m : LinearFactor
      ((localRepresentation K L T z v hL hz hW).comp
        (globalImage (localProjection K L T z v hL hz)).subtype)
      ((pResidual 2 (localMap K L T z v hL hz).range).subgroupOf
        (globalImage (localProjection K L T z v hL hz))) (d.factors.factor i)) :
    ((elementaryAbelianMaxJ (K ⊔ Tv T v)).subgroupOf (K ⊔ Tv T v)).map
      (localMap K L T z v hL hz) = plusImage K L T z v hL hz K := by
  have hJ : (elementaryAbelianMaxJ (K ⊔ Tv T v)).subgroupOf (K ⊔ Tv T v) =
      elementaryAbelianMaxJ (⊤ : Subgroup (K ⊔ Tv T v : Subgroup G)) := by
    apply Subgroup.map_injective (K ⊔ Tv T v).subtype_injective
    rw [map_subgroupOf_eq_of_le (show elementaryAbelianMaxJ (K ⊔ Tv T v) ≤
      K ⊔ Tv T v from sSup_le fun _ hA => hA.1),
      ← elementaryAbelianMaxJ_map_injective _ (K ⊔ Tv T v).subtype_injective,
      ← MonoidHom.range_eq_map, range_subtype]
  rw [hJ]
  exact local_linear_thompson_image K L T z v hL hz hK hnorm hF hb s hW d i m

end Local
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceFactors

end
