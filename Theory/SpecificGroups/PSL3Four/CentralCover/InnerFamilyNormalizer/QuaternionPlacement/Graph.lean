module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Graph.NormalForm
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Graph.LinearNormalization
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Graph.SemilinearSylow

/-!
# Assembly for the graph-involution centralizer's Sylow model

The full graph centralizer on PSL₃(4) is the actual orthogonal group
extended by entrywise Frobenius, times the marked graph involution.
Full automorphism coverage and orthogonal normalization prove that the
faithful candidate map is surjective. A dihedral Sylow subgroup of the
orthogonal–Frobenius factor, multiplied by the graph factor, then gives
a Sylow two-subgroup isomorphic to `DihedralGroup 4 × C2`.

The independent matrix and Sylow calculations are discharged here; the
conditional assembly interfaces are retained. The resulting Sylow model
also supplies quaternion placement in the actual automorphism group.
Source: Aschbacher–Smith 16.1.4(6), printed p.1171, and the quaternion
placement used on printed p.1192.
-/

public section
noncomputable section
open Subgroup
open Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Graph

/-- Adjoin the independent graph factor to a dihedral Sylow subgroup of the
orthogonal group extended by Frobenius. The resulting subgroup is Sylow. -/
theorem exists_model_sylow (S : Sylow 2 Semilinear) (e : S ≃* DihedralGroup 4) :
    ∃ T : Sylow 2 Model, Nonempty (T ≃* DihedralGroup 4 × C2) := by
  let P : Subgroup Model := (S : Subgroup Semilinear).prod ⊤
  let eP : P ≃* DihedralGroup 4 × C2 :=
    ((S : Subgroup Semilinear).prodEquiv (⊤ : Subgroup C2)).trans
      (e.prodCongr Subgroup.topEquiv)
  have hcard : Nat.card P = 2 ^ 4 := by
    rw [Nat.card_congr eP.toEquiv, Nat.card_prod, DihedralGroup.nat_card, card_C2]
    norm_num
  have hp : IsPGroup 2 P := IsPGroup.of_card hcard
  have hi : ¬ 2 ∣ P.index := by
    simpa only [P, Subgroup.index_prod, Subgroup.index_top, mul_one] using S.not_dvd_index
  exact ⟨hp.toSylow hi, ⟨eP⟩⟩

/-- Once the independent matrix normalization and semilinear Sylow calculations
are supplied, this constructs the requested Sylow in the full centralizer. -/
theorem exists_centralizer_sylow_of_inputs
    (hlinear : ∀ A : GeneralLinearGroup (Fin 3) F,
      Commute (linearConj F A) (graph F) → ∃ x : Fixed, linearConj F A = inner x)
    (S : Sylow 2 Semilinear) (e : S ≃* DihedralGroup 4) :
    ∃ T : Sylow 2 (automorphismCentralizer (graph F)),
      Nonempty (T ≃* DihedralGroup 4 × C2) := by
  obtain ⟨T, ⟨eT⟩⟩ := exists_model_sylow S e
  let U : Sylow 2 (automorphismCentralizer (graph F)) :=
    T.mapSurjective (f := centralizerHom)
      (centralizerHom_surjective_of_linear_normalization hlinear)
  let eU : U ≃* T :=
    ((T : Subgroup Model).equivMapOfInjective centralizerHom centralizerHom_injective).symm
  exact ⟨U, ⟨eU.trans eT⟩⟩

/-- The same two explicit inputs suffice for the source's quaternion placement. -/
theorem placement_of_inputs
    (hlinear : ∀ A : GeneralLinearGroup (Fin 3) F,
      Commute (linearConj F A) (graph F) → ∃ x : Fixed, linearConj F A = inner x)
    (S : Sylow 2 Semilinear) (e : S ≃* DihedralGroup 4)
    (P : Subgroup (MulAut PSL)) (hP : Nonempty (P ≃* QuaternionGroup 2))
    (hPC : P ≤ automorphismCentralizer (graph F)) : P ≤ innerWith (graph F) := by
  obtain ⟨T, ⟨eT⟩⟩ := exists_centralizer_sylow_of_inputs hlinear S e
  exact graph_placement_of_sylow_model T eT P hP hPC

/-- Every automorphism centralizing the graph involution comes from the actual
orthogonal, field and graph factors. -/
theorem centralizerHom_surjective : Function.Surjective centralizerHom :=
  centralizerHom_surjective_of_linear_normalization linearConj_eq_inner_of_commute_graph

/-- The full graph centralizer, including its field and graph factors. -/
def centralizerEquiv : Model ≃* automorphismCentralizer (graph F) :=
  MulEquiv.ofBijective centralizerHom ⟨centralizerHom_injective, centralizerHom_surjective⟩

/-- The centralizer equivalence preserves the constructed automorphism action. -/
@[simp] theorem centralizerEquiv_apply (x : Model) :
    centralizerEquiv x = centralizerHom x := by rfl

/-- The full automorphism centralizer of the graph involution of PSL₃(4) has
a Sylow two-subgroup isomorphic to the order-eight dihedral group times C₂. -/
theorem exists_centralizer_sylow :
    ∃ S : Sylow 2 (automorphismCentralizer (graph F)),
      Nonempty (S ≃* DihedralGroup 4 × C2) := by
  obtain ⟨S, ⟨e⟩⟩ := exists_semilinear_sylow
  exact exists_centralizer_sylow_of_inputs linearConj_eq_inner_of_commute_graph S e

/-- Quaternion placement for the actual graph involution, with all centralizer
and Sylow calculations discharged. -/
theorem placement
    (P : Subgroup (MulAut PSL)) (hP : Nonempty (P ≃* QuaternionGroup 2))
    (hPC : P ≤ automorphismCentralizer (graph F)) : P ≤ innerWith (graph F) := by
  obtain ⟨S, ⟨e⟩⟩ := exists_centralizer_sylow
  exact graph_placement_of_sylow_model S e P hP hPC

end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement.Graph
