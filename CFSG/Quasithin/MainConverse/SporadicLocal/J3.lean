module

public import CFSG.Quasithin.MainConverse.SporadicLocal.Criteria
public import CFSG.Quasithin.MainConverse.SporadicLocal.Janko3Reduction
public import CFSG.Quasithin.MainConverse.SporadicLocal.J3.Coverage
public import Theory.GroupTheory.MaximalTwoLocalElementary
public import Theory.GroupTheory.PCoreOvergroup
public import Theory.SpecificGroups.Janko3.Model.Order
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Centralizer
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Affine
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Thompson
public import Theory.SpecificGroups.Janko3.Model.TwoLocal.Generators

/-!
# Quasithinness and even characteristic of J₃

The general elementary-center reduction makes it enough to cover the
normalizers of nontrivial elementary abelian subgroups of one Sylow
2-subgroup. The word-defined candidates imported here are actual subgroups
of the degree-6156 model. The certified ambient order 50232960 and candidate
order 128 identify the latter as Sylow, by its odd index 392445. The imported
exhaustive elementary-subgroup fusion and ambient normalizer calculations
then cover every maximal two-local by conjugates of three fixed candidates.

The three local orders 1920, 2880, 1152 then imply QT. For E, the middle
candidate cannot contain an ambient Sylow two-subgroup, since 128 does not
divide 2880. A self-centralizing intrinsic two-core in the other two
candidates descends to each Sylow-containing subgroup they cover. Thus
only those two intrinsic centralizer facts are required.

The final theorems discharge all concrete premises and transport QT and E
across an actual equivalence to the model, which is the catalogue's J₃
carrier. Simplicity and nonabelianness are unnecessary for these two
conditions. Proper K remains the separate source induction input.
The earlier conditional assembly APIs are preserved.

Source: Aschbacher–Smith, Theorem 0.1.2(5), printed p.4, repeated as
Theorem 0.1.1(5) on p.482; GLS, Number 3, Table 5.3h, printed p.269.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal
open Subgroup Sporadic.Janko3 Sporadic.Janko3.TwoLocal

/-- A finite normalizer calculation inside the concrete Sylow candidate
suffices for every maximal two-local in the actual J₃ carrier. -/
public theorem j3_maximal_cover_of_elementary_cover
    (horder : Nat.card Model = 50232960)
    (hS : Nat.card sylowCandidate = 128)
    (hcover : ∀ A : Subgroup Model, A ≤ sylowCandidate → A ≠ ⊥ →
      IsElementaryAbelian 2 A → ∃ (i : Fin 3) (g : Model),
        normalizer (A : Set Model) ≤ (localFamily i).map (MulAut.conj g).toMonoidHom) :
    ∀ M : Subgroup Model, IsMaximalTwoLocal M → ∃ (i : Fin 3) (g : Model),
      M ≤ (localFamily i).map (MulAut.conj g).toMonoidHom := by
  have hpS : IsPGroup 2 sylowCandidate := IsPGroup.of_card (n := 7) hS
  have hi : sylowCandidate.index = 392445 := by
    have hmul := sylowCandidate.card_mul_index
    rw [hS, horder] at hmul
    omega
  let S : Sylow 2 Model := hpS.toSylow (by rw [hi]; norm_num)
  intro M hM
  apply Theory.GroupTheory.maximalTwoLocal_cover_of_elementary_normalizer_cover S
    localFamily (fun A hAS hA hEA => hcover A hAS hA hEA) hM

private theorem characteristicTwo_of_sylow_le_overgroup
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G)
    (M L : Subgroup G) (hTM : (T : Subgroup G) ≤ M) (hML : M ≤ L)
    (hL : HasCharacteristicTwo L) : HasCharacteristicTwo M := by
  have hTL := hTM.trans hML
  have hsub : ((T.subtype hTL) : Subgroup L) ≤ M.subgroupOf L := by
    intro x hx
    exact hTM hx
  have h := centralizer_pCore_le_of_sylow_le (T.subtype hTL) (M.subgroupOf L) hsub hL
  exact HasCharacteristicTwo.of_equiv (subgroupOfEquivOfLe hML) h

/-- Assemble QT and E from the indicated concrete calculations. Even
characteristic is required only of candidates 0 and 2, intrinsically. -/
public theorem j3_qt_and_even_of_elementary_cover
    (horder : Nat.card Model = 50232960)
    (hS : Nat.card sylowCandidate = 128)
    (h0 : Nat.card (localFamily 0) = 1920)
    (h1 : Nat.card (localFamily 1) = 2880)
    (h2 : Nat.card (localFamily 2) = 1152)
    (hc0 : HasCharacteristicTwo (localFamily 0))
    (hc2 : HasCharacteristicTwo (localFamily 2))
    (hcover : ∀ A : Subgroup Model, A ≤ sylowCandidate → A ≠ ⊥ →
      IsElementaryAbelian 2 A → ∃ (i : Fin 3) (g : Model),
        normalizer (A : Set Model) ≤ (localFamily i).map (MulAut.conj g).toMonoidHom) :
    IsQuasithin Model ∧ IsEvenCharacteristic Model := by
  have hmax := j3_maximal_cover_of_elementary_cover horder hS hcover
  refine ⟨j3_quasithin_of_local_cover localFamily h0 h1 h2 hmax, ?_⟩
  intro T M hM hTM
  obtain ⟨i, g, hML⟩ := hmax M hM
  have hne : i ≠ 1 := by
    intro hi
    subst i
    have hdiv := card_dvd_of_le (hTM.trans hML)
    rw [card_map_of_injective (MulAut.conj g).injective, h1] at hdiv
    have h128 : 2 ^ 7 ∣ Nat.card Model := by rw [horder]; norm_num
    have hbad := (T.pow_dvd_card_of_pow_dvd_card h128).trans hdiv
    norm_num at hbad
  have hL : HasCharacteristicTwo (localFamily i) := by
    fin_cases i
    · exact hc0
    · exact (hne rfl).elim
    · exact hc2
  exact characteristicTwo_of_sylow_le_overgroup T M _ hTM hML
    (hL.of_equiv (equivMapOfInjective _ (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective))

/-- Transport the conditional assembly across an actual model equivalence.
In particular this applies to the finite nonabelian simple groups in the
source converse; no standalone model simplicity certificate is needed. -/
public theorem j3_qt_and_even_of_elementary_cover_of_iso
    {G : Type*} [Group G] [Finite G] (e : G ≃* Model)
    (horder : Nat.card Model = 50232960)
    (hS : Nat.card sylowCandidate = 128)
    (h0 : Nat.card (localFamily 0) = 1920)
    (h1 : Nat.card (localFamily 1) = 2880)
    (h2 : Nat.card (localFamily 2) = 1152)
    (hc0 : HasCharacteristicTwo (localFamily 0))
    (hc2 : HasCharacteristicTwo (localFamily 2))
    (hcover : ∀ A : Subgroup Model, A ≤ sylowCandidate → A ≠ ⊥ →
      IsElementaryAbelian 2 A → ∃ (i : Fin 3) (g : Model),
        normalizer (A : Set Model) ≤ (localFamily i).map (MulAut.conj g).toMonoidHom) :
    IsQuasithin G ∧ IsEvenCharacteristic G := by
  have h := j3_qt_and_even_of_elementary_cover horder hS h0 h1 h2 hc0 hc2 hcover
  exact ⟨Theory.GroupTheory.isQuasithin_of_equiv e.symm h.1, evenCharacteristic_of_model_equiv e h.2⟩

/-- Every maximal two-local of the concrete J₃ carrier lies in a conjugate
of one of the three certified local candidates. -/
public theorem j3_maximal_cover (M : Subgroup Model) (hM : IsMaximalTwoLocal M) :
    ∃ (i : Fin 3) (g : Model),
      M ≤ (localFamily i).map (MulAut.conj g).toMonoidHom :=
  j3_maximal_cover_of_elementary_cover Sporadic.Janko3.model_card sylowCandidate_card
    (J3Coverage.elementary_normalizer_cover Sporadic.Janko3.model_card
      sylowCandidate_card centralizerCandidate_card) M hM

/-- The degree-6156 ATLAS carrier satisfies QT and E, with all order,
coverage and intrinsic two-core premises discharged. -/
public theorem j3_qt_and_even : IsQuasithin Model ∧ IsEvenCharacteristic Model :=
  j3_qt_and_even_of_elementary_cover
    Sporadic.Janko3.model_card sylowCandidate_card
    centralizerCandidate_card localFamily_one_card localFamily_two_card
    centralizerCandidate_centralizer_pCore_le localFamily_two_centralizer_pCore_le
    (J3Coverage.elementary_normalizer_cover Sporadic.Janko3.model_card
      sylowCandidate_card centralizerCandidate_card)

/-- The J₃ case of conditions QT and E in Theorem 0.1.2(5). The input is an
actual equivalence to the model, definitionally
`ClassificationModels.SporadicName.j3.Carrier`, with no remaining local premises. -/
public theorem j3_qt_e_of_equiv
    {G : Type*} [Group G] [Finite G] (e : G ≃* Model) :
    IsQuasithin G ∧ IsEvenCharacteristic G :=
  ⟨Theory.GroupTheory.isQuasithin_of_equiv e.symm j3_qt_and_even.1,
    evenCharacteristic_of_model_equiv e j3_qt_and_even.2⟩

end CFSG.Quasithin.MainConverse.SporadicLocal
