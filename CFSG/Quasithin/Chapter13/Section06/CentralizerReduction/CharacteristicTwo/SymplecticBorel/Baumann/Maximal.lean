module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SymplecticBorel.Baumann.Maximal.InnerActors
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank.OuterMaximum
public import Stellmacher.ElementaryAbelianMaxProduct
public import Theory.ElementaryAbelian.Join

/-!
# Maximum elementary subgroups lie in the Sylow–centralizer product

A conjugate of a concrete symplectic Sylow wing gives an elementary subgroup
of `R ∩ K` of order `2^(3*n)`. Its product with a maximum elementary subgroup
of `R ∩ C_H(K)` is elementary and has the product order, since the factors
commute and are disjoint.

For a maximum elementary subgroup `E` of `R`, restrict the actual normalizer
action to `E`. If its image contains an outer automorphism, the strict model
bound makes that image smaller than the wing. Its kernel embeds in the
component centralizer, where maximality bounds its order by the second factor.
The kernel–image order formula then contradicts maximality of `E`. The proved
inner-action preimage identifies the resulting placement with the literal
join `(R ∩ K) ⊔ (R ∩ C_H(K))`.

Only the two specified involution cocycle descents remain as hypotheses.
Semilinear coverage and the actual Suzuki fixed-group equivalence are proved
upstream; no placement or Thompson decomposition is assumed here. The parent
Baumann assembly retains the discharge of the two descent premises.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927 (PDF p.944),
using the involution types on printed pp.1170–1173.
-/

public section
open Subgroup Stellmacher
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel
variable {H F : Type*} [Group H] [Field F] [Finite F] [CharP F 2]
variable (K : Subgroup H) (e : K ≃* Sp F)

/-- A transported concrete Sylow wing realizes order `2^(3*n)` inside `R ∩ K`. -/
theorem localSylow_exists_elementary_card {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n)
    (R : Subgroup H) (S : Sylow 2 (Sp F))
    (hSyl : (localSylow K e S : Subgroup K).map K.subtype = R ⊓ K) :
    ∃ A : Subgroup H, A ≤ R ⊓ K ∧ IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ (3 * n) := by
  obtain ⟨g, hU, _⟩ := residualAt_conjugate hF hn S
  let f := (K.subtype.comp e.symm.toMonoidHom).comp (MulAut.conj g).toMonoidHom
  have hf : Function.Injective f :=
    (K.subtype_injective.comp e.symm.injective).comp (MulAut.conj g).injective
  have hP : unipotent.map f = R ⊓ K := by
    rw [show f = (K.subtype.comp e.symm.toMonoidHom).comp
      (MulAut.conj g).toMonoidHom from rfl, ← map_map, hU, ← map_map]
    exact hSyl
  let fu := f.comp (unipotent (F := F)).subtype
  have hfu : Function.Injective fu := hf.comp (unipotent (F := F)).subtype_injective
  let A := (CentralRootGeometry.wing (F := F) false).map fu
  let := CentralRootGeometry.wing_elementary (F := F) false
  refine ⟨A, ?_, IsElementaryAbelian.map fu, ?_⟩
  · rw [← hP]
    rintro x ⟨u, _, rfl⟩
    exact mem_map_of_mem f u.property
  · change Nat.card ((CentralRootGeometry.wing (F := F) false).map fu) = _
    rw [card_map_of_injective (f := fu) hfu,
      CentralRootGeometry.card_wing, hF, ← pow_mul, Nat.mul_comm n 3]

variable [Finite H]

/-- The maximum-elementary placement needed in the source Thompson decomposition,
conditional only on the two prescribed involution cocycle descents. -/
theorem maximum_elementary_placement_of_coboundaries {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hfield : Even n → ∀ g : Sp F,
      g * fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) g = 1 →
      ∃ h : Sp F, g = h * (fieldAutomorphism (frobeniusEquiv F 2 ^ (n / 2)) h)⁻¹)
    (hgraph : Odd n → ∀ g : Sp F,
      g * (ExceptionalGraph.graphAut ^ n) g = 1 →
      ∃ h : Sp F, g = h * ((ExceptionalGraph.graphAut ^ n) h)⁻¹)
    (R : Subgroup H) (hp : IsPGroup 2 R) (hR : R ≤ normalizer (K : Set H))
    (S : Sylow 2 (Sp F))
    (hSyl : (localSylow K e S : Subgroup K).map K.subtype = R ⊓ K)
    (E : Subgroup H) (hE : E ∈ elementaryAbelianMaxSubgroups R) :
    E ≤ (R ⊓ K) ⊔ (R ⊓ centralizer (K : Set H)) := by
  let := hE.2.1
  let E' := E.subgroupOf R
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.subgroupOf hE.1
  let φ := restrictedModelAction K e R hR
  let I := E'.map φ
  have hI : IsElementaryAbelian 2 I := IsElementaryAbelian.map φ
  have hi : I ≤ MulAut.innerSubgroup (Sp F) := by
    by_contra hout
    have hIc := EvenTwoRank.OuterMaximum.elementary_outer_card_lt
      hF hn hfield hgraph I hI hout
    obtain ⟨A, hAK, hA, hAc⟩ := localSylow_exists_elementary_card K e hF hn.le R S hSyl
    obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty (R ⊓ centralizer (K : Set H))
    let := hA
    let := hB.2.1
    have hd : Disjoint A B := (component_inter_centralizer_disjoint K e R).mono hAK hB.1
    have hc : A ≤ centralizer (B : Set H) :=
      (hAK.trans inf_le_right).trans (le_centralizer_iff.mpr (hB.1.trans inf_le_right))
    have hAB : IsElementaryAbelian 2 (A ⊔ B : Subgroup H) :=
      IsElementaryAbelian.sup_of_le_centralizer (le_centralizer_iff.mp hc)
    obtain ⟨ab, _⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
    have hABc : Nat.card (A ⊔ B : Subgroup H) = 2 ^ (3 * n) * Nat.card B := by
      rw [← Nat.card_congr ab.toEquiv, Nat.card_prod, hAc]
    have hmax := hE.2.2 (A ⊔ B) (sup_le (hAK.trans inf_le_left) (hB.1.trans inf_le_left)) hAB
    rw [hABc] at hmax
    let f : E' →* MulAut (Sp F) := φ.comp E'.subtype
    let j : E' →* H := R.subtype.comp E'.subtype
    have hj : Function.Injective j := R.subtype_injective.comp E'.subtype_injective
    let : IsElementaryAbelian 2 f.ker := {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
        Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 E') x.val)) }
    have hkerle : f.ker.map j ≤ R ⊓ centralizer (K : Set H) := by
      rintro x ⟨a, ha, rfl⟩
      refine ⟨a.val.property, ?_⟩
      exact (restrictedModelAction_eq_one_iff K e R hR a.val).mp ha
    have hkc := hB.2.2 (f.ker.map j) hkerle (IsElementaryAbelian.map j)
    rw [card_map_of_injective hj] at hkc
    have hcard : Nat.card E' = Nat.card f.ker * Nat.card I := by
      rw [← f.ker.card_mul_index, index_ker]
      simp only [f, MonoidHom.range_comp, range_subtype, I]
    rw [Nat.card_congr (subgroupOfEquivOfLe hE.1).toEquiv] at hcard
    have hlt : Nat.card E < 2 ^ (3 * n) * Nat.card B := by
      rw [hcard]
      calc
        Nat.card f.ker * Nat.card I ≤ Nat.card B * Nat.card I := Nat.mul_le_mul_right _ hkc
        _ < Nat.card B * 2 ^ (3 * n) := Nat.mul_lt_mul_of_pos_left hIc Nat.card_pos
        _ = 2 ^ (3 * n) * Nat.card B := Nat.mul_comm _ _
    exact (not_lt_of_ge hmax) hlt
  intro x hx
  rw [← restrictedModelAction_inner_preimage K e R hR hp S hSyl]
  refine ⟨⟨x, hE.1 hx⟩, ?_, rfl⟩
  exact hi (mem_map_of_mem φ (show (⟨x, hE.1 hx⟩ : R) ∈ E' from hx))
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SymplecticBorel
