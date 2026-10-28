module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreRecognition.SylowInputs.ThreeBounds
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Recognition.Preparation
public import Theory.SpecificGroups.Alternating.FiveInvolutionFusion
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Join

/-!
# The marked cubic plane before first-centralizer recognition

Choose a cubic element y in the actual component K = E(C_G(t)) inverted
by the marked z. The choice is transported through the component embedding
from the conjugacy of involutions in A₅. The seed X centralizes K and has
trivial intersection with it, since A₅ is centerless. Consequently the
literal join I = X ⊔ ⟨y⟩ is elementary abelian of order nine and is
normalized by z. It is contained in an ambient Sylow three-subgroup.

The second-centralizer alternatives, together with I ≤ C_G(⟨y⟩), give
order nine for every Sylow three of that centralizer. We do not infer
that z normalizes the chosen ambient Sylow merely from its action on I.
The remaining placement argument must justify its choice or use the
normalizer action on the four lines of I.

Source: Aschbacher, *Sporadic Groups* (1994), 47.3, printed p.262,
the construction of I = X × Y before the order calculation.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreSylowInputs

private def standardInvolution : InvolutionGeometry.A5 :=
  ⟨Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3, by
    change _ ∈ alternatingGroup (Fin 5)
    simp⟩
private def standardCubic : InvolutionGeometry.A5 :=
  ⟨Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 4, by
    change _ ∈ alternatingGroup (Fin 5)
    simp⟩

private theorem standardInvolution_order : orderOf standardInvolution = 2 := by
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)
private theorem standardCubic_order : orderOf standardCubic = 3 := by
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private theorem exists_inverted_cubic (a : InvolutionGeometry.A5) (ha : orderOf a = 2) :
    ∃ b : InvolutionGeometry.A5, orderOf b = 3 ∧ a * b * a⁻¹ = b⁻¹ := by
  obtain ⟨g, hg⟩ := isConj_iff.mp (alternatingGroup.five_involutions_isConj
    standardInvolution a standardInvolution_order ha)
  let e := MulAut.conj g
  refine ⟨e standardCubic, (e.orderOf_eq _).trans standardCubic_order, ?_⟩
  have he : e standardInvolution = a := hg
  rw [← he, ← map_inv, ← map_mul, ← map_mul, ← map_inv]
  exact congrArg e (by decide +kernel :
    standardInvolution * standardCubic * standardInvolution⁻¹ = standardCubic⁻¹)

variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- The cubic generator and its inversion identity live in the original component. -/
theorem exists_inverted_component_cubic (E : EarlierConclusions D) :
    ∃ y : G, y ∈ InvolutionGeometry.rootComponent E.geometry.t ∧ orderOf y = 3 ∧
      D.z * y * D.z⁻¹ = y⁻¹ := by
  have hz := E.geometry.z_mem_component
  rw [← E.componentMap_range] at hz
  obtain ⟨a, ha⟩ := hz
  have hao : orderOf a = 2 := by
    rw [← orderOf_injective E.componentMap E.componentMap_injective, ha]
    exact D.localType.involution
  obtain ⟨b, hb, hab⟩ := exists_inverted_cubic a hao
  refine ⟨E.componentMap b, E.componentMap_mem b,
    (orderOf_injective E.componentMap E.componentMap_injective b).trans hb, ?_⟩
  simpa only [map_mul, map_inv, ha] using congrArg E.componentMap hab

/-- The centralizing seed meets the actual centerless component trivially. -/
theorem component_seed_disjoint (E : EarlierConclusions D) :
    Disjoint D.X (InvolutionGeometry.rootComponent E.geometry.t) := by
  rw [disjoint_def]
  intro x hx hk
  rw [← E.componentMap_range] at hk
  obtain ⟨a, rfl⟩ := hk
  have ha : a ∈ center InvolutionGeometry.A5 := by
    apply mem_center_iff.mpr
    intro b
    apply E.componentMap_injective
    simpa only [map_mul] using
      E.geometry.X_centralizes_component hx (E.componentMap b) (E.componentMap_mem b)
  rw [alternatingGroup.center_eq_bot (by simp), mem_bot] at ha
  simp [ha]

/-- The literal product X times the component cubic has order nine. -/
theorem plane_card (E : EarlierConclusions D) {y : G}
    (hy : y ∈ InvolutionGeometry.rootComponent E.geometry.t) (hyo : orderOf y = 3) :
    Nat.card (D.X ⊔ zpowers y : Subgroup G) = 9 := by
  have hyK : zpowers y ≤ InvolutionGeometry.rootComponent E.geometry.t := zpowers_le.mpr hy
  rw [card_sup_eq_mul_of_normalizes_of_disjoint D.X (zpowers y)
    ((hyK.trans E.component_le).trans (Subgroup.centralizer_le_normalizer _))
    ((component_seed_disjoint E).mono_right hyK), D.card_X, Nat.card_zpowers, hyo]

/-- The two commuting cubic factors give an elementary abelian plane. -/
theorem plane_elementary (E : EarlierConclusions D) {y : G}
    (hy : y ∈ InvolutionGeometry.rootComponent E.geometry.t) (hyo : orderOf y = 3) :
    IsElementaryAbelian 3 (D.X ⊔ zpowers y : Subgroup G) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic D.X := isCyclic_of_prime_card D.card_X
  let : IsElementaryAbelian 3 D.X := {
    exponent_dvd_p := D.card_X ▸ Group.exponent_dvd_nat_card }
  let : IsElementaryAbelian 3 (zpowers y) := {
    exponent_dvd_p := by rw [← hyo, ← Nat.card_zpowers]; exact Group.exponent_dvd_nat_card }
  exact IsElementaryAbelian.sup_of_le_centralizer
    ((zpowers_le.mpr hy).trans E.component_le)

/-- The chosen involution normalizes the plane, with no assertion about its Sylow extensions. -/
theorem plane_z_normalizes {y : G}
    (hyinv : D.z * y * D.z⁻¹ = y⁻¹) :
    D.z ∈ normalizer ((D.X ⊔ zpowers y : Subgroup G) : Set G) := by
  apply normalizer_inf_normalizer_le_normalizer_sup D.X (zpowers y)
  refine ⟨Subgroup.centralizer_le_normalizer _ ?_, ?_⟩
  · exact fun x hx => mem_centralizer_singleton_iff.mp (D.X_le hx)
  · apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers (D.z * y * D.z⁻¹) = zpowers y
    rw [hyinv, zpowers_inv]

/-- The actual plane lies in the centralizer used in the independent alternatives. -/
theorem plane_le_cubic_centralizer (E : EarlierConclusions D) {y : G}
    (hy : y ∈ InvolutionGeometry.rootComponent E.geometry.t) (hyo : orderOf y = 3) :
    D.X ⊔ zpowers y ≤ SecondNormalizer.cubicCentralizer y := by
  let := plane_elementary E hy hyo
  exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
    (centralizer_le (show zpowers y ≤ D.X ⊔ zpowers y from le_sup_right))

/-- Both alternatives have three-part exactly nine, using the embedded plane for the lower bound. -/
theorem cubic_centralizer_three_card (E : EarlierConclusions D)
    (hAlt : SecondNormalizer.CentralizerAlternatives E.geometry)
    {y : G} (hy : y ∈ InvolutionGeometry.rootComponent E.geometry.t) (hyo : orderOf y = 3)
    (T : Sylow 3 (SecondNormalizer.cubicCentralizer y)) : Nat.card T = 9 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hlo : 2 ≤ (Nat.card (SecondNormalizer.cubicCentralizer y)).factorization 3 := by
    apply (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp
    simpa only [plane_card E hy hyo, show (3 : ℕ) ^ 2 = 9 by norm_num] using
      card_dvd_of_le (plane_le_cubic_centralizer E hy hyo)
  have hhi : (Nat.card (SecondNormalizer.cubicCentralizer y)).factorization 3 < 3 := by
    apply Nat.lt_of_not_ge
    intro hn
    apply cubic_centralizer_not_twenty_seven E.geometry hAlt hy hyo
    exact (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').mpr hn
  rw [T.card_eq_multiplicity, show
    (Nat.card (SecondNormalizer.cubicCentralizer y)).factorization 3 = 2 by omega]
  norm_num

/-- Choose the source plane and an ambient Sylow extension; invariance of the extension is not assumed. -/
theorem exists_source_plane (E : EarlierConclusions D) :
    ∃ (y : G) (P : Sylow 3 G),
      y ∈ InvolutionGeometry.rootComponent E.geometry.t ∧ orderOf y = 3 ∧
      D.z * y * D.z⁻¹ = y⁻¹ ∧ D.X ⊔ zpowers y ≤ (P : Subgroup G) := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨y, hy, hyo, hinv⟩ := exists_inverted_component_cubic E
  let := plane_elementary E hy hyo
  obtain ⟨P, hP⟩ := (IsElementaryAbelian.isPGroup 3 (D.X ⊔ zpowers y : Subgroup G)).exists_le_sylow
  exact ⟨y, P, hy, hyo, hinv, hP⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreSylowInputs
