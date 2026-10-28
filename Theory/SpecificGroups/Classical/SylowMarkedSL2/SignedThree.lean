module
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.Control
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.ModelBounds
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.CentralCover
public import Theory.SpecificGroups.SL3.CenterProjectiveComparison
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
/-!
# The marked classical three-dimensional normalizer rows of C.5.12

In each actual SL₃(5), PSL₃(5), SU₃(5), and PSU₃(5) carrier, a full
Sylow two-subgroup normalizing an SL₂(5) subgroup makes that subgroup invariant
under every automorphism preserving the Sylow subgroup. Its central involution
is the unique involution of the cyclic Sylow center, and recovers the original
SL₂(5) as the derived involution centralizer. The projective rows use the actual
central odd-kernel projections. No restriction on the unitary outer diagonal
three-group is imposed.
Source: Aschbacher–Smith C.5.12, printed p.163, and A.3.21(a), p.55.
-/
public section
open Subgroup Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups IsMulCommutative
namespace Theory.SpecificGroups.Classical.SylowMarkedSL2
variable {F E : Type*} [Field F] [Finite F] [Field E] [Finite E]
theorem sl3_preserves_sl2_five (hF : Nat.card F = 5)
    (L : Subgroup SL(3,F)) (eL : L ≃* SL(2,E)) (hE : Nat.card E = 5)
    (S : Sylow 2 SL(3,F)) (hSL : (S : Subgroup _) ≤ normalizer (L : Set SL(3,F)))
    (a : MulAut SL(3,F)) (ha : (S : Subgroup _).map a.toMonoidHom = S) : L.map a.toMonoidHom = L := by
  apply automorphism_preserves_sl2_five _ (linear_derived_centralizer_card_le hF) L eL hE S hSL a ha
  intro T hn
  exact center_isCyclic_of_nonabelian_two_subgroup SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective
    (by intro g; apply Units.ext; exact g.property)
    (GorensteinWalter.two_ne_zero_of_odd_card F (by rw [hF]; decide)) T T.isPGroup' hn

theorem psl3_preserves_sl2_five (hF : Nat.card F = 5)
    (L : Subgroup PSL(3,F)) (eL : L ≃* SL(2,E)) (hE : Nat.card E = 5)
    (S : Sylow 2 PSL(3,F)) (hSL : (S : Subgroup _) ≤ normalizer (L : Set PSL(3,F)))
    (a : MulAut PSL(3,F)) (ha : (S : Subgroup _).map a.toMonoidHom = S) : L.map a.toMonoidHom = L := by
  let q := PSL3.projection F
  have hq : q.ker ≤ center SL(3,F) := by rw [PSL3.projection_ker]
  have hc : ∀ x ∈ q.ker, x ^ 3 = 1 := by
    intro x hx
    have hz := hq hx
    have hd := (orderOf_dvd_natCard (⟨x,hz⟩ : center SL(3,F))).trans (SL3.card_center_dvd_three F)
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp hd)
  apply automorphism_preserves_sl2_five _
    (derived_centralizer_bound_of_central_cube_cover q (PSL3.projection_surjective F) hq hc
      (linear_derived_centralizer_card_le hF)) L eL hE S hSL a ha
  intro T hn
  exact center_isCyclic_of_central_coprime_cover SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective
    (by intro g; apply Units.ext; exact g.property)
    (GorensteinWalter.two_ne_zero_of_odd_card F (by rw [hF]; decide)) q
    (PSL3.projection_surjective F) hq
    (by change Nat.Coprime 2 (Nat.card (PSL3.projection F).ker); rw [PSL3.projection_ker]; exact (SL3.odd_card_center F).coprime_two_left) T T.isPGroup' hn

theorem su3_preserves_sl2_five (J : HermitianForm 3 F)
    (hF : Nat.card F = 25) (hc : ∀ x, J.conj x = x ^ 5)
    (L : Subgroup J.specialSubgroup) (eL : L ≃* SL(2,E)) (hE : Nat.card E = 5)
    (S : Sylow 2 J.specialSubgroup) (hSL : (S : Subgroup _) ≤ normalizer (L : Set J.specialSubgroup))
    (a : MulAut J.specialSubgroup) (ha : (S : Subgroup _).map a.toMonoidHom = S) : L.map a.toMonoidHom = L := by
  apply automorphism_preserves_sl2_five _ (unitary_derived_centralizer_card_le J hF hc) L eL hE S hSL a ha
  intro T hn
  exact center_isCyclic_of_nonabelian_two_subgroup J.specialSubgroup.subtype J.specialSubgroup.subtype_injective
    (fun g => g.property.2)
    (GorensteinWalter.two_ne_zero_of_odd_card F (by rw [hF]; decide)) T T.isPGroup' hn

theorem psu3_preserves_sl2_five (J : HermitianForm 3 F)
    (hF : Nat.card F = 25) (hc : ∀ x, J.conj x = x ^ 5)
    (L : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (eL : L ≃* SL(2,E)) (hE : Nat.card E = 5)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (hSL : (S : Subgroup _) ≤ normalizer (L : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    (ha : (S : Subgroup _).map a.toMonoidHom = S) : L.map a.toMonoidHom = L := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let q := J.specialToProjective
  have h3 : ∀ x ∈ q.ker, x ^ 3 = 1 := by
    intro x hx
    exact congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x,hx⟩)
  apply automorphism_preserves_sl2_five _
    (derived_centralizer_bound_of_central_cube_cover q J.specialToProjective_surjective
      J.specialToProjective_ker_le_center h3 (unitary_derived_centralizer_card_le J hF hc)) L eL hE S hSL a ha
  intro T hn
  exact center_isCyclic_of_central_coprime_cover J.specialSubgroup.subtype J.specialSubgroup.subtype_injective
    (fun g => g.property.2) (GorensteinWalter.two_ne_zero_of_odd_card F (by rw [hF]; decide))
    q J.specialToProjective_surjective J.specialToProjective_ker_le_center
    J.odd_card_specialToProjective_ker.coprime_two_left T T.isPGroup' hn
end Theory.SpecificGroups.Classical.SylowMarkedSL2
