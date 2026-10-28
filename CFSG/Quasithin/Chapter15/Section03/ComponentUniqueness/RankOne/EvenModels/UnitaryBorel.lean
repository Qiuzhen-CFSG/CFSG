module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BorelFields
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.UnitaryBorel.CubicFixer
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison

/-!
# The upstairs PSU₃(4) Borel centralizer calculation

Borel invariance of the actual normal four-group forces fixed-field order
four. Every order-three element of the component Borel belongs to the
original actor, by its proved theta identity. The concrete cubic fixer
calculation therefore makes an element of `C_S(Y₊)` act trivially on `L`.
This gives the literal upstairs equality, without quotient-centralizer
identifications or using the contrary centralizer inequality in its proof.

The arbitrary Hermitian form is transported by a genuine matrix basis
change. Simplicity for semilinear coverage is inherited from the component:
the projective unitary model is centerless and the component is quasisimple.
The Borel equality remains explicit, as supplied by the separate parabolic
inspection. Source: Aschbacher--Smith, proof of 15.3.43, printed p.1140.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels

private theorem unitary_four_cubic_fixer
    {H : Type*} [Group H] [Finite H] [Theory.GroupTheory.IsQuasisimple H]
    (hm : ClassicalGroup.IsPSU H 3 4) (P : Sylow 2 H) (a : MulAut H)
    (hfix : ∀ b ∈ normalizer (P : Set H), orderOf b = 3 → a b = b) : a = 1 := by
  obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := hm
  let J0 := Unitary.FormTransport.standardForm J
  obtain ⟨C, hC⟩ := Unitary.FormTransport.exists_standard_basis J 2 (by decide) hcard hconj
  let f := e.trans (Unitary.FormTransport.projectiveEquiv J C hC)
  let K := ProjectiveSpecialUnitaryMatrixGroup J0
  let : Theory.GroupTheory.IsQuasisimple K :=
    Theory.GroupTheory.IsQuasisimple.of_mulEquiv f
  have hz : center K = ⊥ :=
    HermitianForm.EvenProjectiveComparison.center_eq_bot J0 (n := 2)
      (by decide) hcard hconj
  let : IsSimpleGroup (K ⧸ center K) := Theory.GroupTheory.IsQuasisimple.simple
  let ez : (K ⧸ center K) ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot
  let : IsSimpleGroup K := ez.symm.isSimpleGroup
  let P' := P.mapSurjective (f := f.toMonoidHom) f.surjective
  have hB : (normalizer (P : Set H)).map f.toMonoidHom = normalizer (P' : Set K) :=
    Subgroup.map_equiv_normalizer_eq (P : Subgroup H) f
  have ha : MulAut.congr f a = 1 := by
    apply UnitaryBorel.eq_one_of_fixes_sylowNormalizer_cubics J0 rfl hcard hconj P'
    intro b hb hb3
    rw [← hB] at hb
    obtain ⟨x, hx, rfl⟩ := hb
    have hx3 : orderOf x = 3 :=
      (orderOf_injective f.toMonoidHom f.injective x).symm.trans hb3
    change f (a (f.symm (f x))) = f x
    rw [f.symm_apply_apply, hfix x hx hx3]
  exact (MulAut.congr f).injective (ha.trans (map_one _).symm)

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- The genuine unitary Borel gives the literal centralizer equality in `G`.
The Borel identification is the only premise beyond the reduced configuration
and its positive-degree unitary model. -/
theorem unitary_borel_centralizers
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) (hB : M ⊓ L = borel L S) :
    S ⊓ centralizer (Yplus : Set G) = S ⊓ centralizer (L : Set G) := by
  obtain ⟨rfl, _⟩ := unitary_borel_degree_eq_two c hn hm hB
  let : Theory.GroupTheory.IsQuasisimple L := by
    let := c.component.2
    exact Theory.GroupTheory.IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe c.component_le)
  obtain ⟨P, hP⟩ := component_sylow c
  have hPL : (S ⊓ L).subgroupOf L = (P : Subgroup L) := by
    rw [← hP]
    exact comap_map_eq_self_of_injective L.subtype_injective _
  have hBN : (normalizer (P : Set L)).map L.subtype = borel L S := by
    change (normalizer ((P : Subgroup L) : Set L)).map L.subtype = _
    rw [← hPL, ← subgroupOf_normalizer_eq inf_le_right, subgroupOf_map_subtype]
    exact inf_comm _ _
  have htheta : (theta (normalizer (P : Set L))).map L.subtype ≤ Yplus := by
    rw [theta_map_of_injective L.subtype L.subtype_injective, hBN, ← hB]
    exact (theta_mono (le_inf inf_le_left (inf_le_right.trans c.component_le))).trans
      c.theta_eq.le
  apply le_antisymm
  · rintro s ⟨hs, hsy⟩
    let si : normalizer (L : Set G) :=
      ⟨s, c.normalizes ((sylow_le_local c hs).2)⟩
    let a := L.normalizerMonoidHom si
    have ha : a = 1 := by
      apply unitary_four_cubic_fixer hm P
      intro b hb hb3
      have hy : (b : G) ∈ Yplus :=
        htheta (mem_map_of_mem L.subtype (subset_closure ⟨hb, hb3⟩))
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hsy b hy).symm
    have hc : si ∈ L.normalizerMonoidHom.ker := ha
    rw [normalizerMonoidHom_ker] at hc
    exact ⟨hs, hc⟩
  · exact inf_le_inf_left S (centralizer_le c.y_le_component)

/-- The conditional unitary Borel branch is excluded by the independent
upstairs centralizer inequality from 15.3.43(c). -/
theorem not_unitary_borel
    (c : ReducedConfiguration Yplus S M I L V₁ V₂) {n : ℕ} (hn : 0 < n)
    (hm : ClassicalGroup.IsPSU L 3 (2 ^ n)) (hB : M ⊓ L = borel L S) : False :=
  centralizers_ne c (unitary_borel_centralizers c hn hm hB)

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels
