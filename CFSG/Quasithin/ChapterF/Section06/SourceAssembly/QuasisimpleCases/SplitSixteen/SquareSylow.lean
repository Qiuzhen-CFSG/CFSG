module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.SplitSixteen.SquareComponent
public import Theory.GroupTheory.SplitDihedralCentralSupplement
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.DihedralGeneratedFactor

/-!
# The actual outer involution for the square-field component

Its Sylow is dihedral of order eight. The larger split Sylow has center
of order four and therefore has a central involution outside the component.
The normal component has index two, so this particular involution generates
the full ambient extension and fixes its original Sylow intersection.

Source: Aschbacher--Smith F.6.18(8), printed p.310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.ClassicalSmallSylow
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G]

/-- Every Sylow of the original square-field subgroup is actually D8. -/
theorem square_psl_subgroup_sylow_dihedral_eight
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL K 2 (p ^ 2)) (S : Sylow 2 K) :
    Nat.card S = 8 ∧ Nonempty (S ≃* DihedralGroup 4) := by
  obtain ⟨F, _, _, hF, ⟨j⟩⟩ := hm
  have hq : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 2, hp, ho, by decide, hF⟩
  let U := S.mapSurjective (f := j.toMonoidHom) j.surjective
  let a : S ≃* U := j.subgroupMap (S : Subgroup K)
  obtain ⟨m, _, ⟨b⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F hq U
  let c := a.trans b
  have hc : (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) ^ 4 = 1 := by
    have hx := split_sixteen_sylow_section_pow_four T eT K (MonoidHom.id K)
      Function.surjective_id S (c.symm (DihedralGroup.r 1))
    simpa only [map_pow, c.apply_symm_apply, map_one] using congrArg c hx
  have hd := orderOf_dvd_of_pow_eq_one hc
  rw [DihedralGroup.orderOf_r_one] at hd
  have hm4 : 2 ^ m ≤ 4 := Nat.le_of_dvd (by decide) hd
  have hU : Nat.card U ≤ 8 := by
    rw [Nat.card_congr b.toEquiv, DihedralGroup.nat_card]
    omega
  have hcardU : Nat.card U = 8 := by
    rcases psl2_small_sylow_parameters hq U hU with ⟨_, hmod⟩ | ⟨hc, _⟩
    · rw [hF] at hmod
      have he := degree_one_of_small_degree_nonsquare_mod_eight (by decide : 2 ≤ 2) hmod
      omega
    · exact hc
  have hm2 : m = 2 := by
    have h := hcardU
    rw [Nat.card_congr b.toEquiv, DihedralGroup.nat_card] at h
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    norm_num only [show 2 ^ 2 = 4 by decide]
    omega
  subst m
  exact ⟨(Nat.card_congr a.toEquiv).trans hcardU, ⟨c⟩⟩

/-- A concrete outer involution centralizes the original common Sylow
and generates the normal square-field component extension. -/
theorem square_psl_component_central_involution
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) [K.Normal] (hquot : IsPGroup 2 (G ⧸ K))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL K 2 (p ^ 2)) :
    ∃ t : G, t ∈ T ∧ orderOf t = 2 ∧ t ∉ K ∧ K ⊔ zpowers t = ⊤ ∧
      ∀ x ∈ (T : Subgroup G), t * x = x * t := by
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal K
  obtain ⟨hS8, ⟨eS⟩⟩ := square_psl_subgroup_sylow_dihedral_eight T eT K hp ho hm S
  let N : Subgroup T := K.subgroupOf (T : Subgroup G)
  let a : N ≃* S := {
    toFun := fun x => ⟨⟨x.val.val, x.property⟩, by rw [hS]; exact x.val.property⟩
    invFun := fun s => ⟨⟨s.val.val, by have hs : (s : K) ∈ (S : Subgroup K) := s.property; change (s : K) ∈ (T : Subgroup G).subgroupOf K; exact hS ▸ hs⟩, s.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  have hN : Nat.card (center N) = 2 := by
    rw [Nat.card_congr (centerCongr (a.trans eS)).toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  obtain ⟨z, hz, hzout, hzo⟩ := exists_central_involution_outside_of_split_sixteen eT N hN
  let t : G := z
  have htout : t ∉ K := hzout
  have hT16 : Nat.card T = 16 := (Nat.card_congr eT.toEquiv).trans split_sixteen_card
  have hindex : K.index = 2 := by
    obtain ⟨n, hn⟩ := hquot.exists_card_eq
    change K.index = 2 ^ n at hn
    by_cases hn0 : n = 0
    · have htop : K = ⊤ := Subgroup.index_eq_one.mp (by simpa [hn0] using hn)
      exact (htout (htop ▸ Subgroup.mem_top t)).elim
    · by_cases hn1 : n = 1
      · simpa [hn1] using hn
      · have hn2 : 2 ≤ n := by omega
        have h8 : 8 ∣ Nat.card K := hS8 ▸ S.card_subgroup_dvd_card
        have h4 : 4 ∣ K.index := by
          rw [hn]
          exact Nat.pow_dvd_pow 2 hn2
        have h32 : 32 ∣ Nat.card G := by
          simpa only [K.card_mul_index] using Nat.mul_dvd_mul h8 h4
        have hh := Nat.le_of_dvd (Nat.card_pos (α := T))
          (T.pow_dvd_card_of_pow_dvd_card (n := 5) h32)
        omega
  refine ⟨t, z.property, (Subgroup.orderOf_coe z).trans hzo, htout, ?_, ?_⟩
  · apply top_unique
    intro x _
    by_cases hx : x ∈ K
    · exact (show K ≤ K ⊔ zpowers t from le_sup_left) hx
    · have hxt : x * t⁻¹ ∈ K := by
        rw [K.mul_mem_iff_of_index_two hindex, K.inv_mem_iff]
        exact iff_of_false hx htout
      have hh := (K ⊔ zpowers t).mul_mem ((show K ≤ K ⊔ zpowers t from le_sup_left) hxt)
        ((show zpowers t ≤ K ⊔ zpowers t from le_sup_right) (mem_zpowers t))
      simpa using hh
  · intro x hx
    exact congrArg (fun w : T => (w : G)) (mem_center_iff.mp hz ⟨x, hx⟩).symm

end CFSG.Quasithin.ChapterF.SourceAssembly
