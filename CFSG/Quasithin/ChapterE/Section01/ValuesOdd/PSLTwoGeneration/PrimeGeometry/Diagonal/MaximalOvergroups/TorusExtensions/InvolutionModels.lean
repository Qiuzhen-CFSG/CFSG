module

public import GorensteinWalter.PGL2InnerInvolutionFusion
public import GorensteinWalter.PGL2InnerAction
public import GorensteinWalter.PGL2TorusCentralizer
public import GorensteinWalter.DihedralGenerators
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# Full dihedral centralizers of inner involutions in PGL₂

Of the split and nonsplit tori over an odd finite field, one has order
divisible by four. Its involution is a square in that cyclic torus, hence
belongs to the canonical PSL₂ image of index two. The explicit torus
centralizer calculation and the dihedral presentation identify its whole
centralizer. Inner-involution fusion then transports this model to every
involution in the canonical image.

This is the model calculation used in the dihedral-intersection branch of
Aschbacher--Smith E.1.14(6), printed p.214, citing Aschbacher (1982), Lemma
4.10. The torus matrices and fusion are supplied by the narrow
Gorenstein--Walter modules imported above.
-/

noncomputable section
open Subgroup GorensteinWalter

private theorem reflected_join_dihedral
    {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) (w : G) (hUc : IsCyclic U) (hwU : w ∉ U)
    (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹) :
    Nonempty ((U ⊔ zpowers w : Subgroup G) ≃* DihedralGroup (Nat.card U)) := by
  obtain ⟨r, hrgen⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top U).mp hUc
  have hrU : r ∈ U := hrgen ▸ mem_zpowers r
  let D : Subgroup G := U ⊔ zpowers w
  let ρ : D := ⟨r, (le_sup_left : U ≤ D) hrU⟩
  let σ : D := ⟨w, (le_sup_right : zpowers w ≤ D) (mem_zpowers w)⟩
  have hgen : (⊤ : Subgroup D) = zpowers ρ ⊔ zpowers σ := by
    apply le_antisymm
    · intro x _
      have hxmap : (x : G) ∈ (zpowers ρ ⊔ zpowers σ).map D.subtype := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        change (x : G) ∈ zpowers r ⊔ zpowers w
        rw [hrgen]
        exact x.property
      obtain ⟨y, hy, hyx⟩ := mem_map.mp hxmap
      exact (Subtype.ext hyx : y = x) ▸ hy
    · exact le_top
  have hσ2 : σ ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hwsq)
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (hwinv r hrU)
  have hσρ : σ ∉ zpowers ρ := by
    intro hmem
    apply hwU
    rw [← hrgen]
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hmem
    exact ⟨k, congrArg Subtype.val hk⟩
  have he := dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have hord : orderOf ρ = Nat.card U := by
    rw [← Subgroup.orderOf_coe ρ]
    change orderOf r = Nat.card U
    rw [← Nat.card_zpowers, hrgen]
  rwa [hord] at he

private theorem cyclic_involution_mem_index_two
    {G : Type*} [Group G] [Finite G] (H U : Subgroup G)
    (hH : H.index = 2) (hUc : IsCyclic U) (h4 : 4 ∣ Nat.card U)
    {s : G} (hsU : s ∈ U) (hs : IsInvolution s) : s ∈ H := by
  let : IsCyclic U := hUc
  obtain ⟨r, hr⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := U)
  let a : U := r ^ (Nat.card U / 4)
  have ha : orderOf a = 4 := by
    simpa only [hr] using
      (orderOf_pow_orderOf_div (x := r) (by rw [hr]; exact Nat.card_pos.ne')
        (by rwa [hr]))
  have ha2 : orderOf (a ^ 2) = 2 := by rw [orderOf_pow, ha]; norm_num
  have hs2 : orderOf (⟨s, hsU⟩ : U) = 2 :=
    orderOf_eq_prime (Subtype.ext hs.2)
      (fun h => hs.1 (congrArg Subtype.val h))
  have heq : (⟨s, hsU⟩ : U) = a ^ 2 := IsCyclic.eq_of_orderOf_eq_two hs2 ha2
  have heqG : s = (a : G) ^ 2 := congrArg Subtype.val heq
  rw [heqG]
  exact H.sq_mem_of_index_two hH a

private theorem map_centralizer_singleton
    {G : Type*} [Group G] (e : G ≃* G) (s : G) :
    (centralizer ({s} : Set G)).map e.toMonoidHom =
      centralizer ({e s} : Set G) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change e x * e s = e s * e x
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hx)
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using (mem_centralizer_singleton_iff.mp hy)

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups
variable {F : Type*} [Field F] [Finite F]

private instance finitePGLModels : Finite (PGL2 F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- A torus whose order is divisible by four supplies a canonical inner
involution and the full reflected-torus centralizer. -/
private theorem exists_inner_torus_centralizer_model
    (hF : IsOddPrimePower (Nat.card F)) :
    ∃ s : PGL2 F,
      s ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ∧
      IsInvolution s ∧ ∃ n : ℕ,
      (n = Nat.card F - 1 ∨ n = Nat.card F + 1) ∧
      Nonempty (centralizer ({s} : Set (PGL2 F)) ≃* DihedralGroup n) := by
  have hodd : Odd (Nat.card F) := by
    obtain ⟨p, f, _, hp, _, hq⟩ := hF
    rw [hq]
    exact hp.pow
  have hfour : 4 ∣ Nat.card F - 1 ∨ 4 ∣ Nat.card F + 1 := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hdata : ∃ U : Subgroup (PGL2 F), ∃ s w : PGL2 F,
      IsCyclic U ∧ (Nat.card U = Nat.card F - 1 ∨ Nat.card U = Nat.card F + 1) ∧
      4 ∣ Nat.card U ∧ s ∈ U ∧ IsInvolution s ∧ w ∉ U ∧ w * w = 1 ∧
      (∀ x : PGL2 F, x ∈ U → w * x * w⁻¹ = x⁻¹) ∧
      centralizer ({s} : Set (PGL2 F)) = U ⊔ zpowers w := by
    rcases hfour with hfour | hfour
    · obtain ⟨U, s, w, hUc, hUcard, hsU, hssq, hsne, hwU, hwsq, hwinv, hC, _⟩ :=
        pgl2_split_torus_centralizer_data F hodd
      exact ⟨U, s, w, hUc, Or.inl hUcard, hUcard ▸ hfour, hsU,
        ⟨hsne, by simpa [pow_two] using hssq⟩, hwU, hwsq, hwinv, hC⟩
    · obtain ⟨U, s, w, hUc, hUcard, hsU, hssq, hsne, hwU, hwsq, hwinv, hC, _⟩ :=
        pgl2_nonsplit_torus_centralizer_data F hodd
      exact ⟨U, s, w, hUc, Or.inr hUcard, hUcard ▸ hfour, hsU,
        ⟨hsne, by simpa [pow_two] using hssq⟩, hwU, hwsq, hwinv, hC⟩
  obtain ⟨U, s, w, hUc, hUcard, h4, hsU, hs, hwU, hwsq, hwinv, hC⟩ := hdata
  have hsinner := cyclic_involution_mem_index_two _ U
    (pgl2_psl2Range_index_eq_two F hF) hUc h4 hsU hs
  obtain ⟨e⟩ := reflected_join_dihedral U w hUc hwU hwsq hwinv
  exact ⟨s, hsinner, hs, Nat.card U, hUcard, ⟨(MulEquiv.subgroupCongr hC).trans e⟩⟩

/-- Every inner involution has the full split or nonsplit dihedral centralizer,
transported along the actual inner-involution conjugacy. -/
public theorem inner_involution_centralizer_model
    (hF : IsOddPrimePower (Nat.card F)) (hlarge : 3 < Nat.card F)
    (s : PGL2 F)
    (hsinner : s ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range)
    (hs : IsInvolution s) :
    ∃ n : ℕ, (n = Nat.card F - 1 ∨ n = Nat.card F + 1) ∧
      Nonempty (centralizer ({s} : Set (PGL2 F)) ≃* DihedralGroup n) := by
  obtain ⟨t, htinner, ht, n, hn, ⟨e⟩⟩ := exists_inner_torus_centralizer_model hF
  have hJ := pgl2_commutator_eq_psl2_range_of_card_gt_three F hF hlarge
  obtain ⟨g, _, hg⟩ := pgl2_inner_involutions_conjugate hF hlarge
    (hJ ▸ hsinner) hs (hJ ▸ htinner) ht
  have hmap : (centralizer ({s} : Set (PGL2 F))).map (MulAut.conj g).toMonoidHom =
      centralizer ({t} : Set (PGL2 F)) := by
    simpa only [MulAut.conj_apply, hg] using map_centralizer_singleton (MulAut.conj g) s
  exact ⟨n, hn, ⟨((MulAut.conj g).subgroupMap _).trans
    ((MulEquiv.subgroupCongr hmap).trans e)⟩⟩
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.MaximalOvergroups
