module

public import CFSG.Quasithin.ChapterG.Section06.Source
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# A Sylow-normalized cubic excludes the two transvection factors

The inversion relation first puts the original cubic in the factor containing
the marked transvection. If a Sylow element exchanged the two factors, its
conjugate cubic would lie in their trivial intersection. Hence the Sylow fixes
the first factor. Its conjugacy orbit has size at most two, so the odd index
of a Sylow overgroup makes that factor normal in the full group. Generation
by the marked element's normal closure then contradicts the second factor.

This proves the factor-interchange exclusion in Aschbacher–Smith, C.5.12,
printed p.163, on the literal two-factor output of G.6.4. No realization of
that output for an arbitrary representation is asserted here.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section06
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {a : G}

omit [Finite G] in
theorem TwoFactorModules.inverted_element_mem_first
    (d : TwoFactorModules ρ a) (c : G) (hi : a * c = c ^ 2 * a) : c ∈ d.first := by
  have he : a * (c * a⁻¹ * c⁻¹) = c := by
    calc
      a * (c * a⁻¹ * c⁻¹) = (a * c) * a⁻¹ * c⁻¹ := by group
      _ = (c ^ 2 * a) * a⁻¹ * c⁻¹ := by rw [hi]
      _ = c := by group
  let K := normalClosure ({a} : Set G)
  have haK : a ∈ K := subset_normalClosure (Set.mem_singleton a)
  have hcK : c ∈ K := he ▸ K.mul_mem haK
    ((inferInstance : K.Normal).conj_mem a⁻¹ (K.inv_mem haK) c)
  have hKF : K ≤ normalizer (d.first : Set G) := by
    change normalClosure ({a} : Set G) ≤ normalizer (d.first : Set G)
    rw [← d.join_eq]
    apply sup_le d.first.le_normalizer
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [d.commute]
    exact bot_le
  have hca : c * a⁻¹ * c⁻¹ ∈ d.first :=
    (mem_normalizer_iff.mp (hKF hcK) a⁻¹).mp (d.first.inv_mem d.marked)
  exact he ▸ d.first.mul_mem d.marked hca

theorem TwoFactorModules.not_sylow_normalizes_inverted_cubic
    (d : TwoFactorModules ρ a) (S : Sylow 2 G) (c : G) (hcne : c ≠ 1)
    (hi : a * c = c ^ 2 * a)
    (hn : (S : Subgroup G) ≤ normalizer (zpowers c : Set G)) : False := by
  have hcF := d.inverted_element_mem_first c hi
  have hSF : (S : Subgroup G) ≤ normalizer (d.first : Set G) := by
    intro s hs
    rcases d.permutation s with h | h
    · exact mem_normalizer_iff_map_conj_eq.mpr h.1
    · have hc' : s * c * s⁻¹ ∈ d.first :=
        (zpowers_le.mpr hcF) ((mem_normalizer_iff.mp (hn hs) c).mp (mem_zpowers c))
      have hc'' : s * c * s⁻¹ ∈ d.second := by
        rw [← h.1]
        exact mem_map_of_mem (MulAut.conj s).toMonoidHom hcF
      have hz : s * c * s⁻¹ = 1 := d.disjoint.le ⟨hc', hc''⟩
      have hcz := congrArg (fun x : G => s⁻¹ * x * s) hz
      exact (hcne (by simpa only [mul_assoc, inv_mul_cancel_left,
        inv_mul_cancel, mul_one, one_mul] using hcz)).elim
  have hpair : d.first ≠ d.second := by
    intro he
    apply d.second_nontrivial
    simpa only [he, inf_idem] using d.disjoint
  have hsub : (Set.range fun g : G => d.first.map (MulAut.conj g).toMonoidHom) ⊆
      {d.first, d.second} := by
    rintro _ ⟨g, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (d.permutation g).imp And.left And.left
  have hindex : (normalizer (d.first : Set G)).index ≤ 2 := by
    rw [← ncard_conjugates_eq_index_normalizer]
    exact (Set.ncard_le_ncard hsub).trans_eq (Set.ncard_pair hpair)
  have hindexne : (normalizer (d.first : Set G)).index ≠ 2 := by
    intro he
    have hd := index_dvd_of_le hSF
    rw [he] at hd
    exact S.not_dvd_index hd
  have hindexpos := (normalizer (d.first : Set G)).index_ne_zero_of_finite
  have hnormal : d.first.Normal := normalizer_eq_top_iff.mp
    (index_eq_one.mp (by omega))
  let := hnormal
  have hKF : normalClosure ({a} : Set G) ≤ d.first :=
    normalClosure_le_normal (by simpa only [Set.singleton_subset_iff, SetLike.mem_coe] using d.marked)
  have hsecond : d.second ≤ d.first := by
    have hj : d.first ⊔ d.second ≤ d.first := by rwa [d.join_eq]
    exact le_sup_right.trans hj
  apply d.second_nontrivial
  apply bot_unique
  intro x hx
  exact d.disjoint.le ⟨hsecond hx, hx⟩
end CFSG.Quasithin.ChapterG.Section06
