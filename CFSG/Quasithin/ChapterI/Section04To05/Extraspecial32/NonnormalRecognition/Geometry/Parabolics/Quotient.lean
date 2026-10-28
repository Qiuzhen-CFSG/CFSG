module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Assembly
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups

/-!
# Lifting the two maximal overgroups through the actual quotient

The binary rank-two models have exactly two maximal overgroups of a Sylow
2-subgroup. A surjective quotient whose kernel is a normal two-subgroup
preserves this bound. Prime indices and the literal chamber intersection
then identify any specified pair. All subgroup transport is by the actual
quotient homomorphism or the canonical inclusion equivalence.

This is the subgroup-lattice step in Aschbacher, “A 2-local characterization
of M12”, Lemma 3.2, printed p.37. The split-extension stabilizer calculation
is separate; this module does not assert it.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Parabolics

variable {G K : Type*} [Group G] [Group K]

def HasTwoMaximalOvergroups (B : Subgroup G) : Prop :=
  ∃ P R : Subgroup G, ∀ U : Subgroup G,
    IsCoatom U → B ≤ U → U = P ∨ U = R

theorem isCoatom_of_prime_index (P : Subgroup G) (hp : P.index.Prime) :
    IsCoatom P := by
  refine ⟨fun he => hp.ne_one (he ▸ index_top), ?_⟩
  intro U hU
  rcases (Nat.dvd_prime hp).mp (index_dvd_of_le hU.le) with hu | hu
  · exact index_eq_one.mp hu
  · have hmul := relIndex_mul_index hU.le
    rw [hu] at hmul
    have hi : P.relIndex U = 1 := by nlinarith [hp.pos]
    exact (hU.not_ge (relIndex_eq_one.mp hi)).elim

theorem hasTwoMaximalOvergroups_PSL (S : Sylow 2 Matrix.PSL3Two.PSL) :
    HasTwoMaximalOvergroups (S : Subgroup Matrix.PSL3Two.PSL) := by
  obtain ⟨P, R, _, _, _, _, _, _, h⟩ := Matrix.PSL3Two.sylow_parabolics S
  exact ⟨P, R, fun U hu hb => (h U hu).mp hb⟩

theorem hasTwoMaximalOvergroups_product (S : Sylow 2 SymmetricThreeProduct.G) :
    HasTwoMaximalOvergroups (S : Subgroup SymmetricThreeProduct.G) := by
  obtain ⟨P, R, _, _, h⟩ := SymmetricThreeProduct.exists_parabolics_over_sylow S
  exact ⟨P, R, fun U hu hb => (h U).mp ⟨hu, hb⟩⟩

theorem hasTwoMaximalOvergroups_comap (f : G →* K) (hf : Function.Surjective f)
    (B : Subgroup G) (hk : f.ker ≤ B) (ht : HasTwoMaximalOvergroups (B.map f)) :
    HasTwoMaximalOvergroups B := by
  obtain ⟨P, R, h⟩ := ht
  refine ⟨P.comap f, R.comap f, ?_⟩
  intro U hU hBU
  have hker : f.ker ≤ U := hk.trans hBU
  have hc : (U.map f).comap f = U := comap_map_eq_self hker
  have hm : IsCoatom (U.map f) := by
    refine ⟨?_, ?_⟩
    · intro he
      apply hU.1
      rw [← hc, he, comap_top]
    · intro V hv
      have hlt : U < V.comap f := by
        rw [← hc]
        exact (comap_lt_comap_of_surjective hf).mpr hv
      have he := hU.2 _ hlt
      exact (comap_injective hf) (he.trans (comap_top f).symm)
  rcases h (U.map f) hm (map_mono hBU) with he | he
  · exact Or.inl (hc.symm.trans (congrArg (comap f) he))
  · exact Or.inr (hc.symm.trans (congrArg (comap f) he))

theorem rankTwo_of_maximal (B P R : Subgroup G)
    (ht : HasTwoMaximalOvergroups B) (hp : IsCoatom P) (hr : IsCoatom R)
    (hne : P ≠ R) (hi : P ⊓ R = B) :
    Quasithin.I5.RankTwoParabolics G B P R := by
  refine ⟨hp, hr, hne, hi, ?_⟩
  obtain ⟨X, Y, h⟩ := ht
  have hP := h P hp (hi ▸ inf_le_left)
  have hR := h R hr (hi ▸ inf_le_right)
  intro U hBU hU
  have hU' := h U hU hBU
  rcases hP with rfl | rfl <;> rcases hR with rfl | rfl
  · exact (hne rfl).elim
  · exact hU'
  · exact hU'.symm
  · exact (hne rfl).elim

theorem hasTwoMaximalOvergroups_quotient [Finite G] [Finite K]
    (N : Subgroup G) [N.Normal] (hn : IsPGroup 2 N)
    (e : (G ⧸ N) ≃* K) (model : ∀ S : Sylow 2 K,
      HasTwoMaximalOvergroups (S : Subgroup K)) (S : Sylow 2 G) :
    HasTwoMaximalOvergroups (S : Subgroup G) := by
  let f : G →* K := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hk : f.ker = N := by
    ext x
    change e (QuotientGroup.mk' N x) = 1 ↔ x ∈ N
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  apply hasTwoMaximalOvergroups_comap f hf _
  · rw [hk]
    exact hn.le_sylow_of_normal S
  · exact model (S.mapSurjective hf)


theorem rankTwo_of_prime_indices [Finite G] (B P R : Subgroup G)
    (ht : HasTwoMaximalOvergroups B) (hp : P.index.Prime) (hr : R.index.Prime)
    (hi : P ⊓ R = B) (hb : Nat.card B < Nat.card P) :
    Quasithin.I5.RankTwoParabolics G B P R := by
  apply rankTwo_of_maximal B P R ht (isCoatom_of_prime_index P hp)
    (isCoatom_of_prime_index R hr) _ hi
  intro he
  rw [← hi, ← he, inf_idem] at hb
  exact (lt_irrefl _ hb)

theorem rankTwo_comap_equiv (e : G ≃* K) {B P R : Subgroup K}
    (h : Quasithin.I5.RankTwoParabolics K B P R) :
    Quasithin.I5.RankTwoParabolics G (B.comap e.toMonoidHom)
      (P.comap e.toMonoidHom) (R.comap e.toMonoidHom) := by
  refine ⟨(isCoatom_comap e).mpr h.left_maximal,
    (isCoatom_comap e).mpr h.right_maximal,
    fun he => h.distinct (comap_injective e.surjective he),
    (comap_inf P R e.toMonoidHom).symm.trans (congrArg (comap e.toMonoidHom) h.borel_eq), ?_⟩
  intro U hBU hU
  have hB : B ≤ U.map e.toMonoidHom := by
    rw [← map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective B]
    exact map_mono hBU
  have hc : (U.map e.toMonoidHom).comap e.toMonoidHom = U :=
    comap_map_eq_self_of_injective e.injective U
  rcases h.exhaustive _ hB ((e.mapSubgroup.isCoatom_iff U).mpr hU) with he | he
  · exact Or.inl (hc.symm.trans (congrArg (comap e.toMonoidHom) he))
  · exact Or.inr (hc.symm.trans (congrArg (comap e.toMonoidHom) he))

theorem rankTwo_subgroupOf (M N R T L : Subgroup G) (hML : M ≤ L)
    (h : Quasithin.I5.RankTwoParabolics M (T.subgroupOf M)
      (N.subgroupOf M) (R.subgroupOf M)) :
    Quasithin.I5.RankTwoParabolics (M.subgroupOf L)
      ((T.subgroupOf L).subgroupOf (M.subgroupOf L))
      ((N.subgroupOf L).subgroupOf (M.subgroupOf L))
      ((R.subgroupOf L).subgroupOf (M.subgroupOf L)) :=
  rankTwo_comap_equiv (subgroupOfEquivOfLe hML) h

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Parabolics

end
