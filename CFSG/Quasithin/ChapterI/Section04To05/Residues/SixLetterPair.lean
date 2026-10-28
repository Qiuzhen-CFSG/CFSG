module
public import CFSG.Quasithin.ChapterI.Section04To05.Residues.SourceLifting
public import Theory.SpecificGroups.SymmetricSix.Parabolics

/-!
# The two parabolics of a six-letter quotient

In A₆ and S₆ every maximal overgroup of a Sylow two-subgroup has relative
index three. Thus any strict proper overgroup is already maximal. The
concrete two-parabolic classification gives the intersection and exhaustive
pair; pulling back through a normal two-group kernel retains all these
properties on the original subgroups.

This supplies the first-vertex residue in Aschbacher–Smith 13.4.9,
printed p.906, from the quotient and the original subgroups, without
assuming a rank-two geometry.
-/

public noncomputable section
open Subgroup
namespace Quasithin.I5.RankTwoParabolics
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem eq_of_prime_interval {B U A : Subgroup G}
    (hBU : B < U) (hUA : U ≤ A) (hi : B.relIndex A = 3) : U = A := by
  have hm := relIndex_mul_relIndex B U A hBU.le hUA
  rw [hi] at hm
  have hd : B.relIndex U ∣ 3 := ⟨U.relIndex A, hm.symm⟩
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with he | he
  · exact (hBU.not_ge (relIndex_eq_one.mp he)).elim
  · rw [he] at hm
    have hu : U.relIndex A = 1 := by omega
    exact le_antisymm hUA (relIndex_eq_one.mp hu)

private theorem of_cubic_coatoms (B A C : Subgroup G)
    (hc : ∀ U : Subgroup G, (IsCoatom U ∧ B ≤ U) ↔ U = A ∨ U = C)
    (hi : A ⊓ C = B) (hBA : B.relIndex A = 3) (hBC : B.relIndex C = 3)
    (P R : Subgroup G) (hBP : B < P) (hBR : B < R)
    (hP : P ≠ ⊤) (hR : R ≠ ⊤) (hne : P ≠ R) :
    RankTwoParabolics G B P R := by
  have classify (U : Subgroup G) (hBU : B < U) (hu : U ≠ ⊤) : U = A ∨ U = C := by
    obtain ⟨Y,hY,hUY⟩ := (eq_top_or_exists_le_coatom U).resolve_left hu
    rcases (hc Y).mp ⟨hY,hBU.le.trans hUY⟩ with rfl | rfl
    · exact Or.inl (eq_of_prime_interval hBU hUY hBA)
    · exact Or.inr (eq_of_prime_interval hBU hUY hBC)
  have hp := classify P hBP hP
  have hr := classify R hBR hR
  refine ⟨((hc P).mpr hp).1,((hc R).mpr hr).1,hne,?_,?_⟩
  · rcases hp with rfl | rfl <;> rcases hr with rfl | rfl
    · exact (hne rfl).elim
    · exact hi
    · exact (inf_comm _ _).trans hi
    · exact (hne rfl).elim
  · intro U hBU hU
    have hu := (hc U).mp ⟨hU,hBU⟩
    rcases hp with rfl | rfl <;> rcases hr with rfl | rfl
    · exact (hne rfl).elim
    · exact hu
    · exact hu.symm
    · exact (hne rfl).elim

private theorem six_model (S : Sylow 2 (Equiv.Perm (Fin 6)))
    (P R : Subgroup (Equiv.Perm (Fin 6)))
    (hSP : (S : Subgroup _) < P) (hSR : (S : Subgroup _) < R)
    (hP : P ≠ ⊤) (hR : R ≠ ⊤) (hne : P ≠ R) :
    RankTwoParabolics _ (S : Subgroup _) P R := by
  open Theory.SpecificGroups.SymmetricSix in
  obtain ⟨g,hg,hc⟩ := coatoms_over_sylow S
  let a := MulAut.conj g
  open Theory.SpecificGroups.SymmetricSix in
  apply of_cubic_coatoms (S : Subgroup _) (a.mapSubgroup duadStabilizer)
    (a.mapSubgroup synthemeStabilizer) hc ?_ ?_ ?_ P R hSP hSR hP hR hne
  · rw [←a.mapSubgroup.map_inf]
    exact hg
  · rw [←hg]
    exact (relIndex_map_map_of_injective _ _ a.injective).trans
      Theory.SpecificGroups.SymmetricSix.borel_relIndex_duad
  · rw [←hg]
    exact (relIndex_map_map_of_injective _ _ a.injective).trans
      Theory.SpecificGroups.SymmetricSix.borel_relIndex_syntheme

private theorem alternating_six_model (S : Sylow 2 (alternatingGroup (Fin 6)))
    (P R : Subgroup (alternatingGroup (Fin 6)))
    (hSP : (S : Subgroup _) < P) (hSR : (S : Subgroup _) < R)
    (hP : P ≠ ⊤) (hR : R ≠ ⊤) (hne : P ≠ R) :
    RankTwoParabolics _ (S : Subgroup _) P R := by
  open Theory.SpecificGroups.SymmetricSix in
  obtain ⟨g,hg,hc⟩ := a6_coatoms_over_sylow S
  let a := MulAut.conj g
  open Theory.SpecificGroups.SymmetricSix in
  apply of_cubic_coatoms (S : Subgroup _) (a.mapSubgroup a6DuadStabilizer)
    (a.mapSubgroup a6SynthemeStabilizer) hc ?_ ?_ ?_ P R hSP hSR hP hR hne
  · rw [←a.mapSubgroup.map_inf]
    exact hg
  · rw [←hg]
    exact (relIndex_map_map_of_injective _ _ a.injective).trans
      Theory.SpecificGroups.SymmetricSix.a6Borel_relIndex_duad
  · rw [←hg]
    exact (relIndex_map_map_of_injective _ _ a.injective).trans
      Theory.SpecificGroups.SymmetricSix.a6Borel_relIndex_syntheme

/-- Two distinct proper strict overgroups of a Sylow subgroup give the
full rank-two residue in either six-letter quotient. -/
theorem of_six_letter_two_quotient (N : Subgroup G) [N.Normal] (hn : IsPGroup 2 N)
    (e : Nonempty ((G ⧸ N) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((G ⧸ N) ≃* Equiv.Perm (Fin 6)))
    (S : Sylow 2 G) (P R : Subgroup G)
    (hSP : (S : Subgroup G) < P) (hSR : (S : Subgroup G) < R)
    (hP : P ≠ ⊤) (hR : R ≠ ⊤) (hne : P ≠ R) :
    RankTwoParabolics G (S : Subgroup G) P R := by
  have transfer {A : Type} [Group A] [Finite A] (eA : (G ⧸ N) ≃* A)
      (model : ∀ (U : Sylow 2 A) (B C : Subgroup A), (U : Subgroup A) < B →
        (U : Subgroup A) < C → B ≠ ⊤ → C ≠ ⊤ → B ≠ C →
        RankTwoParabolics A (U : Subgroup A) B C) :
      RankTwoParabolics G (S : Subgroup G) P R := by
    let q := eA.toMonoidHom.comp (QuotientGroup.mk' N)
    have hq : Function.Surjective q := eA.surjective.comp (QuotientGroup.mk'_surjective N)
    have hk : q.ker ≤ (S : Subgroup G) := by
      rw [MonoidHom.ker_comp_of_injective _ _ eA.injective,QuotientGroup.ker_mk']
      exact hn.le_sylow_of_normal S
    have hc (U : Subgroup G) (hSU : (S : Subgroup G) ≤ U) :
        (U.map q).comap q = U := comap_map_eq_self (hk.trans hSU)
    have hs (U : Subgroup G) (hSU : (S : Subgroup G) < U) :
        (S : Subgroup G).map q < U.map q := by
      refine lt_of_le_of_ne (map_mono hSU.le) ?_
      intro he
      have hh := congrArg (comap q) he
      rw [hc _ le_rfl,hc U hSU.le] at hh
      exact hSU.ne hh
    have hp (U : Subgroup G) (hSU : (S : Subgroup G) ≤ U) (hu : U ≠ ⊤) :
        U.map q ≠ ⊤ := by
      intro he
      exact hu (by rw [←hc U hSU,he,comap_top])
    have hd : P.map q ≠ R.map q := by
      intro he
      have hh := congrArg (comap q) he
      rw [hc P hSP.le,hc R hSR.le] at hh
      exact hne hh
    have hh := (model (S.mapSurjective hq) (P.map q) (R.map q)
      (hs P hSP) (hs R hSR) (hp P hSP.le hP) (hp R hSR.le hR) hd).comap_surjective q hq
    change RankTwoParabolics G (((S : Subgroup G).map q).comap q)
      ((P.map q).comap q) ((R.map q).comap q) at hh
    rwa [hc _ le_rfl,hc P hSP.le,hc R hSR.le] at hh
  rcases e with h | h
  · obtain ⟨e⟩ := h
    exact transfer e alternating_six_model
  · obtain ⟨e⟩ := h
    exact transfer e six_model
end Quasithin.I5.RankTwoParabolics
