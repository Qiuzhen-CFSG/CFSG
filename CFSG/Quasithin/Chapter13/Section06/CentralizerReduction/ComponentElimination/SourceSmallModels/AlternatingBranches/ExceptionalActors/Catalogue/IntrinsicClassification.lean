module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.BlockCandidates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors.Catalogue.PlaneMarking

/-!
# Intrinsic exceptional A₇ actor classification

An arbitrary permitted actor is transported through the actual permutation
relabeling supplied by the plane marking. The transported subgroup satisfies
the literal block hypotheses, so the four-candidate exhaustion applies. The
full plane commutator excludes whichever diagonal candidate acts trivially;
this leaves exactly the three source actors, with the active diagonal selected
by the given representation and plane.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 13.6.22, printed p.932.
-/

@[expose] public section
open Subgroup Equiv
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
open Catalogue Catalogue.PlaneMarking
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A7 W} {P : Submodule (ZMod 2) W}
  {S : Sylow 2 A7} {D : Subgroup A7}

private theorem quotient_card_map_equiv (e : MulAut A7) (C : Subgroup A7)
    (h : Nat.card (C ⧸ pCore 2 C) = 3) :
    Nat.card (C.map e.toMonoidHom ⧸ pCore 2 (C.map e.toMonoidHom)) = 3 := by
  let eC := C.equivMapOfInjective e.toMonoidHom e.injective
  exact (Nat.card_congr (QuotientGroup.congr _ _ eC (pCore_map_iso 2 eC)).toEquiv).symm.trans h

private theorem normalized_comap (e : MulAut A7)
    (hnorm : (S : Subgroup A7) ≤ normalizer (D : Set A7)) :
    let S0 : Sylow 2 A7 := S.mapSurjective (f := e.symm.toMonoidHom)
      (by intro z; exact ⟨e z, by simp⟩)
    (S0 : Subgroup A7) ≤ normalizer (D.comap e.toMonoidHom : Set A7) := by
  have he_surj : Function.Surjective e.symm.toMonoidHom := by
    intro z
    exact ⟨e z, by simp⟩
  let S0 : Sylow 2 A7 := S.mapSurjective (f := e.symm.toMonoidHom) he_surj
  dsimp only
  intro x hx
  rw [mem_normalizer_iff]
  intro y
  have hSmap : (S0 : Subgroup A7).map e.toMonoidHom = S := by
    rw [Sylow.coe_mapSurjective he_surj, Subgroup.map_map]
    ext z
    simp
  have hx' : e.toMonoidHom x ∈ (S : Subgroup A7) := by
    rw [← hSmap]
    exact ⟨x, hx, rfl⟩
  have hn := (mem_normalizer_iff.mp (hnorm hx') (e.toMonoidHom y))
  constructor
  · intro hy
    apply Subgroup.mem_comap.mpr
    have hcy := hn.mp (Subgroup.mem_comap.mp hy)
    simpa only [map_mul, map_inv] using hcy
  · intro hy
    apply Subgroup.mem_comap.mpr
    apply hn.mpr
    have hcy : (e.toMonoidHom x) * (e.toMonoidHom y) *
        (e.toMonoidHom x)⁻¹ ∈ D := by
      simpa only [map_mul, map_inv] using (Subgroup.mem_comap.mp hy)
    exact hcy

private theorem mapped_candidate_properties (e : MulAut A7)
    (C : Subgroup A7)
    (hc : C ≤ blockStabilizer)
    (hn : blockStabilizer ≤ normalizer (C : Set A7))
    (hp : IsPPerfect 2 C) (hq : Nat.card (C ⧸ pCore 2 C) = 3) :
    C.map e.toMonoidHom ≤ blockStabilizer.map e.toMonoidHom ∧
      blockStabilizer.map e.toMonoidHom ≤
        normalizer (C.map e.toMonoidHom : Set A7) ∧
      IsPPerfect 2 (C.map e.toMonoidHom) ∧
      Nat.card (C.map e.toMonoidHom ⧸ pCore 2 (C.map e.toMonoidHom)) = 3 := by
  refine ⟨map_mono hc, ?_, ?_, quotient_card_map_equiv e C hq⟩
  · rw [← map_equiv_normalizer_eq C e]
    exact map_mono hn
  · let eC : C ≃* C.map e.toMonoidHom :=
      C.equivMapOfInjective e.toMonoidHom e.injective
    exact hp.of_surjective eC.toMonoidHom eC.surjective

/-- The four group-theoretic candidates in any fixed permutation marking. -/
theorem permittedActor_four_candidates_in_marking
    (h : PermittedActor ρ P S D) (g : Equiv.Perm (Fin 7))
    (hstab : subspaceStabilizer ρ P = blockStabilizer.map (relabelling g).toMonoidHom) :
    D = cyclicActor.map (relabelling g).toMonoidHom ∨
    D = naturalActor.map (relabelling g).toMonoidHom ∨
    D = diagonalPlus.map (relabelling g).toMonoidHom ∨
    D = diagonalMinus.map (relabelling g).toMonoidHom := by
  let e : MulAut A7 := relabelling g
  let he_surj : Function.Surjective e.symm.toMonoidHom := by
    intro z
    exact ⟨e z, by simp⟩
  let D0 : Subgroup A7 := D.comap e.toMonoidHom
  have hS0 : (S.mapSurjective (f := e.symm.toMonoidHom) he_surj : Subgroup A7) ≤ blockStabilizer := by
    intro x hx
    rw [Sylow.coe_mapSurjective he_surj] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hxS : e.toMonoidHom x ∈ (S : Subgroup A7) := by
      rw [← hxy]
      rw [show e.toMonoidHom (e.symm.toMonoidHom y) = y by
        simpa only [MulEquiv.coe_toMonoidHom] using e.apply_symm_apply y]
      exact hy
    have hxstab := h.sylow_stabilizes hxS
    rw [hstab] at hxstab
    obtain ⟨b, hb, heq⟩ := hxstab
    have heq' : e.toMonoidHom b = e.toMonoidHom x := by
      simpa [e] using heq
    have hbx : b = x := e.injective heq'
    simpa [hbx] using hb
  have hD0 : D0 ≤ blockStabilizer := by
    intro x hx
    have hxD : e.toMonoidHom x ∈ D := Subgroup.mem_comap.mp hx
    have hxstab := h.stabilizes hxD
    rw [hstab] at hxstab
    obtain ⟨b, hb, heq⟩ := hxstab
    have heq' : e.toMonoidHom b = e.toMonoidHom x := by
      simpa [e] using heq
    have hbx : b = x := e.injective heq'
    simpa [hbx] using hb
  have hnorm0 : (S.mapSurjective (f := e.symm.toMonoidHom) he_surj : Subgroup A7) ≤
      normalizer (D0 : Set A7) := by
    exact normalized_comap e h.normalized
  have hp0 : IsPPerfect 2 D0 := by
    let eD : D0 ≃* D :=
      (D0.equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective D))
    exact h.twoPerfect.of_surjective eD.symm.toMonoidHom eD.symm.surjective
  have hq0 : Nat.card (D0 ⧸ pCore 2 D0) = 3 := by
    let eD : D0 ≃* D :=
      (D0.equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self_of_surjective e.surjective D))
    exact (Nat.card_congr (QuotientGroup.congr _ _ eD (pCore_map_iso 2 eD)).toEquiv).trans
      h.quotient_card
  have hcands := four_candidates
    (S.mapSurjective (f := e.symm.toMonoidHom) he_surj)
    hS0 D0 hD0 hnorm0 hp0 hq0
  have hmapD : D0.map e.toMonoidHom = D :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective D
  have heq (C : Subgroup A7) (hC : D0 = C) : D = C.map e.toMonoidHom := by
    rw [← hmapD, hC]
  rcases hcands with hC | hC | hC | hC
  · exact Or.inl (heq _ hC)
  · exact Or.inr (Or.inl (heq _ hC))
  · exact Or.inr (Or.inr (Or.inl (heq _ hC)))
  · exact Or.inr (Or.inr (Or.inr (heq _ hC)))

/-- Every marked candidate with full plane commutator satisfies the intrinsic
contract, with normalization by the specified Sylow. -/
theorem permittedActor_of_mapped_candidate
    (g : Equiv.Perm (Fin 7))
    (hstab : subspaceStabilizer ρ P = blockStabilizer.map (relabelling g).toMonoidHom)
    (hS : (S : Subgroup A7) ≤ subspaceStabilizer ρ P)
    (C : Subgroup A7)
    (hC : C = cyclicActor ∨ C = naturalActor ∨ C = diagonalPlus ∨ C = diagonalMinus)
    (hcomm : subspaceCommutator ρ P (C.map (relabelling g).toMonoidHom) = P) :
    PermittedActor ρ P S (C.map (relabelling g).toMonoidHom) := by
  obtain ⟨hc, hn, hp, hq⟩ := candidate_properties C hC
  obtain ⟨hc', hn', hp', hq'⟩ := mapped_candidate_properties (relabelling g) C hc hn hp hq
  exact ⟨hS, hstab.symm ▸ hc', (hstab ▸ hS).trans hn', hp', hq', hcomm⟩

namespace Catalogue

/-- The three literal actors in one marking. The Boolean records which diagonal
has full commutator on the given plane; it is selected by `exists_actor_catalogue`. -/
def markedActors (g : Equiv.Perm (Fin 7)) (positive : Bool) (i : Fin 3) : Subgroup A7 :=
  (![cyclicActor, naturalActor, if positive then diagonalPlus else diagonalMinus] i).map
    (relabelling g).toMonoidHom

theorem markedActors_injective (g : Equiv.Perm (Fin 7)) (positive : Bool) :
    Function.Injective (markedActors g positive) := by
  obtain ⟨hcn, hcp, hcm, hnp, hnm, hpm⟩ := candidates_pairwise_distinct
  intro i j hij
  have he := Subgroup.map_injective (relabelling g).injective hij
  cases positive <;> fin_cases i <;> fin_cases j <;>
    simp_all [markedActors, Ne.symm]

/-- A single marking classifies all permitted actors. The unselected diagonal
fixes the plane pointwise, and every one of the three selected subgroups is
permitted. The marking is constructed from the representation and plane. -/
theorem exists_actor_catalogue
    (ρ : Representation (ZMod 2) A7 W) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W = 4)
    (P : Submodule (ZMod 2) W) (hP : Module.finrank (ZMod 2) P = 2)
    (S : Sylow 2 A7) (hS : (S : Subgroup A7) ≤ subspaceStabilizer ρ P) :
    ∃ (g : Equiv.Perm (Fin 7)) (positive : Bool),
      subspaceStabilizer ρ P = blockStabilizer.map (relabelling g).toMonoidHom ∧
      subspaceCommutator ρ P
        ((if positive then diagonalMinus else diagonalPlus).map (relabelling g).toMonoidHom) = ⊥ ∧
      Function.Injective (markedActors g positive) ∧
      ∀ D : Subgroup A7, PermittedActor ρ P S D ↔ ∃ i : Fin 3, D = markedActors g positive i := by
  obtain ⟨g, hstab, hcyc, hnat, hdiag⟩ :=
    exists_marked_plane ρ hρ hdim P hP S hS
  have hPne : P ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hP
    omega
  have construct (C : Subgroup A7)
      (hc : C = cyclicActor ∨ C = naturalActor ∨ C = diagonalPlus ∨ C = diagonalMinus)
      (hcomm : subspaceCommutator ρ P (C.map (relabelling g).toMonoidHom) = P) :
      PermittedActor ρ P S (C.map (relabelling g).toMonoidHom) :=
    permittedActor_of_mapped_candidate g hstab hS C hc hcomm
  have cyc := construct cyclicActor (Or.inl rfl) hcyc
  have nat := construct naturalActor (Or.inr (Or.inl rfl)) hnat
  have exclude (D I : Subgroup A7) (h : PermittedActor ρ P S D)
      (hi : subspaceCommutator ρ P I = ⊥) : D ≠ I := by
    intro he
    exact hPne (h.commutator_eq.symm.trans (he ▸ hi))
  rcases hdiag with ⟨hp, hm⟩ | ⟨hm, hp⟩
  · refine ⟨g, true, hstab, hm, markedActors_injective g true, ?_⟩
    intro D
    constructor
    · intro h
      rcases permittedActor_four_candidates_in_marking h g hstab with hc | hn | hd | hi
      · exact ⟨0, hc⟩
      · exact ⟨1, hn⟩
      · exact ⟨2, hd⟩
      · exact (exclude D _ h hm hi).elim
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact cyc
      · exact nat
      · exact construct diagonalPlus (Or.inr (Or.inr (Or.inl rfl))) hp
  · refine ⟨g, false, hstab, hp, markedActors_injective g false, ?_⟩
    intro D
    constructor
    · intro h
      rcases permittedActor_four_candidates_in_marking h g hstab with hc | hn | hi | hd
      · exact ⟨0, hc⟩
      · exact ⟨1, hn⟩
      · exact (exclude D _ h hp hi).elim
      · exact ⟨2, hd⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact cyc
      · exact nat
      · exact construct diagonalMinus (Or.inr (Or.inr (Or.inr rfl))) hm

end Catalogue

/-- Every permitted actor is a cyclic, natural, or active diagonal subgroup
in a literal permutation marking. -/
theorem permittedActor_three_candidates
    (h : PermittedActor ρ P S D)
    (hρ : Function.Injective ρ) (hdim : Module.finrank (ZMod 2) W = 4)
    (hP : Module.finrank (ZMod 2) P = 2) :
    ∃ g : Equiv.Perm (Fin 7),
      D = cyclicActor.map (relabelling g).toMonoidHom ∨
      D = naturalActor.map (relabelling g).toMonoidHom ∨
      (D = diagonalPlus.map (relabelling g).toMonoidHom ∧
        subspaceCommutator ρ P (diagonalPlus.map (relabelling g).toMonoidHom) = P) ∨
      (D = diagonalMinus.map (relabelling g).toMonoidHom ∧
        subspaceCommutator ρ P (diagonalMinus.map (relabelling g).toMonoidHom) = P) := by
  obtain ⟨g, positive, _, _, _, hc⟩ :=
    exists_actor_catalogue ρ hρ hdim P hP S h.sylow_stabilizes
  obtain ⟨i, hi⟩ := (hc D).mp h
  refine ⟨g, ?_⟩
  fin_cases i
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · cases positive
    · exact Or.inr (Or.inr (Or.inr ⟨hi, by
      have hc := h.commutator_eq
      rw [hi] at hc
      simpa [Catalogue.markedActors] using hc⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hi, by
      have hc := h.commutator_eq
      rw [hi] at hc
      simpa [Catalogue.markedActors] using hc⟩))

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.ExceptionalActors
