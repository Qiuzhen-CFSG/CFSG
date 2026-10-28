module
public import Theory.SpecificGroups.BinaryLinear.FirstNodeParabolic

/-!
# The two endpoint minimal parabolics in a binary flag

A Sylow conjugator adjusts the graph automorphism to reverse the original
flag. It transports the first-node S₃ quotient and its large two-residual
to the other endpoint. Both nodes are fixed by every Sylow-preserving
inner automorphism. Together with the Sylow-center centralizer they
generate the whole group, since every minimal parabolic occurs in this
join. This constructs the intrinsic pair used in the inner-action branch
of Aschbacher--Smith 15.1.22(7), printed pp.1099--1100 of refs/quasithin.pdf.
-/

public section
open Subgroup
namespace BinaryLinear.InvariantNodeActions
open OuterCyclic OrderedResidualConjugators

private theorem residual_card_equiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B] (e : A ≃* B) :
    Nat.card (pResidual 2 A) = Nat.card (pResidual 2 B) := by
  rw [←map_pResidual_of_surjective 2 e.toMonoidHom e.surjective,
    card_map_of_injective e.injective]

private theorem node_ne_top {m : ℕ} (hm : 2 ≤ m) (b : Basis m) (i : Fin m) :
    minimalParabolic b i ≠ ⊤ := by
  obtain ⟨j,hji⟩ : ∃ j : Fin m, j ≠ i := by
    let : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr hm
    exact exists_ne i
  intro he
  have hh : cutStabilizer b ∅ ≤ cutStabilizer b {i}ᶜ := by rw [←minimalParabolic,he]; exact le_top
  exact (cutStabilizer_le_iff b ∅ {i}ᶜ).mp hh hji

/-- The two endpoint minimal parabolics have literal S₃ quotients,
large residuals, and generate with the Sylow-center centralizer. -/
theorem exists_endpoint_minimal_pair {m : ℕ} (hm : 3 ≤ m)
    (S : Sylow 2 (LinearGroup (m+1))) :
    ∃ P Q : Subgroup (LinearGroup (m+1)),
      (S : Subgroup _) ≤ P ∧ (S : Subgroup _) ≤ Q ∧ P ≠ ⊤ ∧ Q ≠ ⊤ ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((Q ⧸ pCore 2 Q) ≃* Equiv.Perm (Fin 3)) ∧
      16 ≤ Nat.card (pResidual 2 P) ∧ 16 ≤ Nat.card (pResidual 2 Q) ∧
      ¬ 9 ∣ Nat.card P ∧ ¬ 9 ∣ Nat.card Q ∧
      (∀ a : MulAut (LinearGroup (m+1)), a ∈ MulAut.innerSubgroup _ →
        (S : Subgroup _).map a.toMonoidHom = S →
        P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q) ∧
      centralizer ((center (S : Subgroup (LinearGroup (m+1)))).map
        (S : Subgroup (LinearGroup (m+1))).subtype : Set (LinearGroup (m+1))) ⊔ (P ⊔ Q) = ⊤ := by
  let : Finite (LinearGroup (m+1)) := Finite.of_injective
    (fun g : LinearGroup (m+1) => (g : Space (m+1) → Space (m+1))) DFunLike.coe_injective
  obtain ⟨b,hb⟩ := sylow_eq_cutStabilizer S
  let i : Fin m := ⟨0,by omega⟩
  let P := minimalParabolic b i
  let Q := minimalParabolic b i.rev
  let γ := graphLinear (m+1)
  let S' := S.mapSurjective (f := γ.symm.toMonoidHom) γ.symm.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (LinearGroup (m+1)) S S'
  have hg' : (S : Subgroup _).map (MulAut.conj g).toMonoidHom = S' := by
    exact congrArg (fun U : Sylow 2 (LinearGroup (m+1)) => (U : Subgroup (LinearGroup (m+1)))) hg
  have hfix : (cutStabilizer b Set.univ).map (γ * MulAut.conj g).toMonoidHom =
      cutStabilizer b Set.univ := by
    rw [←hb]
    change (S : Subgroup _).map (γ.toMonoidHom.comp (MulAut.conj g).toMonoidHom) = _
    rw [←map_map,hg']
    change ((S : Subgroup _).map γ.symm.toMonoidHom).map γ.toMonoidHom = _
    ext x
    simp only [mem_map_equiv,MulEquiv.symm_symm,MulEquiv.apply_symm_apply]
  have hpq : P.map (γ * MulAut.conj g).toMonoidHom = Q :=
    graph_inner_reverses_minimalParabolic b g hfix i
  let ep : P ≃* Q := ((γ * MulAut.conj g).subgroupMap P).trans (MulEquiv.subgroupCongr hpq)
  have hPcard : 16 ≤ Nat.card (pResidual 2 P) := by
    have hh := first_node_residual_card_ge_sixteen hm b
    rwa [nodeResidual,card_subtype] at hh
  let eqP := first_node_quotient hm b
  refine ⟨P,Q,?_,?_,node_ne_top (by omega) b i,node_ne_top (by omega) b i.rev,
    ⟨eqP⟩,⟨(QuotientGroup.congr _ _ ep (pCore_map_iso 2 ep)).symm.trans eqP⟩,
    hPcard,?_,node_card_not_nine b i,node_card_not_nine b i.rev,?_,?_⟩
  · rw [hb]
    exact (cutStabilizer_le_iff _ _ _).mpr (Set.subset_univ _)
  · rw [hb]
    exact (cutStabilizer_le_iff _ _ _).mpr (Set.subset_univ _)
  · rwa [←residual_card_equiv ep]
  · rintro a ⟨x,rfl⟩ ha
    rw [hb] at ha
    exact ⟨inner_fixes_minimalParabolic b x ha i,inner_fixes_minimalParabolic b x ha i.rev⟩
  · rw [sylow_center_centralizer_eq_endCuts (by omega) S b hb]
    apply top_unique
    rw [←iSup_minimalParabolic_eq_top (by omega) b]
    apply iSup_le
    intro j
    by_cases hji : j=i
    · subst j
      exact le_sup_left.trans le_sup_right
    by_cases hjr : j=i.rev
    · subst j
      exact le_sup_right.trans le_sup_right
    apply le_trans _ le_sup_left
    apply (cutStabilizer_le_iff b {j}ᶜ _).mpr
    intro k hk he
    have hk' : k.val=0 ∨ k.val=m-1 := hk
    have hj0 : j.val ≠ 0 := fun hh => hji (Fin.ext hh)
    have hjlast : j.val ≠ m-1 := fun hh => hjr (Fin.ext (by simpa [i,Fin.val_rev] using hh))
    subst k
    exact hk'.elim hj0 hjlast
end BinaryLinear.InvariantNodeActions
