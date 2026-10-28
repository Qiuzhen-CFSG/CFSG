module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ActionKernel
public import Theory.GroupTheory.PResidual.CoprimeContainment
public import Theory.GroupTheory.PResidual.TwoKernelComparison
public import Theory.GroupTheory.SymmetricThreeTwoCoreResidual

/-!
# The full action kernel and the cubic residual

Clause (c) of 13.4.7 puts the cubic residual of C_X(V₀) inside one of
K₁,K₂. The local kernel equality then puts that residual in O₂(X).
A two-perfect two-group is trivial, so C_X(V₀) has order prime to three.
The two relative normality hypotheses also make it normalize both Kᵢ.

The S₃-over-O₂ markings identify each local two-residual with its
prime-to-three residual. Together with F.6.6, this proves the corresponding
identity in X, without a solvability assumption on X or its action image.
Source: Aschbacher–Smith 13.4.7, printed pp.899–900. The source structural
alternatives and their exclusions are not assumed or proved in this module.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G]

/-- The residual generation in the original join is also generation by its cubic residual. -/
theorem pair_twoResidual_eq_primeToThree {T : Sylow 2 G} {A B : Subgroup G}
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B) :
    (pResidual 2 (A ⊔ B : Subgroup G)).map (A ⊔ B).subtype =
      (primeToResidual 3 (A ⊔ B : Subgroup G)).map (A ⊔ B).subtype := by
  let X := A ⊔ B
  have hg := pair_goldschmidt hTA hTB eA eB hne
  have hr := congrArg (Subgroup.map X.subtype) hg.twoResidual_eq_sup
  rw [Subgroup.map_sup,map_embedded_pResidual,map_embedded_pResidual,
    map_subgroupOf_eq_of_le le_sup_left,map_subgroupOf_eq_of_le le_sup_right] at hr
  apply le_antisymm
  · rw [hr,SymmetricThreeTwoCore.twoResidual_eq_primeToThree eA,
      SymmetricThreeTwoCore.twoResidual_eq_primeToThree eB]
    exact sup_le (embedded_primeToResidual_mono 3 le_sup_left)
      (embedded_primeToResidual_mono 3 le_sup_right)
  · exact map_mono primeToResidual_three_le_twoResidual

omit [Finite G] in
private theorem kernel_le_fixed_centralizer (X Z K : Subgroup G) :
    X ⊓ centralizer (conjugateSpanBy Z X : Set G) ≤
      X ⊓ centralizer ((Z ⊓ centralizer (K : Set G) : Subgroup G) : Set G) :=
  inf_le_inf_left X (centralizer_le (inf_le_left.trans (le_conjugateSpanBy Z X)))

/-- Clause (c)'s literal residual identity removes every cubic element from the action kernel. -/
theorem original_pair_kernel_primeToThree {T : Sylow 2 G} {L V A B : Subgroup G}
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂) :
    Nat.Coprime 3 (Nat.card ((A ⊔ B) ⊓ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G) : Subgroup G)) := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z X
  let C := X ⊓ centralizer (W : Set G)
  obtain ⟨_,hA,hB,_⟩ := original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB
  have hR : (primeToResidual 3 C).map C.subtype ≤ X.pCoreIn 2 := by
    have step (Y : Subgroup G) (hY : Y ⊓ centralizer (W : Set G) = X.pCoreIn 2)
        (hr : let K := (pResidual 2 Y).map Y.subtype
          let F := X ⊓ centralizer ((Z ⊓ centralizer (K : Set G) : Subgroup G) : Set G)
          (primeToResidual 3 F).map F.subtype = K) :
        (primeToResidual 3 C).map C.subtype ≤ X.pCoreIn 2 := by
      have hm := embedded_primeToResidual_mono 3
        (kernel_le_fixed_centralizer X Z ((pResidual 2 Y).map Y.subtype))
      rw [hr] at hm
      rw [←hY]
      exact le_inf (hm.trans (map_subtype_le _))
        ((map_subtype_le _).trans inf_le_right)
    rcases hres with hres | hres
    · exact step A hA hres
    · exact step B hB hres
  apply coprime_card_of_primeToResidual_le_pGroup 3 2 (by decide)
    ((X.pCoreIn 2).subgroupOf C) (isPGroup_pCoreIn 2 X).comap_subtype
  intro c hc
  exact hR (mem_map_of_mem C.subtype hc)

omit [Finite G] in
/-- The normality part of (c) makes the full action kernel normalize each residual. -/
theorem kernel_normalizes_residual (X Z K : Subgroup G)
    (hKX : K ≤ X)
    (hn : (K.subgroupOf (X ⊓ centralizer
      ((Z ⊓ centralizer (K : Set G) : Subgroup G) : Set G))).Normal) :
    X ⊓ centralizer (conjugateSpanBy Z X : Set G) ≤ normalizer (K : Set G) := by
  have hKC : K ≤ X ⊓ centralizer ((Z ⊓ centralizer (K : Set G) : Subgroup G) : Set G) :=
    le_inf hKX (le_centralizer_iff.mpr inf_le_right)
  exact (kernel_le_fixed_centralizer X Z K).trans
    ((normal_subgroupOf_iff_le_normalizer hKC).mp hn)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
