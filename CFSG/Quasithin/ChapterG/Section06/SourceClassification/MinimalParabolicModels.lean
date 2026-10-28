module
public import CFSG.Quasithin.ChapterG.Section06.Source
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.BinaryLinear.Ambient
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.AlternatingSix.Image
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.AlternatingSeven.Ambient
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# The one-factor G.6 catalogue inside a minimal parabolic

The binary linear groups of dimension at least three have two proper Sylow
parabolics. The same obstruction excludes S6. For S7 and S8, the normal
alternating subgroup supplies the invariant parabolic pair, using A8 = SL4(2)
in the latter case. Thus the original one-factor action is either the binary
plane action of GL2(2) = S3 or the natural binary permutation action of S5.
The surviving actor and module markings are retained unchanged.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, G.6.4,
printed p.346, applied in the proof of 10.2.1, printed p.743.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section06
open BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
variable {G M : Type*} [Group G] [Finite G] [Group M]

private theorem minimal_of_equiv (S : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (e : G ≃* M) : ChapterB.IsMinimalParabolicOver (S.mapSurjective (f := e.toMonoidHom) e.surjective) ⊤ :=
  ChapterB.minimalParabolic_map_of_kernel_le_core S hP e.toMonoidHom e.surjective
    (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact bot_le)

private theorem index_two_sup_sylow (S : Sylow 2 G) (A : Subgroup G) (hi : A.index = 2) :
    A ⊔ (S : Subgroup G) = ⊤ := by
  apply index_eq_one.mp
  have hd : (A ⊔ (S : Subgroup G)).index ∣ 2 := by
    simpa only [hi] using index_dvd_of_le
      (show A ≤ A ⊔ (S : Subgroup G) from le_sup_left)
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
  · exact he
  · have hdS := index_dvd_of_le (show (S : Subgroup G) ≤ A ⊔ (S : Subgroup G) from le_sup_right)
    rw [he] at hdS
    exact (S.not_dvd_index hdS).elim

private theorem not_minimal_linear_three (S : Sylow 2 (LinearGroup 3)) :
    ¬ ChapterB.IsMinimalParabolicOver S ⊤ := by
  let : Finite (LinearGroup 3) := Finite.of_equiv SL(3, ZMod 2) (slEquivLinear 3).toEquiv
  intro hP
  let e := linearThreeEquivProjective
  have h := minimal_of_equiv S hP e
  obtain ⟨P,Q,hP,hQ,hne,hI,-,-,-⟩ := Matrix.PSL3Two.sylow_parabolics (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hSP : (S.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup Matrix.PSL3Two.PSL) ≤ P :=
    hI ▸ inf_le_left
  have hSQ : (S.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup Matrix.PSL3Two.PSL) ≤ Q :=
    hI ▸ inf_le_right
  exact hne ((ChapterB.minimalParabolicMax_unique _ h hP hSP).trans
    (ChapterB.minimalParabolicMax_unique _ h hQ hSQ).symm)

private theorem not_minimal_linear_large {n : ℕ} (hn : n = 4 ∨ n = 5)
    (S : Sylow 2 (LinearGroup n)) : ¬ ChapterB.IsMinimalParabolicOver S ⊤ := by
  let : Finite (LinearGroup n) := Finite.of_equiv SL(n, ZMod 2) (slEquivLinear n).toEquiv
  exact ChapterB.not_minimalParabolic_of_binary_linear_supplement S ⊤ hn
    (topEquiv.trans (slEquivLinear n).symm) (by simp)

private theorem not_minimal_symmetric_seven (S : Sylow 2 (Equiv.Perm (Fin 7))) :
    ¬ ChapterB.IsMinimalParabolicOver S ⊤ :=
  ChapterB.not_minimalParabolic_of_alternatingSeven_supplement S (alternatingGroup (Fin 7))
    (MulEquiv.refl _) (index_two_sup_sylow S _ alternatingGroup.index_eq_two)

private theorem not_minimal_symmetric_eight (S : Sylow 2 (Equiv.Perm (Fin 8))) :
    ¬ ChapterB.IsMinimalParabolicOver S ⊤ :=
  ChapterB.not_minimalParabolic_of_binary_linear_supplement S (alternatingGroup (Fin 8))
    (Or.inl rfl)
    (Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans Atlas.Order20160A8.sl4TwoEquivPSL.symm)
    (index_two_sup_sylow S _ alternatingGroup.index_eq_two)

private theorem minimal_symmetric_parameter (S : Sylow 2 G)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤) {n : ℕ} (hn : 5 ≤ n) (hn' : n ≤ 8)
    (e : G ≃* Equiv.Perm (Fin n)) : n = 5 := by
  interval_cases n
  · rfl
  · exact (ChapterB.not_minimalParabolic_symmetricSix _ (minimal_of_equiv S hP e)).elim
  · exact (not_minimal_symmetric_seven _ (minimal_of_equiv S hP e)).elim
  · exact (not_minimal_symmetric_eight _ (minimal_of_equiv S hP e)).elim

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {a : G}

/-- The one-factor G.6.4 catalogue reduces to the marked binary plane or S5 natural action. -/
theorem factor_model_minimal_parabolic_models {W : Submodule (ZMod 2) V}
    (h : FactorModel ρ ⊤ W) (S : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver S ⊤) :
    HasModelOn ρ ⊤ W (binaryLinearAction 2) ∨
      HasModelOn ρ ⊤ W (BinaryPermutation.naturalRepresentation (Fin 5)) := by
  rcases h with ⟨n,hn,hn',hm⟩ | ⟨n,hn,hn',hm⟩ | ⟨n,hn,hm⟩
  · obtain ⟨e,f,stable,intertwines⟩ := hm
    have hPm := minimal_of_equiv S hP (topEquiv.symm.trans e)
    interval_cases n
    · exact Or.inl ⟨e,f,stable,intertwines⟩
    · exact (not_minimal_linear_three _ hPm).elim
    · exact (not_minimal_linear_large (Or.inl rfl) _ hPm).elim
    · exact (not_minimal_linear_large (Or.inr rfl) _ hPm).elim
  · have he : n = 5 := by
      obtain ⟨e,-,-,-⟩ := hm
      exact minimal_symmetric_parameter S hP hn hn' (topEquiv.symm.trans e)
    subst n
    exact Or.inr hm
  · obtain ⟨e,-,-,-⟩ := hm
    have he : n = 5 := minimal_symmetric_parameter S hP (by omega) (by omega)
      (topEquiv.symm.trans e)
    omega

/-- Original one-factor output, retaining the chosen action and its full module. -/
theorem one_factor_minimal_parabolic_models
    (h : OneFactor ρ a) (S : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver S ⊤) :
    HasModelOn ρ ⊤ ⊤ (binaryLinearAction 2) ∨
      HasModelOn ρ ⊤ ⊤ (BinaryPermutation.naturalRepresentation (Fin 5)) := by
  have hm := factor_model_minimal_parabolic_models h.2.1 S hP
  rwa [h.2.2] at hm

/-- The surviving marked actors are S3 and S5. -/
theorem one_factor_minimal_parabolic_actor
    (h : OneFactor ρ a) (S : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver S ⊤) :
    Nonempty (G ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (G ≃* Equiv.Perm (Fin 5)) := by
  rcases one_factor_minimal_parabolic_models h S hP with ⟨e,-,-,-⟩ | ⟨e,-,-,-⟩
  · exact Or.inl ⟨(topEquiv.symm.trans e).trans linearTwoEquivSymmetricThree⟩
  · exact Or.inr ⟨topEquiv.symm.trans e⟩

end CFSG.Quasithin.ChapterG.Section06
