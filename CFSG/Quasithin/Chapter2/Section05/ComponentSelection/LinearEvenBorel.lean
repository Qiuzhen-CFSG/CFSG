module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.RankTwoBorelSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.LinearEvenSource
public import CFSG.Quasithin.MainConverse.EvenLinearLocal.LinearThreeGeometry.Centralizers
public import Theory.SpecificGroups.PSL3.BorelTwoParabolics

/-!
# The actual binary PSL3 Borel intersection in Section 2.5

The two projective parabolics and Borel are pulled back through the actual
component quotient. A two-group kernel lies in the component Sylow, so the
Borel is its full normalizer; characteristic two lifts through that kernel.
The original empty-Gamma-even source theorem forces the intersection to be
this Borel and produces a Sylow element interchanging the parabolics.

Source: Aschbacher--Smith 2.5.2(2), printed p.551, including binary covers.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G] {M H : Subgroup G}

/-- Literal Borel identification and diagram interchange for an aligned
component quotient with two-group kernel. All two-parabolic inputs are
proved from the actual matrix model. -/
theorem linear_even_aligned_borel_source
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M)
    (D : Subgroup H) (hD : IsComponent H D) (hout : ¬ D.map H.subtype ≤ M)
    (F : Type*) [Field F] [Finite F] {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (f : D →* PSL(3,F)) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hU : ((S : Subgroup H).subgroupOf D).map f = unipotent F) :
    ((M.subgroupOf H).subgroupOf D) = (borel F).comap f ∧
      ∃ s : normalizer (D : Set H), (s : H) ∈ S ∧
        ((pointParabolic F).comap f).map (D.normalizerMonoidHom s).toMonoidHom =
          (lineParabolic F).comap f ∧
        ((lineParabolic F).comap f).map (D.normalizerMonoidHom s).toMonoidHom =
          (pointParabolic F).comap f := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let : f.range.Normal := by rw [f.range_eq_top_of_surjective hf]; infer_instance
  let B := (borel F).comap f
  let P := (pointParabolic F).comap f
  let Q := (lineParabolic F).comap f
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_subnormal D hD.1
  have hkerR : f.ker ≤ (R : Subgroup D) :=
    (le_sSup ⟨inferInstance,hk⟩ : f.ker ≤ pCore 2 D).trans (by
      intro x hx
      obtain ⟨y,hy,he⟩ := pCoreIn_le_sylow D R (mem_map_of_mem D.subtype hx)
      exact (Subtype.ext he : y = x) ▸ hy)
  have hpre : (unipotent F).comap f = (S : Subgroup H).subgroupOf D := by
    rw [← hU, Subgroup.comap_map_eq_self (hR ▸ hkerR)]
  have hB : B = normalizer ((S : Subgroup H).subgroupOf D : Set D) := by
    rw [show B = (borel F).comap f from rfl, ← normalizer_unipotent F hn hF,
      comap_normalizer_eq_of_surjective _ hf, hpre]
  have hBc : centralizer (pCore 2 B : Set B) ≤ pCore 2 B :=
    f.centralizer_pCore_comap_of_normal_range hk _
      (BorelStructure.borel_core_selfCentralizing F hF)
  have hPc : centralizer (pCore 2 P : Set P) ≤ pCore 2 P :=
    f.centralizer_pCore_comap_of_normal_range hk _
      (MainConverse.LinearThreeGeometry.parabolic_characteristicTwo F true)
  have hQc : centralizer (pCore 2 Q : Set Q) ≤ pCore 2 Q :=
    f.centralizer_pCore_comap_of_normal_range hk _
      (MainConverse.LinearThreeGeometry.parabolic_characteristicTwo F false)
  have hP : IsCoatom P := isCoatom_comap_of_surjective hf (projective_parabolics_isCoatom F).1
  have hQ : IsCoatom Q := isCoatom_comap_of_surjective hf (projective_parabolics_isCoatom F).2
  have hPQ : P ≠ Q := fun he => projective_parabolics_ne F ((comap_injective hf) he)
  have hinf : P ⊓ Q = B := by
    change (pointParabolic F).comap f ⊓ (lineParabolic F).comap f = (borel F).comap f
    rw [← comap_inf, projective_parabolics_inf]
  have hsup : P ⊔ Q = ⊤ := by
    have hker : f.ker ≤ P ⊔ Q := ((pointParabolic F).ker_le_comap f).trans le_sup_left
    have he : (P ⊔ Q).map f = ⊤ := by
      rw [Subgroup.map_sup, map_comap_eq_self_of_surjective hf,
        map_comap_eq_self_of_surjective hf, parabolics_sup_eq_top]
    rw [← Subgroup.comap_map_eq_self hker, he, comap_top]
  have hcover : ∀ J : Subgroup D, B ≤ J → J ≠ ⊤ → J ≤ P ∨ J ≤ Q := by
    intro J hBJ hJ
    have hker : f.ker ≤ J := ((borel F).ker_le_comap f).trans hBJ
    have hproper : J.map f ≠ ⊤ := by
      intro he
      apply hJ
      rw [← Subgroup.comap_map_eq_self hker, he, comap_top]
    have hBJ' : borel F ≤ J.map f := by
      have hh := map_mono (f := f) hBJ
      rwa [map_comap_eq_self_of_surjective hf] at hh
    exact (BorelOvergroups.overgroup_borel F (J.map f) hBJ' hproper).imp
      map_le_iff_le_comap.mp map_le_iff_le_comap.mp
  exact rank_two_intersection_eq_borel_source hH hempty S hSM D hD hout B P Q
    hB hBc hPc hQc hP hQ hPQ hinf hsup hcover

/-- Sylow conjugacy aligns the actual quotient, then source 2.5.1 forces
its original component intersection to be the full Borel preimage. -/
theorem exists_linear_even_borel_source
    (hH : H ∈ gammaZero (Chapter1.He G) M)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (S : Sylow 2 H) (hSM : (S : Subgroup H).map H.subtype ≤ M)
    (D : Subgroup H) (hD : IsComponent H D) (hout : ¬ D.map H.subtype ≤ M)
    (F : Type*) [Field F] [Finite F] {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (f₀ : D →* PSL(3,F)) (hf₀ : Function.Surjective f₀) (hk : IsPGroup 2 f₀.ker) :
    ∃ f : D →* PSL(3,F), Function.Surjective f ∧ f.ker = f₀.ker ∧
      ((S : Subgroup H).subgroupOf D).map f = unipotent F ∧
      ((M.subgroupOf H).subgroupOf D) = (borel F).comap f ∧
      ∃ s : normalizer (D : Set H), (s : H) ∈ S ∧
        ((pointParabolic F).comap f).map (D.normalizerMonoidHom s).toMonoidHom =
          (lineParabolic F).comap f ∧
        ((lineParabolic F).comap f).map (D.normalizerMonoidHom s).toMonoidHom =
          (pointParabolic F).comap f := by
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_subnormal D hD.1
  let P := R.mapSurjective (f := f₀) hf₀
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(3,F) P (unipotentSylow F hn hF)
  let f := (MulAut.conj g).toMonoidHom.comp f₀
  have hf : Function.Surjective f := (MulAut.conj g).surjective.comp hf₀
  have hker : f.ker = f₀.ker := MonoidHom.ker_comp_of_injective _ _ (MulAut.conj g).injective
  have hU : ((S : Subgroup H).subgroupOf D).map f = unipotent F := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((R : Subgroup D).map f₀).map (MulAut.conj g).toMonoidHom = unipotent F at hh
    rw [map_map,hR] at hh
    exact hh
  obtain ⟨hB, hs⟩ := linear_even_aligned_borel_source hH hempty S hSM D hD hout
    F hn hF f hf (hker ▸ hk) hU
  exact ⟨f,hf,hker,hU,hB,hs⟩

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
