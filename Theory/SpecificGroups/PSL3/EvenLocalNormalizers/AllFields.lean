module
public import Theory.SpecificGroups.PSL3.EvenLocalNormalizers
/-!
# Binary PSL₃ local normalizers at every field size

The actual Sylow-conjugacy and explicit root-plane conjugators work whenever
n>0; they include the field of two elements. Combining this with the proved
root centralizer calculation gives characteristic two of every nontrivial
two-subgroup normalizer. The same argument passes through a two-group kernel
contained in the specified radical, retaining its nontrivial projective image.

Source application: Aschbacher–Smith, 2.5.3(4), printed p.553.
The earlier n≥2 public APIs are preserved.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.EvenInnerCentralizers
variable (F : Type*) [Field F]
theorem involution_isConj_root_of_positive [Finite F] {n : ℕ} (hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (t : PSL(3,F)) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    IsConj t (root F) := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, show n ≠ 0 by omega])
  let : CharP F 2 := ringChar.of_eq hc
  obtain ⟨y, hty⟩ :=
    (LinearThree.unipotentSylow F (by omega) hF).exists_isConj_of_orderOf_eq_prime_pow
      (n := 1) (by simpa only [pow_one] using orderOf_eq_prime ht2 ht)
  have hy : (y : PSL(3,F)) ∈ (projective F).range :=
    (LinearThree.projective_range F).ge y.property
  obtain ⟨u,hu⟩ := hy
  obtain ⟨g,hg⟩ := isConj_iff.mp hty
  have hconj : MulAut.conj g t = projective F u := hg.trans hu.symm
  have hu2 : u ^ 2 = 1 := by
    apply projective_injective F
    rw [map_pow, ← hconj, ← map_pow, ht2, map_one, map_one]
  have hun : u ≠ 1 := by
    intro he
    apply ht
    apply (MulAut.conj g).injective
    rw [hconj, he, map_one, map_one]
  have hroot : IsConj (projective F u) (root F) :=
    (projection F).map_isConj (specialLinear_isConj_root F u hun hu2)
  exact hty.trans (hu ▸ hroot)


/-- The characteristic-two normalizer theorem includes the binary field. -/
theorem normalizer_core_selfCentralizing_of_positive [Finite F] {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (R : Subgroup PSL(3,F)) (hp : IsPGroup 2 R) (hne : R ≠ ⊥) :
    Subgroup.centralizer (pCore 2 (normalizer (R : Set PSL(3,F))) :
      Set (normalizer (R : Set PSL(3,F)))) ≤ pCore 2 (normalizer (R : Set PSL(3,F))) := by
  apply Subgroup.normalizer_core_selfCentralizing_of_prime_centralizers ?_ R hp hne
  intro t ht
  obtain ⟨g,hg⟩ := isConj_iff.mp (involution_isConj_root_of_positive F hn hF t
    (by intro he; simp [he] at ht) (ht ▸ pow_orderOf_eq_one t))
  let e := MulAut.conj g
  have he : e t = root F := hg
  let j := (CentralizerSmallKernelTransport.centralizerEquiv e t).trans
    (MulEquiv.subgroupCongr (congrArg (fun v : PSL(3,F) => Subgroup.centralizer ({v} : Set PSL(3,F))) he))
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 j).mpr
    (root_centralizer_core_selfCentralizing F hn hF)
theorem cover_normalizer_core_selfCentralizing_of_positive [Finite F]
    {E : Type*} [Group E] [Finite E] (f : E →* PSL(3,F))
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (R : Subgroup E) (hp : IsPGroup 2 R) (hker : f.ker ≤ R)
    (hne : R.map f ≠ ⊥) :
    Subgroup.centralizer (pCore 2 (normalizer (R : Set E)) :
      Set (normalizer (R : Set E))) ≤ pCore 2 (normalizer (R : Set E)) := by
  have hpre : (R.map f).comap f = R := Subgroup.comap_map_eq_self hker
  have hN : normalizer (R : Set E) = (normalizer (R.map f : Set PSL(3,F))).comap f := by
    rw [comap_normalizer_eq_of_surjective _ hf, hpre]
  let : f.range.Normal := by
    rw [f.range_eq_top_of_surjective hf]
    infer_instance
  rw [hN]
  exact f.centralizer_pCore_comap_of_normal_range hk _
    (normalizer_core_selfCentralizing_of_positive F hn hF (R.map f) (hp.map f) hne)

end Matrix.PSL3.EvenInnerCentralizers
