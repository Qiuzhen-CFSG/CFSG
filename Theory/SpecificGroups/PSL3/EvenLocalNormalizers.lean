module
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.MarkedInvariants
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.InvolutionConjugacy
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.BorelStructure
public import Theory.GroupTheory.LocalCoreFromPrimeCentralizers
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Characteristic two of every binary PSL3 local normalizer

The highest-root centralizer lies in the Borel and its two-core is the
full unitriangular Sylow subgroup. The Borel centralizer calculation then
makes the root centralizer characteristic two. Involution conjugacy gives
this for all involution centralizers; the prime-centralizer criterion
finally covers every nonidentity two-subgroup normalizer.

Source application: Aschbacher--Smith 2.5.3(4), printed p.553, the PSL3
branch of 2.5.2(2). No ambient source marking or local conclusion is assumed.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.EvenInnerCentralizers
variable (F : Type*) [Field F] [Finite F]

/-- The actual highest-root centralizer has self-centralizing two-core. -/
theorem root_centralizer_core_selfCentralizing {n : ℕ}
    (hn : 0 < n) (hF : Nat.card F = 2 ^ n) :
    Subgroup.centralizer (pCore 2 (centralizer F) : Set (centralizer F)) ≤
      pCore 2 (centralizer F) := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, show n ≠ 0 by omega])
  let : CharP F 2 := ringChar.of_eq hc
  rw [MarkedInvariants.twoCore_eq_unipotent F hF hn]
  intro x hx
  have hxB : (x : PSL(3,F)) ∈ LinearThree.borel F := by
    obtain ⟨g, hg, he⟩ := (centralizer_map F).ge x.property
    apply he ▸ mem_map_of_mem (projection F) ?_
    obtain ⟨h10,h20,h21,_⟩ := (mem_centralizerSL_iff F g).mp hg
    exact (LinearThree.mem_borelSL_iff F g).mpr ⟨h10,h20,h21⟩
  have hxC : (x : PSL(3,F)) ∈ Subgroup.centralizer (LinearThree.unipotent F : Set PSL(3,F)) := by
    intro y hy
    obtain ⟨u, rfl⟩ := (LinearThree.projective_range F).ge hy
    exact congrArg Subtype.val (hx (unipotentInCentralizer F u) ⟨u,rfl⟩)
  have hxU := LinearThree.BorelStructure.borel_inf_centralizer_unipotent_le F ⟨hxB,hxC⟩
  obtain ⟨u, hu⟩ := (LinearThree.projective_range F).ge hxU
  exact ⟨u, Subtype.ext hu⟩

/-- Every involution centralizer has characteristic two. -/
theorem involution_centralizer_core_selfCentralizing {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (t : PSL(3,F)) (ht : orderOf t = 2) :
    Subgroup.centralizer (pCore 2 (Subgroup.centralizer ({t} : Set PSL(3,F))) :
      Set (Subgroup.centralizer ({t} : Set PSL(3,F)))) ≤
      pCore 2 (Subgroup.centralizer ({t} : Set PSL(3,F))) := by
  obtain ⟨g,hg⟩ := exists_conjugator_root F hn hF t
    (by intro he; simp [he] at ht) (ht ▸ pow_orderOf_eq_one t)
  let e := MulAut.conj g
  have he : e t = root F := hg
  let j := (CentralizerSmallKernelTransport.centralizerEquiv e t).trans
    (MulEquiv.subgroupCongr (congrArg (fun v : PSL(3,F) => Subgroup.centralizer ({v} : Set PSL(3,F))) he))
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 j).mpr
    (root_centralizer_core_selfCentralizing F (by omega) hF)

/-- All nontrivial two-subgroup normalizers have characteristic two. -/
theorem normalizer_core_selfCentralizing {n : ℕ}
    (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (R : Subgroup PSL(3,F)) (hp : IsPGroup 2 R) (hne : R ≠ ⊥) :
    Subgroup.centralizer (pCore 2 (normalizer (R : Set PSL(3,F))) :
      Set (normalizer (R : Set PSL(3,F)))) ≤ pCore 2 (normalizer (R : Set PSL(3,F))) :=
  Subgroup.normalizer_core_selfCentralizing_of_prime_centralizers
    (involution_centralizer_core_selfCentralizing F hn hF) R hp hne

/-- The same conclusion lifts through a two-group kernel when the actual
radical contains that kernel and has nontrivial projective image. Central
radicals are deliberately excluded by the image hypothesis. -/
theorem cover_normalizer_core_selfCentralizing
    {E : Type*} [Group E] [Finite E] (f : E →* PSL(3,F))
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
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
    (normalizer_core_selfCentralizing F hn hF (R.map f) (hp.map f) hne)

end Matrix.PSL3.EvenInnerCentralizers
