module
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.StandardAction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FormTransport
public import CFSG.Quasithin.ClassicalModels
public import Theory.PGroupCore
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect-subgroup two-cores in binary unitary degree three

A nontrivial two-subgroup has a unique fixed point in the rank-one action:
a Sylow two-subgroup acts regularly away from that point. Its normalizer
therefore lies in a solvable Borel. A perfect subgroup has trivial two-core,
and every homomorphism from a perfect group kills that group's two-core.
The argument retains the actual Hermitian form and includes the parameter
f = 1. It requires no pushing-up or global component hypotheses.

Source: Aschbacher–Smith F.1.3(1), printed pp.259–260, and the unitary row
of the component inspection in 4.4.11, printed p.621. The structural proof
also occurs inside Chapter C's ordinary-placement argument.
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.Unitary

private theorem normalizer_le_of_regular
    {G Ω : Type*} [Group G] [MulAction G Ω]
    (S : Subgroup G) (α : Ω)
    (hN : normalizer (S : Set G) = MulAction.stabilizer G α)
    (hreg : ∀ a b : Ω, a ≠ α → b ≠ α → ∃! s : S, (s : G) • a = b)
    (P : Subgroup G) (hne : P ≠ ⊥) (hPS : P ≤ S) :
    normalizer (P : Set G) ≤ normalizer (S : Set G) := by
  intro g hg
  rw [hN, MulAction.mem_stabilizer_iff]
  by_contra hmove
  obtain ⟨r,hr⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hc : g⁻¹ * (r : G) * g ∈ P := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer (P : Set G)).inv_mem hg) (r : G)).mp r.property
  have hfix : (g⁻¹ * (r : G) * g) • α = α :=
    MulAction.mem_stabilizer_iff.mp (hN ▸ S.le_normalizer (hPS hc))
  have hfix' : (r : G) • (g • α) = g • α := by
    have hh := congrArg (fun a => g • a) hfix
    simpa only [mul_smul,smul_inv_smul] using hh
  obtain ⟨s,_,hs⟩ := hreg (g • α) (g • α) hmove hmove
  have he : (⟨r,hPS r.property⟩ : S) = 1 :=
    (hs _ hfix').trans (hs 1 (one_smul _ _)).symm
  exact hr (Subtype.ext (congrArg (fun s : S => (s : G)) he))

private theorem standard_two_normalizer_solvable
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    [Finite (ProjectiveSpecialUnitaryMatrixGroup J)]
    {f : ℕ} (hf : 0 < f)
    (hc : Nat.card F = (2 ^ f) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ f))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hp : IsPGroup 2 P) (hne : P ≠ ⊥) :
    Group.IsSolvable (normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  obtain ⟨ρ,α,S,_,_,hsol,_,_,_,hN,hreg,_⟩ :=
    standard_psu_borel_data J f hf hc hconj hJ
  let U := ProjectiveSpecialUnitaryMatrixGroup J
  let Ω := {l : Projectivization F (Fin 3 → F) // l ∈
    {l | ∃ (v : Fin 3 → F) (hv : v ≠ 0), l = Projectivization.mk F v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}}
  let ρ' : U →* Equiv.Perm Ω := ρ
  let : MulAction U Ω := MulAction.compHom Ω ρ'
  obtain ⟨T,hPT⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq U T S
  let e := MulAut.conj g
  have hm : (T : Subgroup U).map e.toMonoidHom = (S : Subgroup U) :=
    congrArg Sylow.toSubgroup hg
  have hN' : normalizer (S : Set U) = MulAction.stabilizer U (α : Ω) := hN
  have hreg' : ∀ a b : Ω, a ≠ α → b ≠ α → ∃! s : S, (s : U) • a = b := hreg
  have hn : normalizer (P.map e.toMonoidHom : Set U) ≤ normalizer (S : Set U) :=
    normalizer_le_of_regular (G := U) (Ω := Ω) (S : Subgroup U) α hN' hreg'
      (P.map e.toMonoidHom)
      (fun h => hne ((map_eq_bot_iff_of_injective P e.injective).mp h))
      ((map_mono hPT).trans_eq hm)
  have hn' : (normalizer (P : Set U)).map e.toMonoidHom ≤ normalizer (S : Set U) := by
    rwa [map_equiv_normalizer_eq]
  let j := (normalizer (P : Set U)).equivMapOfInjective e.toMonoidHom e.injective
  let : Group.IsSolvable (normalizer (S : Set U)) := hsol
  exact Group.isSolvable_of_isSolvable_injective
    (f := (inclusion hn').comp j.toMonoidHom) ((inclusion_injective hn').comp j.injective)

/-- Every nontrivial two-subgroup of a binary unitary-three model has a solvable normalizer. -/
theorem two_normalizer_solvable
    {U : Type*} [Group U] [Finite U] {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSU U 3 (2 ^ f))
    (P : Subgroup U) (hp : IsPGroup 2 P) (hne : P ≠ ⊥) :
    Group.IsSolvable (normalizer (P : Set U)) := by
  obtain ⟨F,_,_,J,hc,hconj,⟨e⟩⟩ := hm
  obtain ⟨C,hC⟩ := FormTransport.exists_standard_basis J f hf hc hconj
  let J₀ := FormTransport.standardForm J
  let a := e.trans (FormTransport.projectiveEquiv J C hC)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J₀) := Finite.of_surjective a a.surjective
  have hn := standard_two_normalizer_solvable J₀ hf hc hconj rfl
    (P.map a.toMonoidHom) (hp.map _) (fun he => hne
      ((map_eq_bot_iff_of_injective P a.injective).mp he))
  let : Group.IsSolvable ((normalizer (P : Set U)).map a.toMonoidHom) := by
    rwa [map_equiv_normalizer_eq]
  let j := (normalizer (P : Set U)).equivMapOfInjective a.toMonoidHom a.injective
  exact Group.isSolvable_of_isSolvable_injective (f := j.toMonoidHom) j.injective

/-- A homomorphism from a perfect group into a binary unitary-three model kills its two-core. -/
theorem perfect_hom_twoCore_le_ker
    {U A : Type*} [Group U] [Finite U] [Group A] [Group.IsPerfect A]
    {f : ℕ} (hf : 0 < f) (hm : ClassicalGroup.IsPSU U 3 (2 ^ f))
    (j : A →* U) : pCore 2 A ≤ j.ker := by
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  have hbot : pCore 2 j.range = ⊥ := by
    by_contra hne
    let P := (pCore 2 j.range).map j.range.subtype
    have hp : IsPGroup 2 P := pCore_isPGroup.map _
    have hP : P ≠ ⊥ := fun he => hne
      ((map_eq_bot_iff_of_injective _ j.range.subtype_injective).mp he)
    let : Group.IsSolvable (normalizer (P : Set U)) := two_normalizer_solvable hf hm P hp hP
    have hnorm : j.range ≤ normalizer (P : Set U) := by
      have hh := (pCore 2 j.range).le_normalizer_map j.range.subtype
      simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
    let : Group.IsSolvable j.range :=
      Group.isSolvable_of_isSolvable_injective (f := inclusion hnorm) (inclusion_injective hnorm)
    let : Nontrivial j.range := (Subgroup.nontrivial_iff_ne_bot _).mpr (by
      intro he
      have : Subsingleton j.range := by rw [he]; infer_instance
      exact hne (Subsingleton.elim _ _))
    exact Group.IsPerfect.not_isSolvable j.range inferInstance
  have him : (pCore 2 A).map j.rangeRestrict ≤ pCore 2 j.range :=
    le_sSup ⟨(inferInstance : (pCore 2 A).Normal).map _ j.rangeRestrict_surjective,
      pCore_isPGroup.map _⟩
  rw [hbot] at him
  have hk := (Subgroup.map_eq_bot_iff _).mp (bot_unique him)
  intro a ha
  exact congrArg Subtype.val (hk ha)

/-- Every perfect subgroup of a binary unitary-three model has trivial two-core. -/
theorem perfect_subgroup_twoCore_eq_bot
    {U : Type*} [Group U] [Finite U] {f : ℕ} (hf : 0 < f)
    (hm : ClassicalGroup.IsPSU U 3 (2 ^ f))
    (P : Subgroup U) [Group.IsPerfect P] : pCore 2 P = ⊥ := by
  have hk := perfect_hom_twoCore_le_ker hf hm P.subtype
  rw [P.subtype.ker_eq_bot P.subtype_injective] at hk
  exact bot_unique hk

end CFSG.Quasithin.ChapterF.Source.Unitary
