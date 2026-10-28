module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DihedralEight.PrimeExtension
public import Theory.GroupTheory.SplitDihedralNotDihedral
public import GorensteinWalter.PGL2DihedralSylow
public import GorensteinWalter.PSL2DihedralSylow
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable

/-!
# Prime PSL2 components are excluded in the split-sixteen branch

If the prime PSL2 component is the whole ambient group, its Sylow is
dihedral. If proper, faithful conjugation identifies the ambient group
with the actual PGL2, which also has dihedral Sylow. Both contradict the
original C2 times D8 Sylow, with no local-recognition premise.

Source: Aschbacher--Smith F.6.18(8)--(9), printed p.310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G : Type*} [Group G] [Finite G]

theorem not_odd_psl_ambient_of_split_sixteen
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    {q : ℕ} (hq : GorensteinWalter.IsOddPrimePower q)
    (hm : ClassicalGroup.IsPSL G 2 q) : False := by
  obtain ⟨F, _, _, hF, ⟨j⟩⟩ := hm
  let S := T.mapSurjective (f := j.toMonoidHom) j.surjective
  let a : T ≃* S := j.subgroupMap (T : Subgroup G)
  obtain ⟨m, _, ⟨b⟩⟩ := GorensteinWalter.psl2_odd_hasDihedralSylowTwo_model F (hF ▸ hq) S
  exact split_sixteen_not_dihedral _ (eT.symm.trans (a.trans b))

theorem not_odd_pgl_ambient_of_split_sixteen
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    {F : Type*} [Field F] [Finite F]
    (hq : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (j : G ≃* GorensteinWalter.PGL2 F) : False := by
  let S := T.mapSurjective (f := j.toMonoidHom) j.surjective
  let a : T ≃* S := j.subgroupMap (T : Subgroup G)
  obtain ⟨m, _, ⟨b⟩⟩ := GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model F hq S
  exact split_sixteen_not_dihedral _ (eT.symm.trans (a.trans b))

/-- The actual generalized Fitting subgroup cannot be prime-field PSL2. -/
theorem not_prime_psl_component_of_split_sixteen
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) [K.Normal] (hF : generalizedFitting G = K)
    (hK : IsComponent G K) {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hm : ClassicalGroup.IsPSL K 2 p) : False := by
  by_cases htop : K = ⊤
  · let j : G ≃* K := topEquiv.symm.trans (MulEquiv.subgroupCongr htop).symm
    exact not_odd_psl_ambient_of_split_sixteen T eT
      ⟨p, 1, Fact.out, hp, by decide, by simp⟩ (hm.of_mulEquiv j)
  · let : IsQuasisimple K := hK.2
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    have hlarge : 3 < p := by
      obtain ⟨F, _, _, hF, ⟨j⟩⟩ := hm
      let : Group.IsPerfect PSL(2,F) :=
        Group.IsPerfect.ofSurjective (f := j.toMonoidHom) j.surjective
      let : Nontrivial PSL(2,F) := j.symm.surjective.nontrivial
      have hc := Matrix.ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
        (hF ▸ hp) (Group.IsPerfect.not_isSolvable PSL(2,F))
      simpa [hF] using hc
    obtain ⟨j⟩ := pgl_prime_of_proper_psl_generalizedFitting K hF htop hlarge hm
    exact not_odd_pgl_ambient_of_split_sixteen T eT
      ⟨p, 1, Fact.out, hp, by decide, by simp⟩ j

end CFSG.Quasithin.ChapterF.SourceAssembly
