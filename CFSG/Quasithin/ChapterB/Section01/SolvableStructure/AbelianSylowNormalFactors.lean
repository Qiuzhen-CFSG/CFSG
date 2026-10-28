module
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.SourceTheorems
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.AbelianSylow
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.SmallAction
public import Theory.GroupTheory.NormalSymmetricThreeMarked
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# Normal solvable FF factors under an abelian Sylow subgroup

An abelian Sylow fixes each factor's nontrivial Sylow intersection, hence
normalizes every factor. With at most two factors, their permutation action
is a two-group action, so the Sylow and two-residual together fix all factors.
A Sylow-normalized two-perfect subgroup of order dividing three times a
power of two, moved by the offender product, is then one factor's cubic
residual and is normal in the full actor.

The original point amalgam in 13.2.12 uses this with its actual reduced
module and the source three-rank bound. This supplies the normality needed
for the solvable F.6 comparison. Source: Aschbacher--Smith B.1.8 and
13.2.12, printed pp.70 and 882.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

theorem factor_normal_of_abelian_sylow (hc : d.count ≤ 2)
    (S : Sylow 2 G) (hS : IsMulCommutative S) (i : Fin d.count) : (d.factor i).Normal := by
  have hSn (t : S) (j : Fin d.count) : d.factorConjugation (t:G) j = j := by
    let : (offenderSubgroup ρ).Normal := offenderSubgroup_normal ρ
    have hs : (d.factor j).IsSubnormal :=
      (d.factor_normal_in_offenderSubgroup j).isSubnormal.trans (d.factor_le_offenderSubgroup j)
        (inferInstance : (offenderSubgroup ρ).Normal).isSubnormal
    obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal (d.factor j) hs
    obtain ⟨a,ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (d.factorSylow_ne_bot j P)
    have hj : (a:G) ∈ d.factor j := d.factorSylow_le j P a.property
    have haS : (a:G) ∈ (S : Subgroup G) := by
      obtain ⟨y,hy,he⟩ := a.property
      rw [hP] at hy
      rw [←he]
      exact hy
    have he : (t:G)*(a:G)*(t:G)⁻¹=(a:G) := by
      have hh := congrArg Subtype.val (hS.is_comm.comm t (⟨a,haS⟩ : S))
      change (t:G)*(a:G)=(a:G)*(t:G) at hh
      rw [hh,mul_inv_cancel_right]
    have hi : (a:G) ∈ d.factor (d.factorConjugation (t:G) j) := by
      rw [←d.factor_map_conj (t:G) j]
      have hh := mem_map_of_mem (MulAut.conj (t:G)).toMonoidHom hj
      change (t:G)*(a:G)*(t:G)⁻¹ ∈ _ at hh
      rwa [he] at hh
    by_contra hne
    exact ha (Subtype.ext (Subgroup.disjoint_def.mp
      (d.factors_independent.pairwiseDisjoint hne) hi hj))
  have hSker : (S : Subgroup G) ≤ d.factorConjugation.ker := by
    intro t ht
    exact Equiv.ext (hSn ⟨t,ht⟩)
  have hp : IsPGroup 2 (Equiv.Perm (Fin d.count)) := by
    have hc' : d.count = 1 ∨ d.count = 2 := by have := d.count_pos; omega
    rcases hc' with he | he
    · apply IsPGroup.of_card (n := 0)
      rw [Nat.card_perm,Nat.card_fin,he]
      rfl
    · apply IsPGroup.of_card (n := 1)
      rw [Nat.card_perm,Nat.card_fin,he]
      rfl
  have hRker : pResidual 2 G ≤ d.factorConjugation.ker := by
    have hh := (isPPerfect_pResidual (G := G) 2).hom_eq_one_of_isPGroup hp
      (d.factorConjugation.comp (pResidual 2 G).subtype)
    intro g hg
    exact DFunLike.congr_fun hh ⟨g,hg⟩
  have htop : d.factorConjugation.ker = ⊤ := top_unique
    ((pResidual_sup_sylow_eq_top S) ▸ sup_le hRker hSker)
  apply normalizer_eq_top_iff.mp
  apply top_unique
  intro g _
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (d.factor i).map (MulAut.conj g).toMonoidHom = d.factor i
  rw [d.factor_map_conj]
  have hh : g ∈ d.factorConjugation.ker := htop.symm ▸ mem_top g
  change d.factorConjugation g = 1 at hh
  rw [hh]
  rfl

theorem cubic_normal_of_abelian_sylow (hc : d.count ≤ 2)
    (S : Sylow 2 G) (hS : IsMulCommutative S) (K : Subgroup G)
    (hp : IsPPerfect 2 K) (hn : (S : Subgroup G) ≤ normalizer (K : Set G))
    (hk : ∃ n, Nat.card K ∣ 3 * 2 ^ n)
    (hm : ¬ offenderSubgroup ρ ≤ centralizer (K : Set G)) : K.Normal := by
  have hex : ∃ i, ¬ d.factor i ≤ centralizer (K : Set G) := by
    by_contra! hh
    apply hm
    rw [←d.iSup_factor]
    exact iSup_le hh
  obtain ⟨i,hi⟩ := hex
  let := d.factor_normal_of_abelian_sylow hc S hS i
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  obtain he | he := NormalSymmetricThreeMarked.eq_residual_or_centralizes_of_card_dvd
    (d.factor i) ((d.factorModel i).trans e) S K hp hn hk
  · rw [he]
    infer_instance
  · exact (hi (le_centralizer_iff.mp he)).elim
end CFSG.Quasithin.ChapterB.SolvableFFFactors
