module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DistinguishedGeometrySource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OutsideFusionSource
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugateSpan
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The elementary product in the centralizing-involution exclusion

For a conjugate E of the distinguished Z containing an outside involution a
that centralizes Z, the TI property makes E centralize Z. The two conjugates
are disjoint, so their product V is elementary abelian of order |Z|²=|U|.
If ze lies in R, then e lies in R and centralizes a. The original fixed-group
identity C_R(a)=Z therefore gives V ∩ R=Z. All inputs are the original source
configuration and the actual conjugate containing a.

Source: Aschbacher–Smith, proof of Lemma 2.4.21, printed p.536,
using Lemmas 2.4.14(1), 2.4.17(1) and 2.4.18(1).
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The product ZZᵍ in the centralizing-involution branch is an elementary
group of module order and intersects R in precisely Z. -/
theorem source_centerless_centralizing_elementary_product
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hz : center (d.block.map d.H.subtype) = ⊥)
    (a g : G) (haT : a ∈ T)
    (haR : a ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (ha2 : a^2=1) (haE : a ∈ (distinguishedZ d).conjBy g)
    (haC : a ∈ centralizer (distinguishedZ d : Set G)) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    let Z := distinguishedZ d
    let E := Z.conjBy g
    let V := Z ⊔ E
    IsElementaryAbelian 2 V ∧
      Nat.card V = Nat.card (sourceModule (d.block.map d.H.subtype)) ∧
      V ⊓ R = Z ∧ E ≤ centralizer (Z : Set G) := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let Z := distinguishedZ d
  let E := Z.conjBy g
  let V := Z ⊔ E
  change IsElementaryAbelian 2 V ∧
    Nat.card V = Nat.card (sourceModule (d.block.map d.H.subtype)) ∧
    V ⊓ R = Z ∧ E ≤ centralizer (Z : Set G)
  have hZeq : Z = R ⊓ centralizer (R : Set G) := distinguishedZ_of_centerless d hz
  have hZR : Z ≤ R := hZeq.le.trans inf_le_left
  have hZ := source_distinguished_elementary d hG T hST hsingle hL hM hTM hunique
  let : IsElementaryAbelian 2 Z := hZ.1
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have ha1 : a ≠ 1 := fun he => haR (he ▸ R.one_mem)
  have hTI := source_distinguished_TI d hG T hST hsingle hL hM hTM hunique
  have hEC : E ≤ centralizer (Z : Set G) :=
    hTI.conjugate_le_centralizer_of_point g a haE ha1 haC
  have hEN : E ≤ normalizer (Z : Set G) := hEC.trans (Subgroup.centralizer_le_normalizer _)
  have hdis : Disjoint Z E := by
    rcases hTI.eq_or_disjoint_conjugate g with he | hd
    · have he' : E = Z := he
      exact False.elim (haR (hZR (he' ▸ (show a ∈ E from haE))))
    · exact hd.symm
  have hV : IsElementaryAbelian 2 V := IsElementaryAbelian.sup_of_le_centralizer hEC
  have hcard : Nat.card V = Nat.card (sourceModule (d.block.map d.H.subtype)) := by
    have hU := source_centerless_elementary_pair_card d hG T hST hsingle hL hM hTM hunique hz
    change Nat.card (sourceModule (d.block.map d.H.subtype)) =
      Nat.card (R ⊓ centralizer (R : Set G) : Subgroup G)^2 at hU
    rw [←hZeq] at hU
    rw [hU]
    change Nat.card (Z ⊔ E : Subgroup G) = Nat.card Z^2
    rw [card_sup_eq_mul_of_normalizes_of_disjoint Z E hEN hdis]
    have hEcard : Nat.card E = Nat.card Z := card_map_of_injective (MulAut.conj g).injective
    rw [hEcard,pow_two]
  have haS : a ∉ S := by
    intro haS
    exact haR ((source_distinguished_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hunique) ▸
      (show a ∈ S ⊓ centralizer (Z : Set G) from ⟨haS,haC⟩))
  have haZ : a ∈ centralizer ((R ⊓ centralizer (R : Set G) : Subgroup G) : Set G) := by
    rw [←hZeq]
    exact haC
  have hfixed : R ⊓ centralizer ({a} : Set G) = Z :=
    (source_outside_involution_center_fixed d hG T hST hsingle hL hM hTM hunique
      a haT haS ha2 haZ).1.trans hZeq.symm
  refine ⟨hV,hcard,?_,hEC⟩
  apply le_antisymm
  · rintro w ⟨hwV,hwR⟩
    have hw : w ∈ (Z : Set G)*(E : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left Z E hEN]
      exact hwV
    obtain ⟨z,hzZ,e,heE,rfl⟩ := hw
    have heR : e ∈ R := (R.mul_mem_cancel_left (hZR hzZ)).mp hwR
    have heC : e ∈ centralizer ({a} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (mul_comm (⟨e,heE⟩ : E) ⟨a,haE⟩)
    exact Z.mul_mem hzZ (hfixed ▸ (show e∈R ⊓ centralizer ({a} : Set G) from ⟨heR,heC⟩))
  · exact le_inf le_sup_left hZR
end CFSG.Quasithin.Chapter2.LinearShadows.Single
