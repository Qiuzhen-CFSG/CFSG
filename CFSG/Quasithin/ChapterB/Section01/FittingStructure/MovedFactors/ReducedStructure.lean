module

public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.Basic

/-!
# The reduced generalized-Fitting step in B.1.10

Suppose G = F(G)KA, A is a two-group, K = [K,A], and K does not
centralize F(G). If K is quasisimple or has order three, then F*(G) = F(G).
Only normality of K inside KA is used; it follows from K = [K,A].

In the quasisimple case set C = C_G(F(G)) and N = F(G)C. The proper
normal subgroup C_K(F(G)) is central in K. More strongly, K ∩ N is
central: otherwise K ≤ N, and perfectness kills its image in the solvable
quotient N/C, contradicting the noncentral action on F(G). Since KA/K
is a two-group, N ∩ KA is solvable. The equality N = F(G)(N ∩ KA)
then makes C solvable, which excludes components outside F(G). In the
cubic case both KA and G are solvable directly.

When O₂(G) = 1, F(G) lies in the odd core. Generalized-Fitting
self-centralization therefore makes every two-subgroup faithful on F(G).
The final theorem supplies the exact minimal-best-offender premise used by
`MovedFactors.conclusion_of_minimal_faithful`; it assumes neither that
premise nor the B.1.9 decomposition.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
B.1.10, printed p.72 (PDF p.83), the paragraph after the first quotient
reduction and the observation (*) preceding it.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.FittingStructure.MovedFactors
variable {G : Type*} [Group G]

private theorem perfect_le_normal_of_le_solvable_sup
    (K F C : Subgroup G) [Group.IsPerfect K] [Group.IsSolvable F] [C.Normal]
    (hle : K ≤ F ⊔ C) : K ≤ C := by
  let q := QuotientGroup.mk' C
  let : Group.IsSolvable (F.map q) :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective F)
  by_contra hn
  apply map_not_le_of_isPerfect_of_isSolvable K q (by simpa [q] using hn) (F.map q)
  simpa [Subgroup.map_sup, q] using map_mono (f := q) hle

private theorem solvable_of_solvable_intersection
    (K T : Subgroup G) [K.Normal] [Group.IsSolvable (G ⧸ K)]
    [Group.IsSolvable (K.subgroupOf T)] : Group.IsSolvable T := by
  let q := (QuotientGroup.mk' K).comp T.subtype
  apply Group.isSolvable_of_ker_le_range (K.subgroupOf T).subtype q
  intro x hx
  exact ⟨⟨x, (QuotientGroup.eq_one_iff x.val).mp hx⟩, rfl⟩

private theorem solvable_normal_of_solvable_intersection_supplement
    (F S N : Subgroup G) [F.Normal] [Group.IsSolvable F]
    (hFN : F ≤ N) (hgen : F ⊔ S = ⊤)
    [Group.IsSolvable (N.subgroupOf S)] : Group.IsSolvable N := by
  let D := (N.subgroupOf S).map S.subtype
  let : Group.IsSolvable D :=
    Group.isSolvable_of_surjective (S.subtype.subgroupMap_surjective (N.subgroupOf S))
  have hN : N = F ⊔ D := by
    apply le_antisymm
    · intro n hn
      have hnG : n ∈ F ⊔ S := by rw [hgen]; trivial
      obtain ⟨f, hf, s, hs, rfl⟩ := mem_sup_of_normal_left.mp hnG
      have hsN : s ∈ N := (N.mul_mem_cancel_left (hFN hf)).mp hn
      exact mul_mem_sup hf (mem_map_of_mem S.subtype
        (show (⟨s, hs⟩ : S) ∈ N.subgroupOf S from hsN))
    · exact sup_le hFN (by rintro _ ⟨s, hs, rfl⟩; exact hs)
  rw [hN]
  exact Group.isSolvable_sup_of_normal_left F D

/-- The source's (*): normality of C_G(F(G)) and noncentrality force its
intersection with a quasisimple K into Z(K). -/
theorem centralizer_subgroupOf_le_center (K : Subgroup G) [IsQuasisimple K]
    (hne : ⁅fittingSubgroup G, K⁆ ≠ ⊥) :
    (centralizer (fittingSubgroup G : Set G)).subgroupOf K ≤ center K := by
  rcases IsQuasisimple.normal_le_center_or_eq_top
      ((centralizer (fittingSubgroup G : Set G)).subgroupOf K) with h | h
  · exact h
  · exact (hne (by rw [commutator_comm]; exact
      commutator_eq_bot_iff_le_centralizer.mpr (subgroupOf_eq_top.mp h))).elim

variable [Finite G]

private theorem solvable_fitting_centralizer
    (K A : Subgroup G) [IsQuasisimple K] (hA : IsPGroup 2 A)
    (hKA : K = ⁅K, A⁆) (hgen : fittingSubgroup G ⊔ (K ⊔ A) = ⊤)
    (hne : ⁅fittingSubgroup G, K⁆ ≠ ⊥) :
    Group.IsSolvable (centralizer (fittingSubgroup G : Set G)) := by
  let F := fittingSubgroup G
  let C := centralizer (F : Set G)
  let N := F ⊔ C
  have hKC : ¬ K ≤ C := by
    intro h
    exact hne (by rw [commutator_comm]; exact commutator_eq_bot_iff_le_centralizer.mpr h)
  have hKN : N.subgroupOf K ≤ center K := by
    rcases IsQuasisimple.normal_le_center_or_eq_top (N.subgroupOf K) with h | h
    · exact h
    · exact (hKC (perfect_le_normal_of_le_solvable_sup K F C
        (subgroupOf_eq_top.mp h))).elim
  let S := K ⊔ A
  let K₀ := K.subgroupOf S
  let A₀ := A.subgroupOf S
  let N₀ := N.subgroupOf S
  have hnorm : A ≤ normalizer K :=
    le_normalizer_iff_commutator_le_left.mpr hKA.symm.le
  let : K₀.Normal := (normal_subgroupOf_iff_le_normalizer
    (show K ≤ S from le_sup_left)).mpr (sup_le K.le_normalizer hnorm)
  have hquot : IsPGroup 2 (S ⧸ K₀) := by
    apply isPGroup_quotient_of_sup_eq_top K₀ A₀ hA.comap_subtype
    rw [← subgroupOf_sup (show K ≤ S from le_sup_left) (show A ≤ S from le_sup_right)]
    exact subgroupOf_self S
  let : Group.IsNilpotent (S ⧸ K₀) := hquot.isNilpotent
  -- The kernel of N ∩ KA → KA/K embeds in the central subgroup K ∩ N.
  let D := K₀.subgroupOf N₀
  let i : D →* K :=
    { toFun := fun x => ⟨x.val.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro x y h
    have he : x.val.val.val = y.val.val.val := congrArg (fun z : K => (z : G)) h
    exact Subtype.ext (Subtype.ext (Subtype.ext he))
  let : Group.IsSolvable (center K) := Group.isSolvable_of_comm (fun x y => mul_comm' x y)
  let j : D →* center K := i.codRestrict _ (fun x => hKN x.val.property)
  let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective
    (f := j) (fun x y h => hi (congrArg Subtype.val h))
  let : Group.IsSolvable N₀ := solvable_of_solvable_intersection K₀ N₀
  let : Group.IsSolvable N :=
    solvable_normal_of_solvable_intersection_supplement F S N le_sup_left hgen
  exact Group.isSolvable_of_isSolvable_injective
    (inclusion_injective (show C ≤ N from le_sup_right))

omit [Finite G] in
private theorem generalizedFitting_eq_of_solvable_centralizer
    [Group.IsSolvable (centralizer (fittingSubgroup G : Set G))] :
    generalizedFitting G = fittingSubgroup G := by
  apply le_antisymm ?_ (fitting_le_generalizedFitting G)
  apply sup_le le_rfl
  apply sSup_le
  intro L hL
  let := hL.2
  rcases hL.normal_dichotomy (fittingSubgroup G) with h | h
  · exact h
  · have hLC := commutator_eq_bot_iff_le_centralizer.mp h
    let : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective
      (inclusion_injective hLC)
    let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
    let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
    exact (Group.IsPerfect.not_isSolvable L inferInstance).elim

private theorem solvable_join_of_cubic
    (K A : Subgroup G) (hK : Nat.card K = 3) (hA : IsPGroup 2 A)
    (hKA : K = ⁅K, A⁆) : Group.IsSolvable (K ⊔ A : Subgroup G) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : IsCyclic K := isCyclic_of_prime_card hK
  let : Group.IsSolvable K := Group.isSolvable_of_comm (fun x y => mul_comm' x y)
  let : Group.IsNilpotent A := hA.isNilpotent
  let S := K ⊔ A
  let K₀ := K.subgroupOf S
  let A₀ := A.subgroupOf S
  have hnorm : A ≤ normalizer K :=
    le_normalizer_iff_commutator_le_left.mpr hKA.symm.le
  let : K₀.Normal := (normal_subgroupOf_iff_le_normalizer
    (show K ≤ S from le_sup_left)).mpr (sup_le K.le_normalizer hnorm)
  let : Group.IsSolvable K₀ := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show K ≤ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show K ≤ S from le_sup_left)).injective
  let : Group.IsSolvable A₀ := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show A ≤ S from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show A ≤ S from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top K₀ A₀
  rw [← subgroupOf_sup (show K ≤ S from le_sup_left) (show A ≤ S from le_sup_right)]
  exact subgroupOf_self S

/-- The group-theoretic reduction in B.1.10, with only relative normality of K. -/
theorem generalizedFitting_eq_fitting_of_reduced
    (K A : Subgroup G) (hK : IsQuasisimple K ∨ Nat.card K = 3)
    (hA : IsPGroup 2 A) (hKA : K = ⁅K, A⁆)
    (hgen : fittingSubgroup G ⊔ (K ⊔ A) = ⊤)
    (hne : ⁅fittingSubgroup G, K⁆ ≠ ⊥) :
    generalizedFitting G = fittingSubgroup G := by
  rcases hK with hK | hK
  · let : IsQuasisimple K := hK
    let : Group.IsSolvable (centralizer (fittingSubgroup G : Set G)) :=
      solvable_fitting_centralizer K A hA hKA hgen hne
    exact generalizedFitting_eq_of_solvable_centralizer
  · let : Group.IsSolvable (K ⊔ A : Subgroup G) := solvable_join_of_cubic K A hK hA hKA
    let : Group.IsSolvable G :=
      Group.isSolvable_of_normal_sup_eq_top (fittingSubgroup G) (K ⊔ A) hgen
    exact generalizedFitting_eq_of_solvable_centralizer

/-- Oddness and generalized-Fitting self-centralization give faithful action
on the Fitting subgroup for every two-subgroup. -/
theorem twoSubgroup_inf_fitting_centralizer_eq_bot
    (hcore : pCore 2 G = ⊥) (hfit : generalizedFitting G = fittingSubgroup G)
    (B : Subgroup G) (hB : IsPGroup 2 B) :
    B ⊓ centralizer (fittingSubgroup G : Set G) = ⊥ := by
  have hc : centralizer (fittingSubgroup G : Set G) ≤ fittingSubgroup G :=
    hfit ▸ centralizer_generalizedFitting_le G
  have hF : fittingSubgroup G ≤ pPrimeCore 2 G :=
    fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore
  obtain ⟨n, hn⟩ := hB.exists_card_eq
  have hcop : Nat.Coprime (Nat.card B) (Nat.card (pPrimeCore 2 G)) := by
    rw [hn]
    exact (pPrimeCore_coprime_card (p := 2) (G := G)).pow_left n
  exact le_bot_iff.mp ((inf_le_inf_left B (hc.trans hF)).trans
    (disjoint_of_coprime_natCard hcop).le_bot)

/-- Every two-subgroup has trivial kernel on F(G) in the reduced B.1.10 case. -/
theorem twoSubgroup_inf_fitting_centralizer_eq_bot_of_reduced
    (hcore : pCore 2 G = ⊥) (K A : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3) (hA : IsPGroup 2 A)
    (hKA : K = ⁅K, A⁆) (hgen : fittingSubgroup G ⊔ (K ⊔ A) = ⊤)
    (hne : ⁅fittingSubgroup G, K⁆ ≠ ⊥) (B : Subgroup G) (hB : IsPGroup 2 B) :
    B ⊓ centralizer (fittingSubgroup G : Set G) = ⊥ :=
  twoSubgroup_inf_fitting_centralizer_eq_bot hcore
    (generalizedFitting_eq_fitting_of_reduced K A hK hA hKA hgen hne) B hB

/-- The precise minimal-offender faithfulness premise consumed by
`MovedFactors.conclusion_of_minimal_faithful`, now proved from the reduced
B.1.10 hypotheses without assuming a representation kernel or decomposition. -/
theorem minimalBestOffender_inf_fitting_centralizer_eq_bot
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hcore : pCore 2 G = ⊥)
    (K A : Subgroup G) (hK : IsQuasisimple K ∨ Nat.card K = 3)
    (hA : Representation.BinaryOffender.IsBestOffender ρ A)
    (hKA : K = ⁅K, A⁆) (hgen : fittingSubgroup G ⊔ (K ⊔ A) = ⊤)
    (hne : ⁅fittingSubgroup G, K⁆ ≠ ⊥)
    (B : Subgroup G) (hB : Representation.BinaryOffender.IsMinimalBestOffender ρ B) :
    B ⊓ centralizer (fittingSubgroup G : Set G) = ⊥ := by
  let : IsElementaryAbelian 2 A := hA.1.2
  let : IsElementaryAbelian 2 B := hB.1.1.2
  exact twoSubgroup_inf_fitting_centralizer_eq_bot_of_reduced hcore K A hK
    (IsElementaryAbelian.isPGroup 2 A) hKA hgen hne B
    (IsElementaryAbelian.isPGroup 2 B)

end CFSG.Quasithin.ChapterB.FittingStructure.MovedFactors

end
