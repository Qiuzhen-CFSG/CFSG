module
public import Theory.GroupTheory.SylowPairSolvableGeneration
public import Theory.GroupTheory.NormalizerQuotientInner
public import Theory.GroupTheory.SolvableResidual.TwoSupplement
public import Theory.GroupTheory.SolvableSylowControl.PrimeKernel
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer
public import Theory.GroupTheory.SylowNormalizerCentralQuotient
public import Mathlib.GroupTheory.IndexNormal

/-!
# Two-perfect actors on marked Sylow quotients

A two-perfect group fixes every orbit of size at most two. Solvable Sylow
control aligns an ambient actor with the original Sylow in a two-core
quotient. Invariance of a perfect subgroup in that quotient lifts whenever
the two-core normalizes it: the subgroup is the solvable residual of its
join with the core. Neither ambient normality of the subgroup nor a trivial
two-core is required. Central-cover transport also preserves solvable Sylow
control and recovers perfect subgroups from their projective images.

These three steps are used together in the rank-two Borel-normalization
argument of Aschbacher–Smith 10.2.3, printed p.746.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory

/-- A two-perfect group fixes any point whose orbit has at most two members. -/
theorem twoPerfect_fixes_pair {A X : Type*} [Group A] [Finite A] [MulAction A X]
    (hA : IsPPerfect 2 A) (x y : X)
    (hpair : ∀ a : A, a • x = x ∨ a • x = y) : ∀ a : A, a • x = x := by
  have horbit : MulAction.orbit A x ⊆ ({x,y} : Set X) := by
    rintro z ⟨a,rfl⟩
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hpair a
  have hi : (MulAction.stabilizer A x).index ≤ 2 := by
    rw [MulAction.index_stabilizer]
    exact (Set.ncard_le_ncard horbit).trans (by simpa using Set.ncard_insert_le x {y})
  have hp := (MulAction.stabilizer A x).index_ne_zero_of_finite
  have ht : MulAction.stabilizer A x = ⊤ := by
    have hc : (MulAction.stabilizer A x).index = 1 ∨
        (MulAction.stabilizer A x).index = 2 := by omega
    rcases hc with hc | hc
    · exact index_eq_one.mp hc
    · let := (MulAction.stabilizer A x).normal_of_index_eq_two hc
      apply hA _ inferInstance
      apply IsPGroup.of_card (n := 1)
      simpa only [←index_eq_card,pow_one] using hc
  intro a
  exact show a ∈ MulAction.stabilizer A x from ht ▸ mem_top a

end Theory.GroupTheory

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A quotient-invariant perfect subgroup lifts when the two-core normalizes it. -/
theorem normalizes_perfect_of_core_quotient_invariant
    (I K A : Subgroup G) [Group.IsPerfect K]
    (hKI : K ≤ I) (hAI : A ≤ normalizer (I : Set G))
    (hcore : I.pCoreIn 2 ≤ normalizer (K : Set G))
    (hinv : ∀ a : A, ((K.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))).map
      (normalizerQuotientAction I (pCore 2 I) (inclusion hAI a)).toMonoidHom =
      (K.subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) :
    A ≤ normalizer (K : Set G) := by
  let Q := I.pCoreIn 2
  let P := K ⊔ Q
  let q := QuotientGroup.mk' (pCore 2 I)
  have hKP : K ≤ P := le_sup_left
  let : (K.subgroupOf P).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hcore)
  let : Group.IsPerfect (K.subgroupOf P) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKP).symm.toMonoidHom)
    (subgroupOfEquivOfLe hKP).symm.surjective
  have hr : (solvableResidual P).map P.subtype = K := by
    rw [(residuals_of_perfect_normal_sup_twoGroup (K.subgroupOf P) (Q.subgroupOf P)
      (isPGroup_pCoreIn 2 I).comap_subtype (codisjoint_subgroupOf_sup K Q).eq_top).2,
      map_subgroupOf_eq_of_le hKP]
  let a := (normalizerQuotientAction I (pCore 2 I)).comp (inclusion hAI)
  have heq (g : A) (i : I) :
      q (I.normalizerMonoidHom (inclusion hAI g) i) = a g (q i) := by
    simp only [a,q,normalizerQuotientAction,MonoidHom.comp_apply,quotientAut_apply_mk]
  have hl : (((K.subgroupOf I).map q).comap q).map I.subtype = P := by
    rw [comap_map_eq,QuotientGroup.ker_mk',Subgroup.map_sup,map_subgroupOf_eq_of_le hKI]
    rfl
  have hn : A ≤ normalizer (P : Set G) := by
    apply le_normalizer_iff.mpr
    intro g hg x hx
    rw [←hl] at hx ⊢
    obtain ⟨i,hi,rfl⟩ := hx
    refine ⟨I.normalizerMonoidHom (inclusion hAI ⟨g,hg⟩) i,?_,rfl⟩
    change q (I.normalizerMonoidHom (inclusion hAI ⟨g,hg⟩) i) ∈ (K.subgroupOf I).map q
    rw [heq]
    exact hinv ⟨g,hg⟩ ▸ mem_map_of_mem (a ⟨g,hg⟩).toMonoidHom hi
  have hh := hn.trans (normalizer_le_normalizer_characteristic_image P (solvableResidual P))
  rwa [hr] at hh
end Theory.GroupTheory

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A solvable actor containing the marked Sylow fixes that Sylow in the
actual two-core quotient whenever the quotient has solvable Sylow control. -/
theorem core_quotient_sylow_invariant
    (I A P : Subgroup G) (hAP : A ≤ P) [Group.IsSolvable P]
    (hPI : P ≤ normalizer (I : Set G)) (S : Sylow 2 I)
    (hSP : (S : Subgroup I).map I.subtype ≤ P)
    (hcontrol : SolvableSylowControl 2 (I ⧸ pCore 2 I)) :
    ∀ a : A, ((S : Subgroup I).map (QuotientGroup.mk' (pCore 2 I))).map
      (normalizerQuotientAction I (pCore 2 I) (inclusion (hAP.trans hPI) a)).toMonoidHom =
      (S : Subgroup I).map (QuotientGroup.mk' (pCore 2 I)) := by
  let q := QuotientGroup.mk' (pCore 2 I)
  have hk : IsPGroup 2 q.ker := by
    rw [show q.ker = pCore 2 I from QuotientGroup.ker_mk' _]
    exact pCore_isPGroup
  have hI := SolvableSylowControl.of_surjective_pKernel q
    (QuotientGroup.mk'_surjective _) hk hcontrol
  have hn := hI.normalizes_sylow I P S hPI hSP
  intro a
  let g := I.normalizerMonoidHom (inclusion (hAP.trans hPI) a)
  have hfix : (S : Subgroup I).map g.toMonoidHom = S := by
    apply map_injective I.subtype_injective
    have he : I.subtype.comp g.toMonoidHom = (MulAut.conj (a:G)).toMonoidHom.comp I.subtype := rfl
    rw [map_map,he,←map_map]
    exact mem_normalizer_iff_map_conj_eq.mp (hn (hAP a.property))
  have he : (normalizerQuotientAction I (pCore 2 I)
      (inclusion (hAP.trans hPI) a)).toMonoidHom.comp q = q.comp g.toMonoidHom := by
    ext i
    change quotientAut (pCore 2 I) g (QuotientGroup.mk' (pCore 2 I) i) =
      QuotientGroup.mk' (pCore 2 I) (g i)
    exact quotientAut_apply_mk _ _ _
  rw [map_map,he,←map_map,hfix]
end Theory.GroupTheory

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {X Y : Type*} [Group X] [Finite X] [Group Y]

/-- Solvable Sylow control lifts through any central kernel, with no restriction
on its order. -/
theorem SolvableSylowControl.of_surjective_central_kernel
    {p : ℕ} [Fact p.Prime] (f : X →* Y) (hf : Function.Surjective f)
    (hk : f.ker ≤ center X) (h : SolvableSylowControl p Y) :
    SolvableSylowControl p X := by
  intro S A hA hSA
  let := hA
  have hs : Group.IsSolvable (A.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective A)
  have hn := h (S.mapSurjective hf) (A.map f) hs (map_mono hSA)
  have hh := map_le_iff_le_comap.mp hn
  rwa [S.normalizer_comap_of_central_kernel f hf hk] at hh

/-- A perfect subgroup is recovered as the residual of the full preimage
of its image under a homomorphism with central kernel. -/
theorem perfect_eq_residual_preimage (f : X →* Y) (hk : f.ker ≤ center X)
    (K : Subgroup X) [Group.IsPerfect K] :
    K = (solvableResidual ((K.map f).comap f)).map ((K.map f).comap f).subtype := by
  apply le_antisymm
  · exact le_map_solvableResidual_of_isPerfect _ _ (le_comap_map f K)
  · let R := (solvableResidual ((K.map f).comap f)).map ((K.map f).comap f).subtype
    let : Group.IsPerfect R := Group.IsPerfect.map _
    exact perfect_le_of_map_le_of_central_kernel f hk R K
      (map_le_iff_le_comap.mpr (map_subtype_le _))
end Theory.GroupTheory
