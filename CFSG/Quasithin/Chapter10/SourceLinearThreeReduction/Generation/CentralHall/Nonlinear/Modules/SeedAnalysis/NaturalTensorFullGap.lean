module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.NaturalTensorLargeActors
public import Theory.Representation.BinaryOffender.KernelImageRank

/-!
# The full tensor actor below the seed dimension

The rank of a full image is at most the seed-image rank plus the full image
of its pointwise seed kernel. Combining this with the additive codimension
budget transfers the H.1.1 gap to every original full actor of codimension
less than 4n. Conjugation first makes the actor move the seed, and the small
displacement makes it preserve that seed. Induction on codimension handles
the entire remaining kernel, whose budget is strictly smaller.

Thus a moving higher-Thompson actor with j+1<n has full codimension at least
4n and image rank at least 4n-j. E.6.26 supplies that actual actor when the
original H-star generation parameter is at most j. The final Hall alternative
retains the original quotient and both factor markings. These are still lower
bounds, not the ambient exclusion or an identification of seed and full module.
Source: Aschbacher--Smith H.1.1(2), B.2.4(1), 9.2.1 and 9.2.4,
printed pp.378,75,730, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02 ChapterE
open Representation.BinaryOffender.NaturalTensor
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary
local instance (n : ℕ) : Algebra (ZMod 2) (GaloisField 2 n) := ZMod.algebra _ 2
local instance : IsElementaryAbelian 2 D.fullModule :=
  D.fullModule_elementary (source_module_nonsolvable_uniqueness D)


/-- The rank loss from the full action is bounded by the actual image of the
pointwise seed kernel; no restriction-faithfulness assumption is needed. -/
theorem original_full_rank_le_seed_add_kernel (A : Subgroup D.maximalLocal)
    [IsElementaryAbelian 2 A]
    (hs : A.map D.maximalLocal.subtype ≤ normalizer (D.seed : Set G)) :
    rank (A.map (originalFullAutomizerHom D)) ≤
      rank (originalPreservingSeedHom D A hs).range +
        rank (((originalPreservingSeedHom D A hs).ker.map A.subtype).map
          (originalFullAutomizerHom D)) := by
  have hh := rank_range_le_range_add_kernel_image (originalPreservingSeedHom D A hs)
    ((originalFullAutomizerHom D).comp A.subtype)
  rw [MonoidHom.range_comp,Subgroup.range_subtype,←map_map] at hh
  exact hh

/-- Below the seed dimension, the H.1.1 gap holds on the full module.
Induction on displacement handles the entire pointwise seed kernel, while
conjugation ensures that the same actor has a nontrivial seed image. -/
theorem original_even_full_rank_gap_below_seed_dimension
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (A : Subgroup D.maximalLocal) [IsElementaryAbelian 2 A]
    (hne : A.map (originalFullAutomizerHom D) ≠ ⊥)
    (hsmall : fixedCodim (automizerRepresentation D.fullModule)
      (A.map (originalFullAutomizerHom D)) < 4*n) :
    rank (A.map (originalFullAutomizerHom D)) + n ≤
      fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) + 1 := by
  let : FiniteDimensional (ZMod 2) (Additive D.fullModule) := Module.Finite.of_finite
  suffices hh : ∀ d : ℕ, ∀ (A : Subgroup D.maximalLocal), IsElementaryAbelian 2 A →
      A.map (originalFullAutomizerHom D) ≠ ⊥ →
      fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) = d →
      d < 4*n → rank (A.map (originalFullAutomizerHom D)) + n ≤ d+1 by
    exact hh _ A inferInstance hne rfl hsmall
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro A hA hne hd hsmall
    let := hA
    obtain ⟨m,hm⟩ := original_exists_conjugate_moving_seed D A hne
    let C := A.map (MulAut.conj m).toMonoidHom
    let : IsElementaryAbelian 2 C := IsElementaryAbelian.map _
    have hc : fixedCodim (automizerRepresentation D.fullModule)
        (C.map (originalFullAutomizerHom D)) = d := by
      rw [←original_full_fixedCodim_map D,show C = A.map (MulAut.conj m).toMonoidHom from rfl,
        fixedCodim_map_conj,original_full_fixedCodim_map D]
      exact hd
    have hs : C.map D.maximalLocal.subtype ≤ normalizer (D.seed : Set G) := by
      rintro _ ⟨a,ha,rfl⟩
      apply original_seed_stable_of_full_displacement_lt D c a
      have hb := operatorFixedCodim_le_fixedCodim (originalFullAction D) C ha
      rw [original_full_fixedCodim_map D,hc] at hb
      rw [original_nonseparated_even_seed_finrank_eq D c n hn e ht htn hsep]
      omega
    let f := originalPreservingSeedHom D C hs
    have hmove : f.range ≠ ⊥ := by
      intro hz
      apply hm
      rintro _ ⟨a,ha,rfl⟩
      apply (originalPreservingSeedHom_mem_ker D C hs ⟨a,ha⟩).mp
      have hmem : f ⟨a,ha⟩ ∈ f.range := ⟨⟨a,ha⟩,rfl⟩
      rw [hz] at hmem
      exact mem_bot.mp hmem
    let K := f.ker.map C.subtype
    let : IsElementaryAbelian 2 f.ker :=
      IsElementaryAbelian.of_injective f.ker.subtype f.ker.subtype_injective
    let : IsElementaryAbelian 2 K := IsElementaryAbelian.map _
    have hk : fixedCodim (automizerRepresentation D.fullModule)
        (K.map (originalFullAutomizerHom D)) =
        fixedCodim ((originalFullAction D).comp C.subtype) f.ker := by
      rw [←original_full_fixedCodim_map D]
      unfold fixedCodim
      rw [fixedSpace_comp_map]
    have hgap := (original_even_preserving_seed_budget_gap D c n hn e ht htn hsep C hs hmove).2.1
    change fixedCodim ((originalFullAction D).comp C.subtype) f.ker + rank f.range + n ≤
      fixedCodim (automizerRepresentation D.fullModule) (C.map (originalFullAutomizerHom D)) + 1 at hgap
    rw [hc,←hk] at hgap
    have hkr : rank (K.map (originalFullAutomizerHom D)) ≤
        fixedCodim (automizerRepresentation D.fullModule) (K.map (originalFullAutomizerHom D)) := by
      by_cases hz : K.map (originalFullAutomizerHom D) = ⊥
      · rw [hz,BinaryOffender.rank_bot]
        exact Nat.zero_le _
      · have hlt : fixedCodim (automizerRepresentation D.fullModule)
            (K.map (originalFullAutomizerHom D)) < d := by omega
        have hh := ih _ hlt K inferInstance hz rfl (by omega)
        omega
    have hr := original_full_rank_le_seed_add_kernel D C hs
    change rank (C.map (originalFullAutomizerHom D)) ≤ rank f.range +
      rank (K.map (originalFullAutomizerHom D)) at hr
    have he : C.map (originalFullAutomizerHom D) =
        (A.map (originalFullAutomizerHom D)).map
          (MulAut.conj (originalFullAutomizerHom D m)).toMonoidHom := by
      rw [show C = A.map (MulAut.conj m).toMonoidHom from rfl,map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro a
      change originalFullAutomizerHom D (m*a*m⁻¹) =
        originalFullAutomizerHom D m * originalFullAutomizerHom D a *
          (originalFullAutomizerHom D m)⁻¹
      rw [map_mul,map_mul,map_inv]
    rw [he,rank_map_conj] at hr
    omega

/-- Below j = n-1 every moving Thompson actor has full fixed codimension
at least the entire seed dimension, even when its seed restriction has a kernel. -/
theorem original_even_thompson_actor_seed_dimension_bound
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    (j : ℕ) (hj : j+1 < n) (A : Subgroup D.maximalLocal)
    (hA : A ∈ ChapterB.thompsonFamily ((T : Subgroup G).subgroupOf D.maximalLocal) j)
    (hne : A.map (originalFullAutomizerHom D) ≠ ⊥) :
    4*n ≤ fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) ∧
      4*n-j ≤ rank (A.map (originalFullAutomizerHom D)) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  have hu := original_full_thompson_fixedCodim_bound D j A hA hne
  have hl : 4*n ≤ fixedCodim (automizerRepresentation D.fullModule)
      (A.map (originalFullAutomizerHom D)) := by
    by_contra! hsmall
    have hh := original_even_full_rank_gap_below_seed_dimension D c n hn e ht htn hsep A hne hsmall
    omega
  exact ⟨hl,by omega⟩

/-- The original H-star group's low-generation alternative now costs at least
the whole seed dimension on the full module. -/
@[expose] def OriginalEvenSeedDimensionThompsonAnalysis (H : Subgroup G) (n : ℕ) : Prop :=
  ∀ j : ℕ, 0 < j → j+1 < n → generationParameter H ≤ j →
    ∃ A : Subgroup D.maximalLocal,
      A ∈ ChapterB.thompsonFamily ((T : Subgroup G).subgroupOf D.maximalLocal) j ∧
      IsElementaryTwo (A.map (originalFullAutomizerHom D)) ∧
      4*n ≤ fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) ∧
      fixedCodim (automizerRepresentation D.fullModule) (A.map (originalFullAutomizerHom D)) ≤
        rank (A.map (originalFullAutomizerHom D)) + j ∧
      4*n-j ≤ rank (A.map (originalFullAutomizerHom D))

/-- E.6.26's literal moving actor satisfies the strengthened full-module bound. -/
theorem original_even_seed_dimension_thompson_analysis
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (n : ℕ) (hn : 3 ≤ n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G)))
    : OriginalEvenSeedDimensionThompsonAnalysis D H n := by
  intro j hj hjn hgen
  obtain ⟨A,hA,he,_hl,hb,_hr⟩ :=
    original_even_exists_thompson_actor D c n hn e ht htn hsep j hj (by omega) hgen
  obtain ⟨hl,hr⟩ := original_even_thompson_actor_seed_dimension_bound
    D c n hn e ht htn hsep j hjn A hA he.1
  exact ⟨A,hA,he,hl,hb,hr⟩

/-- The original Hall alternative, with the quotient, factor markings and
field action retained, now excludes all Thompson actors below seed dimension.
This still does not assert seed/full equality or complete the Cartan exclusion. -/
theorem original_hall_conclusion_or_natural_tensor_full_gap
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B) :
    (IsPGroup 3 B ∨ ∃ n : ℕ, Monoid.exponent B ∣ 2^n+1) ∨
      ∃ (t : G) (ht : t ∈ (T : Subgroup G)), t ∉ normalizer (L : Set G) ∧
        ∃ n : ℕ, 3 ≤ n ∧ ∃ e : (L ⧸ pCore 2 L) ≃* SL(2,GaloisField 2 n),
          ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
            D.seed ≤ centralizer (L : Set G)) ∧
          OriginalEvenNaturalTensorAnalysis D ht n e ∧
          OriginalEvenSeedDeterminantCoordinates D ht n e ∧
          OriginalEvenLargeThompsonAnalysis D H n ∧
          (∀ A : Subgroup D.maximalLocal, IsElementaryAbelian 2 A →
            A.map (originalFullAutomizerHom D) ≠ ⊥ →
            fixedCodim (automizerRepresentation D.fullModule)
              (A.map (originalFullAutomizerHom D)) < 4*n →
            rank (A.map (originalFullAutomizerHom D)) + n ≤
              fixedCodim (automizerRepresentation D.fullModule)
                (A.map (originalFullAutomizerHom D)) + 1) ∧
          OriginalEvenSeedDimensionThompsonAnalysis D H n := by
  rcases original_hall_conclusion_or_natural_tensor_large_thompson D c with hh |
    ⟨t,ht,htn,n,hn,e,hs,ha,hdet,_hm,_hdisp,_hfull,_hl,_hr,_hcent,_hth,_hsmall,hlarge⟩
  · exact Or.inl hh
  · refine Or.inr ⟨t,ht,htn,n,hn,e,hs,ha,hdet,hlarge,?_,
      original_even_seed_dimension_thompson_analysis D c n hn e ht htn hs⟩
    intro A hA hne hsmall
    let := hA
    exact original_even_full_rank_gap_below_seed_dimension D c n hn e ht htn hs A hne hsmall

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
