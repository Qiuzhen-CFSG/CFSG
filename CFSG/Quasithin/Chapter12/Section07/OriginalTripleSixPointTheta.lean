module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointResidual
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.ThetaSixSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
public import Theory.GroupTheory.CubicClosureSimple
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The original triple-six point residual is theta of its actual overgroup

The original Hypothesis 12.2.1 and the proved A/C source theorems give
theta(N_G(K)) = K. The chosen module supplies T-normalization. In the actual
point centralizer C_K(t), cubic elements map onto its A5 quotient through a
two-group kernel, so they generate precisely its two-residual. Intersecting
the original normalizer with C_G(t) introduces no further cubic elements.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 12.2.8,
12.7.2(6) and 12.7.4(3), printed pp.797 and 839--840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
open ChapterA.Section03.OddPrime.SourceModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The cubics in the original C_K(t) generate its actual two-residual. -/
theorem tripleSixPointCentralizer_cubicClosure (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    closure {c : (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) | orderOf c = 3} =
      pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) := by
  let C := K ⊓ centralizer ({(t : G)} : Set G)
  let N : Subgroup C := closure {c : C | orderOf c = 3}
  let e := tripleSixPointCentralizerEquiv D a t ht heven
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 q.ker := by
    rw [show q.ker = pCore 2 C by
      dsimp only [q]
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']]
    exact pCore_isPGroup
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hthree : 3 ∣ Nat.card (alternatingGroup (Fin 5)) := by
    rw [nat_card_alternatingGroup]
    norm_num
  have him : N.map q = ⊤ :=
    (cubic_closure_map_of_two_kernel q hq hk).trans
      (cubic_closure_eq_top_of_simple hthree)
  have hn : (⊤ : Subgroup C) ≤ normalizer (N : Set C) := by
    apply le_normalizer_closure_iff.mpr
    intro g _ x hx
    exact subset_closure ((MulAut.conj g).orderOf_eq x |>.trans hx)
  let : N.Normal := normalizer_eq_top_iff.mp (top_unique hn)
  have hs : N ⊔ q.ker = ⊤ := by
    have hh := congrArg (comap q) him
    simpa only [comap_map_eq, comap_top] using hh
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    exact mem_pResidual_of_orderOf_coprime (by rw [hx]; decide)
  · exact sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top N q.ker hk hs⟩

omit [Finite G] in
private theorem map_cubicClosure (M : Subgroup G) :
    (closure {x : M | orderOf x = 3}).map M.subtype =
      closure {x : G | x ∈ M ∧ orderOf x = 3} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, (M.orderOf_coe y).trans hy⟩
  · rintro ⟨hx, h3⟩
    exact ⟨⟨x, hx⟩, (M.orderOf_coe ⟨x, hx⟩).symm.trans h3, rfl⟩

/-- Source 12.7.2(6) for the actual component and normalizer. The chosen
module and earlier A/C theorems discharge the source normalization inputs. -/
theorem original_tripleSix_normalizer_theta
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T K) (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) :
    closure {x : G | x ∈ normalizer (K : Set G) ∧ orderOf x = 3} = K := by
  let e := a.groupEquiv
  have hc : (center (K ⧸ pCore 2 K)).map e.toMonoidHom =
      center Atlas.Codes.HexEvenAutomorphisms := by
    ext b
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact (centerCongr e ⟨c, hc⟩).property
    · intro hb
      exact ⟨e.symm b, (centerCongr e.symm ⟨b, hb⟩).property, e.apply_symm_apply b⟩
  exact h.source_theta_eq_of_central_quotient_six D.sylow_normalizes_component
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    ((QuotientGroup.congr _ _ e hc).trans Hexacode.even_quotient_center_equiv)

/-- The literal ambient Lt is theta of N_G(K) intersect C_G(t), with the
same original K, t and ambient group throughout. -/
theorem tripleSixPointCentralizerResidual_theta
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T K) (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype =
      (theta (normalizer (K : Set G) ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (normalizer (K : Set G) ⊓ centralizer ({(t : G)} : Set G)).subtype := by
  rw [← tripleSixPointCentralizer_cubicClosure D a t ht heven,
    map_cubicClosure, theta, map_cubicClosure]
  apply congrArg Subgroup.closure
  ext x
  constructor
  · rintro ⟨hx, h3⟩
    exact ⟨⟨K.le_normalizer hx.1, hx.2⟩, h3⟩
  · rintro ⟨hx, h3⟩
    have hxK : x ∈ K := by
      rw [← original_tripleSix_normalizer_theta h D a]
      exact subset_closure ⟨hx.1, h3⟩
    exact ⟨⟨hxK, hx.2⟩, h3⟩

/-- The intrinsic theta identity required by the 12.7.4(3) source assembly. -/
theorem tripleSixPointCentralizerResidual_subgroupOf_theta
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T K) (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K) :
    ((pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
      (K ⊓ centralizer ({(t : G)} : Set G)).subtype).subgroupOf
        (normalizer (K : Set G) ⊓ centralizer ({(t : G)} : Set G)) =
      theta (normalizer (K : Set G) ⊓ centralizer ({(t : G)} : Set G) : Subgroup G) := by
  apply map_injective (normalizer (K : Set G) ⊓
    centralizer ({(t : G)} : Set G)).subtype_injective
  rw [map_subgroupOf_eq_of_le
    ((map_subtype_le _).trans (inf_le_inf K.le_normalizer le_rfl))]
  exact tripleSixPointCentralizerResidual_theta h D a t ht heven

end CFSG.Quasithin.Chapter12.Section07
