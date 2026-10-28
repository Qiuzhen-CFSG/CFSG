module
public import CFSG.Quasithin.Chapter10.SourceA5PointCarrierSieve
public import CFSG.Quasithin.Chapter10.SourceA5PointLocalLie
public import CFSG.Quasithin.Chapter10.SourceA5PointLocalTriality
public import CFSG.Quasithin.Chapter10.SourceA5PointLocalMathieuShape
public import CFSG.Quasithin.Chapter10.SourceA5PointExceptionalSieve

/-!
# Selecting the original rank-two point markings

Every rank-two row of the actual simple central quotient is resolved: the
linear, symplectic, G₂ and triality carriers supply field-four markings;
Ree, Tits and the two small derived endpoints contradict the original A₅
section and moved-module bound. The normalized moved subgroup excludes the
small sporadic rows, while native M22 marking and the M23 calculation supply
their original point alternatives. Only M24, J4, Held and Ru remain for the
separate sporadic embedding inspection.

Source: Aschbacher–Smith 10.2.9, printed pp.750–751, and A.3.12/A.3.14.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterA.Section03
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- Every source C rank-two carrier gives an actual field-four point marking. -/
theorem source_a5_point_rank_two_quasisimple_marking
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {v : G} (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [Group.IsPerfect I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    {n : ℕ} (hm : ChapterA.Section02.IsTheoremCRankTwoModel (I ⧸ center I) n) :
    SourceA5PointQuasisimpleMarking.{u,0} L I := by
  cases hm with
  | linear hf hm =>
    exact (source_a5_point_linear_three_model_marking D e hn hvL hv0 hs hLI hIX hI hf hm).2
  | symplectic hf hm =>
    exact (source_a5_point_symplectic_model_marking D e hn hvL hv0 hs hLI hIX hI hf hm).2
  | g2 hf hm =>
    exact (source_a5_point_g2_model_marking D e hn hvL hv0 hs hLI hIX hI hf hm).2
  | triality hf hm =>
    obtain ⟨eI⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff
      (I ⧸ center I) n (by omega)).mp hm
    exact source_a5_point_triality_quasisimple_marking D e hn hvL hv0 hs hLI.le hIX hI
      n (by omega) eI
  | ree_f4 m hm _ he =>
    exact (source_a5_not_ree_containing_quotient D e hLI.le hm he.some).elim
  | symplectic_derived _ he =>
    exact (source_a5_not_symplectic_binary_containing_quotient D e hLI.le he.some).elim
  | g2_derived _ he =>
    exact (source_a5_not_g2_binary_containing_quotient e hLI.le (by simp) he.some).elim
  | tits _ he =>
    exact (source_a5_not_tits_containing_quotient D e hLI.le he.some).elim

/-- The entire original quasisimple inspection reduces to four concrete sporadic carriers. -/
theorem source_a5_point_quasisimple_marking_or_four_sporadic
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (t : G) {v : G}
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [IsQuasisimple I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent) :
    SourceA5PointQuasisimpleMarking.{u,0} L I ∨
      ∃ name : ClassificationModels.SporadicName,
        (name = .m24 ∨ name = .j4 ∨ name = .he ∨ name = .ru) ∧
        Nonempty ((I ⧸ center I) ≃* name.Carrier) := by
  rcases source_a5_point_center_quotient_carriers D e hn t hv hvne hvL hv0 hs hLI hIX hI
    with ⟨n,hm⟩ | ⟨name,hnames,he⟩
  · exact Or.inl (source_a5_point_rank_two_quasisimple_marking D e hn hvL hv0 hs hLI hIX hI hm)
  · rcases hnames with h22 | h23 | h24 | hj4 | hhe | hru
    · subst name
      exact Or.inl (source_a5_point_m22_quasisimple_marking_of_local
        D e hn hvL hv0 hs hLI hIX hI he.some)
    · subst name
      exact Or.inl (.mathieu23 he.some)
    · exact Or.inr ⟨name,Or.inl h24,he⟩
    · exact Or.inr ⟨name,Or.inr (Or.inl hj4),he⟩
    · exact Or.inr ⟨name,Or.inr (Or.inr (Or.inl hhe)),he⟩
    · exact Or.inr ⟨name,Or.inr (Or.inr (Or.inr hru)),he⟩

/-- The proved rows give the original alternative; only four sporadic carriers remain. -/
theorem source_a5_point_quasisimple_alternative_or_four_sporadic
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (t : G) {v : G}
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom) (hvne : v ≠ 1)
    (hv0 : v ∉ centralizer (localOrbit T L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G)))
    {I : Subgroup G} [IsQuasisimple I] (hLI : L < I)
    (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G)) :
    SourceA5PointComponentAlternative D e t I ∨
      ∃ name : ClassificationModels.SporadicName,
        (name = .m24 ∨ name = .j4 ∨ name = .he ∨ name = .ru) ∧
        Nonempty ((I ⧸ center I) ≃* name.Carrier) := by
  rcases source_a5_point_quasisimple_marking_or_four_sporadic
    D e hn t hv hvne (hcross hv) hv0 hs hLI hIX hI with hm | he
  · exact Or.inl (source_a5_point_alternative_of_quasisimple_marking
      D e t I hLI.le hv hNI hcross hm)
  · exact Or.inr he

end CFSG.Quasithin.Chapter10
