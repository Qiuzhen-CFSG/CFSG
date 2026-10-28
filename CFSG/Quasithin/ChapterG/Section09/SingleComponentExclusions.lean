module
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.TwistedExclusions
public import CFSG.Quasithin.ChapterG.Section07.AlternatingSevenCover
public import CFSG.Quasithin.ChapterG.Section07.SporadicLocal
public import CFSG.Quasithin.ChapterG.Section07.SporadicLocal.Rudvalis
public import CFSG.Quasithin.ChapterG.Section07.SporadicLocal.JankoFourRank
public import CFSG.Quasithin.ChapterG.Section07.SporadicLocal.HigmanSimsRank
public import Theory.SpecificGroups.Held.TwoRank.Automorphisms
public import Theory.Representation.Suzuki.BinaryDegree
public import Theory.SpecificGroups.SU3.EvenTwoRank.Automorphisms.Unconditional
public import Theory.Representation.SU3.BinaryDegree

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.AutomorphismRankBound
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.TraceCompleteness

/-!
# Direct single-component exclusions for the original G.9 action

The actor embeds in the automorphism group of the actual irreducible
component. The completed model rank bounds and faithful binary degree bounds
exclude Suzuki, triple A7, M11, J1, J4, HS, He and Ru under the original G.9
inequality. The unitary theorem uses a genuine special covering action and
the literal central quotient. Hall--Janko is excluded under the stronger
bound d <= m+2 occurring in the two sharp source branches.

No group or module catalogue is assumed beyond each explicit model witness.
Simplicity is retained exactly where supplied by the simple catalogue row.
Source: Aschbacher--Smith G.7.2--3 and G.9.3, printed pp.347--356.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.ChapterG.Section09
open Section07 Section07.SporadicLocal
open DefiningCharacteristic.TwistedExclusions
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L : Subgroup G} {m : ℕ}
  (h : ComponentHypothesis K ρ A L L m)

include h

theorem ComponentHypothesis.not_suzuki {k : ℕ} (hk : 1 ≤ k)
    (e : L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup k) : False :=
  not_suzuki_of_degree_bound h hk e
    (fun σ _ hf => Representation.Suzuki.finrank_ge hk σ hf)

theorem ComponentHypothesis.not_triple_alternating_seven
    (e : L ⧸ center L ≃* alternatingGroup (Fin 7))
    (hz : Nat.card (center L) = 3) : False := by
  let : IsQuasisimple L := h.component.2
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hr := AlternatingSevenCover.cover_automorphism_two_rank e
  have hd := h.single_component_degree_bound
  exact AlternatingSevenCover.no_small_faithful_binary_representation e hz
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) (by omega)

theorem ComponentHypothesis.not_m11_central_quotient
    (e : L ⧸ center L ≃* Sporadic.Mathieu.M11) : False := by
  let : IsQuasisimple L := h.component.2
  have hr := m11_centralQuotient_automorphism_twoRank_le_three e
  have hl := m11_centralQuotient_finrank_ge_ten ρ h.faithful L e
  have hu := h.single_component_degree_bound
  omega

theorem ComponentHypothesis.not_j1_central_quotient
    (e : L ⧸ center L ≃* Janko1.Model) : False := by
  let : IsQuasisimple L := h.component.2
  have hr := j1_centralQuotient_automorphism_twoRank_le_three e
  have hl := j1_centralQuotient_finrank_ge_ten ρ h.faithful L e
  have hu := h.single_component_degree_bound
  omega

theorem ComponentHypothesis.not_higman_sims
    (e : L ≃* Sporadic.LeechRelated.HS.Carrier) : False := by
  have hl := hs_finrank_ge_twenty ρ h.faithful L e
  have hu := h.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := hs_automorphism_twoRank_le_five
  omega

theorem ComponentHypothesis.not_held (e : L ≃* Held.He) : False := by
  have hl := he_finrank_ge_twenty ρ h.faithful L e
  have hu := h.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := Held.automorphism_rank_le_six
  omega

theorem ComponentHypothesis.not_janko_four [IsSimpleGroup L]
    (e : L ≃* Janko4.Model) : False := by
  let : IsQuasisimple L := h.component.2
  let : IsSimpleGroup Janko4.Model := e.symm.isSimpleGroup
  let : Group.IsPerfect Janko4.Model := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  have hl := j4_finrank_ge_one_hundred_ten ρ h.faithful L e
  have hu := h.single_component_degree_bound
  rw [primeRank_equiv 2 (MulAut.congr e)] at hu
  have hr := j4_automorphism_twoRank_le_eleven
  omega

theorem ComponentHypothesis.not_rudvalis [IsSimpleGroup L]
    (e : L ≃* Rudvalis.Model) : False := by
  have hl := ru_finrank_ge_twenty ρ h.faithful L e
  have hr := ru_automorphism_twoRank_le_six_of_equiv e
  have hu := h.single_component_degree_bound
  omega

theorem ComponentHypothesis.not_binary_unitary_three
    {F : Type*} [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hm : Nonempty (L ≃* J.specialSubgroup) ∨
      Nonempty (L ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))
    (e : L ⧸ center L ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) : False :=
  not_unitary_three_of_estimates h J hn hcard hconj hm e
    (fun σ hi hnt => Representation.SU3.BinaryDegree.finrank_ge_of_irreducible
      J hn hcard hconj σ hi hnt)
    (BenderSuzuki.MatrixGroups.HermitianForm.EvenTwoRank.automorphism_two_rank_le
      J hn hcard hconj)

/-- The sharp original degree is at most eight, below the actual binary
Hall--Janko minimum twelve. -/
theorem ComponentHypothesis.not_janko_two_of_sharp_degree
    (hd : Module.finrank (ZMod 2) V ≤ m+2)
    (e : L ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  let σ : Representation (ZMod 2) Sporadic.LeechRelated.J2.Carrier V :=
    (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : Representation.IsIrreducible (ρ.comp L.subtype) := h.irreducible
  have hi : Representation.IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h.irreducible
  have hf : Function.Injective σ := h.faithful.comp (L.subtype_injective.comp e.symm.injective)
  have hr := h.toSetup.rank_le_automorphisms (L := L) (by
    rw [normalizer_eq_top_iff.mpr h.normal_H]; exact le_top)
  rw [primeRank_equiv 2 (MulAut.congr e)] at hr
  have hb := Sporadic.LeechRelated.J2.automorphism_primeRank_le_six
  have hdeg := Representation.JankoTwo.SmallBinaryDegrees.finrank_twelve_of_lt_twentyEight
    σ hf hi (by omega)
  omega

end CFSG.Quasithin.ChapterG.Section09
