module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.RankOneReversal
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.RankEightConfinement

/-!
# The reverse central point of the rank-eight endpoint

Reverse the selected rank-one endpoint while retaining its product in H.
The reversed actor again lies in a dihedral factor. Its central-point placement
then transports back through the literal original conjugator; the intervening
H-element merely permutes the two covering supports. Factor labels are aligned
separately by critical-endpoint translations.

Source: Aschbacher--Smith 14.6.13(2), printed p.1032.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open OddNormalizer OrthogonalSource SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter13.Section08 Chapter13.Section08.SourceCompletion Chapter13.Section08.CriticalGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The covering supports follow the actual permutation of the two source summands. -/
theorem exchanged_supports_permuted {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (T : Subgroup G) (hTH : T ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a T p H0 H1 H2)
    (x : H) :
    ((firstSupport a H1).map (MulAut.conj (x:G)).toMonoidHom = firstSupport a H1 ∧
      (firstSupport a H2).map (MulAut.conj (x:G)).toMonoidHom = firstSupport a H2) ∨
    ((firstSupport a H1).map (MulAut.conj (x:G)).toMonoidHom = firstSupport a H2 ∧
      (firstSupport a H2).map (MulAut.conj (x:G)).toMonoidHom = firstSupport a H1) := by
  unfold firstSupport
  rw [supportPreimage_conjugate a _ x,supportPreimage_conjugate a _ x]
  rcases exchanged_spaces_permuted a T hTH p H0 H1 H2 d
      (QuotientGroup.mk' (pCore 2 H) x) with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl ⟨congrArg (supportPreimage a) h1,congrArg (supportPreimage a) h2⟩
  · exact Or.inr ⟨congrArg (supportPreimage a) h1,congrArg (supportPreimage a) h2⟩

omit [Finite G] in
/-- The H-adjustment in the reverse endpoint merely permutes the two supports. -/
theorem reverse_point_of_product {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (a : LocalQuotientAction H U Z) (T : Subgroup G) (hTH : T ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a T p H0 H1 H2)
    (g j : G) (hprod : j*g ∈ H)
    (hpoint : Z.map (MulAut.conj j).toMonoidHom ≤ firstSupport a H1 ∨
      Z.map (MulAut.conj j).toMonoidHom ≤ firstSupport a H2) :
    Z ≤ (firstSupport a H1).map (MulAut.conj g).toMonoidHom ∨
      Z ≤ (firstSupport a H2).map (MulAut.conj g).toMonoidHom := by
  let x : H := ⟨(j*g)⁻¹,H.inv_mem hprod⟩
  have hx : j⁻¹ = g*(x:G) := by dsimp [x]; group
  have back (S : Subgroup G) (hs : Z.map (MulAut.conj j).toMonoidHom ≤ S) :
      Z ≤ (S.map (MulAut.conj (x:G)).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
    have hm := map_mono (f := (MulAut.conj j⁻¹).toMonoidHom) hs
    rw [show (Z.map (MulAut.conj j).toMonoidHom).map (MulAut.conj j⁻¹).toMonoidHom = Z from
      conjBy_inv Z j,hx] at hm
    exact hm.trans_eq (conjBy_mul S g (x:G))
  have hp := exchanged_supports_permuted a T hTH p H0 H1 H2 d x
  rcases hpoint with h1 | h2 <;> rcases hp with ⟨hs1,hs2⟩ | ⟨hs1,hs2⟩
  · exact Or.inl (by simpa only [hs1] using back _ h1)
  · exact Or.inr (by simpa only [hs1] using back _ h1)
  · exact Or.inr (by simpa only [hs2] using back _ h2)
  · exact Or.inl (by simpa only [hs2] using back _ h2)

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
include hG hempty hM hunique hmany hcard e hab hH

/-- The reverse central point lies in one of the literal conjugated supports,
using the same selected endpoint, before independently marking its factors. -/
theorem source_rankEight_reverse_point_either
    (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a (T : Subgroup G) p H0 H1 H2) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let : IsElementaryAbelian 2 D.UH :=
      ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH
    ∀ c : SelectedQuadraticEndpoint h a,
      Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 8 →
      D.V₁ ≤ c.endpoint.conjugate (firstSupport a H1) ∨
        D.V₁ ≤ c.endpoint.conjugate (firstSupport a H2) := by
  dsimp only
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)›
  intro c hdim
  obtain ⟨_,hr,hd⟩ := source_rankEight_selected_confinement
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 d c hdim
  obtain ⟨hb,_,_⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hunique hmany hcard e hab H hH
  obtain ⟨r,_,hprod,_,_⟩ := c.rank_one_reversal hb hr hd
  have hp := source_rankEight_selected_point
    hG T hempty hM hunique hmany hcard e hab H hH a p H0 H1 H2 d r hdim
  exact reverse_point_of_product a (T : Subgroup G) hH.1.2 p H0 H1 H2 d
    c.endpoint.representative r.endpoint.representative hprod (hp.imp And.right And.right)

end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
