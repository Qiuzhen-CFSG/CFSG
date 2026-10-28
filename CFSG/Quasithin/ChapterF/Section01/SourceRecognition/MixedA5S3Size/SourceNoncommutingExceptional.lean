module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.SourceNoncommutingParameters
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.MixedA5S3Size.DGSProfiles
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalCubic

/-!
# The exceptional mixed noncommuting core order

At distance two the critical endpoint is cubic and its middle vertex is
quintic. In the exceptional D = Z branch the original Chapter 10 core-order
calculation gives order 32 for that quintic vertex core. Actual graph
conjugation and the reduced-completion inclusion transport it to the first
original parabolic core. The full mixed Borel then has two-core order 128,
and the unreduced source Sylow has order 128 or 256.

The only branch premise is the literal D = Z equality; no numerical or
recognition conclusion is supplied as a premise.
Source: DGS, *Groups and Graphs* (1985), 10.9, pp.162--163;
Aschbacher--Smith F.1.9--12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.MixedDGS
open CFSG.Quasithin.ChapterF.Source.DGS85
open CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
variable {G : Type*} [Group G] [Finite G] {K U S : Subgroup G}
local notation "F" => Reduction.reducedFamily ![K,U] S

/-- The exceptional branch determines the original full Borel core and
the two possible unreduced Sylow orders. -/
theorem noncommuting_two_exceptional_size (h : HypothesisF11 ![K,U] S)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (eU : (U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3))
    {v m w t : Vertex F} (hc : IsCriticalPair F v w)
    (hne : ⁅Z F v,Z F w⁆ ≠ ⊥) (hb : b F = 2)
    (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w)
    (ht : (graph F).Adj v t) (htne : t ≠ m)
    (hD : D F m t = Z F v) :
    Nat.card (twoCore (commonBorel ![K,U] S)) = 128 ∧
      (Nat.card S = 128 ∨ Nat.card S = 256) := by
  have H := Reduction.reduced_triple h
  obtain ⟨hv,hm⟩ := noncommuting_two_cubic_orientation h eK eU hc hne hb hvm hmw
  have hcentral := Reduction.reduced_bTwo_middle_central h hc hne hb hvm hmw
  have hcomm := (Reduction.reduced_bTwo_center_identities h hc hne hb hvm hmw).2.2.2
  obtain ⟨k,f,n,ch,a,c,hactor⟩ :=
    Reduction.reduced_bTwo_center_action_exists h hc hne hb hvm hmw
  let := f
  let := n
  let := ch
  have ha : a = ZMod.algebra k 2 := Subsingleton.elim _ _
  subst a
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  have hk := source_action_field_card h hactor c.quotient c.onto c.kernel
    (graph_linear_two h eU v hv).some
  have horders := c.exceptional_linear_core_orders H
    (Reduction.reduced_borel_core_sylow h) (Reduction.reduced_vertex_sylow h)
    hb hactor hcentral ht htne hcomm.le
    (Reduction.reduced_graph_core_obstruction h v m hvm)
    (graph_linear_four h eK m hm).some hD (LinearEquiv.refl _ _)
  have hmiddle : Nat.card (Q F m) = 32 := by
    have hh : Nat.card (Q F m) = Nat.card k ^ 3 * Nat.card (GaloisField 2 2) := horders.2
    rw [hk,Nat.card_zmod,GaloisField.card 2 2 (by decide)] at hh
    norm_num at hh
    exact hh
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F m
  rw [hm] at hg
  have hbase : Nat.card (Q F (base F false)) = 32 := by
    rw [←hg,Q_translate,card_map_of_injective (MulAut.conj g).injective] at hmiddle
    exact hmiddle
  have hfirst : Nat.card (pCore 2 (parabolic ![K,U] S 0)) = 32 := by
    have hmapped := congrArg (fun A : Subgroup G => Nat.card A)
      (NoncommutingProfile.reduced_base_Q_map h false)
    rw [card_map_of_injective (Reduction.G₀ ![K,U] S).subtype_injective,hbase] at hmapped
    change 32 = Nat.card (twoCore (parabolic ![K,U] S 0)) at hmapped
    exact (card_map_of_injective (K := pCore 2 (parabolic ![K,U] S 0))
      (parabolic ![K,U] S 0).subtype_injective).symm.trans hmapped.symm
  have hR : Nat.card (pCore 2 (commonBorel ![K,U] S)) = 128 := by
    rw [h.mixed_borel_core_card eK eU,hfirst]
  have htwo : Nat.card (twoCore (commonBorel ![K,U] S)) = 128 := by
    exact (card_map_of_injective (K := pCore 2 (commonBorel ![K,U] S))
      (commonBorel ![K,U] S).subtype_injective).trans hR
  have hs := h.mixed_sylow_card_borel_core_cases eK eU
  rw [hR] at hs
  exact ⟨htwo,by simpa using hs⟩

end CFSG.Quasithin.ChapterF.Source.MixedDGS
