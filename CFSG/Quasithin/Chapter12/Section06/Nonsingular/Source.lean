module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.LocalStructure
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.Cover

/-!
# Source kernel, local normalization, and terminal consequences

The original section hypotheses give C_L(V)=O₂(L)=O₂,Z(L), with compatible
quotient coordinates. The actual nonsingular A₆ marking and L_v≤K_v
are now constructed from these hypotheses. The full centralizer C_L(v)
has index 28 in L. Local normalization constructs S and discharges the
kernel and intersection premises; the selected ambient Sylow arrangement
and its index four remain explicit.

The terminal contradiction now uses the canonical K_v=O^{3′}(G_v^∞).
Its two-perfectness and Q≤R_v are proved from their definitions and the
original chosen module. The block, splitting, index and commutator inputs
remain explicit: this is not yet Theorem 12.6.2.

The singular-subspace consequence retains V, C_V(L), and the actual
quadratic form on their quotient. It is conditional on nonsingular
point-centralizer control, and does not prove C_V(L)=1 (Lemma 12.6.23).
Construction of the remaining inputs to 12.6.2 and elimination of the
fixed space are still required before applying the permutation exclusion.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Theorem 12.6.2, printed pp.823--828, and Lemma 12.6.28, pp.834--835.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]

/-- The literal Section06 application of 12.6.5. T-normalization comes from
the original Irr⁺ choice, and the supplied Sylow position in M_v restricts
to C_LT(v). This general adapter retains the A₆ marking and L_v≤K_v;
the nonsingular specialization below constructs both. The selected ambient
Sylow position and its index four remain explicit. -/
theorem SourceHypothesis.local_normalization
    {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}
    (H : SourceHypothesis K T L V) (v : V)
    (hLK : Lv L (v : G) ≤ Kv (v : G))
    (e : Star (Lv L (v : G)) ≃* alternatingGroup (Fin 6))
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4) :
    ∃ S : Sylow 2 (Gv (v : G)),
      let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
      Tv T (v : G) ≤ S₀ ∧
      R L (Kv (v : G)) S₀ (v : G) ≤ normalizer (Lv L (v : G) : Set G) ∧
      ⁅Lv L (v : G), R L (Kv (v : G)) S₀ (v : G)⁆ ≤ (Lv L (v : G)).pCoreIn 2 ∧
      R L (Kv (v : G)) S₀ (v : G) = S₀ ⊓ coreQuotientCentralizer (Lv L (v : G)) := by
  have hT : (T : Subgroup G) ≤ M L := H.chosen.sylow_normalizes_component
  obtain ⟨P, hP⟩ := hTv.restrict
    (show Tv T (v : G) ≤ LT T L ⊓ Gv (v : G) from inf_le_inf le_sup_right le_rfl)
    (show LT T L ⊓ Gv (v : G) ≤ Mv L (v : G) from
      inf_le_inf (sup_le L.le_normalizer hT) le_rfl)
  obtain ⟨S, hS, _, hN, hc, he⟩ :=
    exists_nonsingular_sylow_normalization T L (v : G) hT hLK e P hP hi
  exact ⟨S, hS, hN, hc, he⟩

/-- The nonsingular source application of 12.6.5 constructs the A₆ marking
and L_v≤K_v. Only the Sylow arrangement and its index four remain explicit. -/
theorem SourceHypothesis.local_normalization_of_nonsingular
    {K : GroupClass} {T : Sylow 2 G} {L V : Subgroup G}
    [IsElementaryAbelian 2 V] (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes) (v : V)
    (hv : D.Nonsingular v)
    (hTv : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (hi : (Tv T (v : G)).relIndex (T : Subgroup G) = 4) :
    ∃ S : Sylow 2 (Gv (v : G)),
      let S₀ := (S : Subgroup (Gv (v : G))).map (Gv (v : G)).subtype
      Tv T (v : G) ≤ S₀ ∧
      R L (Kv (v : G)) S₀ (v : G) ≤ normalizer (Lv L (v : G) : Set G) ∧
      ⁅Lv L (v : G), R L (Kv (v : G)) S₀ (v : G)⁆ ≤ (Lv L (v : G)).pCoreIn 2 ∧
      R L (Kv (v : G)) S₀ (v : G) = S₀ ⊓ coreQuotientCentralizer (Lv L (v : G)) := by
  obtain ⟨⟨e⟩, _, _, hLK⟩ :=
    D.nonsingular_local_structure H.chosen H.source.quasisimple v hv
  exact H.local_normalization v hLK e hTv hi

/-- The terminal argument with the literal canonical K_v and the inclusion
Q≤R_v supplied by the original Irr⁺ choice. The remaining premises are the
outputs of the still-required local block and cohomology arguments. -/
theorem nonsingular_terminal_contradiction_of_Kv
    (T : Sylow 2 G) (L V S : Subgroup G) [IsElementaryAbelian 2 V]
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (v : V) (hv : D.Nonsingular v)
    (hKnot : ¬ Kv (v : G) ≤ M L)
    (hcore : Rv T L (v : G) = (Kv (v : G) ⊔ S).pCoreIn 2)
    (hQ : IsElementaryAbelian 2 (Q T L))
    (hindex : (Q T L).relIndex (Rv T L (v : G)) = 2)
    (hnormalizer : normalizer (Q T L : Set G) ≤ M L)
    (r : G) (hr : r ∈ Rv T L (v : G))
    (hcomm : ⁅Rv T L (v : G), zpowers r⁆ = zpowers (v : G)) : False :=
  nonsingular_terminal_contradiction T L V (Kv (v : G)) S chosen.normalizes D v hv
    (Kv_isPPerfect (v : G)) hKnot hcore hQ (Q_le_Rv chosen v) hindex hnormalizer r hr hcomm

omit [Finite G] in
/-- If the centralizer of a literal subgroup `E ≤ V` escapes `M L`, then no
element of `E` can be nonsingular in the marked quotient. This conditional
consequence is used in 12.6.28; it does not assert C_V(L)=1 (12.6.23). -/
theorem singular_subgroup_of_nonsingular_centralizer
    {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : L ≤ normalizer (V : Set G)) (D : OrthogonalMarking L V hn)
    (hcontrol : ∀ v : V, D.Nonsingular v → Gv (v : G) ≤ M L)
    (E : Subgroup G) (hEV : E ≤ V)
    (hescape : ¬ centralizer (E : Set G) ≤ M L) :
    ∀ e : E, ¬ D.Nonsingular ⟨e.1, hEV e.2⟩ := by
  intro e he
  apply hescape
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr e.property)).trans
    (hcontrol ⟨e.1, hEV e.2⟩ he)

omit [Finite G] in
/-- The singular-subspace consequence written as the actual quadratic equation
on the quotient `V/C_V(L)`. -/
theorem singular_subgroup_form_eq_zero
    {L V : Subgroup G} [IsElementaryAbelian 2 V]
    (hn : L ≤ normalizer (V : Set G)) (D : OrthogonalMarking L V hn)
    (hcontrol : ∀ v : V, D.Nonsingular v → Gv (v : G) ≤ M L)
    (E : Subgroup G) (hEV : E ≤ V)
    (hescape : ¬ centralizer (E : Set G) ≤ M L) :
    ∀ e : E,
      BinaryPermutation.TerminalOrthogonal.Eight.form
          (D.coordinates (Submodule.Quotient.mk
            (Additive.ofMul (show V from ⟨e.1, hEV e.2⟩)))) = 0 := by
  intro e
  by_contra hne
  exact singular_subgroup_of_nonsingular_centralizer hn D hcontrol E hEV hescape e hne

end CFSG.Quasithin.Chapter12.Section06
