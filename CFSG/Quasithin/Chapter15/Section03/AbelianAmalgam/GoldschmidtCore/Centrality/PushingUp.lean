module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp.Control
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp.Endgame

/-!
# Excluding the noncentral-character branch of 15.3.68(2)

This is a conditional repair argument, independent of the producer of the
bad branch. In the application, H = G₀, K is the kernel of the action
character on B/O₂(B), T = T_E, X = X_E, P = G₁ ∩ K, U = V_E, and
W = Uˢ. The intrinsic R = O₂(P) is mapped into K and then into G.
All hypotheses below concern these actual subgroups, quotient maps and
conjugation actions. No conclusion of 15.3.68(2) is assumed.

The canonical component L = K∞ is the solvable-residual lift of K/O₂(K).
Its intrinsic properties and the actual doubled-natural action discharge
the premises of `DoubledNaturalSource`. B.2.3(4) and 15.3.67(2) exclude the
characteristic alternative. The block quotient has order eight and cannot
contain the fixed-point-free module of order 64. The remaining equality
U = [O₂(L),L] gives [O₂(K),L] ≤ U by perfectness and three-subgroups.
Since W centralizes U and lies in H, it lies in C_H(U) = O₂(K). Hence L
normalizes UW. Two-perfectness puts X first in K and then in L, and maximal
two-locality forces X ≤ N_G(UW) = M, a contradiction.

The universal earlier-source implication is intentionally an explicit
premise. The Chapter C source owner must prove its doubled-natural
specialization, and the parent centrality owner must instantiate it along
with the semilinear branch data before claiming literal 15.3.68(2).

The abandoned faithful-local-component route is not used: a component
lifting H/O₂(H) satisfies L O₂(H) = H, so adjoining ambient T generates
⟨H,T⟩. Source 68(3) forces that group's two-core to be trivial; the lift is
therefore not in the required local-component family. A T_E-local module
does not supply ambient-T faithfulness. Source 15.3.63–65 also supplies no
bound on the dimension of V_Mc. Existing diagnostics remain unchanged.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.3(3)–(4), C.1.7, C.1.30, C.1.37 (printed pp.42–43,123,135,141–143),
and 15.3.50, 15.3.67–68 (printed pp.1145,1152–1154).
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp
open Subgroup Theory.GroupTheory
universe u v
variable {G : Type u} [Group G] [Finite G]

/-- Normalizing a nontrivial elementary subgroup puts the character kernel
inside a genuine two-local, giving its SQTK hypothesis from the ambient group. -/
theorem sqtk_of_normal_elementary {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (K : Subgroup G) (U : Subgroup K) [U.Normal] [IsElementaryAbelian 2 U]
    (hne : U ≠ ⊥) : IsSQTK κ K := by
  let Ug := U.map K.subtype
  let : IsElementaryAbelian 2 Ug := IsElementaryAbelian.map K.subtype
  have hUg : Ug ≠ ⊥ := fun hb => hne ((U.map_eq_bot_iff_of_injective K.subtype_injective).mp hb)
  have hKN : K ≤ normalizer Ug := by
    have h := U.le_normalizer_map K.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h
  have hn := hG.twoLocal_sqtk (show IsTwoLocal (normalizer Ug) from
    ⟨Ug,hUg,IsElementaryAbelian.isPGroup 2 Ug,rfl⟩)
  exact (IsSQTK.equiv (subgroupOfEquivOfLe hKN)).mp (hn.subgroup _)

/-- The actual noncentral-character branch is impossible, conditional only
on the stated universal earlier-source implication and its producer's explicit
group and action data. No commutator bound or normalization by X is a premise. -/
theorem bad_character_excluded {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (hsource : DoubledNaturalSource κ)
    {C : Type v} [Group C]
    (M H K T X W : Subgroup G) (P U : Subgroup K) [U.Normal]
    (S : Sylow 2 K) (χ : H →* C)
    (hχ : IsPGroup 2 χ.range) (hK : χ.ker.map H.subtype = K)
    (hXH : X ≤ H) (hX : IsPPerfect 2 X) (hXM : ¬ X ≤ M)
    (hP : IsCoatom P) (hSP : (S : Subgroup K) ≤ P)
    (eK : (K ⧸ pCore 2 K) ≃* SL)
    (eU : U ≃* Multiplicative DoubleSpace)
    (hU : IsElementaryAbelian 2 U) (hUN : U ≤ pCore 2 K)
    (hC : H ⊓ centralizer (U.map K.subtype : Set G) = (pCore 2 K).map K.subtype)
    (hact : ∀ k u, Multiplicative.toAdd (eU (MulAut.conjNormal k u)) =
      fun j => Matrix.mulVec (eK (QuotientGroup.mk' (pCore 2 K) k)).val
        (Multiplicative.toAdd (eU u) j))
    (hBR : ChapterB.baumann T ≤ ((pCore 2 P).map P.subtype).map K.subtype)
    (hRT : ((pCore 2 P).map P.subtype).map K.subtype ≤ T)
    (hcontrol : characteristicNormalizerClosure (ChapterB.baumann T) ≤ M)
    (s : G) (hW : W = (U.map K.subtype).map (MulAut.conj s).toMonoidHom)
    (hWR : W ≤ ((pCore 2 P).map P.subtype).map K.subtype)
    (hcomm : ⁅W,U.map K.subtype⁆ = ⊥)
    (hM : IsMaximalTwoLocal M)
    (hMA : M ≤ normalizer (U.map K.subtype ⊔ W : Subgroup G)) : False := by
  let := hU
  have hne : U ≠ ⊥ := by
    have hc := doubled_card U eU
    intro hb
    simp [hb] at hc
  have hSQ : IsSQTK κ K := sqtk_of_normal_elementary hG K U hne
  have hXK := twoPerfect_le_character_kernel H K X χ hχ hK hXH hX
  have hKH : K ≤ H := by rw [← hK]; exact map_subtype_le _
  have hlocal := local_control hsource hSQ P U S hP hSP eK eU hU hUN
    (centralizer_restrict H K U hKH hC) hact (by
      intro C hCc hCn hCN
      let := hCc
      exact no_characteristic_baumann_normal K M T X ((pCore 2 P).map P.subtype)
        hBR hRT hcontrol hXK hXM C hCn hCN)
  have hWH : W ≤ H := hWR.trans ((map_subtype_le _).trans hKH)
  have hWe : IsElementaryAbelian 2 W := by
    rw [hW]
    let : IsElementaryAbelian 2 (U.map K.subtype) := IsElementaryAbelian.map K.subtype
    exact IsElementaryAbelian.map (MulAut.conj s).toMonoidHom
  exact ambient_endgame M H K X W U hXK hX eK hC hWH hcomm hlocal.2 hU hWe
    hne hM hMA hXM
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.PushingUp
