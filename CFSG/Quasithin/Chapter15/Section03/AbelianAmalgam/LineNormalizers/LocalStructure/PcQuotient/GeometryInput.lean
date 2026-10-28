module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.Definitions
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Orthogonal.SylowTransport


/-!
# The finite Sylow action needed for P_c

`NormalSylowLineMovement` states the remaining finite model calculation:
a nontrivial normal subgroup of a Sylow two-subgroup of the actual binary
orthogonal group has an element preserving the selected singular line
and moving one of its vectors. The source proves this using the central
involution of the dihedral Sylow subgroup.

The transport theorem below derives nontrivial `P_c` action from that
model calculation and 15.3.49(2). In particular the commutator with `Z_S`
is used only to show that the image of `O₂(M_c)` is nontrivial. It is not
restricted to `P_c`: the central involution can fix `Z_S` while moving `E`.
The model proposition remains to be proved in the separate `SylowCenter`
leaf before the source result can be assembled.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1153, using 15.3.49(2) and the selection before 15.3.66.
-/

@[expose] public section

open Subgroup OrthogonalFourBinary OrthogonalFourBinary.TerminalLines
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.LocalRelations.OrthogonalProducts
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure

/-- The precise finite action calculation for the selected singular line. -/
def NormalSylowLineMovement : Prop :=
  ∀ (P : Sylow 2 OrthogonalFourBinary.IsometryGroup) (L : Subgroup (Multiplicative Space)),
    Nat.card L = 4 → (∀ v ∈ L, form v.toAdd = 0) →
    ∀ S : Sylow 2 (lineStabilizer L),
      (S : Subgroup (lineStabilizer L)).map (lineStabilizer L).subtype =
        (P : Subgroup OrthogonalFourBinary.IsometryGroup) ⊓ lineStabilizer L →
    ∀ Q : Subgroup OrthogonalFourBinary.IsometryGroup, Q ≤ P →
      (P : Subgroup OrthogonalFourBinary.IsometryGroup) ≤ normalizer (Q : Set OrthogonalFourBinary.IsometryGroup) → Q ≠ ⊥ →
      ∃ g ∈ Q ⊓ lineStabilizer L, ∃ v ∈ L, vectorAction g v ≠ v

variable {G : Type*} [Group G] [Finite G] {V M : Subgroup G}

/-- Transport the finite calculation through the genuine compatible action.
All relative normalization and the nontrivial core image are proved here. -/
theorem linePc_noncentral_of_model (hmodel : NormalSylowLineMovement)
    (d : NaturalAction V M) (T : Sylow 2 G) (Mc E Zs Z : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (hTMc : (T : Subgroup G) ≤ Mc)
    (hcore : Stellmacher.twoCoreAmbient Mc ≤ T)
    (hZsV : Zs ≤ V) (hZ : Z ≠ ⊥) (h49 : ⁅Zs, Mc.pCoreIn 2⁆ = Z)
    (hEV : E ≤ V) (hcard : Nat.card E = 4)
    (hs : ∀ e : E, d.singular ⟨e,hEV e.property⟩)
    (P : Sylow 2 (lineM M E))
    (hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype = lineT T E) :
    ¬ linePc Mc E ≤ lineC E := by
  let Qc := Mc.pCoreIn 2
  have hQcT : Qc ≤ T := hcore
  have hQcM : Qc ≤ M := hQcT.trans hTM
  let Q := actionImage d Qc
  have hQne : Q ≠ ⊥ := by
    intro hbot
    have hc : Qc ≤ centralizer (V : Set G) := by
      intro q hq
      let m : M := ⟨q,hQcM hq⟩
      have hm : d.action m ∈ Q := mem_map_of_mem _ hq
      rw [hbot] at hm
      have hk : m ∈ d.action.ker := hm
      rwa [action_ker d] at hk
    have hc' : Qc ≤ centralizer (Zs : Set G) := hc.trans (centralizer_le hZsV)
    apply hZ
    rw [← h49, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc'
  have hTQc : (T : Subgroup G) ≤ normalizer (Qc : Set G) :=
    hTMc.trans (Mc.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc)))
  have hsub : ((T : Subgroup G).subgroupOf M) ≤ normalizer (Qc.subgroupOf M : Set M) := by
    intro m hm q
    exact hTQc hm q
  have hTQ : actionImage d (T : Subgroup G) ≤ normalizer (Q : Set OrthogonalFourBinary.IsometryGroup) :=
    (map_mono hsub).trans (le_normalizer_map d.action)
  obtain ⟨S,hS⟩ := actionImage_sylow d T hTM
  obtain ⟨R,hR⟩ := coordinateLine_sylow d T E hEV P hP
  rw [← hS] at hR
  have hQS : Q ≤ S := hS.symm ▸ map_mono (subgroupOf_mono M hQcT)
  have hSQ : (S : Subgroup OrthogonalFourBinary.IsometryGroup) ≤ normalizer (Q : Set OrthogonalFourBinary.IsometryGroup) := hS ▸ hTQ
  obtain ⟨g,hg,v,hv,hmove⟩ := hmodel S (coordinateLine d E)
    ((coordinateLine_card d E hEV).trans hcard) (coordinateLine_singular d E hEV hs)
    R hR Q hQS hSQ hQne
  obtain ⟨m,hm,hmg⟩ := hg.1
  subst g
  have hmE := (coordinateLine_stabilizer_iff d E hEV m).mp hg.2
  intro hcentral
  have hc := hcentral (show (m : G) ∈ linePc Mc E from ⟨hm,hmE⟩)
  exact hmove ((coordinateLine_pointwise_iff d E hEV m).mpr hc v hv)
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
