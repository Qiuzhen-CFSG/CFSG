module
public import Theory.Representation.PSL3Two.DoubledOffenders
public import Theory.SpecificGroups.PSL3Two.Parabolics.ShearNormalizer

/-!
# The local line flag in a doubled natural module

The unique offender in a Sylow two-subgroup is the line radical. A local
overgroup normalizing a two-subgroup that contains this offender normalizes
the radical itself. The radical normalizer has order24, so a non-two-group
over the Sylow subgroup is exactly the line parabolic. The Sylow, radical,
and parabolic are returned in one matrix marking.

Source: Aschbacher–Smith13.7.16(2), printed p.944, using B.2.20.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G X : Type*} [_root_.Group G] [AddCommGroup X] [Module (ZMod 2) X]
  [FiniteDimensional (ZMod 2) X]

theorem normalizes_unique_offender (ρ : Representation (ZMod 2) G X)
    (P N S D : Subgroup G) (hPN : P ≤ normalizer N)
    (hDN : D ≤ N) (hNS : N ≤ S) (hD : IsOffender ρ D)
    (huniq : ∀ E, E ≤ S → IsOffender ρ E → E = D) : P ≤ normalizer D := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply huniq
  · exact (map_mono hDN).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (hPN hg)) |>.trans hNS
  · refine ⟨hD.1.map_conj g, ?_⟩
    change fixedCodim ρ (D.map (MulAut.conj g).toMonoidHom) ≤ rank (D.map (MulAut.conj g).toMonoidHom)
    rw [fixedCodim_map_conj,rank_map_conj]
    exact hD.2
end Representation.BinaryOffender

namespace BinaryLinearThree.DoubledOffenders
open Matrix.PSL3Two BinaryLinearThree
open scoped Pointwise
variable {G X : Type*} [_root_.Group G] [Finite G] [AddCommGroup X]
 [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]

theorem doubled_local_line_flag (ρ : Representation (ZMod 2) G X)
    (e : G ≃* SL) (b : X ≃ₗ[ZMod 2] (Vector × Vector))
    (hb : ∀ x v, b (ρ x v) = (W.prod W) (e x) (b v))
    (S : Sylow 2 G) (P N D : Subgroup G)
    (hSP : (S : Subgroup G) ≤ P) (hPN : P ≤ normalizer N)
    (hDN : D ≤ N) (hNS : N ≤ (S : Subgroup G)) (hD : IsOffender ρ D)
    (hP : ¬ IsPGroup 2 P) :
    ∃ g : SL,
      (S : Subgroup G).map e.toMonoidHom = borelSL.map (MulAut.conj g).toMonoidHom ∧
      P.map e.toMonoidHom = lineParabolicSL.map (MulAut.conj g).toMonoidHom ∧
      D.map e.toMonoidHom = R.map (MulAut.conj g).toMonoidHom := by
  let S' : Sylow 2 SL := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let B' : Sylow 2 SL := Sylow.ofCard borelSL (by rw [card_borelSL,card_SL]; decide +kernel)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL B' S'
  have hS : (S : Subgroup G).map e.toMonoidHom =
      borelSL.map (MulAut.conj g).toMonoidHom := by
    change (S' : Subgroup SL) = _
    rw [←hg,Sylow.coe_subgroup_smul]
    rfl
  have huniq : ∀ E, E ≤ (S : Subgroup G) → IsOffender ρ E →
      E.map e.toMonoidHom = R.map (MulAut.conj g).toMonoidHom := by
    intro E hES hE
    apply (DoubledOffenders.offender_borel_conjugate_iff g _ ?_).mp
    · exact hE.map_equivariant ρ (W.prod W) e.toMonoidHom e.injective b hb
    · rw [←hS]; exact map_mono hES
  have hDm := huniq D (hDN.trans hNS) hD
  have hPD := normalizes_unique_offender ρ P N (S : Subgroup G) D hPN hDN hNS hD (by
    intro E hES hE
    exact map_injective e.injective ((huniq E hES hE).trans hDm.symm))
  have hPm : P.map e.toMonoidHom ≤
      lineParabolicSL.map (MulAut.conj g).toMonoidHom := by
    have hh := (map_mono (f := e.toMonoidHom) hPD).trans
      (D.le_normalizer_map e.toMonoidHom)
    rwa [hDm,normalizer_shear_conjugate] at hh
  have h8 : 8 ∣ Nat.card (P.map e.toMonoidHom) := by
    have hh := card_dvd_of_le (map_mono (f := e.toMonoidHom) hSP)
    rw [hS,card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective,card_borelSL] at hh
    exact hh
  have hc : Nat.card (lineParabolicSL.map (MulAut.conj g).toMonoidHom) = 24 := by
    rw [card_map_of_injective (MulAut.conj g).injective,card_lineParabolicSL]
  have h24 := card_dvd_of_le hPm
  rw [hc] at h24
  have hle := Nat.le_of_dvd (by decide : 0 < 24) h24
  have hn := Nat.card_pos (α := P.map e.toMonoidHom)
  have h16 : Nat.card (P.map e.toMonoidHom) ≠ 16 := by intro he; rw [he] at h24; norm_num at h24
  have hcard : Nat.card (P.map e.toMonoidHom) = 8 ∨
      Nat.card (P.map e.toMonoidHom) = 24 := by omega
  have he : P.map e.toMonoidHom = lineParabolicSL.map (MulAut.conj g).toMonoidHom := by
    rcases hcard with hcard | hcard
    · exact (hP ((IsPGroup.of_card (n := 3) hcard).of_equiv (e.subgroupMap P).symm)).elim
    · exact eq_of_le_of_card_ge hPm (by omega)
  exact ⟨g,hS,he,hDm⟩
end BinaryLinearThree.DoubledOffenders
