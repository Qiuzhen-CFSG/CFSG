module

public import Theory.GroupTheory.PResidual.PerfectCover
public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.MixedAction
public import CFSG.Quasithin.Chapter2.Section05.PSL2PairSource.PrimeFrattini
public import Theory.Frattini.SquareImage

/-!
# The mixed-action Frattini contradiction

The actions of C_K(tᵍ) and C_{Kˣ}(tᵍ) commute. The proved full-automorphism
centralizer bound kills the latter group's Frattini subgroup. When the
original t is its marked Frattini element, Kᵍ centralizes t. Functoriality
of the two-residual and equal orders then give Kᵍ = K, contradicting the
nontrivial action of tᵍ on K.

The aligned-action theorem derives the Frattini premise from the actual
inner-involution model. The preceding source case analysis must still
supply the odd-dihedral outer fixed subgroup and align the inner action.
Neither is replaced by a hypothesis asserting marked fusion or the final
source contradiction.

Source: Aschbacher–Smith, proof of 2.5.21, printed p.567.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.CounterexampleGeometry
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter2.PSL2PairSource
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
variable {p : ℕ} [Fact p.Prime]
namespace Incoming
variable (d : Incoming κ G p)

/-- The source's mixed-action Frattini calculation. The odd-dihedral model
and the marked Frattini membership are the two remaining local model inputs. -/
theorem mixed_frattini_centralizes (g : G)
    {n : ℕ} (hn : Odd n) (hne : n ≠ 1)
    (e : (d.K ⊓ centralizer ({g⁻¹ * d.t * g} : Set G) : Subgroup G) ≃*
      DihedralGroup n)
    (htphi : d.t ∈ (frattini (conjugate d.K d.x ⊓
      centralizer ({g⁻¹ * d.t * g} : Set G) : Subgroup G)).map
        (conjugate d.K d.x ⊓ centralizer ({g⁻¹ * d.t * g} : Set G)).subtype) :
    conjugate d.K g ≤ centralizer ({d.t} : Set G) := by
  let I := centralizer ({g⁻¹ * d.t * g} : Set G)
  let B := conjugate d.K d.x ⊓ I
  let C := d.K ⊓ I
  let rho : I →* MulAut (conjugate d.K g) :=
    (conjugate d.K g).normalizerMonoidHom.comp (inclusion (d.conjugate_normalized g))
  let f : B →* MulAut (conjugate d.K g) := rho.comp (inclusion inf_le_right)
  have hs (b : B) : f b ^ 2 = 1 := by
    apply d.mixed_action_centralizer_square g hn hne e
    rintro _ ⟨c, rfl⟩
    change rho (inclusion (show C ≤ I from inf_le_right) c) * f b =
      f b * rho (inclusion (show C ≤ I from inf_le_right) c)
    have hcomm : Commute (inclusion (show C ≤ I from inf_le_right) c)
        (inclusion (show B ≤ I from inf_le_right) b) := by
      apply Subtype.ext
      exact (commutator_eq_bot_iff_le_centralizer.mp d.commuting
        c.property.1 b.val b.property.1).symm
    exact (hcomm.map rho).eq
  obtain ⟨b, hb, hbt⟩ := htphi
  have hbker := frattini_le_ker_of_square_image f hs hb
  have hbn : inclusion ((show B ≤ I from inf_le_right).trans (d.conjugate_normalized g)) b ∈
      (conjugate d.K g).normalizerMonoidHom.ker := hbker
  rw [normalizerMonoidHom_ker] at hbn
  have htC : d.t ∈ centralizer (conjugate d.K g : Set G) := hbt ▸ hbn
  intro k hk
  exact mem_centralizer_singleton_iff.mpr (htC k hk)

/-- A conjugate of the residual K contained in C_G(t) must be K itself. -/
theorem conjugate_eq_of_le_centralizer (g : G)
    (hg : conjugate d.K g ≤ centralizer ({d.t} : Set G)) : conjugate d.K g = d.K := by
  let J := centralizer ({d.t} : Set G)
  let Q := conjugate d.K g
  have hKp := isPPerfect_embedded_pResidual 2 J
  rw [d.twoResidual_eq] at hKp
  let e : d.K ≃* Q := (MulAut.conj g⁻¹).subgroupMap d.K
  have hQp : IsPPerfect 2 Q := hKp.of_surjective e.toMonoidHom e.surjective
  let eJ := (subgroupOfEquivOfLe hg).symm
  have hR := le_pResidual_of_isPPerfect (Q.subgroupOf J)
    (hQp.of_surjective eJ.toMonoidHom eJ.surjective)
  have hle := map_mono (f := J.subtype) hR
  rw [map_subgroupOf_eq_of_le hg, d.twoResidual_eq] at hle
  apply eq_of_le_of_card_ge hle
  exact le_of_eq (Nat.card_congr e.toEquiv)

/-- The mixed case contradicts a nontrivial action on K once its actual
odd-dihedral model and marked Frattini membership have been constructed. -/
theorem false_of_mixed_frattini (g : G)
    {n : ℕ} (hn : Odd n) (hne : n ≠ 1)
    (e : (d.K ⊓ centralizer ({g⁻¹ * d.t * g} : Set G) : Subgroup G) ≃*
      DihedralGroup n)
    (htphi : d.t ∈ (frattini (conjugate d.K d.x ⊓
      centralizer ({g⁻¹ * d.t * g} : Set G) : Subgroup G)).map
        (conjugate d.K d.x ⊓ centralizer ({g⁻¹ * d.t * g} : Set G)).subtype)
    (hnc : g⁻¹ * d.t * g ∉ centralizer (d.K : Set G)) : False := by
  have he := d.conjugate_eq_of_le_centralizer g
    (d.mixed_frattini_centralizes g hn hne e htphi)
  have hKJ : d.K ≤ centralizer ({d.t} : Set G) := by
    rw [d.generated]
    exact le_sup_of_le_left le_sup_left
  have hKi := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hKJ
  rw [map_centralizer_equiv] at hKi
  change conjugate d.K g ≤ centralizer ((MulAut.conj g⁻¹) '' ({d.t} : Set G)) at hKi
  rw [Set.image_singleton, show (MulAut.conj g⁻¹) d.t = g⁻¹ * d.t * g by
    change g⁻¹ * d.t * (g⁻¹)⁻¹ = _; rw [inv_inv], he] at hKi
  apply hnc
  intro k hk
  exact mem_centralizer_singleton_iff.mp (hKi hk)

/-- Literal aligned inner action on Kˣ supplies the marked Frattini
membership used above; it is not an assumed Frattini conclusion. -/
theorem false_of_mixed_aligned_inner_action (g : G)
    {n : ℕ} (hn : Odd n) (hne : n ≠ 1)
    (e : (d.K ⊓ centralizer ({g⁻¹ * d.t * g} : Set G) : Subgroup G) ≃*
      DihedralGroup n)
    (hiL : g⁻¹ * d.t * g ∈ normalizer (conjugate d.K d.x : Set G))
    (haction : (conjugate d.K d.x).normalizerMonoidHom ⟨g⁻¹ * d.t * g, hiL⟩ =
      MulAut.conj (⟨d.t, d.mark_mem⟩ : conjugate d.K d.x))
    (hnc : g⁻¹ * d.t * g ∉ centralizer (d.K : Set G)) : False := by
  let L := conjugate d.K d.x
  let i := g⁻¹ * d.t * g
  have heC : L ⊓ centralizer ({i} : Set G) = L ⊓ centralizer ({d.t} : Set G) := by
    have hiff (a : G) (ha : a ∈ L) : a * i = i * a ↔ a * d.t = d.t * a := by
      have hh := congrArg (fun z : MulAut L => (z ⟨a, ha⟩ : G)) haction
      change i * a * i⁻¹ = d.t * a * d.t⁻¹ at hh
      constructor
      · intro h
        exact (mul_inv_eq_iff_eq_mul.mp
          (hh.symm.trans (mul_inv_eq_iff_eq_mul.mpr h.symm))).symm
      · intro h
        exact (mul_inv_eq_iff_eq_mul.mp
          (hh.trans (mul_inv_eq_iff_eq_mul.mpr h.symm))).symm
    ext a
    simp only [mem_inf, mem_centralizer_singleton_iff]
    exact and_congr_right (hiff a)
  apply d.false_of_mixed_frattini g hn hne e _ hnc
  change d.t ∈ (frattini (L ⊓ centralizer ({i} : Set G) : Subgroup G)).map
    (L ⊓ centralizer ({i} : Set G)).subtype
  rw [heC]
  let eL : L ≃* PSL(2, ZMod p) :=
    ((MulAut.conj d.x⁻¹).subgroupMap d.K).symm.trans d.model
  exact model_mark_mem_frattini_centralizer d.prime_ge d.parameter L eL d.mark_mem d.t_order

end Incoming
end CFSG.Quasithin.Chapter2.PSL2PairSource

end
