module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.Contracts
public import Theory.GroupTheory.InvolutionClosedTransfer
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.BSWSetup
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.SmallBranch

/-!
# Transfer and recognition in the literal central quotient

An elementary Sylow two-subgroup and an index-two subgroup closed under
involution fusion give a normal transfer kernel in C_G(t)/⟨t⟩. If that
kernel has one involution class and a four-group centralizer, the checked
Brauer–Suzuki–Wall theorem recognizes A₄ or A₅. The former forces
|C_G(t)| = 48; excluding this order gives A₅ and |C_G(t)| = 240.

The earlier local frame also identifies fusion on E U and computes
N_G(U) = X₃ C_G(t), conditional on the splitting step centralizing U.
These results retain their explicit geometric premises: they do not
construct the source frame or prove the split extension.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1(1), printed p.260.
The A₄/A₅ recognition route uses Aschbacher–Smith I.4.1(1), p.415,
in place of the source citation to FGT Exercise 16.6.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer

variable {G : Type*} [Group G]

theorem quotientKernel_card {t : G} (ht : orderOf t = 2) :
    Nat.card (quotientKernel t) = 2 := by
  rw [quotientKernel, Nat.card_zpowers, ← orderOf_coe]
  exact ht

theorem centralizer_card_eq_four_mul {t : G} (ht : orderOf t = 2)
    (M : Subgroup (CentralQuotient t)) (hM : M.index = 2) :
    Nat.card (involutionCentralizer t) = 4 * Nat.card M := by
  have hq := (quotientKernel t).index_mul_card
  have hm := M.index_mul_card
  rw [quotientKernel_card ht] at hq
  rw [hM] at hm
  change Nat.card (CentralQuotient t) * 2 = _ at hq
  omega

variable [Finite G]

theorem TransferData.exists_kernel {t : G} (F : TransferData t) :
    Nonempty (TransferKernel F) := by
  have hpow (x : F.S) : x ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp F.elementary.exponent_dvd_p x
  have hproper : F.E ≠ ⊤ := by
    intro he
    have hi := F.index
    simp [he] at hi
  obtain ⟨w, hw⟩ := SetLike.exists_not_mem_of_ne_top F.E hproper
  have hwne : w ≠ 1 := fun he => hw (he ▸ F.E.one_mem)
  have hwo : orderOf w = 2 := orderOf_eq_prime (hpow w) hwne
  obtain ⟨M, hnormal, hindex, hinter⟩ :=
    F.S.exists_normal_index_two_of_involution_fusion F.E F.index
      (fun x hx => subset_closure ⟨hx, hpow x⟩) F.closed w hwo hw
  exact ⟨⟨M, hnormal, hindex, hinter⟩⟩

theorem TransferKernel.equiv_alternating_five {D : Seed G} {t : G}
    (ht : OtherInvolution D t) (hsmall : Nat.card (involutionCentralizer t) ≠ 48)
    {F : TransferData t} (K : TransferKernel F)
    (hlocal : DihedralInvolutionCentralizerHypotheses K.M 2) :
    Nonempty (K.M ≃* A5) := by
  obtain ⟨b, _, _, hb⟩ := hlocal.exists_brauerSuzukiWallHypotheses
  have hb2 : Nat.card b.K = 2 := by simpa using hb
  rcases alternating_four_or_five_of_bsw_card_two b hb2 with h4 | h5
  · obtain ⟨e4⟩ := h4
    have hc : Nat.card K.M = 12 :=
      (Nat.card_congr e4.toEquiv).trans
        (alternatingGroup.card_of_card_eq_four (by simp))
    have he := centralizer_card_eq_four_mul ht.1 K.M K.index
    exact (hsmall (by omega)).elim
  · exact h5

omit [Finite G] in
theorem TransferKernel.centralizer_card {t : G} (ht : orderOf t = 2)
    {F : TransferData t} (K : TransferKernel F) (e : K.M ≃* A5) :
    Nat.card (involutionCentralizer t) = 240 := by
  rw [centralizer_card_eq_four_mul ht K.M K.index,
    Nat.card_congr e.toEquiv, card_A5]

namespace LocalFrame
variable {D : Seed G} {t : G} (F : LocalFrame D t)

theorem join_le_centralizer : F.E ⊔ F.U ≤ involutionCentralizer t := by
  rw [← F.A_eq]
  exact map_subtype_le _

theorem join_le_source_centralizer : F.E ⊔ F.U ≤ involutionCentralizer D.z := by
  rw [← F.double_centralizer]
  exact inf_le_right

include F in
theorem z_commutes : Commute D.z t :=
  (mem_centralizer_singleton_iff.mp
    (F.join_le_source_centralizer (mem_sup_right F.t_mem))).symm

theorem E_le_core : F.E ≤ ambientCore D.z := by
  rw [← F.core_intersection]
  exact inf_le_right

theorem involution_fusion (L : LocalCensus D) {u : G}
    (hu : u ∈ F.E ⊔ F.U) (ho : orderOf u = 2) :
    IsConj D.z u ↔ u ∈ F.E := by
  rw [L.core_fusion u (F.join_le_source_centralizer hu) ho]
  constructor
  · intro hc
    exact F.core_intersection ▸ (show u ∈ (F.E ⊔ F.U) ⊓ ambientCore D.z from ⟨hu, hc⟩)
  · exact fun he => F.E_le_core he

theorem other_of_mem_U (L : LocalCensus D) {u : G}
    (hu : u ∈ F.U) (hne : u ≠ 1) : OtherInvolution D u := by
  let : IsElementaryAbelian 2 (F.E ⊔ F.U : Subgroup G) := F.elementary
  have huo : orderOf u = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (A := F.E ⊔ F.U) u (mem_sup_right hu)) hne
  refine ⟨huo, fun hc => hne ?_⟩
  have he := (F.involution_fusion L (mem_sup_right hu) huo).mp hc
  exact (Subgroup.disjoint_def.mp F.disjoint) he hu

theorem centralizer_card_of_le_normalizer
    (hle : involutionCentralizer t ≤ normalizer (F.R : Set G)) :
    Nat.card (involutionCentralizer t) = 48 := by
  simpa only [inf_eq_left.mpr hle] using F.normalizer_intersection_card

theorem centralizer_not_le_normalizer
    (hsmall : Nat.card (involutionCentralizer t) ≠ 48) :
    ¬ involutionCentralizer t ≤ normalizer (F.R : Set G) :=
  fun hle => hsmall (F.centralizer_card_of_le_normalizer hle)

/-- After the splitting step centralizes the four-group, its full ambient
centralizer is exactly the original involution centralizer. -/
theorem centralizer_U_eq
    (hc : involutionCentralizer t ≤ centralizer (F.U : Set G)) :
    centralizer (F.U : Set G) = involutionCentralizer t := by
  refine le_antisymm ?_ hc
  intro g hg
  exact mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp hg t F.t_mem).symm)

/-- The cubic action supplies every coset of the involution centralizer in
the four-group normalizer. This keeps both subgroups embedded in G. -/
theorem normalizer_U_eq {t : G} {D : Seed G} (F : LocalFrame D t)
    (ht : t ≠ 1) (hc : involutionCentralizer t ≤ centralizer (F.U : Set G)) :
    normalizer (F.U : Set G) = F.X3 ⊔ involutionCentralizer t := by
  apply le_antisymm
  · intro g hg
    have hgt : g * t * g⁻¹ ∈ F.U := (hg t).mp F.t_mem
    have hgtne : g * t * g⁻¹ ≠ 1 := by
      intro he
      apply ht
      apply (MulAut.conj g).injective
      simpa only [MulAut.conj_apply, map_one] using he
    obtain ⟨x, hx⟩ := F.X3_transitive t F.t_mem ht _ hgt hgtne
    have hk : (x : G)⁻¹ * g ∈ involutionCentralizer t := by
      apply mem_centralizer_singleton_iff.mpr
      have he := congrArg (fun a : G => (x : G)⁻¹ * a * g) hx
      simpa only [inv_mul_cancel_left, inv_mul_cancel_right,
        mul_assoc, inv_mul_cancel, mul_one] using he.symm
    have hh := (F.X3 ⊔ involutionCentralizer t).mul_mem
      (mem_sup_left x.property) (mem_sup_right hk)
    simpa only [mul_inv_cancel_left] using hh
  · exact sup_le F.X3_normalizes (hc.trans (Subgroup.centralizer_le_normalizer _))

end LocalFrame

theorem QuotientGeometry.exists_recognized_kernel {D : Seed G} {t : G}
    {F : LocalFrame D t} (Q : QuotientGeometry F) (ht : OtherInvolution D t)
    (hsmall : Nat.card (involutionCentralizer t) ≠ 48) :
    ∃ K : TransferKernel Q.transfer, Nonempty (K.M ≃* A5) := by
  obtain ⟨K⟩ := Q.transfer.exists_kernel
  exact ⟨K, K.equiv_alternating_five ht hsmall (Q.kernel_local K).some⟩

theorem QuotientGeometry.centralizer_card {D : Seed G} {t : G}
    {F : LocalFrame D t} (Q : QuotientGeometry F) (ht : OtherInvolution D t)
    (hsmall : Nat.card (involutionCentralizer t) ≠ 48) :
    Nat.card (involutionCentralizer t) = 240 := by
  obtain ⟨K, ⟨e⟩⟩ := Q.exists_recognized_kernel ht hsmall
  exact K.centralizer_card ht.1 e

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer
