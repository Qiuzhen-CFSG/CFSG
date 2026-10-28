module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.KernelReduction
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# The Frattini fixed-subgroup product in Lemma 12.8.9(5)

For the supplied Sylow T, R = C_T(Û) is Sylow in the actual action kernel
C_H(Û). Frattini gives H = N_H(R) C_H(Û). The intersection V ∩ Z(U) = V₁
makes R fix Ṽ₂, and N_H(R) preserves its common fixed subgroup Ṽ₀.
The image of Ṽ₀ under the literal equivariant map Ũ → Û is therefore
H-invariant and contains V̂₂. Generation U = ⟨V₂ᴴ⟩ makes that image all of
Û, giving Ũ = Ṽ₀ Z̃(U). We apply this product to the existing fixed-vector
and action-kernel reductions.

Only the preceding-source inputs 12.8.8(3) and (6) are retained for the
product, with the finite ambient group and invariant abelian flag. The
kernel application also retains the earlier commutator and parabolic
fixed-space inputs; their source assembly belongs to Parabolic.Actions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.9(5), printed p.853, PDF p.870.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The actual R = C_T(Û) is the image of a Sylow subgroup of C_H(Û). -/
theorem exists_sylow_map_eq_rHat [Finite G] (F : InvariantFlag T V n) :
    ∃ Q : Sylow 2 F.uhatAction.ker,
      (Q : Subgroup F.uhatAction.ker).map F.uhatAction.ker.subtype = F.rHat := by
  let S : Sylow 2 F.H := T.subtype (F.invariant 1)
  exact S.exists_sylow_map_eq_inf_of_normal F.uhatAction.ker

/-- Frattini in H, with its normal subgroup C_H(Û) and the original R. -/
theorem rHat_frattini [Finite G] (F : InvariantFlag T V n) :
    normalizer (F.rHat : Set F.H) ⊔ F.uhatAction.ker = ⊤ := by
  obtain ⟨Q, hQ⟩ := F.exists_sylow_map_eq_rHat
  have h := Q.normalizer_sup_eq_top
  change normalizer ((Q : Subgroup F.uhatAction.ker).map F.uhatAction.ker.subtype : Set F.H)
    ⊔ F.uhatAction.ker = ⊤ at h
  rwa [hQ] at h

/-- T normalizes V₂, so the R-commutators lie in V ∩ Z(U) = V₁ by
12.8.8(3). Consequently R fixes the actual tilded plane. -/
theorem tilde_plane_le_rFixedTilde (F : InvariantFlag T V n) [IsMulCommutative V]
    (hcenter : V ⊓ F.ZU = F.Vi 1) :
    (F.tilde (F.Vi 2)).subgroupOf (F.tilde F.U) ≤ F.rFixedTilde := by
  intro a ha
  obtain ⟨u, rfl⟩ := F.tildeMap_surjective F.U F.U_le_H a
  have hu : (u : G) ∈ F.Vi 2 :=
    (F.mem_tilde_iff_of_point_le (F.Vi 2) (F.monotone (by omega))
      ⟨u, F.U_le_H u.property⟩).mp ha
  apply (MonoidHom.mem_commonFixed (F.localTildeAction F.H le_rfl) F.rHat _).mpr
  intro r hr
  have hz : ⁅(r : G), (u : G)⁆ ∈ F.ZU :=
    (F.mem_uhatAction_ker_iff r).mp hr.2 u u.property
  have hv : ⁅(r : G), (u : G)⁆ ∈ V := by
    apply F.le_seed 2
    simpa only [commutatorElement_def, Subgroup.coe_subtype] using (F.Vi 2).mul_mem
      ((mem_normalizer_iff.mp (F.invariant 2 hr.1) u).mp hu) ((F.Vi 2).inv_mem hu)
  have hp : ⁅(r : G), (u : G)⁆ ∈ F.Vi 1 :=
    hcenter ▸ (show ⁅(r : G), (u : G)⁆ ∈ V ⊓ F.ZU from ⟨hv, hz⟩)
  change F.tildeAction F.H F.U le_rfl (le_normalizer_conjugateSpanBy V F.H) r
    (F.tildeMap F.U F.U_le_H u) = _
  rw [F.tildeAction_apply_map F.H F.U le_rfl F.U_le_H]
  apply Subtype.ext
  change F.tildeProjection _ = F.tildeProjection _
  apply QuotientGroup.eq_iff_div_mem.mpr
  change (r : G) * u * (r : G)⁻¹ / u ∈ F.Vi 1
  simpa only [commutatorElement_def, div_eq_mul_inv] using hp


/-- The actor normalizer preserves the common fixed subgroup on the literal image. -/
theorem rFixedTilde_map_normalizer (F : InvariantFlag T V n) (h : F.H)
    (hh : h ∈ normalizer (F.rHat : Set F.H)) :
    F.rFixedTilde.map (F.localTildeAction F.H le_rfl h).toMonoidHom = F.rFixedTilde :=
  MonoidHom.commonFixed_map_of_normalizes (F.localTildeAction F.H le_rfl) F.rHat h hh

private theorem rFixedTilde_image_invariant [Finite G] (F : InvariantFlag T V n) [IsMulCommutative V]
    (hn : 1 ≤ n) (h : F.H) {a : F.Uhat}
    (ha : a ∈ F.rFixedTilde.map (F.tildeToUhat hn)) :
    F.uhatAction h a ∈ F.rFixedTilde.map (F.tildeToUhat hn) := by
  have hh : h ∈ normalizer (F.rHat : Set F.H) ⊔ F.uhatAction.ker := by
    rw [rHat_frattini F]
    exact mem_top h
  obtain ⟨b, hb, c, hc, rfl⟩ := mem_sup_of_normal_right.mp hh
  have hc' : F.uhatAction c = 1 := hc
  rw [map_mul, MulAut.mul_apply, hc']
  change F.uhatAction b a ∈ _
  obtain ⟨v, hv, rfl⟩ := ha
  refine ⟨F.localTildeAction F.H le_rfl b v, ?_, F.tildeToUhat_equivariant hn b v⟩
  have hm : F.localTildeAction F.H le_rfl b v ∈
      F.rFixedTilde.map (F.localTildeAction F.H le_rfl b).toMonoidHom := ⟨v, hv, rfl⟩
  rw [F.rFixedTilde_map_normalizer b hb] at hm
  exact hm

/-- The fixed subgroup surjects onto Û: its image is H-invariant by
Frattini and contains V̂₂, which generates Û by 12.8.8(6). -/
theorem rFixedTilde_image_eq_top [Finite G] (F : InvariantFlag T V n) [IsMulCommutative V]
    (hn : 1 ≤ n) (hcenter : V ⊓ F.ZU = F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) :
    F.rFixedTilde.map (F.tildeToUhat hn) = ⊤ := by
  let D := F.rFixedTilde.map (F.tildeToUhat hn)
  let q := QuotientGroup.mk' (center F.U)
  let K := (D.comap q).map F.U.subtype
  have hseed : F.Vi 2 ≤ K := by
    intro v hv
    let u : F.U := ⟨v, (F.le_seed 2).trans (le_conjugateSpanBy V F.H) hv⟩
    have ht : F.tildeMap F.U F.U_le_H u ∈
        (F.tilde (F.Vi 2)).subgroupOf (F.tilde F.U) :=
      ⟨⟨v, F.U_le_H u.property⟩, hv, rfl⟩
    exact ⟨u, ⟨F.tildeMap F.U F.U_le_H u,
      tilde_plane_le_rFixedTilde F hcenter ht, F.tildeToUhat_apply_map hn u⟩, rfl⟩
  have hnorm : F.H ≤ normalizer (K : Set G) := by
    apply le_normalizer_iff.mpr
    rintro h hh x ⟨u, hu, rfl⟩
    refine ⟨F.uAction ⟨h, hh⟩ u, ?_, rfl⟩
    change q (F.uAction ⟨h, hh⟩ u) ∈ D
    rw [← F.uhatAction_apply_mk]
    exact rFixedTilde_image_invariant F hn ⟨h, hh⟩ hu
  have hUK : F.U ≤ K := by
    rw [hspan]
    exact conjugateSpanBy_le hseed hnorm
  apply top_unique
  intro a _
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center F.U) a
  obtain ⟨v, hv, he⟩ := hUK u.property
  have he' : v = u := Subtype.ext he
  exact he' ▸ hv

/-- The Frattini product used in 12.8.9(5), from exactly the center
intersection of 12.8.8(3) and the generation equality of 12.8.8(6). -/
theorem rFixedTilde_sup_center_eq_top [Finite G] (F : InvariantFlag T V n) [IsMulCommutative V]
    (hn : 1 ≤ n) (hcenter : V ⊓ F.ZU = F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) :
    F.rFixedTilde ⊔ (F.tilde F.ZU).subgroupOf (F.tilde F.U) = ⊤ := by
  have he := congrArg (fun D : Subgroup F.Uhat => D.comap (F.tildeToUhat hn))
    (rFixedTilde_image_eq_top F hn hcenter hspan)
  rwa [comap_map_eq, comap_top, F.tildeToUhat_ker hn] at he

/-- The join is the literal product Ũ = C_{Ũ}(C_T(Û)) Z̃(U).
Normality of the second factor follows from the kernel of Ũ → Û. -/
theorem rFixedTilde_center_factorization [Finite G] (F : InvariantFlag T V n) [IsMulCommutative V]
    (hn : 1 ≤ n) (hcenter : V ⊓ F.ZU = F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (u : F.tilde F.U) :
    ∃ a ∈ F.rFixedTilde, ∃ z ∈ (F.tilde F.ZU).subgroupOf (F.tilde F.U), a * z = u := by
  have : ((F.tilde F.ZU).subgroupOf (F.tilde F.U)).Normal := by
    rw [← F.tildeToUhat_ker hn]
    infer_instance
  apply mem_sup_of_normal_right.mp
  rw [rFixedTilde_sup_center_eq_top F hn hcenter hspan]
  exact mem_top u

/-- Apply the proved product to obtain the vector outside W̃ used in
12.8.9(5); nonabelianness makes W proper, without assuming such a vector. -/
theorem exists_rFixedTilde_outside_W_of_source [Finite G] (F : InvariantFlag T V n) [IsMulCommutative V]
    (hn : 1 ≤ n) (hcenter : V ⊓ F.ZU = F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H)
    (hnonab : ¬ IsMulCommutative F.U) :
    ∃ a : F.tilde F.U, a ∈ F.rFixedTilde ∧ (a : F.G₁tilde) ∉ F.tilde F.W :=
  F.exists_rFixedTilde_outside_W (F.U_not_le_W hspan hnonab)
    (rFixedTilde_sup_center_eq_top F hn hcenter hspan)

/-- Discharge the Frattini-product premise in the actual kernel reduction.
The remaining inputs are [U,U] ≤ V₁ from 12.8.4(2), the two stated
12.8.8 inputs, X ≤ T (provided by `X_le_T_of_core` from 12.8.9(1–2)),
and the commutator pullback of 12.8.9(3), provided by
`parabolicFixedSpace_commutator`. No product or fixed vector is assumed. -/
theorem action_kernels_eq_of_source_frattini [Finite G] (F : InvariantFlag T V n)
    [IsMulCommutative V] (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hn : 2 ≤ n) (g : G) (hgP : g ∈ F.P L)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (hcenter : V ⊓ F.ZU = F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hnonab : ¬ IsMulCommutative F.U)
    (hXT : F.X g ≤ (T : Subgroup G))
    (hfixed : ∀ u ∈ F.U, u ∉ F.W → ∀ s ∈ F.W ⊔ F.X g,
      ⁅s, u⁆ ∈ F.E g → s ∈ F.W) :
    F.xHatKernel g (F.P_le_G₂ hn L hL hgP) = F.E g ∧
      F.xTildeKernel g (F.P_le_G₂ hn L hL hgP) = F.E g :=
  F.action_kernels_eq_of_frattini_product L hL hn g hgP hcomm hspan hnonab hXT hfixed
    (rFixedTilde_sup_center_eq_top F (by omega) hcenter hspan)

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
