module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.Basic
public import Theory.SpecificGroups.BinaryLinear.CubicPairNormalizers.CoreAbsorption.Elementary
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.GroupTheory.Commutator.ConjugateSpan

/-!
# The original natural seed and the point commutator

The two-residual of the binary three-space point stabilizer contains the
shear toward the point and a cubic actor on the other two coordinates.
Their displacements span the whole natural module. The source's original
natural marking transports these elements through O²(L ∩ H), preserving
both the original seed V and its point z.

Thus V = [V,L₁]. Since L₁ ≤ K = O²(H) and K is normal in H, taking the
H-conjugate span gives U = [U,K]. In particular z belongs to [U,K], and
U lies in the actual O₂(K), as needed for the subsequent chief factors.
No earlier commutator equality or unrelated module action is assumed.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
14.7.48(2), printed p.1064; 14.7.68(2), printed pp.1071–1072.
-/

@[expose] public section
noncomputable section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 BinaryLinear.OuterCyclic
open BinaryLinear.CubicPairNormalizers.CoreAbsorption BinaryLinear.SmallParabolicLevi

private def pointActor : Subgroup (LinearGroup 3) where
  carrier := {g | g (Pi.single 0 1) = Pi.single 0 1}
  one_mem' := rfl
  mul_mem' := by intro a b ha hb; change a (b _) = _; rw [hb, ha]
  inv_mem' := by
    intro a ha
    change a.symm (Pi.single 0 1) = Pi.single 0 1
    apply a.injective
    simpa using ha.symm

private theorem root_in_point {r s : Fin 3} (hrs : r ≠ s) (hs : s ≠ 0) :
    root r s hrs 1 ∈ pointActor := by
  change root r s hrs 1 (Pi.single 0 1) = Pi.single 0 1
  ext k
  simp [root_apply, Pi.single_apply, hs]

private theorem first_root_residual : root (0 : Fin 3) 1 (by decide) 1 ∈
    (pResidual 2 pointActor).map pointActor.subtype := by
  apply root_mem_residual (fun i : Fin 3 => if i = 0 then 0 else 1) pointActor
  · intro r s hrs hle
    apply root_in_point hrs
    intro hs
    subst s
    simp [hrs] at hle
  · decide
  · exact Or.inr ⟨2, by decide, rfl⟩

private theorem cubic_residual : cubic (1 : Fin 3) 2 (by decide) ∈
    (pResidual 2 pointActor).map pointActor.subtype := by
  let c : pointActor := ⟨cubic 1 2 (by decide), pointActor.mul_mem
    (root_in_point (by decide) (by decide))
    (root_in_point (by decide) (by decide))⟩
  refine mem_map.mpr ⟨c, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  exact (by decide : Nat.Coprime 2 3).of_dvd_right
    (orderOf_dvd_of_pow_eq_one (show c ^ 3 = 1 from Subtype.ext (cubic_cube 1 2 (by decide))))

private theorem point_displacements_span (D : Submodule (ZMod 2) (Space 3))
    (hD : ∀ g ∈ (pResidual 2 pointActor).map pointActor.subtype,
      ∀ v, g v - v ∈ D) : D = ⊤ := by
  have h0 : Pi.single (0 : Fin 3) 1 ∈ D := by
    have h := hD _ first_root_residual (Pi.single 1 1)
    have he : root (0 : Fin 3) 1 (by decide) 1 (Pi.single 1 1) - Pi.single 1 1 =
        Pi.single 0 1 := by ext k; fin_cases k <;> simp [root_apply]
    rwa [he] at h
  have h1 : Pi.single (1 : Fin 3) 1 ∈ D := by
    have h := hD _ cubic_residual (Pi.single 2 1)
    have he : cubic (1 : Fin 3) 2 (by decide) (Pi.single 2 1) - Pi.single 2 1 =
        Pi.single 1 1 := by ext k; fin_cases k <;> simp [cubic, root_apply]
    rwa [he] at h
  have h2 : Pi.single (2 : Fin 3) 1 ∈ D := by
    have h := D.add_mem (hD _ cubic_residual (Pi.single 1 1)) h1
    have he : cubic (1 : Fin 3) 2 (by decide) (Pi.single 1 1) - Pi.single 1 1 +
        Pi.single 1 1 = Pi.single 2 1 := by
      ext k; fin_cases k <;> simp [cubic, root_apply]
    rwa [he] at h
  apply top_unique
  intro v _
  have he : v = ∑ i : Fin 3, v i • Pi.single i 1 := by ext k; simp [Pi.single_apply]
  rw [he]
  apply D.sum_mem
  intro i _
  apply D.smul_mem
  fin_cases i <;> assumption

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

namespace Data
variable (d : Data T L V F W)

include d in
/-- The actual point residual generates the original natural seed by commutators. -/
theorem seed_eq_commutator_point_residual : V = ⁅V, F.Li L 1⁆ := by
  let := d.natural.chosen.elementary
  let A := d.natural.naturalMarking
  have hzV : d.z ∈ V := F.le_seed 1 (d.point ▸ mem_zpowers d.z)
  let zV : Additive V := Additive.ofMul ⟨d.z, hzV⟩
  have hz0 : A.coordinates zV ≠ 0 := by
    intro he
    have hz : zV = 0 := A.coordinates.map_eq_zero_iff.mp he
    exact d.z_ne_one (congrArg (fun v : Additive V => (v.toMul : G)) hz)
  obtain ⟨e, he⟩ := exists_linearEquiv_apply_eq hz0
    (show (Pi.single (0 : Fin 3) (1 : ZMod 2)) ≠ 0 from by
      intro h; have hh := congrFun h 0; simp at hh)
  let b := A.coordinates.trans e
  let q : L →* LinearGroup 3 := (linearGroupCongr e).toMonoidHom.comp
    (A.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))
  have hq : Function.Surjective q := (linearGroupCongr e).surjective.comp
    (A.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))
  have hbz : b zV = Pi.single 0 1 := he
  have hact (l : L) (v : Additive V) :
      b (Additive.ofMul ⟨(l : G) * v.toMul * (l : G)⁻¹,
        (mem_normalizer_iff.mp (d.natural.chosen.normalizes l.property) v.toMul).mp
          v.toMul.property⟩) = q l (b v) := by
    change e (A.coordinates _) = linearGroupCongr e _ (e (A.coordinates v))
    rw [A.equivariant, linearGroupCongr_apply, e.symm_apply_apply]
    rfl
  have hmem (l : L) : (l : G) ∈ F.H ↔ q l ∈ pointActor := by
    rw [d.centralizer_eq, mem_centralizer_singleton_iff]
    change (l : G) * d.z = d.z * (l : G) ↔ q l (Pi.single 0 1) = Pi.single 0 1
    rw [← hbz, ← hact l zV, b.injective.eq_iff]
    rw [Additive.ofMul.injective.eq_iff, Subtype.ext_iff]
    change (l : G) * d.z = d.z * (l : G) ↔ (l : G) * d.z * (l : G)⁻¹ = d.z
    exact ⟨fun h => by rw [h, mul_inv_cancel_right], fun h => by
      have hh := congrArg (fun x : G => x * l) h
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh⟩
  let N : Subgroup G := L ⊓ F.H
  let f : N →* pointActor :=
    ((q.comp (inclusion (inf_le_left : N ≤ L))).codRestrict pointActor
      (fun x => (hmem ⟨x, x.property.1⟩).mp x.property.2))
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨l, hl⟩ := hq g
    refine ⟨⟨l, l.property, (hmem l).mpr (hl ▸ g.property)⟩, ?_⟩
    exact Subtype.ext hl
  have hres : F.Li L 1 = (pResidual 2 N).map N.subtype := by
    simp only [InvariantFlag.Li, show ¬ (3 = 5 ∧ (1 = 2 ∨ 1 = 3)) by decide,
      if_false]; rfl
  let C : Subgroup G := ⁅V, F.Li L 1⁆
  let D₀ : Submodule (ZMod 2) (Additive V) := (C.subgroupOf V).toAddSubgroup.toZModSubmodule 2
  let D := D₀.map b.toLinearMap
  have hD : D = ⊤ := by
    apply point_displacements_span
    intro g hg v
    obtain ⟨g₀, hg₀, rfl⟩ := mem_map.mp hg
    rw [← map_pResidual_of_surjective 2 f hf] at hg₀
    obtain ⟨x, hx, hfx⟩ := mem_map.mp hg₀
    have hqx : q ⟨x, x.property.1⟩ = g₀ := congrArg Subtype.val hfx
    let w := b.symm v
    let y : V := ⟨(x : G) * w.toMul * (x : G)⁻¹,
      (mem_normalizer_iff.mp (d.natural.chosen.normalizes x.property.1) w.toMul).mp
        w.toMul.property⟩
    refine Submodule.mem_map.mpr ⟨Additive.ofMul y - w, ?_, ?_⟩
    · change ((y / w.toMul : V) : G) ∈ C
      simp only [div_eq_mul_inv]
      rw [show C = ⁅F.Li L 1, V⁆ from commutator_comm _ _]
      exact commutator_mem_commutator (hres ▸ mem_map.mpr ⟨x, hx, rfl⟩)
        w.toMul.property
    · rw [LinearEquiv.toLinearMap_eq_coe, LinearMap.coe_coe, map_sub,
        hact ⟨x, x.property.1⟩ w, hqx, b.apply_symm_apply]
      rfl
  apply le_antisymm
  · intro v hv
    have hm : b (Additive.ofMul ⟨v, hv⟩) ∈ D := hD ▸ Submodule.mem_top
    obtain ⟨w, hw, hew⟩ := Submodule.mem_map.mp hm
    have hwv : w = Additive.ofMul ⟨v, hv⟩ := b.injective hew
    subst w
    exact hw
  · exact le_normalizer_iff_commutator_le_left.mp
      ((F.Li_le L 1).trans inf_le_left |>.trans d.natural.chosen.normalizes)

include d

/-- The original H-span of the natural seed is generated by K-commutators.
The seed actor is the literal O²(L ∩ H), and K is O²(H). -/
theorem U_eq_commutator_K : F.U = ⁅F.U, K F⁆ := by
  have hLK : F.Li L 1 ≤ K F := by
    change (pResidual 2 (L ⊓ F.H : Subgroup G)).map (L ⊓ F.H).subtype ≤ _
    exact embedded_pResidual_mono 2 inf_le_right
  exact conjugateSpanBy_eq_commutator_of_seed V F.H (K F) (F.Li L 1)
    (K_le_H F) (H_normalizes_K F) hLK d.seed_eq_commutator_point_residual

/-- The marked source involution belongs to [U,K]; no new action is chosen. -/
theorem point_mem_U_commutator_K : d.z ∈ ⁅F.U, K F⁆ := by
  rw [← d.U_eq_commutator_K]
  exact d.U₀_le_U d.z_mem_U₀

/-- The original natural closure lies in the actual residual. -/
theorem U_le_K : F.U ≤ K F := by
  rw [d.U_eq_commutator_K]
  exact le_normalizer_iff_commutator_le_right.mp
    (d.conjugationSection.section_le.trans (H_normalizes_K F))

/-- The same original closure lies in O₂(K), giving its literal chief-series
placement for the dual-factor argument. -/
theorem U_le_K_core : F.U ≤ (K F).pCoreIn 2 := by
  let := d.U_elementary
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _)
    d.U_le_K ((K_le_H F).trans d.conjugationSection.normalized)

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
