module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.MarkedRestriction
public import Theory.AtlasPort.LinearGroups.G2.DerivedParabolicGeneration
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement.Bruhat


/-!
# Derived Bruhat coverage and actor generation for G₂(2)′

The sign character splits each positive-root factor into the derived Sylow
and the short-root involution. Bruhat coverage consequently reduces to the
24 even representatives F(1)^a w_i F(1)^b. The parity test uses the genuine
index-two quotient. The two cubic actors, together with the derived Sylow,
generate both order-96 restricted parabolics and hence the actual commutator.

Source application: Aschbacher–Smith, proof of 15.3.49, printed pp.1144–1145.
The coordinate conventions come from the licensed ATLAS port through the
imports (LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff).
-/

@[expose] public section

open Subgroup Atlas.G2 Atlas.G2.Explicit Atlas.G2.BinaryCore Atlas.SplitOctonion
namespace Atlas.G2.BinaryParabolicPair.SevenSylowOvergroups
open SolvableSylowPlacement

abbrev G := Model (ZMod 2)

def representative (i : Fin 12) (a b : Fin 2) : G :=
  shortRoot ^ a.val * weylRep i * shortRoot ^ b.val

def parity (i : Fin 12) : ℕ := ![0,0,1,1,1,1,0,0,0,0,1,1] i

def allowed (i : Fin 12) (a b : Fin 2) : Prop := (a.val + parity i + b.val) % 2 = 0

private theorem project_S : BinaryException.projection (weylS : G) = BinaryException.quotientBit := by
  have h := (QuotientGroup.eq_one_iff cubicActor).mpr
    (commutator_eq_longRootClosure ▸ cubicActor_mem_derived)
  change BinaryException.projection cubicActor = 1 at h
  rw [cubicActor, map_mul] at h
  have hh : BinaryException.quotientBit * BinaryException.quotientBit = 1 := by
    simpa only [pow_two] using BinaryException.quotientBit_sq
  exact mul_left_cancel (h.trans hh.symm)

theorem representative_mem_derived_iff (i : Fin 12) (a b : Fin 2) :
    representative i a b ∈ DerivedModel ↔ allowed i a b := by
  rw [DerivedModel, commutator_eq_longRootClosure, ← QuotientGroup.eq_one_iff]
  change BinaryException.projection (representative i a b) = 1 ↔ _
  have hh : BinaryException.quotientBit * BinaryException.quotientBit = 1 := by
    simpa only [pow_two] using BinaryException.quotientBit_sq
  have hf : BinaryException.projection shortRoot = BinaryException.quotientBit := rfl
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num only [representative, weylRep, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_zero', Matrix.cons_val_succ', pow_zero, pow_one, map_mul, map_one,
      BinaryException.project_R, project_S, hf, hh, one_mul, mul_one,
      quotientBit_ne_one, allowed, parity]

private theorem split_right (u : G) (hu : u ∈ unipotent) :
    ∃ p ∈ derivedSylowAmbient, ∃ a : Fin 2, u = p * shortRoot ^ a.val := by
  have memD (x : G) (hx : Binary.lineSign x = 1) : x ∈ DerivedModel := by
    rw [DerivedModel, commutator_eq_longRootClosure, ← BinaryException.lineSign_kernel]
    exact hx
  rcases Int.units_eq_one_or (Binary.lineSign u) with h | h
  · exact ⟨u, ⟨hu, memD u h⟩, 0, by simp⟩
  · refine ⟨u * shortRoot⁻¹, ⟨unipotent.mul_mem hu
      (unipotent.inv_mem shortRoot_mem_unipotent), memD _ ?_⟩, 1, ?_⟩
    · rw [map_mul, map_inv, h, shortRoot, Binary.lineSign_rootF_one]
      exact mul_inv_cancel _
    · simp

private theorem split_left (u : G) (hu : u ∈ unipotent) :
    ∃ a : Fin 2, ∃ p ∈ derivedSylowAmbient, u = shortRoot ^ a.val * p := by
  obtain ⟨p,hp,a,ha⟩ := split_right u⁻¹ (unipotent.inv_mem hu)
  refine ⟨a,p⁻¹,derivedSylowAmbient.inv_mem hp,?_⟩
  have hf : shortRoot⁻¹ = shortRoot := inv_eq_of_mul_eq_one_left
    (by simpa only [pow_two] using shortRoot_sq)
  have he := congrArg Inv.inv ha
  simpa only [inv_inv, mul_inv_rev, ← inv_pow, hf] using he

/-- Bruhat coverage with both outside factors in the actual derived Sylow. -/
theorem derived_cover (g : DerivedModel) :
    ∃ (i : Fin 12) (a b : Fin 2) (u v : G), u ∈ derivedSylowAmbient ∧
      v ∈ derivedSylowAmbient ∧ allowed i a b ∧ g.val = u * representative i a b * v := by
  obtain ⟨i,u,hu,t,ht,v,hv,hg⟩ := bruhatCover g.val
  have ht1 : t = 1 := by
    obtain ⟨⟨l,m⟩,rfl⟩ := ht
    exact BinaryException.binary_torus l m
  obtain ⟨p,hp,a,ha⟩ := split_right u hu
  obtain ⟨b,q,hq,hb⟩ := split_left v hv
  have he : g.val = p * representative i a b * q := by
    rw [hg,ht1,ha,hb,representative]
    group
  refine ⟨i,a,b,p,q,hp,hq,?_,he⟩
  apply (representative_mem_derived_iff i a b).mp
  have hh := DerivedModel.mul_mem (DerivedModel.mul_mem
    (DerivedModel.inv_mem hp.2) g.prop) (DerivedModel.inv_mem hq.2)
  simpa only [he, mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] using hh

def sylowGenerator : G := rootC 1 * rootE 1 * rootF 1

theorem sylowGenerator_mem : sylowGenerator ∈ derivedSylowAmbient := by
  constructor
  · simpa [unipotentProduct, sylowGenerator] using
      unipotentProduct_mem (![0,0,1,0,1,1] : Fin 6 → ZMod 2)
  · change sylowGenerator ∈ DerivedModel
    rw [DerivedModel, commutator_eq_longRootClosure, ← QuotientGroup.eq_one_iff]
    change BinaryException.projection (rootC 1 * rootE 1 * rootF 1) = 1
    rw [map_mul, map_mul, BinaryException.project_E, mul_one,
      BinaryException.project_C_eq_D, BinaryException.project_D_eq_F,
      ← map_mul, rootF_add, show (1 : ZMod 2) + 1 = 0 by decide, rootF_zero, map_one]

theorem rootE_mem : rootE (1 : ZMod 2) ∈ derivedSylowAmbient := by
  constructor
  · exact subset_closure (by simp)
  · rw [commutator_eq_longRootClosure]
    exact BinaryException.rootE_in_H 1

private theorem parabolic_le (K H : Subgroup DerivedModel)
    (hP : (derivedSylow : Subgroup DerivedModel) ≤ K)
    (hPH : (derivedSylow : Subgroup DerivedModel) ≤ H)
    (hH : Nat.card H = 96) (x : DerivedModel) (hxH : x ∈ H) (hxK : x ∈ K)
    (hx3 : orderOf x = 3) : H ≤ K := by
  have h32 : 32 ∣ Nat.card (K ⊓ H : Subgroup DerivedModel) :=
    card_derivedSylow ▸ card_dvd_of_le (le_inf hP hPH)
  have h3 : 3 ∣ Nat.card (K ⊓ H : Subgroup DerivedModel) := by
    have hd := orderOf_dvd_natCard (⟨x, hxK, hxH⟩ : ↥(K ⊓ H))
    rwa [← Subgroup.orderOf_coe, hx3] at hd
  have h96 := (show Nat.Coprime 32 3 by decide).mul_dvd_of_dvd_of_dvd h32 h3
  have he : K ⊓ H = H := eq_of_le_of_card_ge inf_le_right (by
    rw [hH]
    exact Nat.le_of_dvd Nat.card_pos h96)
  exact he ▸ inf_le_left

/-- The two cubic actors complete the derived Sylow to the whole derived group. -/
theorem eq_top_of_actors (K : Subgroup DerivedModel)
    (hP : (derivedSylow : Subgroup DerivedModel) ≤ K)
    (hc : (⟨cubicActor,cubicActor_mem_derived⟩ : DerivedModel) ∈ K)
    (hm : (⟨movingActor,movingActor_mem_derived⟩ : DerivedModel) ∈ K) : K = ⊤ := by
  have hfirst : derivedFirst ≤ K := parabolic_le K derivedFirst hP
    derivedSylow_le_first card_derivedFirst _ cubicActor_mem_derivedFirst hc
    ((Subgroup.orderOf_coe _).symm.trans cubicActor_order)
  have hmo : orderOf movingActor = 3 := by
    apply orderOf_eq_prime movingActor_cube
    intro h
    apply movingActor_moves
    simp [h]
  have hsecond : derivedSecond ≤ K := parabolic_le K derivedSecond hP
    derivedSylow_le_second card_derivedSecond _ movingActor_mem_derivedSecond hm
    ((Subgroup.orderOf_coe _).symm.trans hmo)
  have hgen : derivedFirst ⊔ derivedSecond = ⊤ := by
    apply map_injective DerivedModel.subtype_injective
    rw [Subgroup.map_sup, derivedFirst_map_subtype, derivedSecond_map_subtype,
      ← MonoidHom.range_eq_map, DerivedModel.range_subtype]
    have h := DerivedParabolicGeneration.binary_restricted_pair_generate
    rw [LieParabolicSetup.parabolic₁_binary] at h
    exact h
  exact top_unique (hgen ▸ sup_le hfirst hsecond)

end Atlas.G2.BinaryParabolicPair.SevenSylowOvergroups
