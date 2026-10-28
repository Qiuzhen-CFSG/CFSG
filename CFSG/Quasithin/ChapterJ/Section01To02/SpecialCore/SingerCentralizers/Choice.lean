module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.Basic
public import Theory.Representation.PSL3Two.NaturalOrbits
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The invariant Singer choice before J.2.3

The natural Ru1 action identifies C_L(Z), for |Z| = 2 and Z ≤ V,
with a point stabilizer in the seven-point action of L. Its order is
2¹⁴·3. The two-residual retains its three-part, so the specified
Sylow three-subgroup B, embedded through the actual residual, has order three.

The choice of B₇ needs only |L| = 2¹⁴·3·7. Its Sylow-seven count divides
3·2¹⁴ and is congruent to one modulo seven. If it were divisible by three,
it would be 3·2ⁱ with i ≤ 14, which has residue three, six or five modulo
seven. Thus the three-group B fixes a Sylow-seven subgroup of L by
conjugation. Mapping this subgroup into G gives the literal `SingerChoice`.

The order theorem retains the two preceding J.2.1 conclusions explicitly;
the existence theorem holds already under Ru1/Ru2. Both apply to the
source's `LocalSetup` through `toTypeRuSetup`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the choice preceding Lemma J.2.3, printed p.433 (PDF p.444).
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private theorem centralizer_card (d : TypeRuSetup G)
    (hZ : Nat.card d.Z = 2) (hZV : d.Z ≤ d.V) :
    Nat.card (d.L ⊓ d.H : Subgroup G) = 49152 := by
  obtain ⟨z, hz1, _⟩ := (Nat.card_eq_two_iff' (1 : d.Z)).mp hZ
  have hz : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  let v : d.V := ⟨z, hZV z.property⟩
  let c := d.ru1.natural.coordinates
  have hc : Function.Injective c := by
    apply c.ker_eq_bot_iff.mp
    rw [d.ru1.natural.kernel_eq, bot_subgroupOf]
  have hv : (c v).toAdd ≠ 0 := by
    intro h
    have he : c v = c 1 := h.trans (map_one c).symm
    exact hz (congrArg Subtype.val (hc he))
  let p : BinaryLinearThree.Point := ⟨(c v).toAdd, hv⟩
  let : MulAction d.L BinaryLinearThree.Point := MulAction.compHom _
    (BinaryLinearThree.pointPerm.comp d.ru1.quotientMap)
  let : MulAction.IsPretransitive d.L BinaryLinearThree.Point := {
    exists_smul_eq := fun x y => by
      obtain ⟨g, hg⟩ := BinaryLinearThree.natural_transitive_nonzero x y x.property y.property
      obtain ⟨l, hl⟩ := d.ru1.quotient_surjective g
      refine ⟨l, Subtype.ext ?_⟩
      change BinaryLinearThree.W (d.ru1.quotientMap l) x = y
      rw [hl]
      exact hg }
  have he : MulAction.stabilizer d.L p = (d.L ⊓ d.H).subgroupOf d.L := by
    ext l
    change (l • p = p) ↔ (l : G) ∈ d.L ⊓ d.H
    rw [mem_inf, and_iff_right l.property]
    rw [← centralizer_generator d hZ z z.property hz, mem_centralizer_singleton_iff]
    have heq := d.ru1.natural.equivariant l v
    change (c ⟨(l : G) * (z : G) * (l : G)⁻¹, _⟩).toAdd =
      BinaryLinearThree.W (d.ru1.quotientMap l) (c v).toAdd at heq
    constructor
    · intro h
      have hp : BinaryLinearThree.W (d.ru1.quotientMap l) (c v).toAdd = (c v).toAdd :=
        congrArg Subtype.val h
      have hec := hc (Multiplicative.toAdd.injective (heq.trans hp))
      have heg : (l : G) * (z : G) * (l : G)⁻¹ = z := congrArg Subtype.val hec
      exact mul_inv_eq_iff_eq_mul.mp heg
    · intro h
      apply Subtype.ext
      change BinaryLinearThree.W (d.ru1.quotientMap l) (c v).toAdd = (c v).toAdd
      rw [← heq]
      congr 2
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr h
  have hi : ((d.L ⊓ d.H).subgroupOf d.L).index = 7 := by
    rw [← he, MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card,
      Matrix.PSL3Two.Fano.card_point]
  have hn := ((d.L ⊓ d.H).subgroupOf d.L).card_mul_index
  rw [hi, Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : d.L ⊓ d.H ≤ d.L)).toEquiv,
    d.ru1.card_L] at hn
  omega

private theorem three_dvd_residual (d : TypeRuSetup G)
    (hZ : Nat.card d.Z = 2) (hZV : d.Z ≤ d.V) :
    3 ∣ Nat.card d.L₁ := by
  let C := d.L ⊓ d.H
  have hC : Nat.card C = 49152 := centralizer_card d hZ hZV
  obtain ⟨n, hn⟩ := (isPGroup_quotient_pResidual (G := C) 2).exists_card_eq
  have hm := card_eq_card_quotient_mul_card_subgroup (pResidual 2 C)
  rw [hC, hn] at hm
  have hd : 3 ∣ 2 ^ n * Nat.card (pResidual 2 C) := by rw [← hm]; decide
  have hr : 3 ∣ Nat.card (pResidual 2 C) :=
    ((by decide : Nat.Coprime 3 2).pow_right n).dvd_of_dvd_mul_left hd
  change 3 ∣ Nat.card ((pResidual 2 C).map C.subtype)
  rwa [card_map_of_injective C.subtype_injective]

/-- The original Sylow subgroup in O²(C_L(Z)), embedded in G, has order three.
The two explicit premises are the preceding conclusions of J.2.1. -/
theorem cubicSubgroup_card (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (hZ : Nat.card d.Z = 2) (hZV : d.Z ≤ d.V) :
    Nat.card (cubicSubgroup d B) = 3 := by
  have hthree : 3 ∣ Nat.card B := B.dvd_card_of_dvd_card (three_dvd_residual d hZ hZV)
  let A := (cubicSubgroup d B).subgroupOf d.L
  have hA : IsPGroup 3 A :=
    (B.isPGroup'.map d.L₁.subtype).of_equiv
      (subgroupOfEquivOfLe (cubicSubgroup_le_L d B)).symm
  obtain ⟨P, hAP⟩ := hA.exists_le_sylow
  have hP : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, d.ru1.card_L]
    decide +kernel
  have hAB : Nat.card A = Nat.card (cubicSubgroup d B) :=
    Nat.card_congr (subgroupOfEquivOfLe (cubicSubgroup_le_L d B)).toEquiv
  have hBB : Nat.card (cubicSubgroup d B) = Nat.card B :=
    card_map_of_injective d.L₁.subtype_injective
  have hd := card_dvd_of_le hAP
  rw [hAB, hP] at hd
  exact Nat.dvd_antisymm hd (hBB ▸ hthree)

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private theorem seven_sylow_card (d : TypeRuSetup G) (P : Sylow 7 d.L) :
    Nat.card P = 7 := by
  rw [P.card_eq_multiplicity, d.ru1.card_L]
  decide +kernel

private theorem seven_sylow_count (d : TypeRuSetup G) :
    ¬ 3 ∣ Nat.card (Sylow 7 d.L) := by
  let P : Sylow 7 d.L := Classical.choice inferInstance
  have hi : P.index = 49152 := by
    have h := P.toSubgroup.card_mul_index
    rw [seven_sylow_card d P, d.ru1.card_L] at h
    omega
  have hd := P.card_dvd_index
  rw [hi] at hd
  have hm : Nat.card (Sylow 7 d.L) % 7 = 1 := card_sylow_modEq_one 7 d.L
  intro hthree
  obtain ⟨k, hk⟩ := hthree
  rw [hk] at hd hm
  have hkdiv : k ∣ 2 ^ 14 := by
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).mp hd
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 2)).mp hkdiv
  interval_cases i <;> norm_num at hm

/-- The B-invariant order-seven subgroup chosen immediately before J.2.3. -/
theorem nonempty_singerChoice (d : TypeRuSetup G) (B : Sylow 3 d.L₁) :
    Nonempty (SingerChoice d B) := by
  let A := (cubicSubgroup d B).subgroupOf d.L
  have hA : IsPGroup 3 A :=
    (B.isPGroup'.map d.L₁.subtype).of_equiv
      (subgroupOfEquivOfLe (cubicSubgroup_le_L d B)).symm
  obtain ⟨P, hP⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 7 d.L)
    (seven_sylow_count d)
  have hAP : A ≤ normalizer (P : Set d.L) :=
    A.sylow_mem_fixedPoints_iff.mp hP
  refine ⟨⟨(P : Subgroup d.L).map d.L.subtype, map_subtype_le _, ?_, ?_⟩⟩
  · rw [card_map_of_injective d.L.subtype_injective, seven_sylow_card d P]
  · have he : A.map d.L.subtype = cubicSubgroup d B :=
      map_subgroupOf_eq_of_le (cubicSubgroup_le_L d B)
    rw [← he]
    exact (map_mono hAP).trans (le_normalizer_map d.L.subtype)

end CFSG.Quasithin.ChapterJ.SpecialCore
