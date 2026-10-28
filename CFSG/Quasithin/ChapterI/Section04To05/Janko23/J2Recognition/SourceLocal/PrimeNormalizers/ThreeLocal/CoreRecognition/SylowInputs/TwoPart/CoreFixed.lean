module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.SourceOrbits.Representatives.SL23Local.CoreConstruction
public import Theory.SpecificGroups.MinusExtraspecial.CubicAction.NormalForm
public import Theory.SpecificGroups.MinusExtraspecial.CubicAction.FixedSubgroup
public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicCentralizer

/-!
# The two-part of the cubic centralizer inside C_G(z)

The proved cubic normal form gives coordinates on the literal core Q.
Its fixed dihedral subgroup maps exactly onto Q ∩ C_G(X), of order eight.
The image of X in H/Q ≃ A₅ has order three and is self-centralizing.
Consequently every two-subgroup of C_H(X) lies in Q and has order at most
eight. All embeddings are the original subgroup inclusions.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.3, printed p.262.
-/

@[expose] public section
open Subgroup
open MinusExtraspecial.CubicAction
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreSylowInputs
variable {G : Type*} [Group G] [Finite G]

/-- The finite fixed subgroup maps to the actual common centralizer. -/
theorem fixedSubgroup_map (D : Seed G) (A : SL23Local.CubicCoordinates D) :
    fixedSubgroup.map A.core = ambientCore D.z ⊓ C D := by
  have hc : C D = centralizer ({(A.t : G)} : Set G) := by
    change centralizer (D.X : Set G) = _
    conv_lhs => rw [← A.zpowers_t, zpowers_eq_closure, centralizer_closure]
  ext q
  constructor
  · rintro ⟨m, hm, rfl⟩
    refine ⟨A.core_mem m, ?_⟩
    change A.core m ∈ C D
    rw [hc, mem_centralizer_singleton_iff]
    have h := A.action m
    rw [(mem_fixedSubgroup m).mp hm] at h
    exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm
  · rintro ⟨hq, hx⟩
    rw [← A.range_core] at hq
    obtain ⟨m, rfl⟩ := hq
    refine ⟨m, ?_, rfl⟩
    change cycle m = m
    apply A.injective
    rw [A.action]
    change A.core m ∈ C D at hx
    rw [hc, mem_centralizer_singleton_iff] at hx
    exact mul_inv_eq_iff_eq_mul.mpr hx.symm

/-- The core centralizer has order eight, with no later local-recognition premise. -/
theorem core_centralizer_card (D : Seed G) :
    Nat.card (ambientCore D.z ⊓ C D : Subgroup G) = 8 := by
  obtain ⟨A⟩ := SL23Local.nonempty_cubicCoordinates_of_normalForm D hasCubicNormalForm
  rw [← fixedSubgroup_map D A, card_map_of_injective A.injective, fixedSubgroup_card]

/-- A two-subgroup centralizing X inside H lies in the literal extraspecial core. -/
theorem local_two_le_core (D : Seed G) (U : Subgroup G) (hU : IsPGroup 2 U)
    (hUH : U ≤ involutionCentralizer D.z) (hUX : U ≤ C D) :
    U ≤ ambientCore D.z := by
  let H := involutionCentralizer D.z
  let Q := localCore D.z
  let q := QuotientGroup.mk' Q
  let Y := D.X.subgroupOf H
  have hY : Nat.card Y = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe D.X_le).toEquiv).trans D.card_X
  have hd : Disjoint Q Y := disjoint_of_coprime_natCard (by
    rw [D.localType.core_card, hY]
    decide)
  have hi : Function.Injective (q.comp Y.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro y hy
    apply Subtype.ext
    exact (disjoint_def.mp hd) ((QuotientGroup.eq_one_iff y.val).mp hy) y.property
  have hYq : Nat.card (Y.map q) = 3 := by
    calc
      _ = Nat.card (q.comp Y.subtype).range := by rw [MonoidHom.range_comp, range_subtype]
      _ = Nat.card Y := Nat.card_congr (MonoidHom.ofInjective hi).symm.toEquiv
      _ = 3 := hY
  let V := U.subgroupOf H
  have hV : IsPGroup 2 V := hU.of_equiv (subgroupOfEquivOfLe hUH).symm
  have hVC : V.map q ≤ centralizer (Y.map q : Set (H ⧸ Q)) := by
    rintro _ ⟨v, hv, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg q (Subtype.ext (hUX hv y.val hy))
  have hd3 := card_dvd_of_le hVC
  rw [alternatingGroup.FiveLocalGeometry.cubic_centralizer_card
    D.localType.quotient_equiv.some (Y.map q) hYq] at hd3
  obtain ⟨n, hn⟩ := (hV.map q).exists_card_dvd_pow
  have hb : V.map q = ⊥ := card_eq_one.mp (Nat.eq_one_of_dvd_coprimes
    ((by norm_num : Nat.Coprime 3 2).pow_right n) hd3 hn)
  intro u hu
  have hq : q (⟨u, hUH hu⟩ : H) = 1 := by
    have hm : q (⟨u, hUH hu⟩ : H) ∈ V.map q := mem_map_of_mem q hu
    simpa only [hb, mem_bot] using hm
  exact mem_map_of_mem H.subtype ((QuotientGroup.eq_one_iff _).mp hq)

/-- The local bound needed after transporting a central involution to z. -/
theorem local_two_card_le (D : Seed G) (U : Subgroup G) (hU : IsPGroup 2 U)
    (hUH : U ≤ involutionCentralizer D.z) (hUX : U ≤ C D) : Nat.card U ≤ 8 := by
  have h := card_le_of_le (le_inf (local_two_le_core D U hU hUH hUX) hUX)
  rwa [core_centralizer_card D] at h

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.CoreSylowInputs
