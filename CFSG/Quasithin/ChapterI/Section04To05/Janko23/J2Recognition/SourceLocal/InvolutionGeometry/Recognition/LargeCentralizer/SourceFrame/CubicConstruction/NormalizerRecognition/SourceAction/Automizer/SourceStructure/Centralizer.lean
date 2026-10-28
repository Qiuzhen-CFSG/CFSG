module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.CubicConstruction.NormalizerRecognition.SourceAction.Automizer.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.CoreInvolutionFusion
public import Theory.SpecificGroups.MinusExtraspecial.NoncentralInvolutions
public import Mathlib.GroupTheory.Rank
/-!
# The source four-group centralizer and its normalizer

The ten noncentral involutions of the local extraspecial core form a single
orbit under H = C_G(z). Orbit–stabilizer gives |C_H(u)| = 192, and the literal
embeddings identify C_H(u) with C_G(E). The root product R has order 64 and
is normal in that centralizer. It is therefore its characteristic Sylow
two-subgroup. Since E = Z(R), this proves N_G(E) = N_G(R).

Source: Aschbacher, *Sporadic Groups* (1994), 8.15(2,5), 46.1–46.3,
printed pp.29–30 and 251. This argument does not assume an ambient order,
normalizer model, complement, or second involution centralizer.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Janko23
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- A noncentral core involution has centralizer of order 192 inside H. -/
theorem core_involution_centralizer_card (h : HTypeAt z)
    (u : localCore z) (hu : u ^ 2 = 1) (huZ : u ∉ center (localCore z)) :
    Nat.card (centralizer ({(u : involutionCentralizer z)} : Set (involutionCentralizer z))) = 192 := by
  let H := involutionCentralizer z
  let Q := localCore z
  have hu2 : orderOf u = 2 := orderOf_eq_prime hu (fun h1 => huZ (h1 ▸ (center Q).one_mem))
  let f : {x : Q // x ^ 2 = 1 ∧ x ∉ center Q} →
      MulAction.orbit (ConjAct H) (u : H) := fun x =>
    ⟨x.val, ConjAct.mem_orbit_conjAct.mpr
      (h.core_noncentral_involutions_isConj x.val u
        (orderOf_eq_prime x.property.1 (by intro h1; apply x.property.2; rw [h1]; exact (center Q).one_mem))
        x.property.2 hu2 huZ)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun y : MulAction.orbit (ConjAct H) (u : H) => (y : H)) he
    · intro x
      obtain ⟨g, hg⟩ := isConj_iff.mp (ConjAct.mem_orbit_conjAct.mp x.property).symm
      let a : MulAut Q := MulAut.conjNormal g
      have ha : a u ^ 2 = 1 := by rw [← map_pow, hu, map_one]
      have han : a u ∉ center Q := by
        intro hc
        have hh := (centerCongr a.symm ⟨a u, hc⟩).property
        apply huZ
        change a.symm (a u) ∈ center Q at hh
        rwa [a.symm_apply_apply] at hh
      refine ⟨⟨a u, ha, han⟩, ?_⟩
      exact Subtype.ext hg
  have ho : Nat.card (MulAction.orbit (ConjAct H) (u : H)) = 10 :=
    (Nat.card_congr (Equiv.ofBijective f hf).symm).trans
      (MinusExtraspecial.card_noncentral_involutions_of_equiv h.core_equiv.some)
  have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct H) (u : H))
  rw [Nat.card_prod, ho, ← nat_card_centralizer_nat_card_stabilizer,
    Nat.card_congr (ConjAct.toConjAct (G := H)).symm.toEquiv, h.centralizer_card] at hh
  change 10 * Nat.card (centralizer ({(u : H)} : Set H)) = 1920 at hh
  dsimp [H] at hh
  omega
end CFSG.Quasithin.Janko23
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Automizer
variable {G : Type*} [Group G] [Finite G] {D : Seed G} (P : ReturningPair D)

theorem centralizer_E_eq :
    centralizer (P.E : Set G) = involutionCentralizer D.z ⊓ involutionCentralizer P.u := by
  apply le_antisymm
  · intro c hc
    exact ⟨mem_centralizer_singleton_iff.mpr (hc D.z P.z_mem_E).symm,
      mem_centralizer_singleton_iff.mpr (hc P.u P.u_mem_E).symm⟩
  · apply le_centralizer_iff.mpr
    apply sup_le
    · apply zpowers_le.mpr
      intro c hc
      exact mem_centralizer_singleton_iff.mp hc.1
    · apply zpowers_le.mpr
      intro c hc
      exact mem_centralizer_singleton_iff.mp hc.2

theorem R_le_centralizer_E : P.R ≤ centralizer (P.E : Set G) := by
  rw [centralizer_E_eq]
  exact P.R_le_double_centralizer

theorem centralizer_E_card : Nat.card (centralizer (P.E : Set G)) = 192 := by
  obtain ⟨uH, huQ, hu⟩ := P.mem_core
  let uQ : localCore D.z := ⟨uH, huQ⟩
  change (uH : G) = P.u at hu
  have hu2 : uQ ^ 2 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change (uH : G) ^ 2 = 1
    rw [hu, ← P.u_order, pow_orderOf_eq_one]
  have hun : uQ ∉ center (localCore D.z) := by
    intro hc
    let e : localCore D.z ≃* ambientCore D.z :=
      (localCore D.z).equivMapOfInjective _ (involutionCentralizer D.z).subtype_injective
    have hm := mem_map_of_mem (ambientCore D.z).subtype (centerCongr e ⟨uQ, hc⟩).property
    rw [D.localType.core_center_image] at hm
    have huline : P.u ∈ zpowers D.z := by
      change (uH : G) ∈ zpowers D.z at hm
      rwa [hu] at hm
    have hc := card_le_of_le (show P.E ≤ zpowers D.z from
      sup_le le_rfl (zpowers_le.mpr huline))
    rw [P.E_card, Nat.card_zpowers, D.localType.involution] at hc
    omega
  have hmap : (centralizer ({uH} : Set (involutionCentralizer D.z))).map
      (involutionCentralizer D.z).subtype = centralizer (P.E : Set G) := by
    rw [centralizer_E_eq]
    apply le_antisymm
    · rintro x ⟨a, ha, rfl⟩
      refine ⟨a.property, mem_centralizer_singleton_iff.mpr ?_⟩
      have hh := congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha)
      change (a : G) * P.u = P.u * (a : G)
      simpa only [Subgroup.coe_mul, hu] using hh
    · intro x hx
      refine ⟨⟨x, hx.1⟩, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      apply Subtype.ext
      change x * (uH : G) = (uH : G) * x
      rw [hu]
      exact mem_centralizer_singleton_iff.mp hx.2
  rw [← hmap, card_map_of_injective (involutionCentralizer D.z).subtype_injective]
  exact core_involution_centralizer_card D.localType uQ hu2 hun

theorem normalizer_E_eq_normalizer_R (L : LocalCensus D) :
    normalizer (P.E : Set G) = normalizer (P.R : Set G) := by
  apply le_antisymm
  · let C := centralizer (P.E : Set G)
    let T := P.R.subgroupOf C
    have ht : Nat.card T = 64 :=
      (Nat.card_congr (subgroupOfEquivOfLe (R_le_centralizer_E P)).toEquiv).trans (P.R_card L)
    have hi : T.index = 3 := by
      have hh := T.card_mul_index
      rw [ht, centralizer_E_card P] at hh
      omega
    let S : Sylow 2 C := (IsPGroup.of_card (n := 6) ht).toSylow (by rw [hi]; decide)
    have hn : T.Normal := (normal_subgroupOf_iff_le_normalizer (R_le_centralizer_E P)).mpr
      (centralizer_E_le_normalizer_R P)
    let : T.Characteristic := Sylow.characteristic_of_normal S hn
    have hh := (normalizer_le_normalizer_centralizer P.E).trans
      (normalizer_le_normalizer_characteristic_image C T)
    rwa [map_subgroupOf_eq_of_le (R_le_centralizer_E P)] at hh
  · have hh := normalizer_le_normalizer_characteristic_image P.R (center P.R)
    rwa [E_center P] at hh
end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.LargeCentralizer.SourceFrame.NormalizerRecognition.SourceAction.Automizer
