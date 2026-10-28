module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.SuzukiPair.OmegaGeometry.Factors
public import Theory.SpecificGroups.Suzuki.RootOmega
/-!
# First omega of the covered paired Suzuki Sylow intersection

In a central extension with elementary central kernel, a square-one lift
of an element makes every lift square-one. Apply this to the product of
the two concrete root omega groups. The resulting full inverse image is
elementary abelian. Exact Sylow restriction identifies it with Ω₁(T₀),
and surjectivity gives its exact image in both model factors.

The lifts are constructed from the actual component embeddings in
PairFactors, using only the multiplier's elementary-center input and the
single-factor involution-lifting clause. This retains the Sz(8) covers;
no claim that Ω₁(T₀) is central in T₀ is made.

Source: Aschbacher–Smith, proof of 13.6.6, p.927, and I.2.2(4),
pp.409–411. The source assembly must discharge the earlier cover inputs.
-/

@[expose] public section
open Subgroup

private theorem preimage_elementary {A Q : Type*} [Group A] [Group Q]
    (f : A →* Q) (hcentral : f.ker ≤ center A)
    (hker : ∀ z ∈ f.ker, z ^ 2 = 1)
    (hlift : ∀ q : Q, q ^ 2 = 1 → ∃ a : A, a ^ 2 = 1 ∧ f a = q)
    (E : Subgroup Q) [IsElementaryAbelian 2 E] : IsElementaryAbelian 2 (E.comap f) := by
  have hp (x : E.comap f) : x ^ 2 = 1 := by
    obtain ⟨y, hy, hfy⟩ := hlift (f x) (elemPow_eq_one_of_isElementaryAbelian _ x.property)
    have hz : (x : A) * y⁻¹ ∈ f.ker := by
      change f ((x : A) * y⁻¹) = 1
      rw [map_mul, map_inv, hfy, mul_inv_cancel]
    have hc : Commute ((x : A) * y⁻¹) y :=
      (mem_center_iff.mp (hcentral hz) y).symm
    apply Subtype.ext
    calc
      (x : A) ^ 2 = (((x : A) * y⁻¹) * y) ^ 2 := by rw [inv_mul_cancel_right]
      _ = ((x : A) * y⁻¹) ^ 2 * y ^ 2 := hc.mul_pow _
      _ = 1 := by rw [hker _ hz, hy, mul_one]
  exact {
    toIsMulCommutative := IsMulCommutative.of_comm (fun x y =>
      (Commute.of_orderOf_dvd_two (fun z => orderOf_dvd_of_pow_eq_one (hp z)) x y).eq)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }

open BenderSuzuki.MatrixGroups Theory.GroupTheory
noncomputable section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
variable {G : Type*} [Group G] {T K : Subgroup G} {v : G}

/-- The full inverse image of the two root omega groups, with the central kernel retained. -/
def Marking.rootOmegaPreimage (d : Marking T K v) : Subgroup (orbit T K v) :=
  ((omegaOneAmbient (SuzukiRootSubgroup d.parameter)).prod
    (omegaOneAmbient (SuzukiRootSubgroup d.parameter))).comap d.quotientMap

private theorem rootOmegaProduct_elementary (m : ℕ) (hm : 0 < m) :
    IsElementaryAbelian 2 ((omegaOneAmbient (SuzukiRootSubgroup m)).prod
      (omegaOneAmbient (SuzukiRootSubgroup m))) := by
  let := suzukiRootSubgroup_omega_elementary m hm
  have hp (x : (omegaOneAmbient (SuzukiRootSubgroup m)).prod
      (omegaOneAmbient (SuzukiRootSubgroup m))) : x ^ 2 = 1 := by
    apply Subtype.ext
    exact Prod.ext (elemPow_eq_one_of_isElementaryAbelian _ x.property.1)
      (elemPow_eq_one_of_isElementaryAbelian _ x.property.2)
  exact {
    toIsMulCommutative := IsMulCommutative.of_comm (fun x y =>
      (Commute.of_orderOf_dvd_two (fun z => orderOf_dvd_of_pow_eq_one (hp z)) x y).eq)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hp }

/-- Commuting single-factor lifts make the full root-omega preimage elementary abelian. -/
theorem PairFactors.rootOmegaPreimage_elementary {d : Marking T K v} (c : PairFactors d)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q) :
    IsElementaryAbelian 2 d.rootOmegaPreimage := by
  let := c.orbit_center_elementary hKG hK
  let := rootOmegaProduct_elementary d.parameter d.positive
  apply preimage_elementary d.quotientMap
    (d.quotientMap_ker.le) ?_ (c.lift_pair_involutions hKG hK hlift)
  intro z hz
  rw [d.quotientMap_ker] at hz
  exact elemPow_eq_one_of_isElementaryAbelian z hz

variable [Finite G]

/-- Identify the actual Ω₁(T₀) with that full preimage using the genuine Sylow witness. -/
theorem PairFactors.omega_eq_preimage {d : Marking T K v} (c : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)) :
    omega T K v = d.rootOmegaPreimage.map (orbit T K v).subtype := by
  let := c.orbit_center_elementary hKG hK
  let := c.rootOmegaPreimage_elementary hKG hK hlift
  let := IsElementaryAbelian.map (p := 2) (A := d.rootOmegaPreimage) (orbit T K v).subtype
  have hW : d.rootOmegaPreimage ≤ (Tv T v).subgroupOf (orbit T K v) := by
    rw [← d.aligned_preimage_eq P hP hKG (IsElementaryAbelian.isPGroup 2 _) ha]
    exact comap_mono (prod_mono (omegaOneAmbient_le _) (omegaOneAmbient_le _))
  have hWT : d.rootOmegaPreimage.map (orbit T K v).subtype ≤ intersection T K v := by
    simpa only [subgroupOf_map_subtype, intersection] using
      map_mono (f := (orbit T K v).subtype) hW
  apply le_antisymm
  · apply (omegaOneAmbient_le_iff _ _).mpr
    intro x hx hp
    let y : orbit T K v := ⟨x, hx.2⟩
    have hyr : d.quotientMap y ∈ (SuzukiRootSubgroup d.parameter).prod
        (SuzukiRootSubgroup d.parameter) := ha (mem_map_of_mem _ hx.1)
    have hpy : (d.quotientMap y) ^ 2 = 1 := by
      rw [← map_pow, show y ^ 2 = 1 from Subtype.ext hp, map_one]
    refine ⟨y, ?_, rfl⟩
    exact ⟨(omegaOneAmbient_le_iff _ _).mp le_rfl _ hyr.1 (congrArg Prod.fst hpy),
      (omegaOneAmbient_le_iff _ _).mp le_rfl _ hyr.2 (congrArg Prod.snd hpy)⟩
  · calc
      d.rootOmegaPreimage.map (orbit T K v).subtype =
          omegaOneAmbient (d.rootOmegaPreimage.map (orbit T K v).subtype) :=
        (omegaOneAmbient_eq_self _).symm
      _ ≤ omega T K v := omegaOneAmbient_mono hWT

/-- The actual paired omega is elementary abelian, also for nontrivial central covers. -/
theorem PairFactors.omega_elementary {d : Marking T K v} (c : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)) :
    IsElementaryAbelian 2 (omega T K v) := by
  rw [c.omega_eq_preimage P hP hKG hK hlift ha]
  let := c.rootOmegaPreimage_elementary hKG hK hlift
  exact IsElementaryAbelian.map _



/-- Both root omega groups are the exact image of the actual ambient omega. -/
theorem PairFactors.omega_image {d : Marking T K v} (c : PairFactors d)
    (P : Sylow 2 (Gv v)) (hP : (P : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hKG : K ≤ Gv v) (hK : IsComponent (Gv v) (K.subgroupOf (Gv v)))
    [IsElementaryAbelian 2 (center K)]
    (hlift : ∀ q : K ⧸ center K, q ^ 2 = 1 →
      ∃ k : K, k ^ 2 = 1 ∧ QuotientGroup.mk' (center K) k = q)
    (ha : ((Tv T v).subgroupOf (orbit T K v)).map d.quotientMap ≤
      (SuzukiRootSubgroup d.parameter).prod (SuzukiRootSubgroup d.parameter)) :
    ((omega T K v).subgroupOf (orbit T K v)).map d.quotientMap =
      (omegaOneAmbient (SuzukiRootSubgroup d.parameter)).prod
        (omegaOneAmbient (SuzukiRootSubgroup d.parameter)) := by
  rw [c.omega_eq_preimage P hP hKG hK hlift ha, subgroupOf, comap_map_eq_self
    (show (orbit T K v).subtype.ker ≤ d.rootOmegaPreimage by
      rw [Subgroup.ker_subtype]
      exact bot_le)]
  rw [Marking.rootOmegaPreimage, map_comap_eq,
    MonoidHom.range_eq_top.mpr d.quotientMap_surjective, top_inf_eq]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SuzukiPair
