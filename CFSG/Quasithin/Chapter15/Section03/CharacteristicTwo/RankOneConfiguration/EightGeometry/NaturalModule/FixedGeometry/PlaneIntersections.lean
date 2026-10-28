module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.LocalSpan
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.CentralInvolution
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.FactorGeometry.PlaneActors.Geometry

/-!
# The two fixed lines in the definite planes

The actual S-action has trivial coordinate shift. Projecting an S-fixed vector
onto either supported plane therefore remains S-fixed. This splits Z_S into
its two plane intersections. The previously proved avoidance of both planes
by Z, together with |Z_S|=4, makes each intersection have order two.

The diagonal seed and the second line span Z_S. The genuine preliminary
V₂ ≤ ⟨Z^{Y₊}⟩ and the source equality V₂=[V₂,Y₊] then give V₂ ≤ U_L,
Z_S ≤ U_I and U_I = Z₁ U_L. No plane-intersection identity is an input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the definite
planes on pp.1121–1122, 15.3.8, the proof of 15.3.11 on p.1124, and
15.3.32 on pp.1132–1133.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry
variable {G : Type*} [Group G]

private theorem plane_mem (d : LocalData G) (i : OrthogonalPlaneIndex) (v : d.V) :
    (v : G) ∈ d.action.plane i ↔ d.action.coordinates v ∈ orthogonalCoordinatePlane i := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact (Subtype.ext he : w = v) ▸ hw
  · intro h
    exact ⟨v, h, rfl⟩

private noncomputable def part (d : LocalData G) (i : OrthogonalPlaneIndex) (v : d.V) : d.V :=
  d.action.coordinates.symm (fun k => if k = i then d.action.coordinates v k else 1)

private theorem part_mem (d : LocalData G) (i : OrthogonalPlaneIndex)
    (v : d.V) (hv : (v : G) ∈ d.ZS) :
    ((part d i v : d.V) : G) ∈ d.ZS ⊓ d.action.plane i := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  let _ := orthogonalAction
  have hpart : d.action.coordinates (part d i v) =
      (fun k => if k = i then d.action.coordinates v k else 1) :=
    d.action.coordinates.apply_symm_apply _
  refine ⟨⟨(part d i v).property, ?_⟩, (plane_mem d i _).mpr ?_⟩
  · intro s hs
    let sM : d.M := ⟨s, d.sylow_le hs.1⟩
    have hshift : (d.action.actor sM).right = 1 :=
      RankTwo.plane_actor_shift_eq_one d.action sM 1 hs.2
    have hfix : d.action.actor sM • d.action.coordinates v = d.action.coordinates v := by
      rw [← d.action.compatible]
      congr 1
      apply Subtype.ext
      change s * (v : G) * s⁻¹ = (v : G)
      rw [hv.2 s hs, mul_inv_cancel_right]
    have hfixpart : d.action.actor sM • d.action.coordinates (part d i v) =
        d.action.coordinates (part d i v) := by
      rw [hpart]
      funext k
      change (d.action.actor sM).left k •
        (if (d.action.actor sM).right⁻¹ * k = i then
          d.action.coordinates v ((d.action.actor sM).right⁻¹ * k) else 1) =
          (if k = i then d.action.coordinates v k else 1)
      rw [hshift, inv_one, one_mul]
      by_cases hk : k = i
      · simp only [if_pos hk]
        have hh := congrFun hfix k
        change (d.action.actor sM).left k •
          d.action.coordinates v ((d.action.actor sM).right⁻¹ * k) = _ at hh
        simpa only [hshift, inv_one, one_mul] using hh
      · simp only [if_neg hk, smul_one]
    rw [← d.action.compatible] at hfixpart
    have hh := congrArg Subtype.val (d.action.coordinates.injective hfixpart)
    change s * (part d i v : G) * s⁻¹ = (part d i v : G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · intro k hk
    rw [hpart]
    exact if_neg hk

theorem fixedPlane_eq_sup_intersections (d : LocalData G) :
    d.ZS = (d.ZS ⊓ d.V₁) ⊔ (d.ZS ⊓ d.V₂) := by
  apply le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro v hv
  let v₀ : d.V := ⟨v, hv.1⟩
  have he : part d 1 v₀ * part d (Multiplicative.ofAdd (1 : ZMod 2)) v₀ = v₀ := by
    apply d.action.coordinates.injective
    rw [map_mul]
    simp only [part, MulEquiv.apply_symm_apply]
    funext k
    have hk : k = 1 ∨ k = Multiplicative.ofAdd (1 : ZMod 2) := by
      revert k
      decide
    have h10 : (1 : OrthogonalPlaneIndex) ≠ Multiplicative.ofAdd (1 : ZMod 2) := by decide
    rcases hk with rfl | rfl <;> simp [h10, h10.symm]
  have h := ((d.ZS ⊓ d.V₁) ⊔ (d.ZS ⊓ d.V₂)).mul_mem
    (mem_sup_left (part_mem d 1 v₀ hv))
    (mem_sup_right (part_mem d (Multiplicative.ofAdd (1 : ZMod 2)) v₀ hv))
  have heG : (part d 1 v₀ : G) * (part d (Multiplicative.ofAdd (1 : ZMod 2)) v₀ : G) = v :=
    congrArg Subtype.val he
  exact heG ▸ h

private theorem seed_le_fixed (d : LocalData G) : d.Z ≤ d.ZS :=
  le_inf (le_conjugateSpanBy d.Z d.M)
    ((centralInvolutions_le_centralizer_sylow d.T).trans (centralizer_le inf_le_left))

private theorem plane_intersection_ne_bot (d : LocalData G)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (i : OrthogonalPlaneIndex) :
    d.ZS ⊓ d.action.plane i ≠ ⊥ := by
  intro h
  have hcases : ∀ i : OrthogonalPlaneIndex, i = 1 ∨ i = Multiplicative.ofAdd (1 : ZMod 2) := by decide
  have hi := hcases i
  have hgen := fixedPlane_eq_sup_intersections d
  rcases hi with rfl | rfl
  · change d.ZS ⊓ d.V₁ = ⊥ at h
    rw [h, bot_sup_eq] at hgen
    exact centralInvolutions_not_le_plane d hindex hZ _
      ((seed_le_fixed d).trans (hgen.le.trans inf_le_right))
  · change d.ZS ⊓ d.V₂ = ⊥ at h
    rw [h, sup_bot_eq] at hgen
    exact centralInvolutions_not_le_plane d hindex hZ _
      ((seed_le_fixed d).trans (hgen.le.trans inf_le_right))

theorem card_plane_intersection [Finite G] (d : LocalData G)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4)
    (i : OrthogonalPlaneIndex) : Nat.card (d.ZS ⊓ d.action.plane i : Subgroup G) = 2 := by
  let A := d.ZS ⊓ d.action.plane i
  have hn : 1 < Nat.card A := (Subgroup.one_lt_card_iff_ne_bot _).mpr
    (plane_intersection_ne_bot d hindex hZ i)
  have hle : Nat.card A ≤ 4 := hZS ▸ card_le_of_le (show A ≤ d.ZS from inf_le_left)
  have hne : Nat.card A ≠ 4 := by
    intro h
    have he : A = d.ZS := eq_of_le_of_card_ge inf_le_left (by omega)
    exact centralInvolutions_not_le_plane d hindex hZ i
      ((seed_le_fixed d).trans (he.ge.trans inf_le_right))
  have hd : Nat.card A ∣ 4 := hZS ▸ card_dvd_of_le (show A ≤ d.ZS from inf_le_left)
  have hcalc : ∀ n : ℕ, 1 < n → n ≤ 4 → n ≠ 4 → n ∣ 4 → n = 2 := by
    intro n hn hle hne hd
    interval_cases n <;> norm_num at *
  exact hcalc _ hn hle hne hd

/-- The diagonal Sylow-central seed and the second fixed line span Z_S. -/
theorem fixedPlane_eq_seed_sup_secondLine [Finite G] (d : LocalData G)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4) :
    d.ZS = d.Z ⊔ (d.ZS ⊓ d.V₂) := by
  let Z₂ := d.ZS ⊓ d.V₂
  have hZ₂ : Nat.card Z₂ = 2 := card_plane_intersection d hindex hZ hZS _
  have hdis : Disjoint d.Z Z₂ := by
    apply disjoint_iff.mpr
    have hd : Nat.card (d.Z ⊓ Z₂ : Subgroup G) ∣ 2 :=
      hZ ▸ card_dvd_of_le (show d.Z ⊓ Z₂ ≤ d.Z from inf_le_left)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hc | hc
    · exact Subgroup.card_eq_one.mp hc
    · have he : d.Z ⊓ Z₂ = d.Z := eq_of_le_of_card_ge inf_le_left (by omega)
      exact (centralInvolutions_not_le_plane d hindex hZ _
        (he.ge.trans (inf_le_right.trans (show Z₂ ≤ d.V₂ from inf_le_right)))).elim
  have hnorm : Z₂ ≤ normalizer (d.Z : Set G) := by
    let _ := d.action.elementary
    have hVV : d.V ≤ centralizer (d.V : Set G) :=
      le_centralizer_iff_isMulCommutative.mpr inferInstance
    exact ((show Z₂ ≤ d.V from inf_le_left.trans inf_le_left).trans hVV).trans
      ((centralizer_le (le_conjugateSpanBy d.Z d.M)).trans (Subgroup.centralizer_le_normalizer _))
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint d.Z Z₂ hnorm hdis
  rw [hZ, hZ₂] at hc
  change Nat.card (d.Z ⊔ (d.ZS ⊓ d.V₂) : Subgroup G) = 2 * 2 at hc
  exact (eq_of_le_of_card_ge (sup_le (seed_le_fixed d) inf_le_left) (by rw [hZS, hc])).symm

/-- The source V₂=[V₂,Y₊] puts V₂ in U_L; the two fixed lines lie in U_I. -/
theorem span_eq_firstLine_sup_componentModule [Finite G] (d : LocalData G)
    {I : Subgroup G} (c : ComponentWitness d I)
    (hnormal : (c.L.subgroupOf I).Normal) (hI : I = c.L ⊔ d.S)
    (hYL : d.Yplus ≤ c.L) (hV₂ : d.V₂ = ⁅d.V₂, d.Yplus⁆)
    (hseed : d.V₂ ≤ localSpan d.Z d.Yplus)
    (hindex : (d.S.subgroupOf (d.T : Subgroup G)).index = 2)
    (hZ : Nat.card d.Z = 2) (hZS : Nat.card d.ZS = 4) :
    d.V₂ ≤ d.componentModule I c.L ∧ d.ZS ≤ d.UI I ∧
      d.UI I = (d.ZS ⊓ d.V₁) ⊔ d.componentModule I c.L := by
  have hVUI : d.V₂ ≤ d.UI I := hseed.trans
    (conjugateSpanBy_mono le_rfl (hYL.trans (component_le c)))
  have hVU : d.V₂ ≤ d.componentModule I c.L := hV₂.le.trans (commutator_mono hVUI hYL)
  have hZSUI : d.ZS ≤ d.UI I := by
    rw [fixedPlane_eq_seed_sup_secondLine d hindex hZ hZS]
    exact sup_le (le_conjugateSpanBy d.Z I) (inf_le_right.trans hVUI)
  refine ⟨hVU, hZSUI, le_antisymm ?_ ?_⟩
  · rw [span_eq_seed_sup_componentModule d c hnormal hI]
    apply sup_le ?_ le_sup_right
    exact (seed_le_fixed d).trans ((fixedPlane_eq_sup_intersections d).le.trans
      (sup_le le_sup_left (inf_le_right.trans (hVU.trans le_sup_right))))
  · exact sup_le (inf_le_left.trans hZSUI) (componentModule_le_span d c)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.FixedGeometry

end
