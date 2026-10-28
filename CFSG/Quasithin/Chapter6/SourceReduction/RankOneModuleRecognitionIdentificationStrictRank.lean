module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictCrossingKernel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictTransvections
public import CFSG.Quasithin.ChapterG.Section10.Basic

/-!
# The rank of the literal crossing quotient

The center of the opposite closure meets the action kernel in its original
conjugate point. Its dotted image therefore has half the order of Z(U).
The full crossing image has kernel E, and E meets Z(U) in the original point.
Since the two hyperplane centralizers are conjugate, cancellation of these
order formulas proves the exact rank identity in 6.2.17(10). Isotropy then
gives the G.10.2 bounds for this same quotient, including its nontriviality.

Source: Aschbacher--Smith, 6.2.17(6),(10), printed pp.689--690, and G.10.2,
printed p.357. The Chapter12 StrictRank application uses the whole reduced
layer. The fixed-vector bound, classification and strict contradiction remain
with qt-d-1222-recognition-strict-elimination. LocalAnalysis is supplied by
qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private theorem image_card_mul_kernel {G H : Type*} [Group G] [Group H] [Finite G]
    (D : Subgroup G) (f : G →* H) :
    Nat.card (D.map f) * Nat.card (D ⊓ f.ker : Subgroup G) = Nat.card D := by
  have hc := (f.ker.subgroupOf D).card_mul_index
  have he : Nat.card (f.ker.subgroupOf D) = Nat.card (D ⊓ f.ker : Subgroup G) := by
    rw [← inf_subgroupOf_left f.ker D]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [he, ← relIndex, relIndex_ker] at hc
  exact (Nat.mul_comm _ _).trans hc

private theorem relative_image_card {G H : Type*} [Group G] [Group H] [Finite G]
    (D K : Subgroup G) (hD : D ≤ K) (f : K →* H) :
    Nat.card ((D.subgroupOf K).map f) *
      Nat.card (D ⊓ f.ker.map K.subtype : Subgroup G) = Nat.card D := by
  have hc := image_card_mul_kernel (D.subgroupOf K) f
  have he : Nat.card ((D.subgroupOf K) ⊓ f.ker : Subgroup K) =
      Nat.card (D ⊓ f.ker.map K.subtype : Subgroup G) := by
    rw [← card_map_of_injective K.subtype_injective,
      map_inf _ _ _ K.subtype_injective, map_subgroupOf_eq_of_le hD]
  rw [he, Nat.card_congr (subgroupOfEquivOfLe hD).toEquiv] at hc
  exact hc

variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

private theorem hat_card_mul_center
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    (D : Subgroup G) (hD : D ≤ sourceClosure (T : Subgroup G) L R z) :
    Nat.card (strictHatSpace (T : Subgroup G) L R z D) *
      Nat.card (D ⊓ (center (sourceClosure (T : Subgroup G) L R z)).map
        (sourceClosure (T : Subgroup G) L R z).subtype : Subgroup G) = Nat.card D := by
  let U := sourceClosure (T : Subgroup G) L R z
  let q := QuotientGroup.mk' (center U)
  let e : strictHatSpace (T : Subgroup G) L R z D ≃ (D.subgroupOf U).map q := {
    toFun := fun x => ⟨x.val.toMul, x.property⟩
    invFun := fun x => ⟨Additive.ofMul x.val, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  have hc := relative_image_card D U hD q
  rw [QuotientGroup.ker_mk'] at hc
  exact hc

/-- The conjugate center has precisely the conjugate point as its kernel
in the literal dotted action. -/
theorem LocalAnalysis.strict_crossing_center_image_card
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G)) :
    Nat.card (strictCrossingCenterImage (T : Subgroup G) L R z d) * 2 =
      Nat.card (center (sourceClosure (T : Subgroup G) L R z)) := by
  let U := sourceClosure (T : Subgroup G) L R z
  let H := centralizer ({z} : Set G)
  let X := strictCrossingGroup (T : Subgroup G) L R z d
  let C' := strictCrossingCenter (T : Subgroup G) L R z d
  let N := (strictQuotientAction (T : Subgroup G) L R z).ker.map H.subtype
  have hdL : d ∈ L := ((map_subtype_le _) hdres).1
  have hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G) := ((map_subtype_le _) hdres).2
  have hCX : C' ≤ X := strictCrossingCenter_le_group h611 hz hdZ
  have hcut : C' ⊓ N = (zpowers z).map (MulAut.conj d⁻¹).toMonoidHom := by
    calc
      C' ⊓ N = C' ⊓ (X ⊓ N) := by rw [← inf_assoc, inf_eq_left.mpr hCX]
      _ = C' ⊓ strictCrossingIntersection (T : Subgroup G) L R z d := by
        rw [A.strict_crossing_action_kernel h611 hnatural hz horder hTH hstrict hdres hdH]
      _ = C' ⊓ U := by
        change C' ⊓ (U ⊓ U.map _) = C' ⊓ U
        rw [inf_left_comm, inf_eq_left.mpr (show C' ≤ U.map _ from hCX.trans inf_le_left), inf_comm]
      _ = _ := A.strict_crossing_center_intersection h611 hnatural hz horder hTH hstrict hdL hdZ hdH
  have hc := relative_image_card C' H
    (hCX.trans (strictCrossingGroup_le_centralizer _ _ _ _ _ hz))
    (QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker)
  rw [QuotientGroup.ker_mk'] at hc
  change Nat.card (strictCrossingCenterImage (T : Subgroup G) L R z d) * Nat.card (C' ⊓ N : Subgroup G) = Nat.card C' at hc
  rw [hcut, card_map_of_injective (MulAut.conj d⁻¹).injective, Nat.card_zpowers, horder] at hc
  change Nat.card (strictCrossingCenterImage (T : Subgroup G) L R z d) * 2 =
    Nat.card (((center U).map U.subtype).map (MulAut.conj d⁻¹).toMonoidHom) at hc
  rw [card_map_of_injective (MulAut.conj d⁻¹).injective,
    card_map_of_injective U.subtype_injective] at hc
  exact hc


private theorem elementary_card_rank (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : Nat.card A = 2 ^ Group.rank A := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  have he : Group.rank A = Module.finrank (ZMod 2) (Additive A) := by
    apply le_antisymm (IsElementaryAbelian.rank_le_finrank (p := 2) A)
    have hc : Nat.card A = 2 ^ Module.finrank (ZMod 2) (Additive A) := by
      rw [Nat.card_congr Additive.ofMul]
      simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [← hc]
    exact Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' A
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 A)))
  rw [he, Nat.card_congr Additive.ofMul]
  simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)

/-- Source 6.2.17(10), with the smaller actor the literal image of Z(U)^d.
The equality uses conjugate subgroup orders and both order-two center cuts. -/
theorem LocalAnalysis.strict_crossing_quotient_rank
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    [IsElementaryAbelian 2 (strictCrossingImage (T : Subgroup G) L R z d)] :
    let X := strictCrossingImage (T : Subgroup G) L R z d
    let X₀ := (strictCrossingCenterImage (T : Subgroup G) L R z d).subgroupOf X
    Module.finrank (ZMod 2) (strictHatSpace (T : Subgroup G) L R z
      (strictCrossingIntersection (T : Subgroup G) L R z d)) + Group.rank (X ⧸ X₀) + 1 =
        Module.finrank (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)) := by
  let U := sourceClosure (T : Subgroup G) L R z
  let H := centralizer ({z} : Set G)
  let C := (center U).map U.subtype
  let S := ZS (T : Subgroup G) L R
  let W := U ⊓ centralizer (S : Set G)
  let E := strictCrossingIntersection (T : Subgroup G) L R z d
  let X := strictCrossingGroup (T : Subgroup G) L R z d
  let Xd := strictCrossingImage (T : Subgroup G) L R z d
  let Cd := strictCrossingCenterImage (T : Subgroup G) L R z d
  let X₀ := Cd.subgroupOf Xd
  let Eh := strictHatSpace (T : Subgroup G) L R z E
  let Wh := strictHatSpace (T : Subgroup G) L R z W
  have hdL : d ∈ L := ((map_subtype_le _) hdres).1
  have hdZ : d ∈ normalizer (S : Set G) := ((map_subtype_le _) hdres).2
  have hEC : E ⊓ C = zpowers z := by
    change (U ⊓ U.map _) ⊓ C = _
    rw [inf_right_comm, inf_eq_right.mpr (map_subtype_le _), inf_comm]
    simpa only [inf_comm] using
      A.strict_center_intersection_crossing h611 hnatural hz horder hTH hstrict hdL hdZ hdH
  have hCW : C ≤ W := by
    refine le_inf (map_subtype_le _) ?_
    rintro c ⟨c, hc, rfl⟩ s hs
    exact congrArg Subtype.val (mem_center_iff.mp hc ⟨s, (hstrict.le hs).1⟩)
  have hXW : Nat.card X = Nat.card W := by
    have he : W.map (MulAut.conj d⁻¹).toMonoidHom = X := by
      have hc : (centralizer (S : Set G)).map (MulAut.conj d⁻¹).toMonoidHom = centralizer (S : Set G) :=
        mem_normalizer_iff_map_conj_eq.mp ((normalizer (centralizer (S : Set G) : Set G)).inv_mem
          (normalizer_le_normalizer_centralizer S hdZ))
      change (U ⊓ centralizer (S : Set G)).map _ = _
      rw [map_inf _ _ _ (MulAut.conj d⁻¹).injective, hc]
      rfl
    rw [← he, card_map_of_injective (MulAut.conj d⁻¹).injective]
  have hEcard : Nat.card Eh * 2 = Nat.card E := by
    have hc := hat_card_mul_center E (show E ≤ U from inf_le_left)
    change Nat.card Eh * Nat.card (E ⊓ C : Subgroup G) = _ at hc
    rwa [hEC, Nat.card_zpowers, horder] at hc
  have hWcard : Nat.card Wh * Nat.card C = Nat.card W := by
    have hc := hat_card_mul_center W (show W ≤ U from inf_le_left)
    change Nat.card Wh * Nat.card (W ⊓ C : Subgroup G) = _ at hc
    rwa [inf_eq_right.mpr hCW] at hc
  have hXcard : Nat.card Xd * Nat.card E = Nat.card X := by
    have hc := relative_image_card X H (strictCrossingGroup_le_centralizer _ _ _ _ _ hz)
      (QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker)
    rw [QuotientGroup.ker_mk', A.strict_crossing_action_kernel h611 hnatural hz horder hTH hstrict hdres hdH] at hc
    exact hc
  have hCcard : Nat.card Cd * 2 = Nat.card C := by
    rw [card_map_of_injective U.subtype_injective]
    exact A.strict_crossing_center_image_card h611 hnatural hz horder hTH hstrict hdres hdH
  have hCX : Cd ≤ Xd := map_mono (comap_mono (strictCrossingCenter_le_group h611 hz hdZ))
  have hQcard : Nat.card (Xd ⧸ X₀) * Nat.card Cd = Nat.card Xd := by
    have hc := X₀.card_mul_index
    rw [index_eq_card, Nat.card_congr (subgroupOfEquivOfLe hCX).toEquiv] at hc
    exact (Nat.mul_comm _ _).trans hc
  have hcard : Nat.card Eh * Nat.card (Xd ⧸ X₀) = Nat.card Wh := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := C))
    calc
      Nat.card Eh * Nat.card (Xd ⧸ X₀) * Nat.card C =
          Nat.card Eh * (Nat.card (Xd ⧸ X₀) * Nat.card Cd) * 2 := by rw [← hCcard]; ring
      _ = Nat.card Xd * (Nat.card Eh * 2) := by rw [hQcard]; ring
      _ = Nat.card Wh * Nat.card C := by rw [hEcard, hXcard, hXW, hWcard]
  have hrank : Module.finrank (ZMod 2) Eh + Group.rank (Xd ⧸ X₀) = Module.finrank (ZMod 2) Wh := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      elementary_card_rank, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, ← pow_add] at hcard
    exact (Nat.pow_right_injective (by decide : 1 < 2)) hcard
  obtain ⟨he, B, ha, hn, _, _, hb, hw, hdim, _⟩ :=
    A.strict_crossing_symplectic_geometry h611 hnatural hz horder hstrict hdZ hdH
  have hWh : Module.finrank (ZMod 2) Wh + 1 =
      Module.finrank (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z)) := by
    change Module.finrank (ZMod 2) (strictHatSpace (T : Subgroup G) L R z W) + 1 = _
    rw [hw]
    exact hdim
  exact (congrArg (· + 1) hrank).trans hWh


/-- The G.10.2 numerical bounds, now discharged on the original crossing
quotient. In particular the quotient by the smaller actor is nontrivial. -/
theorem LocalAnalysis.strict_crossing_rank_bounds
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    [IsElementaryAbelian 2 (strictCrossingImage (T : Subgroup G) L R z d)] :
    let X := strictCrossingImage (T : Subgroup G) L R z d
    let X₀ := (strictCrossingCenterImage (T : Subgroup G) L R z d).subgroupOf X
    let r := Group.rank (X ⧸ X₀)
    let m := Module.finrank (ZMod 2) (Additive (StrictVectorQuotient (T : Subgroup G) L R z))
    0 < r ∧ 4 ≤ m ∧ m ≤ 2 * (r + 1) ∧
      2 * (r + 1) ≤ 2 * (primeRank 2 (StrictActor (T : Subgroup G) L R z) + 1) := by
  let X := strictCrossingImage (T : Subgroup G) L R z d
  let X₀ := (strictCrossingCenterImage (T : Subgroup G) L R z d).subgroupOf X
  have hdZ : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G) := ((map_subtype_le _) hdres).2
  obtain ⟨he, B, _, hn, hdim, _, _, _, _, _, hi⟩ :=
    A.strict_crossing_symplectic_geometry h611 hnatural hz horder hstrict hdZ hdH
  have hbound := B.twice_finrank_le_of_isotropic hn
    (strictHatSpace (T : Subgroup G) L R z (strictCrossingIntersection (T : Subgroup G) L R z d)) hi
  have hr := A.strict_crossing_quotient_rank h611 hnatural hz horder hTH hstrict hdres hdH
  have hqr := (Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
    (QuotientGroup.mk'_surjective X₀)).trans
      (X.rank_le_primeRank 2 (IsElementaryAbelian.isPGroup 2 X))
  dsimp only at hdim hbound hr ⊢
  dsimp only [X₀, X] at hqr
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
