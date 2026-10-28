module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.BinaryRecognition.Reduction
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.NormalSolvable
public import Theory.Quasithin.EvenCharacteristic
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Mathlib.Data.Nat.Factorization.Basic
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The inner binary geometry in the proof of 15.3.35

Work after the component fills the quotient, preserving its given binary
linear equivalence. A nontrivial two-subgroup normalized by the two-local
M has a nonzero proper fixed space. Its subspace stabilizer has
self-centralizing two-core; maximality subject to F*=O₂ therefore makes
M exactly that stabilizer. No ordinary maximality is assumed.

The actual O_{2,Φ} shadow makes YS solvable: its kernel is an extension of
the two-core by the finite nilpotent Frattini subgroup. Normality of Y
and the two-group Sylow supplement show that nine divides |Y|. The small
binary Levi calculation forces both blocks to have dimension two. This
excludes dimension five and identifies the plane in dimension four.
There the already checked radical of order sixteen gives |M|=576, and
the Sylow subgroup and shadow force M=YS.

The plane is marked under the originally supplied equivalence. Coordinate
transport to the fixed radical model remains in `BinaryRecognition.Reduction`.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final
paragraph of the proof of 15.3.35, printed p.1139.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.BinaryRecognition.InnerGeometry
open BinaryLinear BinaryLinear.OuterCyclic
variable {X : Type*} [Group X] [Finite X]

/-- Maximality subject to F*=O₂ constructs an actual subspace stabilizer
under the specified equivalence. -/
theorem exists_parabolic_marking {n : ℕ} (hn : 0 < n)
    {M Y S : Subgroup X} (c : LocalConfiguration (⊤ : Subgroup X) M Y S)
    (e : X ≃* LinearGroup n) :
    ∃ W : Submodule (ZMod 2) (Space n), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      M.map e.toMonoidHom = parabolic W := by
  obtain ⟨Q, hQ, hQtwo, hM⟩ := Theory.Quasithin.isTwoLocal_map e c.twoLocal
  let W := fixedSpace Q
  have hW : W ≠ ⊥ := fixedSpace_ne_bot
    (by simpa [Module.natCard_eq_pow_finrank, Module.finrank_fin_fun, Nat.card_zmod]
      using (Nat.ne_of_gt hn)) hQtwo
  have hWt : W ≠ ⊤ := fixedSpace_ne_top hQ
  have hle : M.map e.toMonoidHom ≤ parabolic W := by
    rw [hM]
    exact normalizer_le_parabolic_fixedSpace Q
  let J := (parabolic W).map e.symm.toMonoidHom
  have hMJ : M ≤ J := by
    simpa [J, map_map] using map_mono (f := e.symm.toMonoidHom) hle
  have hc : centralizer (pCore 2 J : Set J) ≤ pCore 2 J :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.symm.subgroupMap (parabolic W))).mp
      (centralizer_parabolic_twoCore_le hW hWt)
  have hJM : J = M := c.maximal J hMJ
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hc)
  refine ⟨W, hW, hWt, ?_⟩
  rw [← hJM]
  simp [J, map_map]

/-- Solvability lifts through the actual O_{2,Φ} denominator. -/
theorem shadow_join_solvable {Y S : Subgroup X} (h : RankTwoShadow Y S) :
    Group.IsSolvable (Y ⊔ S : Subgroup X) := by
  let H := (Y ⊔ S : Subgroup X)
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  obtain ⟨e⟩ := h
  let : Group.IsSolvable (H ⧸ twoFrattiniCore H) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable (QuotientGroup.mk' (pCore 2 H)).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let : Group.IsNilpotent (frattini (H ⧸ pCore 2 H)) := frattini_nilpotent
  have hk : Group.IsSolvable (twoFrattiniCore H) :=
    isSolvable_comap_of_solvable_ker (QuotientGroup.mk' (pCore 2 H)) _
  exact (Group.isSolvable_iff_subgroup_quotient (twoFrattiniCore H)).mpr
    ⟨hk, inferInstance⟩

omit [Finite X] in
/-- The rank-two Frattini quotient forces an order-36 divisor. -/
theorem shadow_card_dvd {Y S : Subgroup X} (h : RankTwoShadow Y S) :
    36 ∣ Nat.card (Y ⊔ S : Subgroup X) := by
  obtain ⟨e⟩ := h
  have he : Nat.card ((Y ⊔ S : Subgroup X) ⧸ twoFrattiniCore (Y ⊔ S : Subgroup X)) = 36 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  exact he ▸ (twoFrattiniCore (Y ⊔ S : Subgroup X)).index_dvd_card

omit [Finite X] in
/-- The source normality is relative to M, since the component is now top. -/
theorem normal_y_subgroupOf {M Y S : Subgroup X}
    (c : LocalConfiguration (⊤ : Subgroup X) M Y S) : (Y.subgroupOf M).Normal := by
  apply (normal_subgroupOf_iff_le_normalizer (c.yplus_le.trans inf_le_left)).mpr
  intro m hm
  exact (normal_subgroupOf_iff_le_normalizer c.yplus_le).mp c.yplus_normal
    ⟨hm, mem_top m⟩

/-- The Sylow factor contributes no factor of three. Thus the shadow forces
nine to divide the order of the actual normal solvable subgroup Y. -/
theorem nine_dvd_card_y {M Y S : Subgroup X}
    (c : LocalConfiguration (⊤ : Subgroup X) M Y S) : 9 ∣ Nat.card Y := by
  have hYM : Y ≤ M := c.yplus_le.trans inf_le_left
  have hn : M ≤ normalizer (Y : Set X) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp (normal_y_subgroupOf c)
  have hmul := card_mul_eq_card_inf_mul_card_sup_of_normalizes Y S (c.sylow_le.trans hn)
  have hd : 9 ∣ Nat.card Y * Nat.card S := by
    rw [hmul]
    exact dvd_mul_of_dvd_right ((by decide : 9 ∣ 36).trans (shadow_card_dvd c.shadow)) _
  obtain ⟨P, hP⟩ := c.sylow
  have hs : IsPGroup 2 S := hP ▸ P.isPGroup'
  obtain ⟨k, hk⟩ := hs.exists_card_eq
  rw [hk] at hd
  exact ((by decide : Nat.Coprime 9 2).pow_right k).dvd_of_dvd_mul_right hd

/-- The geometric marking retains the actual normal solvable Y, whose order
is divisible by nine. This is the input to the small Levi-factor obstruction. -/
theorem exists_parabolic_normal_solvable_nine {n : ℕ} (hn : 0 < n)
    {M Y S : Subgroup X} (c : LocalConfiguration (⊤ : Subgroup X) M Y S)
    (e : X ≃* LinearGroup n) :
    ∃ W : Submodule (ZMod 2) (Space n), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      M.map e.toMonoidHom = parabolic W ∧
      ∃ N : Subgroup (parabolic W), N.Normal ∧ Group.IsSolvable N ∧
        9 ∣ Nat.card N ∧ N.map (parabolic W).subtype = Y.map e.toMonoidHom := by
  obtain ⟨W, hW, hWt, hM⟩ := exists_parabolic_marking hn c e
  let a := (e.subgroupMap M).trans (MulEquiv.subgroupCongr hM)
  let N := (Y.subgroupOf M).map a.toMonoidHom
  have hYM : Y ≤ M := c.yplus_le.trans inf_le_left
  have hnY := normal_y_subgroupOf c
  have hnN : N.Normal := hnY.map a.toMonoidHom a.surjective
  let : Group.IsSolvable (Y ⊔ S : Subgroup X) := shadow_join_solvable c.shadow
  let : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show Y ≤ Y ⊔ S from le_sup_left)) (inclusion_injective _)
  let : Group.IsSolvable (Y.subgroupOf M) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hYM).toMonoidHom) (subgroupOfEquivOfLe hYM).injective
  have hsN : Group.IsSolvable N := Group.isSolvable_of_surjective
    (a.toMonoidHom.subgroupMap_surjective (Y.subgroupOf M))
  have hcN : Nat.card N = Nat.card Y := by
    rw [card_map_of_injective a.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hYM).toEquiv
  refine ⟨W, hW, hWt, hM, N, hnN, hsN, hcN.symm ▸ nine_dvd_card_y c, ?_⟩
  change ((Y.subgroupOf M).map a.toMonoidHom).map (parabolic W).subtype = _
  rw [map_map]
  have ha : (parabolic W).subtype.comp a.toMonoidHom = e.toMonoidHom.comp M.subtype := by
    ext x
    rfl
  rw [ha, ← map_map, map_subgroupOf_eq_of_le hYM]

private theorem fixed_plane_parabolic_card :
    Nat.card (parabolic FourParabolicRadical.plane) = 576 := by
  let W := FourParabolicRadical.plane
  have hd : Module.finrank (ZMod 2) FourParabolicRadical.Space = 4 := by
    simp [FourParabolicRadical.Space, FourParabolicRadical.Vec,
      Module.finrank_prod]
  have hq : Module.finrank (ZMod 2) (FourParabolicRadical.Space ⧸ W) = 2 := by
    have := W.finrank_quotient_add_finrank
    rw [hd, finrank_plane] at this
    change Module.finrank (ZMod 2) (FourParabolicRadical.Space ⧸ W) + 2 = 4 at this
    omega
  let a : W ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _
    (finrank_plane.trans (Module.finrank_fin_fun (ZMod 2)).symm)
  let b : (FourParabolicRadical.Space ⧸ W) ≃ₗ[ZMod 2] Space 2 :=
    LinearEquiv.ofFinrankEq _ _ (hq.trans (Module.finrank_fin_fun (ZMod 2)).symm)
  let eqv := (SmallParabolicLevi.quotientTwoCoreEquivOfCoordinates W a b).trans
    (SmallParabolicLevi.linearTwoEquivSymmetricThree.prodCongr
      SmallParabolicLevi.linearTwoEquivSymmetricThree)
  have hi : (pCore 2 (parabolic W)).index = 36 := by
    change Nat.card (parabolic W ⧸ pCore 2 (parabolic W)) = 36
    rw [Nat.card_congr eqv.toEquiv, Nat.card_prod]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hk : Nat.card (pCore 2 (parabolic W)) = 16 := by
    rw [← card_map_of_injective (K := pCore 2 (parabolic W)) (f := (parabolic W).subtype)
      (parabolic W).subtype_injective,
      SmallParabolicLevi.map_twoCore_eq_radical]
    exact FourParabolicRadical.card_radical
  rw [← (pCore 2 (parabolic W)).card_mul_index, hk, hi]

omit [Finite X] in
/-- The actual plane stabilizer has order 576, using the already checked
sixteen-element radical and both marked two-dimensional factors. -/
theorem card_of_plane_marking (M : Subgroup X) (e : X ≃* LinearGroup 4)
    (W : Submodule (ZMod 2) (Space 4)) (hW : Module.finrank (ZMod 2) W = 2)
    (hM : M.map e.toMonoidHom = parabolic W) : Nat.card M = 576 := by
  obtain ⟨a, ha⟩ := exists_marked_equiv_of_plane M e W hW hM
  rw [← card_map_of_injective (K := M) (f := a.toMonoidHom) a.injective, ha]
  exact fixed_plane_parabolic_card

/-- Once M is marked as a plane stabilizer, the Sylow subgroup and the
order-36 Frattini shadow exhaust its order. -/
theorem eq_join_of_plane_marking {M Y S : Subgroup X}
    (c : LocalConfiguration (⊤ : Subgroup X) M Y S)
    (e : X ≃* LinearGroup 4) (W : Submodule (ZMod 2) (Space 4))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hM : M.map e.toMonoidHom = parabolic W) : M = Y ⊔ S := by
  have hcard := card_of_plane_marking M e W hW hM
  obtain ⟨P, hP⟩ := c.sylow
  let T : Sylow 2 M := P.subtype (hP.symm ▸ c.sylow_le)
  have hT : Nat.card T = 64 := by
    rw [T.card_eq_multiplicity, hcard, show 576 = 2 ^ 6 * 3 ^ 2 from rfl,
      Nat.factorization_mul (by decide) (by decide)]
    simp only [Finsupp.add_apply, Nat.factorization_pow_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3 ^ 2), add_zero]
    rfl
  have hTS : Nat.card T = Nat.card S := by
    change Nat.card (P.toSubgroup.subgroupOf M) = Nat.card S
    rw [hP]
    exact Nat.card_congr (subgroupOfEquivOfLe c.sylow_le).toEquiv
  have h64 : 64 ∣ Nat.card (Y ⊔ S : Subgroup X) := by
    rw [← hT, hTS]
    exact card_dvd_of_le le_sup_right
  have h576 : 576 ∣ Nat.card (Y ⊔ S : Subgroup X) := by
    have := Nat.lcm_dvd (shadow_card_dvd c.shadow) h64
    norm_num at this ⊢
    exact this
  symm
  apply eq_of_le_of_card_ge (sup_le (c.yplus_le.trans inf_le_left) c.sylow_le)
  rw [hcard]
  exact Nat.le_of_dvd Nat.card_pos h576

/-- Dimension five is incompatible with the normal solvable subgroup
forced by the actual rank-two local configuration. -/
theorem not_equiv_linear_five {M Y S : Subgroup X}
    (c : LocalConfiguration (⊤ : Subgroup X) M Y S)
    (e : X ≃* LinearGroup 5) : False := by
  obtain ⟨W, _, _, _, N, hN, hsN, h9, _⟩ :=
    exists_parabolic_normal_solvable_nine (by decide) c e
  let := hN
  let := hsN
  obtain ⟨hr, hs⟩ := SmallParabolicLevi.normal_solvable_nine_forces_two_blocks
    (by decide : 5 ≤ 5) W N h9
  have hd := W.finrank_quotient_add_finrank
  rw [hr, hs, Module.finrank_fin_fun] at hd
  omega

/-- In dimension four the local is YS and is the stabilizer of an actual
two-plane, marked under the given equivalence e. -/
theorem four_plane_marking {M Y S : Subgroup X}
    (c : LocalConfiguration (⊤ : Subgroup X) M Y S)
    (e : X ≃* LinearGroup 4) :
    M = Y ⊔ S ∧ ∃ W : Submodule (ZMod 2) (Space 4),
      Module.finrank (ZMod 2) W = 2 ∧ (Y ⊔ S).map e.toMonoidHom = parabolic W := by
  obtain ⟨W, _, _, hM, N, hN, hsN, h9, _⟩ :=
    exists_parabolic_normal_solvable_nine (by decide) c e
  let := hN
  let := hsN
  have hW := (SmallParabolicLevi.normal_solvable_nine_forces_two_blocks
    (by decide : 4 ≤ 5) W N h9).1
  have hjoin := eq_join_of_plane_marking c e W hW hM
  exact ⟨hjoin, W, hW, hjoin ▸ hM⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.BinaryRecognition.InnerGeometry
