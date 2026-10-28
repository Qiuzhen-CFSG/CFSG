module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedExtensionTransitivity
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NonseedEightNormalizerAction
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedConjugateTypes
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointPlaneCoreCard
public import Theory.Representation.SpecialLinearNatural.BinaryPointStabilizer
public import Theory.AtlasPort.OtherSporadic.GroupTheory.NormalOrbitDivisibility

/-!
# The six-point inner orbit of the selected elementary sixteen

The normalizer of the nonseed eight is transitive on its six points outside
the marked line. Stabilizing either of its two extensions has index at most
two. The original point core has orbits of size two there, by the actual
point-core centralizer calculation. Normal-orbit divisibility and the
index-two bound therefore force the extension stabilizer to be transitive
on all six points, without assuming that the full normalizer fixes it.
-/

public noncomputable section
open Subgroup Theory.GroupTheory MulAction
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.HigmanSims

private theorem eight_point_fixer {D : Type*} [Group D] [Finite D]
    [IsElementaryAbelian 2 D] (hD : Nat.card D = 8)
    (u x y : D) (hu : u ≠ 1) (hx : x ≠ 1) (hy : y ≠ 1)
    (hxu : x ≠ u) (hyu : y ≠ u) :
    ∃ a : MulAut D, a u = u ∧ a x = y := by
  have hd : Module.finrank (ZMod 2) (Additive D) = 3 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D)
    change Nat.card D = _ at hh
    rw [hD, Nat.card_zmod] at hh
    exact Nat.pow_right_injective (by decide : 1 < 2) (by simpa using hh.symm)
  let e := (Module.finBasisOfFinrankEq (ZMod 2) (Additive D) hd).equivFun
  obtain ⟨g, hgu, hgx⟩ := Representation.BinaryPointStabilizer.exists_point_fixer
    (e (Additive.ofMul u)) (e (Additive.ofMul x)) (e (Additive.ofMul y))
    (fun hh => hu (e.injective (hh.trans e.map_zero.symm)))
    (fun hh => hx (e.injective (hh.trans e.map_zero.symm)))
    (fun hh => hy (e.injective (hh.trans e.map_zero.symm)))
    (fun hh => hxu (e.injective hh)) (fun hh => hyu (e.injective hh))
  let t := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 3 → ZMod 2)
    ((Representation.specialLinearNatural 3).asGroupHom g)
  let a := (e.trans t).trans e.symm
  refine ⟨MulEquiv.toAdditive.symm a.toAddEquiv, ?_, ?_⟩
  · apply e.injective
    change e (e.symm (t (e (Additive.ofMul u)))) = e (Additive.ofMul u)
    rw [e.apply_symm_apply]
    exact hgu
  · apply e.injective
    change e (e.symm (t (e (Additive.ofMul x)))) = e (Additive.ofMul y)
    rw [e.apply_symm_apply]
    exact hgx

variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

omit [Finite G] in
private theorem conjugacy_orbit_count (Q : Subgroup G) (x : G) :
    (conjugacyOrbit Q x).ncard * Nat.card (Q ⊓ involutionCentralizer x : Subgroup G) =
      Nat.card Q := by
  let : MulAction Q G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp Q.subtype)
  have hs : stabilizer Q x = (Q ⊓ involutionCentralizer x).subgroupOf Q := by
    ext q
    change (q : G) * x * (q : G)⁻¹ = x ↔
      (q : G) ∈ Q ∧ (q : G) ∈ involutionCentralizer x
    rw [and_iff_right q.property, mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  have hh := Nat.card_congr (orbitProdStabilizerEquivGroup Q x)
  rw [Nat.card_prod, hs, Nat.card_congr (subgroupOfEquivOfLe
    (show Q ⊓ involutionCentralizer x ≤ Q from inf_le_left)).toEquiv] at hh
  exact hh

private theorem point_core_orbit_two (h : TypeAt z V) (E : pointCoreEights z)
    (x : G) (hx : x ∈ E.val) (hx1 : x ≠ 1) (hxz : x ≠ z) :
    (conjugacyOrbit ((involutionCentralizer z).pCoreIn 2) x).ncard = 2 := by
  let : IsElementaryAbelian 2 E.val := E.property.2.2.1
  have hx2 : orderOf x = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian x hx) hx1
  obtain ⟨g, hxg⟩ := h.centralizer_core_involution_seed_conjugate x (E.property.1 hx) hx2
  have hfix : (g : G) * z * (g : G)⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.mp g.property, mul_inv_cancel_right]
  have ht := h.conj (g : G)
  rw [hfix] at ht
  have hC := ht.point_core_other_point_centralizer_card x hxg hx1 hxz
  have hQ : Nat.card ((involutionCentralizer z).pCoreIn 2) = 64 := by
    rw [pCoreIn, card_map_of_injective (involutionCentralizer z).subtype_injective,
      ← h.centralizer_fitting]
    exact h.centralizer_core_card
  have hh := conjugacy_orbit_count ((involutionCentralizer z).pCoreIn 2) x
  rw [hC, hQ] at hh
  omega

private theorem inner_transitive (h : TypeAt z V) (E : pointCoreEights z)
    (hEn : E.val ∉ pointCoreSeedOrbit z V) (A B : Subgroup G)
    (hEA : E.val ≤ A) (hAe : IsElementaryAbelian 2 A) (hA16 : Nat.card A = 16)
    (hne : A ≠ B) (hQA : (involutionCentralizer z).pCoreIn 2 ≤ normalizer (A : Set G))
    (hall : ∀ F : Subgroup G, E.val ≤ F → IsElementaryAbelian 2 F →
      Nat.card F = 16 → F = A ∨ F = B) :
    ∀ x ∈ E.val, x ≠ 1 → x ≠ z → ∀ y ∈ E.val, y ≠ 1 → y ≠ z →
      ∃ g ∈ (involutionCentralizer z ⊓ normalizer (E.val : Set G)) ⊓ normalizer (A : Set G),
        g * x * g⁻¹ = y := by
  classical
  let H := involutionCentralizer z
  let N := H ⊓ normalizer (E.val : Set G)
  let L := (normalizer (A : Set G)).subgroupOf N
  let Q := H.pCoreIn 2
  let QN := Q.subgroupOf N
  have hQN : Q ≤ N := by
    refine le_inf (pCoreIn_le 2 H) ?_
    apply le_normalizer_iff_commutator_le_right.mpr
    apply commutator_le.mpr
    intro q hq e he
    exact (zpowers_le.mpr E.property.2.1)
      (h.point_core_commutator_mem q e hq (E.property.1 he))
  have hQNL : QN ≤ L := fun q hq => hQA hq
  have hQNdef : QN = (pCore 2 H).comap (inclusion (show N ≤ H from inf_le_left)) := by
    ext q
    change H.subtype (inclusion inf_le_left q) ∈ (pCore 2 H).map H.subtype ↔ _
    exact mem_map_iff_mem H.subtype_injective
  let : QN.Normal := hQNdef ▸ inferInstanceAs
    ((pCore 2 H).comap (inclusion (show N ≤ H from inf_le_left))).Normal
  let R := QN.subgroupOf L
  let : R.Normal := inferInstanceAs (QN.comap L.subtype).Normal
  let : IsElementaryAbelian 2 E.val := E.property.2.2.1
  let : IsElementaryAbelian 2 A := hAe
  let : MulAction N (Subgroup G) :=
    MulAction.compHom (Subgroup G) (MulAut.conj.comp N.subtype)
  have hLs : stabilizer N A = L := by
    ext g
    change A.map (MulAut.conj (g : G)).toMonoidHom = A ↔
      (g : G) ∈ normalizer (A : Set G)
    exact mem_normalizer_iff_map_conj_eq.symm
  have hiL : L.index ≤ 2 := by
    rw [← hLs, index_stabilizer]
    have hsub : orbit N A ⊆ {A, B} := by
      rintro F ⟨g, rfl⟩
      have he : E.val.map (MulAut.conj (g : G)).toMonoidHom = E.val :=
        mem_normalizer_iff_map_conj_eq.mp g.property.2
      apply hall
      · change E.val ≤ A.map (MulAut.conj (g : G)).toMonoidHom
        rw [← he]
        exact map_mono hEA
      · exact IsElementaryAbelian.map (MulAut.conj (g : G)).toMonoidHom
      · exact (card_map_of_injective (MulAut.conj (g : G)).injective).trans hA16
    exact (Set.ncard_le_ncard hsub).trans_eq (Set.ncard_pair hne)
  let : L.Normal := by
    by_cases hi : L.index = 1
    · rw [index_eq_one.mp hi]
      infer_instance
    · have hp := L.index_ne_zero_of_finite
      exact L.normal_of_index_eq_two (by omega)
  let : MulAction N G := MulAction.compHom G
    (ConjAct.toConjAct.toMonoidHom.comp N.subtype)
  let X : Set G := {x | x ∈ E.val ∧ x ≠ 1 ∧ x ≠ z}
  have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
  have hXcard : X.ncard = 6 := by
    have he : X = (E.val : Set G) \ {1, z} := by ext x; simp [X]
    have hs : ({1, z} : Set G) ⊆ E.val := by
      intro x hx
      rcases hx with rfl | hx
      · exact E.val.one_mem
      · exact (Set.mem_singleton_iff.mp hx) ▸ E.property.2.1
    have hh := Set.ncard_sdiff_add_ncard_of_subset hs
    rw [← he, Set.ncard_pair hz1.symm] at hh
    change X.ncard + 2 = Nat.card E.val at hh
    rw [E.property.2.2.2] at hh
    omega
  have hfull (x : G) (hx : x ∈ X) : orbit N x = X := by
    apply Set.Subset.antisymm
    · rintro y ⟨g, rfl⟩
      have hzfix : (g : G) * z * (g : G)⁻¹ = z := by
        rw [mem_centralizer_singleton_iff.mp g.property.1, mul_inv_cancel_right]
      refine ⟨(mem_normalizer_iff.mp g.property.2 x).mp hx.1, ?_, ?_⟩
      · intro hh
        exact hx.2.1 ((MulAut.conj (g : G)).injective
          (hh.trans (map_one _).symm))
      · intro hh
        exact hx.2.2 ((MulAut.conj (g : G)).injective (hh.trans hzfix.symm))
    · intro y hy
      obtain ⟨a, haz, hax⟩ := eight_point_fixer E.property.2.2.2
        (⟨z, E.property.2.1⟩ : E.val) ⟨x, hx.1⟩ ⟨y, hy.1⟩
        (fun he => hz1 (congrArg Subtype.val he))
        (fun he => hx.2.1 (congrArg Subtype.val he))
        (fun he => hy.2.1 (congrArg Subtype.val he))
        (fun he => hx.2.2 (congrArg Subtype.val he))
        (fun he => hy.2.2 (congrArg Subtype.val he))
      obtain ⟨g, hg⟩ := h.point_core_nonseed_eight_point_action_surjective E hEn ⟨a, haz⟩
      refine ⟨g, ?_⟩
      have hh := congrArg (fun t : MulAction.stabilizer (MulAut E.val)
        (⟨z, E.property.2.1⟩ : E.val) => ((t : MulAut E.val) ⟨x, hx.1⟩ : G)) hg
      exact hh.trans (congrArg Subtype.val hax)
  intro x hx hx1 hxz y hy hy1 hyz
  have hxX : x ∈ X := ⟨hx, hx1, hxz⟩
  have hNorbit : (orbit N x).ncard = 6 := (congrArg Set.ncard (hfull x hxX)).trans hXcard
  have hN768 : Nat.card N = 768 := h.point_core_nonseed_eight_normalizer_card E hEn
  have hstab : Nat.card (stabilizer N x) = 128 := by
    have hh := Nat.card_congr (orbitProdStabilizerEquivGroup N x)
    rw [Nat.card_prod, hN768] at hh
    change (orbit N x).ncard * Nat.card (stabilizer N x) = 768 at hh
    rw [hNorbit] at hh
    omega
  have hstabL : Nat.card (stabilizer L x) ≤ 128 := by
    have he : stabilizer L x = (stabilizer N x).subgroupOf L := by ext g; rfl
    rw [he, ← card_subtype L ((stabilizer N x).subgroupOf L), subgroupOf_map_subtype]
    exact (card_le_of_le (show stabilizer N x ⊓ L ≤ stabilizer N x from inf_le_left)).trans_eq hstab
  have hLlarge : 384 ≤ Nat.card L := by
    have hh := L.card_mul_index
    rw [hN768] at hh
    nlinarith
  have hOlarge : 3 ≤ (orbit L x).ncard := by
    have hh := Nat.card_congr (orbitProdStabilizerEquivGroup L x)
    rw [Nat.card_prod] at hh
    change (orbit L x).ncard * Nat.card (stabilizer L x) = Nat.card L at hh
    nlinarith
  have hOdiv : (orbit L x).ncard ∣ 6 := by
    have hh := Atlas.GroupTheory.normal_orbit_card_dvd L x
    change (orbit L x).ncard ∣ (orbit N x).ncard at hh
    rwa [hNorbit] at hh
  let eRQ : R ≃* Q := (subgroupOfEquivOfLe hQNL).trans (subgroupOfEquivOfLe hQN)
  have hRorbit : orbit R x = conjugacyOrbit Q x := by
    ext w
    constructor
    · rintro ⟨r, hr⟩
      exact ⟨eRQ r, hr⟩
    · rintro ⟨q, hq⟩
      obtain ⟨r, rfl⟩ := eRQ.surjective q
      exact ⟨r, hq⟩
  have hEven : 2 ∣ (orbit L x).ncard := by
    have hh := Atlas.GroupTheory.normal_orbit_card_dvd R x
    change (orbit R x).ncard ∣ (orbit L x).ncard at hh
    rw [hRorbit, point_core_orbit_two h E x hx hx1 hxz] at hh
    exact hh
  have hO6 : (orbit L x).ncard = 6 := by
    have hle := Nat.le_of_dvd (by decide : 0 < 6) hOdiv
    interval_cases (orbit L x).ncard <;> omega
  have hOX : orbit L x = X := Set.eq_of_subset_of_ncard_le
    ((orbit_subgroup_subset L x).trans (hfull x hxX).le) (by rw [hXcard, hO6])
  obtain ⟨g, hg⟩ := hOX.symm ▸ (show y ∈ X from ⟨hy, hy1, hyz⟩)
  exact ⟨g.val.val, ⟨g.val.property, g.property⟩, hg⟩

/-- The original pure extension also has a transitive inner six-point
stabilizer, retaining the same original points, generators and two joins. -/
theorem TypeAt.exists_inner_transitive_nonseed_extensions (h : TypeAt z V) :
    ∃ (u c b : G) (E : pointCoreEights u),
      u ∈ V ∧ u ≠ 1 ∧ TypeAt u V ∧ E.val ∉ pointCoreSeedOrbit u V ∧
      Nat.card (centralizer (E.val : Set G)) = 32 ∧
      Nat.card (involutionCentralizer u ⊓ normalizer (E.val : Set G) : Subgroup G) = 768 ∧
      orderOf c = 4 ∧ c ^ 2 = u ∧
      c ∈ (center ((involutionCentralizer u).pCoreIn 2)).map
        ((involutionCentralizer u).pCoreIn 2).subtype ∧
      b ^ 2 = 1 ∧ IsConj b z ∧ ¬ Commute b c ∧ b * c * b⁻¹ = c⁻¹ ∧
      (center (centralizer (E.val : Set G))).map
        (centralizer (E.val : Set G)).subtype = E.val ∧
      let A := E.val ⊔ zpowers b
      let B := E.val ⊔ zpowers (c * b)
      IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧
      IsElementaryAbelian 2 B ∧ Nat.card B = 16 ∧ A ≠ B ∧ A ⊓ B = E.val ∧
      (involutionCentralizer u).pCoreIn 2 ≤ normalizer (A : Set G) ⊓ normalizer (B : Set G) ∧
      centralizer (A : Set G) = A ∧ centralizer (B : Set G) = B ∧
      A ⊓ (involutionCentralizer u).pCoreIn 2 = E.val ∧
      B ⊓ (involutionCentralizer u).pCoreIn 2 = E.val ∧
      (∀ x ∈ A, x ∉ E.val → ∃ q ∈ (involutionCentralizer u).pCoreIn 2, q * b * q⁻¹ = x) ∧
      (∀ x ∈ A, x ≠ 1 → IsConj x z) ∧
      (∀ x ∈ E.val, x ≠ 1 → x ≠ u → ∀ y ∈ E.val, y ≠ 1 → y ≠ u →
        ∃ g ∈ (involutionCentralizer u ⊓ normalizer (E.val : Set G)) ⊓ normalizer (A : Set G),
          g * x * g⁻¹ = y) ∧
      (∀ F : Subgroup G,
        (E.val ≤ F ∧ IsElementaryAbelian 2 F ∧ Nat.card F = 16) ↔ F = A ∨ F = B) := by
  obtain ⟨u, c, b, E, huV, hu1, huT, hEn, hK32, hN768, hc4, hc2, hcZ,
    hb2, hbz, hnc, hbc, hcenter, hAe, hA16, hBe, hB16, hne, hi, hQN,
    hCA, hCB, hAQ, hBQ, horbit, hpure, hall⟩ := h.exists_pure_nonseed_extensions
  have hinner := inner_transitive huT E hEn _ _ le_sup_left hAe hA16 hne
    (hQN.trans inf_le_left) (fun F hEF hFe hFc => (hall F).mp ⟨hEF, hFe, hFc⟩)
  exact ⟨u, c, b, E, huV, hu1, huT, hEn, hK32, hN768, hc4, hc2, hcZ,
    hb2, hbz, hnc, hbc, hcenter, hAe, hA16, hBe, hB16, hne, hi, hQN,
    hCA, hCB, hAQ, hBQ, horbit, hpure, hinner, hall⟩

end CFSG.Quasithin.HigmanSims
