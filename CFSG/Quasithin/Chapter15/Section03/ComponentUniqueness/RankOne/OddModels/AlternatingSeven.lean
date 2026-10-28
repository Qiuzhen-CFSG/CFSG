module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.OddModels.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.ResidualTransport
public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals
public import Theory.Alternating.Aut

/-!
# The alternating-seven component in the rank-one reduction

An actual equivalence L ≃ A₇ embeds the moving four-group and Y₊ in A₇.
Idempotence of the three-prime residual supplies generation by three-elements;
the seven-point action reduces these to elements of order three. The intrinsic
A₇ recognition theorem then identifies Y₊ with A₄, contradicting clause (d).

The geometric refinement realizes conjugation by I through Aut(A₇) = S₇.
Its kernel is exactly C_I(L). Transporting the relative normalizer and the
three-prime residual identifies the action image of M ∩ I with the stabilizer
of three pairs and a singleton. Pulling back through the same action recovers
M ∩ I itself. The triple transposition, its cycle type and its pointwise action
equation are explicit; no abstract family tag or assumed stabilizer is used.
The intrinsic residual calculation does not require a chosen source involution.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the A₇ paragraph
of 15.3.43, printed p.1140, with (a), (b), (d) on p.1139 and 1.1.5(3)(d),
printed pp.501–502. The source assembly constructs `ReducedConfiguration`;
these theorems prove its A₇ model branch, not the whole of 15.3.43.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.OddModels
variable {G : Type*} [Group G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}

/-- The actual A₇ model forces the original three-prime residual to be A₄.
The recognition proof uses the moving normal four-group and the two-core index;
it does not use `ReducedConfiguration.not_alternating_four`. -/
theorem alternating_seven_residual (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    (e : L ≃* alternatingGroup (Fin 7)) :
    Nonempty (Yplus ≃* alternatingGroup (Fin 4)) := by
  let Y := (Yplus.subgroupOf L).map e.toMonoidHom
  let V := (V₂.subgroupOf L).map e.toMonoidHom
  let eY : Yplus ≃* Y := (subgroupOfEquivOfLe c.y_le_component).symm.trans
    (equivMapOfInjective _ e.toMonoidHom e.injective)
  have hVL := plane_le_component c
  have hVY := (plane_normal_in_residual c).1
  have hVY' : V ≤ Y := map_mono (subgroupOf_mono L hVY)
  have hYMI : Yplus ≤ M ⊓ I := c.residual ▸ map_subtype_le _
  have hYN : Yplus.subgroupOf L ≤ normalizer (V₂.subgroupOf L : Set L) := by
    rw [← subgroupOf_normalizer_eq hVL]
    intro x hx
    exact c.plane_two_normalized (hYMI hx)
  have hVN : (V.subgroupOf Y).Normal := normal_subgroupOf_of_le_normalizer
    ((map_mono hYN).trans ((V₂.subgroupOf L).le_normalizer_map e.toMonoidHom))
  let : IsElementaryAbelian 2 V₂ := c.plane_two_elementary
  let : IsElementaryAbelian 2 (V₂.subgroupOf L) := IsElementaryAbelian.subgroupOf hVL
  have hVE : IsElementaryAbelian 2 V := IsElementaryAbelian.map e.toMonoidHom
  have hVc : Nat.card V = 4 := by
    rw [card_map_of_injective e.injective,
      Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv, c.plane_two_card]
  have hcommL : ⁅V₂.subgroupOf L, Yplus.subgroupOf L⁆ = V₂.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hVL,
      map_subgroupOf_eq_of_le c.y_le_component, c.plane_two_commutator]
  have hcomm : ⁅V, Y⁆ = V := by
    rw [← map_commutator, hcommL]
  have hidx : (pCore 2 Y).index = 3 := by
    rw [← pCore_map_iso 2 eY]
    exact (index_map_equiv _ eY).trans c.index
  let K := primePowerGenerated 3 (M ⊓ I : Subgroup G)
  let eR : K ≃* Yplus :=
    (equivMapOfInjective K (M ⊓ I).subtype (M ⊓ I).subtype_injective).trans
      (MulEquiv.subgroupCongr c.residual.symm)
  have hgenY : primePowerGenerated 3 Y = ⊤ :=
    primePowerGenerated_eq_top_of_surjective 3 (eR.trans eY).toMonoidHom
      (eR.trans eY).surjective (primePowerGenerated_self 3)
  have hres : Y = (primePowerGenerated 3 Y).map Y.subtype := by
    rw [hgenY, ← MonoidHom.range_eq_map, Y.range_subtype]
  have hgen := AlternatingSeven.ThreeResidualLocals.order_three_generated_of_residual_eq
    (alternatingGroup (Fin 7)).subtype (alternatingGroup (Fin 7)).subtype_injective Y Y hres
  obtain ⟨e4⟩ := AlternatingSeven.ThreeResidualLocals.residual_mulEquiv_alternating_four
    Y V hVY' hVN hVE hVc hcomm hidx hgen
  exact ⟨eY.trans e4⟩

private noncomputable def sevenAutEquiv :
    Equiv.Perm (Fin 7) ≃* MulAut (alternatingGroup (Fin 7)) :=
  MulEquiv.ofBijective MulAut.conjNormal
    (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7 (by decide) (by decide))

private noncomputable def sevenAction {H : Type*} [Group H]
    (K : Subgroup H) [K.Normal] (e : K ≃* alternatingGroup (Fin 7)) :
    H →* Equiv.Perm (Fin 7) :=
  sevenAutEquiv.symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal)

private theorem sevenAction_on_component {H : Type*} [Group H]
    (K : Subgroup H) [K.Normal] (e : K ≃* alternatingGroup (Fin 7)) (k : K) :
    sevenAction K e k = e k := by
  apply sevenAutEquiv.injective
  change sevenAutEquiv (sevenAutEquiv.symm _) = MulAut.conjNormal (e k).val
  rw [sevenAutEquiv.apply_symm_apply]
  apply MulEquiv.ext
  intro y
  apply Subtype.ext
  change (e (k * e.symm y * k⁻¹)).val = (e k).val * y.val * (e k).val⁻¹
  simp

private theorem sevenAction_range {H : Type*} [Group H]
    (K : Subgroup H) [K.Normal] (e : K ≃* alternatingGroup (Fin 7)) :
    alternatingGroup (Fin 7) ≤ (sevenAction K e).range := by
  intro a ha
  refine ⟨e.symm ⟨a, ha⟩, ?_⟩
  rw [sevenAction_on_component, e.apply_symm_apply]

private theorem sevenAction_ker {H : Type*} [Group H]
    (K : Subgroup H) [K.Normal] (e : K ≃* alternatingGroup (Fin 7)) :
    (sevenAction K e).ker = centralizer (K : Set H) := by
  ext h
  rw [MonoidHom.mem_ker]
  have hiff : sevenAction K e h = 1 ↔ MulAut.conjNormal (H := K) h = 1 := by
    change sevenAutEquiv.symm ((MulAut.congr e) (MulAut.conjNormal h)) = 1 ↔ _
    constructor
    · intro hh
      apply (MulAut.congr e).injective
      apply sevenAutEquiv.symm.injective
      simpa only [map_one] using hh
    · intro hh
      rw [hh, map_one, map_one]
  rw [hiff]
  constructor
  · intro hh k hk
    have he := congrArg (fun a : MulAut K => (a ⟨k, hk⟩ : H)) hh
    change h * k * h⁻¹ = k at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hh
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    change h * (k : H) * h⁻¹ = k
    rw [← hh k k.property]
    simp

private theorem sevenAction_injective_restriction {H : Type*} [Group H]
    (K : Subgroup H) [K.Normal] (e : K ≃* alternatingGroup (Fin 7))
    (Y : Subgroup H) (hYK : Y ≤ K) :
    Function.Injective ((sevenAction K e).comp Y.subtype) := by
  intro x y hxy
  have h : e ⟨x, hYK x.property⟩ = e ⟨y, hYK y.property⟩ := by
    apply Subtype.ext
    exact (sevenAction_on_component K e ⟨x, hYK x.property⟩).symm.trans
      (hxy.trans (sevenAction_on_component K e ⟨y, hYK y.property⟩))
  exact Subtype.ext (congrArg (fun z : K => (z : H)) (e.injective h))

private theorem sevenAction_map_le {H : Type*} [Group H]
    (K : Subgroup H) [K.Normal] (e : K ≃* alternatingGroup (Fin 7))
    (Y : Subgroup H) (hYK : Y ≤ K) :
    Y.map (sevenAction K e) ≤ alternatingGroup (Fin 7) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [sevenAction_on_component K e ⟨y, hYK hy⟩]
  exact (e ⟨y, hYK hy⟩).property


private theorem relative_image_normalizer
    {H P : Type*} [Group H] [Group P] (f : H →* P)
    (Y B : Subgroup H) (hYB : Y ≤ B) (hker : f.ker ≤ B)
    (hθ : theta B = Y) (hN : normalizer (Y : Set H) = B) :
    B.map f = f.range ⊓ normalizer (Y.map f : Set P) := by
  have hN' := image_normalizer_of_theta f.rangeRestrict f.rangeRestrict_surjective Y B
    hYB (by simpa only [MonoidHom.ker_rangeRestrict] using hker) hθ hN
  have hle : Y.map f ≤ f.range := map_le_range f Y
  have hYi : Y.map f.rangeRestrict = (Y.map f).subgroupOf f.range := by
    apply map_injective f.range.subtype_injective
    rw [map_subgroupOf_eq_of_le hle, map_map, MonoidHom.subtype_comp_rangeRestrict]
  calc
    B.map f = (B.map f.rangeRestrict).map f.range.subtype := by
      rw [map_map, MonoidHom.subtype_comp_rangeRestrict]
    _ = (normalizer (Y.map f.rangeRestrict : Set f.range)).map f.range.subtype := by rw [hN']
    _ = _ := by
      rw [hYi, ← subgroupOf_normalizer_eq hle, subgroupOf_map_subtype, inf_comm]


/-- Realize the component action on seven points and identify the actual local
subgroup as the preimage of a partition stabilizer of type `2,2,2,1`.
The action kernel is exactly `C_I(L)`, so its range faithfully realizes `I/C_I(L)`.
Both the residual image and the original ambient intersection are retained. -/
theorem alternating_seven_partition_geometry [Finite G] (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    (e : L ≃* alternatingGroup (Fin 7)) :
    ∃ f : I →* Equiv.Perm (Fin 7),
      f.ker = c.toComponentAction.kernel ∧
      (∀ x : L, f ⟨x, c.component_le x.property⟩ = (e x : Equiv.Perm (Fin 7))) ∧
      Nonempty (c.toComponentAction.Quotient ≃* f.range) ∧
      (Yplus.subgroupOf I).map f = threeResidualIn ((M.subgroupOf I).map f) ∧
      ∃ t : Equiv.Perm (Fin 7), t.cycleType = {2, 2, 2} ∧ t ^ 2 = 1 ∧
        t.partition.parts = {2, 2, 2, 1} ∧
        (M.subgroupOf I).map f = f.range ⊓
          AlternatingSeven.ThreeResidualLocals.pairPartitionStabilizer t ∧
        M.subgroupOf I =
          (AlternatingSeven.ThreeResidualLocals.pairPartitionStabilizer t).comap f ∧
        M ⊓ I = ((AlternatingSeven.ThreeResidualLocals.pairPartitionStabilizer t).comap f).map
          I.subtype ∧
        (∀ a : Fin 7, MulAction.orbit (zpowers t) a = ({a, t a} : Set (Fin 7))) ∧
        (∀ x : I, (x : G) ∈ M ↔ ∀ a, f x (t a) = t (f x a)) := by
  let K := L.subgroupOf I
  let : K.Normal := normal_subgroupOf_of_le_normalizer c.normalizes
  let eK : K ≃* alternatingGroup (Fin 7) := (subgroupOfEquivOfLe c.component_le).trans e
  let f := sevenAction K eK
  have hker : f.ker = c.toComponentAction.kernel := by
    rw [sevenAction_ker]
    ext x
    constructor
    · intro hx l hl
      exact congrArg Subtype.val (hx ⟨l, c.component_le hl⟩ hl)
    · intro hx l hl
      exact Subtype.ext (hx l hl)
  have hkerB : f.ker ≤ M.subgroupOf I := by
    rw [hker]
    exact c.toComponentAction.kernel_le_intersection c.y_le_component c.normalizer_eq
  have hon (x : L) : f ⟨x, c.component_le x.property⟩ = (e x : Equiv.Perm (Fin 7)) :=
    sevenAction_on_component K eK ⟨⟨x, c.component_le x.property⟩, x.property⟩
  let eqQ : c.toComponentAction.Quotient ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  refine ⟨f, hker, hon, ⟨eqQ⟩, ?_⟩
  let Y := Yplus.subgroupOf I
  let B := M.subgroupOf I
  have hYI : Yplus ≤ I := c.y_le_component.trans c.component_le
  have hYB : Y ≤ B := by
    intro x hx
    have hYMI : Yplus ≤ M ⊓ I := c.residual ▸ map_subtype_le _
    exact (hYMI hx).1
  have hθ : theta B = Y := by
    apply map_injective I.subtype_injective
    rw [theta_map_of_injective I.subtype I.subtype_injective,
      subgroupOf_map_subtype, c.theta_eq, map_subgroupOf_eq_of_le hYI]
  have hN : normalizer (Y : Set I) = B := by
    rw [← subgroupOf_normalizer_eq hYI]
    ext x
    exact ⟨fun hx => (c.normalizer_eq.le ⟨x.property, hx⟩).1,
      fun hx => (c.normalizer_eq.ge ⟨hx, x.property⟩).2⟩
  have hB := relative_image_normalizer f Y B hYB hkerB hθ hN
  have hresI : Y = threeResidualIn B := by
    apply map_injective I.subtype_injective
    rw [map_subgroupOf_eq_of_le hYI, threeResidualIn_map, subgroupOf_map_subtype,
      ← c.residual]
  have hres : Y.map f = threeResidualIn (B.map f) := by
    rw [hresI, threeResidualIn_map]
  have hYK : Y ≤ K := subgroupOf_mono I c.y_le_component
  have hYf : Function.Injective (f.comp Y.subtype) :=
    sevenAction_injective_restriction K eK Y hYK
  let eY : Y ≃* Y.map f := MulEquiv.ofBijective (f.subgroupMap Y)
    ⟨fun a b hab => hYf (congrArg Subtype.val hab), f.subgroupMap_surjective Y⟩
  obtain ⟨e4⟩ := alternating_seven_residual c e
  let e4' : Y.map f ≃* alternatingGroup (Fin 4) :=
    eY.symm.trans ((subgroupOfEquivOfLe hYI).trans e4)
  refine ⟨hres, ?_⟩
  obtain ⟨t, ht, ht2, hparts, hBpart, horb, _hact⟩ :=
    AlternatingSeven.ThreeResidualLocals.residual_a4_partition_geometry
      f.range (Y.map f) (B.map f) (sevenAction_range K eK)
      (sevenAction_map_le K eK Y hYK) hB hres e4'
  have hpre : B = (AlternatingSeven.ThreeResidualLocals.pairPartitionStabilizer t).comap f := by
    have h := congrArg (fun U : Subgroup (Equiv.Perm (Fin 7)) => U.comap f) hBpart
    rw [comap_map_eq, sup_eq_left.mpr hkerB, comap_inf, MonoidHom.comap_range_self] at h
    simpa using h
  have hpreG : M ⊓ I =
      ((AlternatingSeven.ThreeResidualLocals.pairPartitionStabilizer t).comap f).map
        I.subtype := by
    rw [← hpre, subgroupOf_map_subtype]
  refine ⟨t, ht, ht2, hparts, hBpart, hpre, hpreG, horb, ?_⟩
  intro x
  change x ∈ B ↔ _
  rw [hpre]
  exact AlternatingSeven.ThreeResidualLocals.mem_pairPartitionStabilizer_iff t (f x) ht2


/-- The A₇ branch contradicts the previously established exclusion of A₄ for `Y₊`. -/
theorem not_alternating_seven (c : ReducedConfiguration Yplus S M I L V₁ V₂)
    (e : L ≃* alternatingGroup (Fin 7)) : False :=
  c.not_alternating_four (alternating_seven_residual c e)

end CFSG.Quasithin.Chapter15.Section03.RankOne.OddModels
