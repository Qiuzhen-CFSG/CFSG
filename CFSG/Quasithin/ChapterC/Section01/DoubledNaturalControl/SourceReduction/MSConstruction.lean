module
public import CFSG.Quasithin.ChapterC.Section01.DoubledNaturalControl.SourceReduction.Setup
public import CFSG.Quasithin.ChapterB.Section02.Baumann
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Constructing the genuine local MS hypotheses

Baumann's theorem transfers the Sylow-centralizer condition. Since the
centralizer is the ambient two-core, this places O₂(J) in B. Equality of
the images of B and R then identifies B with R ∩ J. The two-core of
H = P ∩ J maps to that same subgroup, and the source Sylow subgroup
restricts to a Sylow subgroup of the normal J, giving odd index.

For (MS3), a characteristic subgroup of B normal in J is normalized by
both L and T, hence by K. The quotient isomorphism is transported from
the specified component marking. These arguments construct every MS
field; the finite-geometry inputs remain the image equality and the
actual B.2.18 family, not assumed MS or Baumann conclusions.

Source: Aschbacher--Smith, C.1.37, printed pp.142--143, and B.2.18(3),
printed pp.80--81.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.DoubledNaturalControl.SourceReduction
open Subgroup Theory.GroupTheory Stellmacher
universe u
variable {K : Type u} [Group K] [Finite K]
  {κ : GroupClass.{u}} {L P U : Subgroup K} [L.Normal] [U.Normal]
  {T : Sylow 2 K} (d : SourceData κ L P U T)

/-- The literal first alternative of C.1.37 in K. -/
def CharacteristicObstruction (P : Subgroup K) : Prop :=
  ∃ C : Subgroup (B P), C.Characteristic ∧ C ≠ ⊥ ∧ (C.map (B P).subtype).Normal

private theorem eq_of_sylowIn_of_two {G : Type*} [Group G]
    {A E : Subgroup G} (h : IsSylowSubgroupIn A E) (hp : IsPGroup 2 E) : A = E := by
  obtain ⟨S, hS⟩ := h
  have hs : (S : Subgroup E) = ⊤ := (S.is_maximal' (hp.to_subgroup ⊤) le_top).symm
  change (S : Subgroup E).map E.subtype = A at hS
  simpa only [hs, ← MonoidHom.range_eq_map, range_subtype] using hS.symm

private theorem sylowIn_self_of_two {G : Type*} [Group G]
    (E : Subgroup G) (hp : IsPGroup 2 E) : IsSylowSubgroupIn E E := by
  let S : Sylow 2 E := Sylow.nonempty.some
  have hs : (S : Subgroup E) = ⊤ := (S.is_maximal' (hp.to_subgroup ⊤) le_top).symm
  refine ⟨S, ?_⟩
  rw [hs, ← MonoidHom.range_eq_map, range_subtype]

namespace SourceData
include d

omit [Finite K] in
/-- B.2.18(3) has the actual Sylow-centralizer input: both centralizers
are precisely the ambient two-core. -/
theorem sylow_centralizer_input :
    IsSylowSubgroupIn (R P ⊓ centralizer (U : Set K))
      ((pResidual 2 K ⊔ R P) ⊓ centralizer (U : Set K)) := by
  rw [d.centralizer_eq_core, inf_eq_right.mpr d.core_le_radical,
    inf_eq_right.mpr (d.core_le_radical.trans le_sup_right)]
  exact sylowIn_self_of_two Q pCore_isPGroup

/-- The exact Baumann family premises imply the needed core containment.
The family and its codimension bound remain explicit inputs here. -/
theorem core_le_baumann_of_family (X : Fin 3 → Subgroup K)
    (h : ChapterB.BaumannArgument.HypothesesAD U (R P) X)
    (hJI : elementaryAbelianMaxJ (R P) ≤ ⨆ i, X i) :
    pCore 2 (J L P) ≤ BJ L P := by
  let := d.elementary
  have hs := (ChapterB.lemma_B_2_18_3 U (R P) X h hJI d.sylow_centralizer_input).1
  rw [d.centralizer_eq_core, d.residual_eq] at hs
  have he : B P ⊓ Q = J L P ⊓ Q :=
    eq_of_sylowIn_of_two hs (pCore_isPGroup.to_le inf_le_right)
  intro n hn
  have hnq : (n : K) ∈ Q := by
    rw [d.core_eq_comap] at hn
    exact hn
  have hnb : (n : K) ∈ B P ⊓ Q := he.symm ▸ ⟨n.property, hnq⟩
  exact hnb.1

omit [Finite K] in
/-- The explicit local overgroup is proper. -/
theorem parabolic_proper : HJ L P < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro htop
  have hJP : J L P ≤ P := by
    intro j hj
    exact (show (⟨j, hj⟩ : J L P) ∈ HJ L P from htop ▸ mem_top _)
  have hKP : (⊤ : Subgroup K) ≤ P := by
    rw [← d.generation]
    exact sup_le (le_sup_left.trans hJP) d.sylow_le
  exact d.maximal.1 (top_le_iff.mp hKP)

/-- Restriction of the source Sylow subgroup to the normal generated group
proves the odd index required by (MS2)(a). -/
theorem parabolic_odd : Odd (HJ L P).index := by
  let := d.group_normal
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_normal (J L P)
  have hSP : (S : Subgroup (J L P)) ≤ HJ L P := by
    rw [hS]
    exact comap_mono d.sylow_le
  exact (Nat.not_even_iff_odd).mp (fun h =>
    S.not_dvd_index ((even_iff_two_dvd.mp h).trans (index_dvd_of_le hSP)))

/-- Swapping the two intersections retains the same underlying element. -/
noncomputable def parabolicIntersectionEquiv : HJ L P ≃* (J L P).subgroupOf P where
  toFun x := ⟨⟨x, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The two-core in the explicit local overgroup maps to R ∩ J in K. -/
theorem parabolic_core_map :
    ((pCore 2 (HJ L P)).map (HJ L P).subtype).map (J L P).subtype = R P ⊓ J L P := by
  let := d.group_normal
  let e := parabolicIntersectionEquiv (L := L) (P := P)
  have he := pCore_map_iso 2 e
  have hc := pCore_subnormal_eq_comap 2
    (inferInstance : ((J L P).subgroupOf P).Normal).isSubnormal
  have hm := congrArg (fun A : Subgroup ((J L P).subgroupOf P) =>
    (A.map ((J L P).subgroupOf P).subtype).map P.subtype) he
  rw [hc, map_comap_eq, range_subtype] at hm
  rw [map_inf _ _ _ P.subtype_injective, subgroupOf_map_subtype] at hm
  have hinter : (J L P ⊓ P) ⊓ R P = R P ⊓ J L P := by
    ext x
    exact ⟨fun h => ⟨h.2, h.1.1⟩,
      fun h => ⟨⟨h.2, (map_subtype_le _) h.1⟩, h.1⟩⟩
  change _ = (J L P ⊓ P) ⊓ R P at hm
  rw [hinter] at hm
  have hhom : P.subtype.comp (((J L P).subgroupOf P).subtype.comp e.toMonoidHom) =
      (J L P).subtype.comp (HJ L P).subtype := by
    ext x
    rfl
  simpa only [map_map, hhom] using hm

/-- If B has the whole radical image and contains the generated group's
core, then its intersection with R is exactly the local radical. -/
theorem radical_intersection_eq
    (himage : (B P).map d.ρK = (R P).map d.ρK)
    (hcore : pCore 2 (J L P) ≤ BJ L P) : R P ⊓ J L P = B P := by
  apply le_antisymm
  · intro r hr
    have hrbar : d.ρK r ∈ (B P).map d.ρK :=
      himage.symm ▸ mem_map_of_mem d.ρK hr.1
    obtain ⟨b, hb, hbr⟩ := hrbar
    have hq : r * b⁻¹ ∈ Q := by
      rw [← d.ambient_projection_kernel]
      change d.ρK (r * b⁻¹) = 1
      rw [map_mul, map_inv, hbr, mul_inv_cancel]
    have hj : r * b⁻¹ ∈ J L P := mul_mem hr.2 (inv_mem (mem_sup_right hb))
    have hn : (⟨r * b⁻¹, hj⟩ : J L P) ∈ pCore 2 (J L P) := by
      rw [d.core_eq_comap]
      exact hq
    have hb' := hcore hn
    change r * b⁻¹ ∈ B P at hb'
    simpa only [inv_mul_cancel_right] using (B P).mul_mem hb' hb
  · exact le_inf inf_le_left le_sup_right

/-- Genuine (MS2)(a), with HJ as the witness. -/
theorem parabolic_radical
    (himage : (B P).map d.ρK = (R P).map d.ρK)
    (hcore : pCore 2 (J L P) ≤ BJ L P) :
    (pCore 2 (HJ L P)).map (HJ L P).subtype = BJ L P := by
  apply map_injective (J L P).subtype_injective
  rw [d.parabolic_core_map, d.radical_intersection_eq himage hcore,
    map_subgroupOf_eq_of_le (show B P ≤ J L P from le_sup_right)]

omit d [Group K] [Finite K] [L.Normal] [U.Normal] in
private theorem characteristic_map_equiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (C : Subgroup G) (hC : C.Characteristic) :
    (C.map e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  obtain ⟨y, hy, rfl⟩ := hx
  let b : MulAut G := e.trans (a.trans e.symm)
  refine ⟨b y, (characteristic_iff_le_comap.mp hC b) hy, ?_⟩
  exact e.apply_symm_apply _

omit [Finite K] in
/-- In the absence of the literal obstruction in K, the generated group
satisfies genuine (MS3). Normality inside J is promoted using L and T. -/
theorem characteristic_condition (hno : ¬ CharacteristicObstruction P) :
    MSCharacteristicCondition (BJ L P) := by
  intro C hC hne hn
  let e : BJ L P ≃* B P := subgroupOfEquivOfLe le_sup_right
  let D : Subgroup (B P) := C.map e.toMonoidHom
  have hD : D.Characteristic := characteristic_map_equiv e C hC
  have hDne : D ≠ ⊥ := by
    intro hz
    apply hne
    apply eq_bot_iff.mpr
    intro c hc
    have hc' : e c ∈ D := mem_map_of_mem e.toMonoidHom hc
    rw [hz] at hc'
    have he : e c = 1 := hc'
    exact e.map_eq_one_iff.mp he
  have hmap : D.map (B P).subtype =
      (C.map (BJ L P).subtype).map (J L P).subtype := by
    rw [map_map, map_map]
    rfl
  have hJN : J L P ≤ normalizer (D.map (B P).subtype : Set K) := by
    rw [hmap]
    have h := (C.map (BJ L P).subtype).le_normalizer_map (J L P).subtype
    let := hn
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using h
  have hTN : (T : Subgroup K) ≤ normalizer (D.map (B P).subtype : Set K) := by
    let := hD
    exact d.sylow_normalizes_baumann.trans
      (normalizer_le_normalizer_characteristic_image (B P) D)
  have hnormal : (D.map (B P).subtype).Normal := by
    apply normalizer_eq_top_iff.mp
    apply eq_top_iff.mpr
    rw [← d.generation]
    exact sup_le (le_sup_left.trans hJN) hTN
  exact hno ⟨D, hD, hDne, hnormal⟩

/-- The complete MS input once the two independent finite-geometry premises
and the actual Baumann family have been supplied. No MS field is assumed. -/
noncomputable def msInput
    (hno : ¬ CharacteristicObstruction P)
    (himage : (B P).map d.ρK = (R P).map d.ρK)
    (X : Fin 3 → Subgroup K)
    (h : ChapterB.BaumannArgument.HypothesesAD U (R P) X)
    (hJI : elementaryAbelianMaxJ (R P) ≤ ⨆ i, X i) :
    BinaryMS.Input κ (LJ L P) (BJ L P) where
  sqtk := d.sqtk.subgroup (J L P)
  fitting := d.group_fitting
  product := group_product
  component := d.group_component
  radical := ⟨HJ L P, d.parabolic_proper, d.parabolic_odd,
    d.parabolic_radical himage (d.core_le_baumann_of_family X h hJI)⟩
  characteristic := d.characteristic_condition hno
  quotientEquiv := d.componentEquiv

end SourceData
end CFSG.Quasithin.ChapterC.DoubledNaturalControl.SourceReduction
