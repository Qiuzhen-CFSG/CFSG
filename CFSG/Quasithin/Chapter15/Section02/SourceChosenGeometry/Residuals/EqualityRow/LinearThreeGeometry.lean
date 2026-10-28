module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.ComponentSelection
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.EqualityRow.NonlinearGeometry
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.ModelOnly.Geometry

/-!
# Original binary L3 geometry from the residual input

The actual wreath overgroup meets M in T and meets an escaping I in KS.
Its intersection with a binary L3 component maps to the opposite parabolic;
the two-residual supplies a cubic factor with its original quotient map.
The component-orbit and core-commutator arguments retain normality inside I.
All plane geometry is supplied by `ResidualInput`, without the partner's
prime-to-three residual identity.

Source: Aschbacher--Smith, 15.2.21--23, printed pp.1114--1116,
refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : ChosenGeometry.ResidualInput hsource H B)
include d

/-- The original outside subgroup meets M in T: Sylow maximality lifts through its wreath quotient. -/
theorem local_intersection_eq_sylow_of_residual : M ⊓ H = (T : Subgroup G) := by
  have hTH := d.geometry.outside.1.1.2
  let P := T.subtype hTH
  obtain ⟨e⟩ := d.geometry.quotient
  let ew := RegularWreathProduct.congr SLTwoPermThree.sl2Two_equiv_perm_three.some.symm
    (MulEquiv.refl (Multiplicative (ZMod 2)))
  have hp := WreathTwoResidual.sylow_isCoatom_of_core_quotient P (e.trans ew)
  have hne : (M ⊓ H).subgroupOf H ≠ ⊤ := by
    intro he
    apply d.geometry.outside.1.2
    intro x hx
    have hh : (⟨x,hx⟩ : H) ∈ (M ⊓ H).subgroupOf H := he ▸ mem_top _
    exact hh.1
  have hle : (P : Subgroup H) ≤ (M ⊓ H).subgroupOf H :=
    fun x hx => ⟨hsource.maximal.1.2 hx,x.property⟩
  have he := congrArg (map H.subtype) ((hp.le_iff_eq hne).mp hle)
  change ((M ⊓ H).subgroupOf H).map H.subtype =
    ((T : Subgroup G).subgroupOf H).map H.subtype at he
  simpa only [map_subgroupOf_eq_of_le inf_le_right,
    map_subgroupOf_eq_of_le hTH] using he

/-- The S-orbit of a C-component is normal relative to I, by the source two-orbit theorem. -/
theorem component_orbit_normalizes_of_residual (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    {X : Subgroup G} (hX : X ∈ Chapter1.cComponentsIn I) :
    I ≤ normalizer (conjugateSpanBy X (planeSylow T ⁅V,B⁆) : Set G) := by
  obtain ⟨P,hP⟩ := d.sylow_in_escape hI
  have hs := Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1
  have hQ : IsSQTK KnownSimple.IsKnownSimple (I ⧸ pCore 2 I) := by
    refine ⟨?_,hs.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hs.stronglyQuasithin p hp ho)
  let Y := conjugateSpanBy (X.subgroupOf I) (P : Subgroup I)
  let : Y.Normal := conjugateSpanBy_sylow_normal (X.subgroupOf I) P
    (Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hX.2)
  have he : Y.map I.subtype = conjugateSpanBy X (planeSylow T ⁅V,B⁆) := by
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hX.1,hP]
    rfl
  rw [← he]
  intro x hx
  apply Y.le_normalizer_map I.subtype
  exact ⟨⟨x,hx⟩,by rw [normalizer_eq_top]; trivial,rfl⟩

/-- An S-fixed C-component is normal relative to the actual escaping I. -/
theorem normal_of_orbit_eq_of_residual (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    {X : Subgroup G} (hX : X ∈ Chapter1.cComponentsIn I)
    (he : conjugateSpanBy X (planeSylow T ⁅V,B⁆) = X) :
    I ≤ normalizer (X : Set G) := by
  rw [← he]
  exact component_orbit_normalizes_of_residual d hI hX

/-- The core commutator bound yields both normalization directions for O^{3′}(M ∩ X) and K2. -/
theorem cubic_residual_commutator_le_of_residual (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    {X K2 : Subgroup G} (hXI : X ≤ I)
    (hIX : I ≤ normalizer (X : Set G))
    (hSK2 : planeSylow T ⁅V,B⁆ ≤ normalizer (K2 : Set G))
    (hK2 : IsPPerfect 2 K2) (hc : ⁅X,K2⁆ ≤ X.pCoreIn 2) :
    let Y := (primeToResidual 3 (M ⊓ X : Subgroup G)).map (M ⊓ X).subtype
    ⁅Y,K2⁆ ≤ Y ⊓ K2 := by
  let Y := (primeToResidual 3 (M ⊓ X : Subgroup G)).map (M ⊓ X).subtype
  have hQS : X.pCoreIn 2 ≤ planeSylow T ⁅V,B⁆ :=
    (pCoreIn_mono_of_normalizes hXI hIX).trans (d.core_le_plane hI)
  have hQM : X.pCoreIn 2 ≤ M := hQS.trans (inf_le_left.trans hsource.maximal.1.2)
  have he : (pResidual 2 K2).map K2.subtype = K2 := by
    rw [(pResidual_eq_top_iff 2 K2).mpr hK2,←MonoidHom.range_eq_map,range_subtype]
  have hXK2 : X ≤ normalizer (K2 : Set G) := by
    have hh := normalizes_residual_of_commutator_le_two X (planeSylow T ⁅V,B⁆) K2
      (X.pCoreIn 2) hSK2 hQS (isPGroup_pCoreIn 2 X)
      (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
      (by simpa only [he] using hc)
    simpa only [he] using hh
  have hK2MX : K2 ≤ normalizer ((M ⊓ X : Subgroup G) : Set G) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono inf_le_right le_rfl).trans hc).trans
      (le_inf hQM (pCoreIn_le 2 X))
  have hK2Y : K2 ≤ normalizer (Y : Set G) :=
    hK2MX.trans (normalizer_le_normalizer_characteristic_image (M ⊓ X)
      (primeToResidual 3 (M ⊓ X : Subgroup G)))
  exact le_inf (le_normalizer_iff_commutator_le_left.mp hK2Y)
    (le_normalizer_iff_commutator_le_right.mp
      (((map_subtype_le _).trans inf_le_right).trans hXK2))

include d in
/-- The original intersection H ∩ I is KS, using the supplied Sylow
subgroup and the source residual; this does not assume that X is normal. -/
theorem local_escape_intersection_of_residual (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    H ⊓ I = (pResidual 2 H).map H.subtype ⊔ planeSylow T ⁅V,B⁆ := by
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I := (le_sup_left.trans (d.residual_sup_planeCentralizer_le hI)).trans inf_le_right
  have hSI : planeSylow T ⁅V,B⁆ ≤ I :=
    (le_sup_right.trans (d.residual_sup_planeCentralizer_le hI)).trans inf_le_right
  apply le_antisymm ?_ (sup_le (le_inf (map_subtype_le _) hKI)
    (le_inf (inf_le_left.trans d.geometry.outside.1.1.2) hSI))
  intro x hx
  let P := T.subtype d.geometry.outside.1.1.2
  have hmem : (⟨x,hx.1⟩ : H) ∈ pResidual 2 H ⊔ (P : Subgroup H) := by
    rw [pResidual_sup_sylow_eq_top P]
    trivial
  obtain ⟨k,hk,t,ht,he⟩ := mem_sup_of_normal_left.mp hmem
  have htI : (t : G) ∈ I := by
    have hh : (k : G) * (t : G) = x := congrArg H.subtype he
    have hi := I.mul_mem (I.inv_mem (hKI (mem_map_of_mem H.subtype hk))) hx.2
    rw [← hh] at hi
    change (k : G)⁻¹ * ((k : G) * (t : G)) ∈ I at hi
    simpa only [inv_mul_cancel_left] using hi
  have htS : (t : G) ∈ planeSylow T ⁅V,B⁆ := by
    have hh : (t : G) ∈ I ⊓ (T : Subgroup G) := ⟨htI,ht⟩
    rw [d.twoGroup_intersection hI le_rfl] at hh
    exact hh.1
  have hh : (k : G) * (t : G) = x := congrArg H.subtype he
  rw [← hh]
  exact mul_mem_sup (mem_map_of_mem H.subtype hk) htS

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : ChosenGeometry.ResidualInput hsource H B)

include d in
/-- The original rank-two residual meets X in a subgroup of order divisible by three. -/
theorem Branch.residual_component_intersection_three_dvd_of_residual
    {X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : Branch M I X n F) (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    3 ∣ Nat.card ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G) := by
  have hKX : (pResidual 2 H).map H.subtype ≤ normalizer (X : Set G) := by
    have hh := d.residual_normalizes_component hI b.input.component.2
    rwa [map_subgroupOf_eq_of_le b.input.component.1] at hh
  apply d.residual_intersection_three_dvd hI b.input.component.1 hKX
  obtain ⟨e⟩ := b.model
  have hd : 3 ∣ Nat.card (X ⧸ pCore 2 X) := by
    rw [Nat.card_congr e.toEquiv]
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using b.field_card)
    exact Theory.SpecificGroups.three_dvd_card_sl_three F
  exact hd.trans (by simpa only [index_eq_card] using (pCore 2 X).index_dvd_card)


end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : ChosenGeometry.ResidualInput hsource H B)

include d in
private theorem component_sylow_intersection_of_residual (hI : PlaneEscapes Mc ⁅V,B⁆ I)
    (hX : X ∈ Chapter1.cComponentsIn I) :
    ∃ P : Sylow 2 X, (P : Subgroup X) = (planeSylow T ⁅V,B⁆).subgroupOf X := by
  obtain ⟨R,hR⟩ := d.sylow_in_escape hI
  obtain ⟨Q,hQ⟩ := R.exists_subgroupOf_eq_of_subnormal (X.subgroupOf I) hX.2.subnormal
  let e := subgroupOfEquivOfLe hX.1
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (Q : Subgroup (X.subgroupOf I)).map e.toMonoidHom = _
  rw [hQ]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    have hR' : map I.subtype (R : Subgroup I) = planeSylow T ⁅V,B⁆ := by
      simpa only [ChosenGeometry.planeCentralizer] using hR
    exact hR' ▸ mem_map_of_mem I.subtype hy
  · intro hx
    have hr : (⟨x,hX.1 x.property⟩ : I) ∈ R := by
      apply (mem_map_iff_mem I.subtype_injective).mp
      rwa [hR]
    exact ⟨⟨⟨x,hX.1 x.property⟩,x.property⟩,hr,rfl⟩

include d in
private theorem local_seven_not_dvd_of_residual : ¬ 7 ∣ Nat.card H := by
  obtain ⟨e⟩ := d.geometry.quotient
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  have hc : Nat.card (H ⧸ pCore 2 H) = 72 := by
    rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card, Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card]
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 H),hc,hn]
  intro hd
  rcases (by decide : Nat.Prime 7).dvd_mul.mp hd with hh | hh
  · norm_num at hh
  · have := (by decide : Nat.Prime 7).dvd_of_dvd_pow hh
    norm_num at this

include d in
/-- One quotient marking sends the actual H ∩ X to a maximal parabolic
and S ∩ X to its Borel in the binary branch. -/
theorem Branch.binary_local_marking_of_residual
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    ∃ e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL,
      ((H.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map e.toMonoidHom =
        Matrix.PSL3Two.lineParabolicSL ∧
      (((planeSylow T ⁅V,B⁆).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
        e.toMonoidHom = Matrix.PSL3Two.borelSL := by
  obtain ⟨e₀⟩ := b.model
  let := Fintype.ofFinite F
  have hc : Nat.card F = 2 := by simpa using b.field_card
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hc)).symm
  let e₁ := e₀.trans (Atlas.fieldEquivSL 3 ef)
  let q := QuotientGroup.mk' (pCore 2 X)
  let J := H.subgroupOf X
  let A := J.map q
  let j : J →* H := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : H => (z : G)) he
  have hne : A ≠ ⊤ := by
    intro he
    have hd := (J.card_map_dvd q).trans (card_dvd_of_injective j hj)
    change Nat.card A ∣ Nat.card H at hd
    rw [he,Nat.card_congr topEquiv.toEquiv,Nat.card_congr e₁.toEquiv,
      Matrix.PSL3Two.card_SL] at hd
    exact local_seven_not_dvd_of_residual d ((by decide : 7 ∣ 168).trans hd)
  have hd : 3 ∣ Nat.card J := by
    have hle : (pResidual 2 H).map H.subtype ⊓ X ≤ H ⊓ X :=
      inf_le_inf_right X (map_subtype_le _)
    have hh := (b.residual_component_intersection_three_dvd_of_residual d hI).trans (card_dvd_of_le hle)
    rw [← card_map_of_injective (K := J) X.subtype_injective,subgroupOf_map_subtype]
    exact hh
  have htwo : ¬ IsPGroup 2 A := by
    intro hp
    have hzero : primeRank 3 A = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr (by
      intro hd
      obtain ⟨r,hr⟩ := hp.exists_card_eq
      rw [hr] at hd
      exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd))
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3)
      q (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)] at hzero
    exact (PrimeRank.eq_zero_iff_not_dvd_card.mp hzero) hd
  obtain ⟨P,hP⟩ := component_sylow_intersection_of_residual d hI b.input.component
  have hPJ : (P : Subgroup X) ≤ J := by
    rw [hP]
    exact comap_mono (inf_le_left.trans d.geometry.outside.1.1.2)
  obtain ⟨e,hs,ha⟩ := Matrix.PSL3Two.exists_sylow_line_marking
    (e₁.trans Matrix.PSL3Two.equiv) (P.mapSurjective (QuotientGroup.mk'_surjective _)) A
    (map_mono hPJ) hne htwo
  exact ⟨e,ha,by simpa only [Sylow.coe_mapSurjective,hP] using hs⟩


/-- Taking O² of K ∩ X or of H ∩ X gives the same actual subgroup. -/
private theorem binary_intersection_residual_eq_local_of_residual :
    (pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
      ((pResidual 2 H).map H.subtype ⊓ X).subtype =
    (pResidual 2 (H ⊓ X : Subgroup G)).map (H ⊓ X).subtype := by
  let A := (pResidual 2 H).map H.subtype ⊓ X
  let B := (pResidual 2 (H ⊓ X : Subgroup G)).map (H ⊓ X).subtype
  have hBA : B ≤ A := le_inf (embedded_pResidual_mono 2 inf_le_left)
    ((map_subtype_le _).trans inf_le_right)
  have hp : IsPPerfect 2 (B.subgroupOf A) :=
    (isPPerfect_embedded_pResidual 2 (H ⊓ X)).of_surjective
      (subgroupOfEquivOfLe hBA).symm.toMonoidHom (subgroupOfEquivOfLe hBA).symm.surjective
  apply le_antisymm (embedded_pResidual_mono 2 (inf_le_inf_right X (map_subtype_le _)))
  have hh := map_mono (f := A.subtype) (le_pResidual_of_isPPerfect (B.subgroupOf A) hp)
  rwa [map_subgroupOf_eq_of_le hBA] at hh

include d in
/-- The same marking identifies the literal candidate K₁ = O²(K ∩ X)
with the line-parabolic residual in the component quotient. -/
theorem Branch.binary_factor_marking_of_residual
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    let L := (pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
      ((pResidual 2 H).map H.subtype ⊓ X).subtype
    ∃ e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL,
      ((H.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map e.toMonoidHom =
        Matrix.PSL3Two.lineParabolicSL ∧
      (((planeSylow T ⁅V,B⁆).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
        e.toMonoidHom = Matrix.PSL3Two.borelSL ∧
      ((L.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map e.toMonoidHom =
        Matrix.PSL3Two.MarkedAutomorphisms.lineA := by
  dsimp only
  rw [binary_intersection_residual_eq_local_of_residual]
  obtain ⟨e,hJ,hS⟩ := b.binary_local_marking_of_residual d hI
  refine ⟨e,hJ,hS,?_⟩
  let J := H.subgroupOf X
  have hh : ((pResidual 2 (H ⊓ X : Subgroup G)).map (H ⊓ X).subtype).subgroupOf X =
      (pResidual 2 J).map J.subtype := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans inf_le_right),
      map_embedded_pResidual,subgroupOf_map_subtype]
  rw [hh,map_embedded_pResidual,map_embedded_pResidual,hJ]
  exact Matrix.PSL3Two.MarkedAutomorphisms.line_residual

include d in
/-- The actual candidate O²(K ∩ X) has quotient of order three by its
own two-core. The core is not confused with the two-residual. -/
theorem Branch.binary_factor_core_quotient_card_of_residual
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    let L := (pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
      ((pResidual 2 H).map H.subtype ⊓ X).subtype
    Nat.card (L ⧸ pCore 2 L) = 3 := by
  let L := (pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
    ((pResidual 2 H).map H.subtype ⊓ X).subtype
  have hLX : L ≤ X := (map_subtype_le _).trans inf_le_right
  obtain ⟨e,_,_,hL⟩ := b.binary_factor_marking_of_residual d hI
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  let A := L.subgroupOf X
  have hf : A.map f = Matrix.PSL3Two.MarkedAutomorphisms.lineA := by
    rw [← map_map]
    exact hL
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hkA : IsPGroup 2 (f.subgroupMap A).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let eA := f.subgroupMap A |>.pCoreQuotientEquiv (f.subgroupMap_surjective A) hkA
  let eL := subgroupOfEquivOfLe hLX
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr eA.toEquiv,hf]
    exact Matrix.PSL3Two.MarkedAutomorphisms.card_line_core_quotient
  rw [Nat.card_congr (QuotientGroup.congr (pCore 2 A) (pCore 2 L) eL
    (pCore_map_iso 2 eL)).toEquiv] at hc
  exact hc


include d in
/-- The original H ∩ X is a maximal subgroup of X, lifting the binary
parabolic through O₂(X). -/
theorem Branch.binary_local_isCoatom_of_residual
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ⁅V,B⁆ I) :
    IsCoatom (H.subgroupOf X) := by
  obtain ⟨e,hJ,_⟩ := b.binary_local_marking_of_residual d hI
  have hm : IsCoatom ((H.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) :=
    (e.mapSubgroup.isCoatom_iff _).mp (by
      change IsCoatom (((H.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map e.toMonoidHom)
      rw [hJ]
      exact Matrix.PSL3Two.isCoatom_lineParabolicSL)
  have hc := isCoatom_comap_of_surjective (QuotientGroup.mk'_surjective (pCore 2 X)) hm
  have hcore : X.pCoreIn 2 ≤ H :=
    (pCoreAmbient_mono_of_isSubnormalIn X I 2 b.input.component.1
      b.input.component.2.subnormal).trans
      ((d.core_le_plane hI).trans (inf_le_left.trans d.geometry.outside.1.1.2))
  have hk : (QuotientGroup.mk' (pCore 2 X)).ker ≤ H.subgroupOf X := by
    rw [QuotientGroup.ker_mk']
    exact fun x hx => hcore (mem_map_of_mem X.subtype hx)
  rwa [comap_map_eq_self hk] at hc

include d in
/-- Once the preliminary block reduction puts X outside Mc, its actual
centralizer of ⁅V,B⁆ and its Mc-intersection are both H ∩ X. -/
theorem Branch.binary_centralizer_eq_local_of_residual
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hout : ¬ X ≤ Mc) :
    Mc ⊓ X = H ⊓ X ∧ X ⊓ centralizer ((⁅V,B⁆ : Subgroup G) : Set G) = H ⊓ X := by
  have hne : Mc.subgroupOf X ≠ ⊤ := by
    intro he
    apply hout
    intro x hx
    exact (show (⟨x,hx⟩ : X) ∈ Mc.subgroupOf X from he ▸ mem_top _)
  have he := ((b.binary_local_isCoatom_of_residual d hI).le_iff_eq hne).mp
    (comap_mono d.geometry.in_partner)
  have hMX : Mc ⊓ X = H ⊓ X := by
    have hh := congrArg (map X.subtype) he
    simpa only [subgroupOf_map_subtype] using hh
  refine ⟨hMX,le_antisymm ?_ ?_⟩
  · rw [← hMX]
    exact le_inf (inf_le_right.trans ((d.plane_centralizer_le_intersection hI).trans inf_le_left))
      inf_le_left
  · apply le_inf inf_le_right
    have hh : H ⊓ X ≤ H ⊓ I := inf_le_inf_left H b.input.component.1
    rw [local_escape_intersection_of_residual d hI] at hh
    exact hh.trans (sup_le d.residual_centralizes_plane inf_le_right)

include d in
/-- The candidate cubic factor is exactly O²(M₀), where M₀ = Mc ∩ X is
the printed opposite parabolic. -/
theorem Branch.binary_factor_eq_opposite_residual_of_residual
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hout : ¬ X ≤ Mc) :
    (pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
      ((pResidual 2 H).map H.subtype ⊓ X).subtype =
    (pResidual 2 (Mc ⊓ X : Subgroup G)).map (Mc ⊓ X).subtype := by
  rw [binary_intersection_residual_eq_local_of_residual]
  have he := (b.binary_centralizer_eq_local_of_residual d hI hout).1
  apply congrArg (fun Y : Subgroup G =>
    (pResidual 2 Y).map Y.subtype) at he
  exact he.symm

include d in
/-- When X is normal in I, the original candidate K₁ is normal in Mᵢ.
This discharges the normality step immediately after (*) on printed p.1116. -/
theorem Branch.binary_factor_normalized_of_residual
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ⁅V,B⁆ I) (hout : ¬ X ≤ Mc)
    (hn : I ≤ normalizer (X : Set G)) :
    Mc ⊓ I ≤ normalizer
      (((pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
        ((pResidual 2 H).map H.subtype ⊓ X).subtype) : Set G) := by
  rw [b.binary_factor_eq_opposite_residual_of_residual d hI hout]
  exact ((le_inf (inf_le_left.trans Mc.le_normalizer) (inf_le_right.trans hn)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (Mc ⊓ X) (pResidual 2 (Mc ⊓ X : Subgroup G)))


end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly
