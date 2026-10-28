module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.Nonbinary
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.BinaryRank
public import Theory.SpecificGroups.PSL3Two.Parabolics.ResidualRecognition
public import Theory.SpecificGroups.PSL3Two.Parabolics.CoveredResidualCommutator

/-!
# The actual binary parabolic and its cubic factor

The original H has no prime divisor seven, while H ∩ X contains the
Sylow intersection S ∩ X and has order divisible by three. The binary
Sylow-overgroup classification therefore marks its image in X/O₂(X)
as a parabolic S₄, and marks S ∩ X as its Borel. Functoriality of O²
identifies O²(K ∩ X) with that parabolic's residual; its intrinsic
two-core quotient has order three.

Once the preliminary block reduction puts X outside Mc, maximality
identifies Mc ∩ X and C_X(ZS) with H ∩ X. The intersection with the
original M ∩ X is exactly S ∩ X. If X is normal in I, the same factor
is normal in Mc ∩ I and satisfies the cubic, S-invariant factor criteria
of 15.2.21, together with the reducibility premise already proved.

The component-orbit normality, choice of the complementary distinguished
factor, and final 15.2.22 contradiction remain with this branch's owner.
The preliminary escape premise is discharged by the earlier block
reduction owned by qt-e-152-char2-block-exclusion and final assembly
qt-e-152-char2-component-models.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
15.2.23, printed p.1116; refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include d in
private theorem component_sylow_intersection (hI : PlaneEscapes Mc ZS I)
    (hX : X ∈ Chapter1.cComponentsIn I) :
    ∃ P : Sylow 2 X, (P : Subgroup X) = (planeSylow T ZS).subgroupOf X := by
  obtain ⟨R,hR⟩ := d.sylow_in_escape hI
  obtain ⟨Q,hQ⟩ := R.exists_subgroupOf_eq_of_subnormal (X.subgroupOf I) hX.2.subnormal
  let e := subgroupOfEquivOfLe hX.1
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (Q : Subgroup (X.subgroupOf I)).map e.toMonoidHom = _
  rw [hQ]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hR ▸ mem_map_of_mem I.subtype hy
  · intro hx
    have hr : (⟨x,hX.1 x.property⟩ : I) ∈ R := by
      apply (mem_map_iff_mem I.subtype_injective).mp
      rwa [hR]
    exact ⟨⟨⟨x,hX.1 x.property⟩,x.property⟩,hr,rfl⟩

include d in
private theorem local_seven_not_dvd : ¬ 7 ∣ Nat.card H := by
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
theorem Branch.binary_local_marking
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) :
    ∃ e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL,
      ((H.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map e.toMonoidHom =
        Matrix.PSL3Two.lineParabolicSL ∧
      (((planeSylow T ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
        e.toMonoidHom = Matrix.PSL3Two.borelSL := by
  obtain ⟨e₀⟩ := b.ms.1.model
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
    exact local_seven_not_dvd d ((by decide : 7 ∣ 168).trans hd)
  have hd : 3 ∣ Nat.card J := by
    have hle : (pResidual 2 H).map H.subtype ⊓ X ≤ H ⊓ X :=
      inf_le_inf_right X (map_subtype_le _)
    have hh := (b.residual_component_intersection_three_dvd d hI).trans (card_dvd_of_le hle)
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
  obtain ⟨P,hP⟩ := component_sylow_intersection d hI b.input.component
  have hPJ : (P : Subgroup X) ≤ J := by
    rw [hP]
    exact comap_mono (inf_le_left.trans d.geometry.outside.1.1.2)
  obtain ⟨e,hs,ha⟩ := Matrix.PSL3Two.exists_sylow_line_marking
    (e₁.trans Matrix.PSL3Two.equiv) (P.mapSurjective (QuotientGroup.mk'_surjective _)) A
    (map_mono hPJ) hne htwo
  exact ⟨e,ha,by simpa only [Sylow.coe_mapSurjective,hP] using hs⟩


/-- Taking O² of K ∩ X or of H ∩ X gives the same actual subgroup. -/
private theorem binary_intersection_residual_eq_local :
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
theorem Branch.binary_factor_marking
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) :
    let L := (pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
      ((pResidual 2 H).map H.subtype ⊓ X).subtype
    ∃ e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL,
      ((H.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map e.toMonoidHom =
        Matrix.PSL3Two.lineParabolicSL ∧
      (((planeSylow T ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
        e.toMonoidHom = Matrix.PSL3Two.borelSL ∧
      ((L.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map e.toMonoidHom =
        Matrix.PSL3Two.MarkedAutomorphisms.lineA := by
  dsimp only
  rw [binary_intersection_residual_eq_local]
  obtain ⟨e,hJ,hS⟩ := b.binary_local_marking d hI
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
theorem Branch.binary_factor_core_quotient_card
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) :
    let L := (pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
      ((pResidual 2 H).map H.subtype ⊓ X).subtype
    Nat.card (L ⧸ pCore 2 L) = 3 := by
  let L := (pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
    ((pResidual 2 H).map H.subtype ⊓ X).subtype
  have hLX : L ≤ X := (map_subtype_le _).trans inf_le_right
  obtain ⟨e,_,_,hL⟩ := b.binary_factor_marking d hI
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
/-- The original intersection H ∩ I is KS, using the supplied Sylow
subgroup and the source residual; this does not assume that X is normal. -/
theorem local_escape_intersection (hI : PlaneEscapes Mc ZS I) :
    H ⊓ I = (pResidual 2 H).map H.subtype ⊔ planeSylow T ZS := by
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I := (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  have hSI : planeSylow T ZS ≤ I :=
    (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
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
  have htS : (t : G) ∈ planeSylow T ZS := by
    have hh : (t : G) ∈ I ⊓ (T : Subgroup G) := ⟨htI,ht⟩
    rw [d.twoGroup_intersection hI le_rfl] at hh
    exact hh.1
  have hh : (k : G) * (t : G) = x := congrArg H.subtype he
  rw [← hh]
  exact mul_mem_sup (mem_map_of_mem H.subtype hk) htS

include d in
/-- The original H ∩ X is a maximal subgroup of X, lifting the binary
parabolic through O₂(X). -/
theorem Branch.binary_local_isCoatom
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) :
    IsCoatom (H.subgroupOf X) := by
  obtain ⟨e,hJ,_⟩ := b.binary_local_marking d hI
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
centralizer of ZS and its Mc-intersection are both H ∩ X. -/
theorem Branch.binary_centralizer_eq_local
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc) :
    Mc ⊓ X = H ⊓ X ∧ X ⊓ centralizer (ZS : Set G) = H ⊓ X := by
  have hne : Mc.subgroupOf X ≠ ⊤ := by
    intro he
    apply hout
    intro x hx
    exact (show (⟨x,hx⟩ : X) ∈ Mc.subgroupOf X from he ▸ mem_top _)
  have he := ((b.binary_local_isCoatom d hI).le_iff_eq hne).mp
    (comap_mono d.geometry.in_partner)
  have hMX : Mc ⊓ X = H ⊓ X := by
    have hh := congrArg (map X.subtype) he
    simpa only [subgroupOf_map_subtype] using hh
  refine ⟨hMX,le_antisymm ?_ ?_⟩
  · rw [← hMX]
    exact le_inf (inf_le_right.trans ((d.centralizer_le_intersection hI).trans inf_le_left))
      inf_le_left
  · apply le_inf inf_le_right
    have hh : H ⊓ X ≤ H ⊓ I := inf_le_inf_left H b.input.component.1
    rw [local_escape_intersection d hI] at hh
    exact hh.trans (sup_le d.residual_centralizes inf_le_right)

include d in
/-- The candidate cubic factor is exactly O²(M₀), where M₀ = Mc ∩ X is
the printed opposite parabolic. -/
theorem Branch.binary_factor_eq_opposite_residual
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc) :
    (pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
      ((pResidual 2 H).map H.subtype ⊓ X).subtype =
    (pResidual 2 (Mc ⊓ X : Subgroup G)).map (Mc ⊓ X).subtype := by
  rw [binary_intersection_residual_eq_local,(b.binary_centralizer_eq_local d hI hout).1]

include d in
/-- When X is normal in I, the original candidate K₁ is normal in Mᵢ.
This discharges the normality step immediately after (*) on printed p.1116. -/
theorem Branch.binary_factor_normalized
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (hn : I ≤ normalizer (X : Set G)) :
    Mc ⊓ I ≤ normalizer
      (((pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
        ((pResidual 2 H).map H.subtype ⊓ X).subtype) : Set G) := by
  rw [b.binary_factor_eq_opposite_residual d hI hout]
  exact ((le_inf (inf_le_left.trans Mc.le_normalizer) (inf_le_right.trans hn)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (Mc ⊓ X) (pResidual 2 (Mc ⊓ X : Subgroup G)))


include d in
/-- The two literal parabolics are distinct and their intersection is the
original S ∩ X. This fixes the word “opposite” without an arbitrary marking. -/
theorem Branch.binary_opposite_intersections
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc) :
    M ⊓ X ≠ Mc ⊓ X ∧ (M ⊓ X) ⊓ (Mc ⊓ X) = planeSylow T ZS ⊓ X := by
  have he := (b.binary_centralizer_eq_local d hI hout).1
  refine ⟨?_,?_⟩
  · intro hh
    have hl : H ⊓ X ≤ (T : Subgroup G) := by
      rw [← local_intersection_eq_sylow d]
      exact le_inf (fun x hx => (hh.symm ▸ he.symm ▸ hx).1) inf_le_left
    have hp := T.isPGroup'.to_le hl
    obtain ⟨r,hr⟩ := hp.exists_card_eq
    have hd := (b.residual_component_intersection_three_dvd d hI).trans
      (card_dvd_of_le (inf_le_inf_right X (map_subtype_le (pResidual 2 H))))
    rw [hr] at hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  · have hmeet : (M ⊓ X) ⊓ (Mc ⊓ X) = (M ⊓ H) ⊓ X := by
      rw [he]
      ext x
      simp only [mem_inf]
      tauto
    rw [hmeet,local_intersection_eq_sylow d]
    apply le_antisymm
    · intro x hx
      have hi : x ∈ I ⊓ (T : Subgroup G) := ⟨b.input.component.1 hx.2,hx.1⟩
      rw [d.twoGroup_intersection hI le_rfl] at hi
      exact ⟨hi.1,hx.2⟩
    · exact inf_le_inf_right X inf_le_left

include d in
/-- The original cubic factor candidate meets the literal 15.2.21 factor
criteria once the component-orbit step has supplied relative normality.
Its normality in Mᵢ and the required reducibility are derived here. -/
theorem Branch.binary_factor_source_data
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (hn : I ≤ normalizer (X : Set G)) :
    let K := (pResidual 2 H).map H.subtype
    let L := (pResidual 2 (K ⊓ X : Subgroup G)).map (K ⊓ X).subtype
    L ≤ K ∧ IsPPerfect 2 L ∧ Nat.card (L ⧸ pCore 2 L) = 3 ∧
      planeSylow T ZS ≤ normalizer (L : Set G) ∧
      Mc ⊓ I ≤ normalizer (L : Set G) ∧
      ¬ IsSmallActionIrreducible (planeSylow T ZS) K := by
  have hnorm := b.binary_factor_normalized d hI hout hn
  exact ⟨(map_subtype_le _).trans inf_le_left,isPPerfect_embedded_pResidual 2 _,
    b.binary_factor_core_quotient_card d hI,
    (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans hnorm,hnorm,
    b.binary_reducible_of_normalized d hI
      (((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right).trans hn)⟩

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree
