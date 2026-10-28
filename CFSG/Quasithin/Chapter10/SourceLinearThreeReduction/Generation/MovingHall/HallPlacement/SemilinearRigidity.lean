module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.HallPlacement.InvariantTorus
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Semilinear
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.InnerPlacement

/-!
# From reverse torus normalization to actual Hall placement

Odd order makes the original Hall preserve each component. Its literal
action on the marked orbit quotient is diagonal-semilinear because it
preserves the orbit Sylow and the full invariant torus. If this torus also
normalizes the Hall, the quadratic unit calculation kills both field
factors. Section-centralizer coprimality lifts the resulting inner action
to containment in the original orbit, hence its two-residual Borel.

The remaining reverse-normalization premise is discharged from source
Borel normalization in `ResidualPlacement`. Final source assembly remains
with the moving-Hall owner.
Source: Aschbacher–Smith 10.2.3, printed pp.745–746.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
open Chapter3.Section02 Chapter4 Matrix.SpecialLinearGroup BenderSuzuki.ZD.Linear
open CentralHall
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Odd order removes the component-exchange coordinate of the Hall action. -/
theorem hall_normalizes_component {H : Subgroup G} {B : Subgroup H}
    (c : MovingHall.Context D H B) : B.map H.subtype ≤ normalizer (L : Set G) := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  let M := D.maximalLocal
  let C := B.map H.subtype
  let N := (normalizer (L : Set G)).subgroupOf M
  let A := C.subgroupOf M
  have hCM : C ≤ M := map_le_iff_le_comap.mpr c.hall_le
  have hi : N.index = 2 := normalizer_relIndex_eq_two_of_pair M L
    (L.map (MulAut.conj t).toMonoidHom)
    (source_nonnormal_maximal_pair D c.nonnormal ht htn) t
    (le_normalizer_componentOrbit L T ht)
    (fun he => htn (mem_normalizer_iff_map_conj_eq.mpr he))
  let : N.Normal := normal_of_index_eq_two hi
  have hd : N.relIndex A ∣ 2 := hi ▸ N.relIndex_dvd_index_of_normal A
  have ho : Odd (Nat.card A) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hCM).toEquiv,
      card_map_of_injective H.subtype_injective]
    exact c.hall_odd
  have hle : A ≤ N := relIndex_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes ho.coprime_two_right (N.relIndex_dvd_card A) hd)
  intro b hb
  exact hle (show (⟨b,hCM hb⟩ : M) ∈ A from hb)

/-- Restriction of literal conjugation to the original component quotient. -/
private def componentAction {H : Subgroup G} {B : Subgroup H}
    (c : MovingHall.Context D H B) : B →* MulAut (L ⧸ pCore 2 L) :=
  (normalizerPCoreQuotientAction L).comp
    ((H.subtype.comp B.subtype).codRestrict (normalizer (L : Set G))
      (fun b => hall_normalizes_component D c
        (mem_map_of_mem H.subtype b.property)))

/-- Any compatible product marking intertwines the first component actions. -/
private theorem componentAction_first {H : Subgroup G} {B : Subgroup H}
    (c : MovingHall.Context D H B)
    {S : Type*} [Group S] (e : (L ⧸ pCore 2 L) ≃* S)
    (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (S × S))
    (hq : ∀ l : L, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
      ⟨l,le_componentOrbit L T l.property⟩) =
        (e (QuotientGroup.mk' (pCore 2 L) l), 1))
    (b : B) (l : L) :
    q (action D B c.hall_le b
      (QuotientGroup.mk' (pCore 2 (localOrbit T L))
        ⟨l,le_componentOrbit L T l.property⟩)) =
      (e (componentAction D c b (QuotientGroup.mk' (pCore 2 L) l)), 1) := by
  change q (quotientAut (pCore 2 (localOrbit T L)) _ _) =
    (e (quotientAut (pCore 2 L) _ _), 1)
  rw [quotientAut_apply_mk, quotientAut_apply_mk]
  exact hq ((L.normalizerMonoidHom
    ⟨b.val.val, hall_normalizes_component D c
      (mem_map_of_mem H.subtype b.property)⟩) l)

private theorem quotient_action_kernel_le_section
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) :
    (normalizerQuotientAction (localOrbit T L) (pCore 2 (localOrbit T L))).ker.map
      D.maximalLocal.subtype ≤ sectionCentralizer (localOrbit T L) := by
  let K := (normalizerQuotientAction (localOrbit T L) (pCore 2 (localOrbit T L))).ker
  have hKM : K ≤ D.maximalLocal.subgroupOf D.maximalLocal := fun x _ => x.property
  have hk : (action D K hKM).ker = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    exact x.property
  have hh := action_kernel_image_le D K hKM
  rw [hk,←MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype] at hh
  exact hh

/-- Innerness on the original product quotient places the faithful Hall group in L₀. -/
theorem hall_le_orbit_of_inner
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {H : Subgroup G} {B : Subgroup H} (c : MovingHall.Context D H B)
    {J : Type*} [Group J]
    (e : (L ⧸ pCore 2 L) ≃* J)
    (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (J × J))
    (hinner : ∀ b : B, action D B c.hall_le b ∈
      MulAut.innerSubgroup (localOrbit T L ⧸ pCore 2 (localOrbit T L))) :
    B.map H.subtype ≤ localOrbit T L := by
  let R := localOrbit T L
  let Q := R ⧸ pCore 2 R
  let C := B.map H.subtype
  let f := (action D B c.hall_le).codRestrict (MulAut.innerSubgroup Q) hinner
  have hfi : Function.Injective f := fun _ _ h =>
    action_injective D B c.hall_le c.faithful (congrArg Subtype.val h)
  have hcard : Nat.card B ∣ Nat.card Q :=
    (card_dvd_of_injective f hfi).trans (card_range_dvd (MulAut.conj : Q →* MulAut Q))
  have hCM : C ≤ D.maximalLocal := map_le_iff_le_comap.mpr c.hall_le
  have hc : Nat.Coprime (Nat.card C) (Nat.card (sectionCentralizer R)) := by
    rw [show Nat.card C = Nat.card B from card_map_of_injective H.subtype_injective]
    apply Nat.coprime_of_dvd
    intro p hp hpB hpC
    let : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      intro he
      subst p
      exact (Nat.not_even_iff_odd.mpr (c.hall_odd)) (even_iff_two_dvd.mpr hpB)
    have hL : p ∣ Nat.card (L ⧸ pCore 2 L) := by
      have hd := hpB.trans hcard
      rw [Nat.card_congr q.toEquiv,Nat.card_prod] at hd
      rw [Nat.card_congr e.toEquiv]
      exact (hp.dvd_mul.mp hd).elim id id
    exact hp.coprime_iff_not_dvd.mp
      (source_nonnormal_sectionCentralizer_prime_coprime D c.nonnormal p hp2 hL) hpC
  have hkcard : Nat.card (normalizerQuotientAction R (pCore 2 R)).ker ∣
      Nat.card (sectionCentralizer R) := by
    rw [←card_map_of_injective (normalizer (R : Set G)).subtype_injective]
    exact card_dvd_of_le (quotient_action_kernel_le_section D)
  apply le_of_normalizerQuotientAction_inner R (pCore 2 R) C hCM
    (hc.coprime_dvd_right hkcard)
  rintro _ ⟨a,ha,rfl⟩
  obtain ⟨b,hb,hba⟩ := ha
  have he : a = (⟨b,c.hall_le hb⟩ : D.maximalLocal) := Subtype.ext hba.symm
  rw [he]
  exact hinner ⟨b,hb⟩

variable {F : Type*} [Field F] [Finite F] [CharP F 2]
/-- The literal quotient action preserves the same marked orbit Sylow. -/
private theorem hall_action_preserves_marked_sylow {H : Subgroup G} {B : Subgroup H}
    (c : MovingHall.Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃* (SL(2,F) × SL(2,F)))
    (hS : ((T : Subgroup G).subgroupOf (localOrbit T L)).map
      (q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localOrbit T L)))) =
        (upperUnipotent F).prod (upperUnipotent F))
    (b : B) :
    ((upperUnipotent F).prod (upperUnipotent F)).map
      (MulAut.congr q (action D B c.hall_le b)).toMonoidHom =
        (upperUnipotent F).prod (upperUnipotent F) := by
  let R := localOrbit T L
  let f := q.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  let α := MulAut.congr q (action D B c.hall_le b)
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    rw [←hS] at hx ⊢
    obtain ⟨y,hy,rfl⟩ := hx
    let bM : D.maximalLocal := ⟨(b:G),c.hall_le b.property⟩
    let y' := R.normalizerMonoidHom bM y
    have hy' : y' ∈ (T : Subgroup G).subgroupOf R := by
      have hb := hall_normalizes_orbit_sylow D c e (mem_map_of_mem H.subtype b.property)
      change (b:G) ∈ normalizer (((T : Subgroup G) ⊓ R : Subgroup G) : Set G) at hb
      exact ((mem_normalizer_iff.mp hb y).mp ⟨hy,y.property⟩).1
    refine ⟨y',hy',?_⟩
    change q (QuotientGroup.mk' (pCore 2 R) y') =
      q (action D B c.hall_le b (q.symm (q (QuotientGroup.mk' (pCore 2 R) y))))
    rw [q.symm_apply_apply]
    change q (QuotientGroup.mk' (pCore 2 R) y') =
      q (quotientAut (pCore 2 R) _ _)
    rw [quotientAut_apply_mk]
    rfl
  · rw [card_map_of_injective α.injective]


/-- Reverse normalization of the actual invariant torus eliminates both field
factors and places the original Hall in the original Borel. -/
theorem hall_le_borel_of_invariant_tori_normalize
    {H : Subgroup G} {B : Subgroup H} (c : MovingHall.Context D H B)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hreverse : ∀ C : Subgroup G, C ≤ sourceOrbitBorel T L →
      IsHallSubgroup Subgroup.OddHall.oddPrimes (C.subgroupOf (sourceOrbitBorel T L)) →
      B.map H.subtype ≤ normalizer (C : Set G) → C ≤ normalizer (B.map H.subtype : Set G)) :
    B.map H.subtype ≤ sourceOrbitBorel T L := by
  obtain ⟨C,hC,hHall,hBC,_,e',q,d,hd,hcomp,hS,hdiag⟩ :=
    exists_hall_invariant_source_borel_marking D c e
  have hCB := hreverse C hC hHall hBC
  let ρ := (MulAut.congr q).toMonoidHom.comp (action D B c.hall_le)
  have hsemi : ∀ b : B, ∃ (d : Fˣ × Fˣ) (σ τ : F ≃+* F),
      ρ b = (MulAut.conj (diag2 (d.1:F) d.1.ne_zero) * sl2FieldAut σ).prodCongr
        (MulAut.conj (diag2 (d.2:F) d.2.ne_zero) * sl2FieldAut τ) := by
    intro b
    let a := MulAut.congr e' (componentAction D c b)
    have ha : ∀ x, ρ b (x,1) = (a x,1) := by
      intro x
      obtain ⟨l,rfl⟩ := (e'.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) x
      have hh := componentAction_first D c e' q hcomp b l
      change q (action D B c.hall_le b
        (q.symm (e' (QuotientGroup.mk' (pCore 2 L) l),1))) = _
      rw [←hcomp,q.symm_apply_apply]
      change q (action D B c.hall_le b _) =
        (e' (componentAction D c b (e'.symm (e' (QuotientGroup.mk' (pCore 2 L) l)))),1)
      rw [e'.symm_apply_apply]
      exact hh
    apply pair_sylow_torus_preserving_semilinear
      (CentralHall.Nonlinear.HallGeometry.source_sl2_field_card_gt_two D e') (ρ b) a ha
      (hall_action_preserves_marked_sylow D c e' q hS b)
    intro z
    obtain ⟨x,hx⟩ := hd.2 z
    let bC : normalizer (C : Set G) := ⟨(b : G),hBC (mem_map_of_mem H.subtype b.property)⟩
    let x' : C := C.normalizerMonoidHom bC x
    refine ⟨d x',?_⟩
    change q (action D B c.hall_le b (q.symm _)) = _
    rw [←hx,←hdiag x,q.symm_apply_apply]
    change q (quotientAut (pCore 2 (localOrbit T L)) _ _) = _
    rw [quotientAut_apply_mk]
    exact hdiag x'
  obtain ⟨φ,hφ,hdecomp⟩ := exists_pair_diagonal_field_hom ρ hsemi
  have hfield (b : B) : (φ b).1 = 1 ∧ (φ b).2 = 1 := by
    apply original_torus_field_factors_eq_one D c C
      ((hC.trans (map_subtype_le _)).trans inf_le_left) hBC hCB q d hd.2
      (by simpa only [splitDiagonalHom_apply] using hdiag) b
    intro z
    simpa only [splitDiagonalHom_apply,ρ,MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom,MulAut.congr_apply,MulEquiv.trans_apply] using hφ b z
  have hinner (b : B) : action D B c.hall_le b ∈
      MulAut.innerSubgroup (localOrbit T L ⧸ pCore 2 (localOrbit T L)) := by
    have hdecomp' : ∀ b, ∃ d : Fˣ × Fˣ, ρ b =
        (MulAut.conj (splitDiagonalHom d.1) * sl2FieldAut (φ b).1).prodCongr
          (MulAut.conj (splitDiagonalHom d.2) * sl2FieldAut (φ b).2) := by
      simpa only [splitDiagonalHom_apply] using hdecomp
    have hm := (pair_diagonal_field_inner_iff ρ φ hdecomp' b).mp
      (Prod.ext (hfield b).1 (hfield b).2)
    rw [←MulAut.map_innerSubgroup_congr q] at hm
    exact (mem_map_iff_mem (MulAut.congr q).injective).mp hm
  exact hall_le_borel_of_le_orbit D c e (hall_le_orbit_of_inner D c e' q hinner)

end CFSG.Quasithin.Chapter10.MovingHall.HallPlacement
