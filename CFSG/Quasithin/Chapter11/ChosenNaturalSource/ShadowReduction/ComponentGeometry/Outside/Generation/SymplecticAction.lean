module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.SymplecticAction.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.HallOrder
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.Attainment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core.RootPlacement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.TransvectionFree.Action

/-!
# Generation one in the original Sp₄ equal-component row

The actual normalizer action on the original central quotient is conjugated
by the caller's symplectic flag alignment. The first residual maps onto
the standard point-local group, and its two-core maps into the model core.
The odd-action calculation therefore applies to the full Hall actor from
E.2.2. Its order is coprime to q−1 by HallOrder, so its quotient action is
trivial. Central-cover uniqueness lifts this to all of V, including its
possible central kernel. Hall faithfulness then forces the actor to be
trivial, contradicting its cyclic subgroup of order 2ⁿ−1 if n(H)>1.

The final consumer constructs the original selected H with n(H)=1 and
both literal O²(H) alternatives. The exact OddKernelNormalizer input is
used only for faithfulness and remains with
qt-d-1222-natural-odd-kernel-normalizer. Earlier geometry, 11.3.2, the
linear fixed-space premise and Kz=K retain qt-d-1222-natural-local-geometry,
qt-d-1222-shadow-linear-geometry, qt-d-1222-shadow-component-triangle and
qt-d-1222-shadow-component-comparison as producers, with final discharge
by qt-d-1222-shadow-components.

The G₂ row, strict-component reduction and generation of the smaller
R₁ O²(H) carrier remain with qt-d-1222-shadow-component-witness. This module
does not assert the full 11.4.4 or 11.5.1.
Source: Aschbacher--Smith, printed pp.778--779 of refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Matrix Representation Theory.GroupTheory
open scoped MatrixGroups commutatorElement
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
open LocalGeometry
open Theory.SpecificGroups.SymplecticFour
open LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core
open LocalGeometry.WeakClosure.Nonnormalization.NormalizedPlane.TransvectionFree
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer SymplecticNaturalNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : InvariantFlag (.sp4 m))

private theorem map_core_le {A B : Type*} [Group A] [Group B]
    (q : A →* B) (P : Subgroup A) : (P.pCoreIn 2).map q ≤ (P.map q).pCoreIn 2 := by
  let j := q.subgroupMap P
  have hn : ((pCore 2 P).map j).Normal := Normal.map inferInstance j (q.subgroupMap_surjective P)
  have h : (pCore 2 P).map j ≤ pCore 2 (P.map q) := le_sSup ⟨hn,pCore_isPGroup.map j⟩
  have hh := map_mono (f := (P.map q).subtype) h
  change ((pCore 2 P).map j).map (P.map q).subtype ≤ (P.map q).pCoreIn 2 at hh
  rw [Subgroup.map_map] at hh
  change (pCore 2 P).map (q.comp P.subtype) ≤ _ at hh
  change ((pCore 2 P).map P.subtype).map q ≤ _
  rw [Subgroup.map_map]
  exact hh

/-- Coprime odd actors centralizing the original symplectic point section fix
the entire seed, including its original central kernel. -/
theorem ofFlag_sp4_odd_section_centralizes
    (B : Subgroup G) (ho : Odd (Nat.card B))
    (hBV : B ≤ normalizer (V : Set G))
    (hc : ⁅B,f.Li 0⁆ ≤ (f.Li 0).pCoreIn 2)
    (hco : Nat.Coprime (Nat.card B) (2 ^ S.field.degree - 1)) :
    B ≤ centralizer (V : Set G) := by
  have hlarge : 2 < Nat.card S.field.Carrier := by
    rw [S.field.card_eq]
    exact (show (2:ℕ)^1 < 2^S.field.degree from Nat.pow_lt_pow_right (by decide) S.nonbinary)
  let a := Sp4.alignment m
  let N := normalizer (V : Set G)
  let t := naturalElement hlarge a⁻¹
  let Q : N →* naturalNormalizer (F := S.field.Carrier) :=
    (MulAut.conj t).toMonoidHom.comp
      ((linearAction (quotientAction D S m)).codRestrict naturalNormalizer
        (quotientAction_mem_normalizer D S m))
  let q : N →* (Vector S.field.Carrier ≃ₗ[ZMod 2] Vector S.field.Carrier) :=
    naturalNormalizer.subtype.comp Q
  let P := (f.Li 0).subgroupOf N
  have hAL : f.Li 0 ≤ L := (localResidual_le _).trans inf_le_left
  have hAN : f.Li 0 ≤ N := hAL.trans D.normalizes
  have hq (l : L) : q (inclusion D.normalizes l) =
      naturalHom ((MulAut.conj a⁻¹) ((Coordinates.sp4 m).quotientMap l)) := by
    have hh : linearAction (quotientAction D S m) (inclusion D.normalizes l) =
        naturalHom ((Coordinates.sp4 m).quotientMap l) := by
      apply LinearEquiv.ext
      exact quotientAction_component D S m l
    change naturalHom a⁻¹ * linearAction (quotientAction D S m) (inclusion D.normalizes l) *
      (naturalHom a⁻¹)⁻¹ = naturalHom (a⁻¹ * (show Sp S.field.Carrier from (Coordinates.sp4 m).quotientMap l) * (a⁻¹)⁻¹)
    simp only [hh,map_mul,map_inv]
  have hPQ : P.map q = (pointLocal (F := S.field.Carrier)).map naturalHom := by
    have hcomp : P.map q = ((modelImage D S m (f.Li 0)).map
        (MulAut.conj a⁻¹).toMonoidHom).map naturalHom := by
      ext u
      constructor
      · rintro ⟨x,hx,rfl⟩
        refine ⟨_,⟨(Coordinates.sp4 m).quotientMap ⟨x,hAL hx⟩,⟨⟨x,hAL hx⟩,hx,rfl⟩,rfl⟩,?_⟩
        exact (hq ⟨x,hAL hx⟩).symm
      · rintro ⟨_,⟨_,⟨l,hl,rfl⟩,rfl⟩,rfl⟩
        exact ⟨inclusion D.normalizes l,hl,hq l⟩
    rw [hcomp,modelImage_point D S m f]
    apply congrArg (Subgroup.map naturalHom)
    have he : (MulAut.conj a⁻¹).toMonoidHom.comp (MulAut.conj a).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change a⁻¹ * (a*x*a⁻¹) * (a⁻¹)⁻¹ = x
      group
    rw [Subgroup.map_map,he,Subgroup.map_id]
  have hcore : (((f.Li 0).pCoreIn 2).subgroupOf N).map q ≤
      ((pointLocal (F := S.field.Carrier)).pCoreIn 2).map naturalHom := by
    rw [←pCoreIn_subgroupOf 2 (f.Li 0) N hAN]
    have hh := map_core_le q P
    rw [hPQ,←map_pCoreIn_of_injective 2 _ _ naturalHom_injective] at hh
    exact hh
  intro b hb
  let b' : N := ⟨b,hBV hb⟩
  have hpow : Q b' ^ Nat.card B = 1 := by
    rw [←map_pow]
    have hbpow : b ^ Nat.card B = 1 :=
      congrArg (fun x : B => (x : G)) (pow_card_eq_one' (x := (⟨b,hb⟩ : B)))
    have he : b' ^ Nat.card B = 1 := Subtype.ext hbpow
    rw [he,map_one]
  have hcomm : ∀ x ∈ pointLocal (F := S.field.Carrier),
      conjugation hlarge (Q b') x / x ∈ (pointLocal (F := S.field.Carrier)).pCoreIn 2 := by
    intro x hx
    apply (mem_map_iff_mem naturalHom_injective).mp
    have hact : naturalHom (conjugation hlarge (Q b') x / x) = ⁅q b',naturalHom x⁆ := by
      rw [map_div,conjugation_apply]
      rfl
    rw [hact]
    obtain ⟨y,hy,he⟩ := hPQ.ge (mem_map_of_mem naturalHom hx)
    rw [←he,←map_commutatorElement]
    exact hcore (mem_map_of_mem q (show ⁅b',y⁆ ∈ ((f.Li 0).pCoreIn 2).subgroupOf N from
      hc (commutator_mem_commutator hb hy)))
  have hb1 : Q b'=1 := SymplecticAction.odd_coprime_point_section_eq_one
    S.field.card_eq S.nonbinary (Q b') ho (S.field.card_eq.symm ▸ hco) hpow hcomm
  have hq1 : linearAction (quotientAction D S m) b' = 1 := by
    have h1 := (MulAut.conj t).injective (hb1.trans (map_one _).symm)
    exact congrArg Subtype.val h1
  have hfull := fullAction_eq_one_of_quotient D S m b' hq1
  intro v hv
  obtain ⟨w,hw⟩ := D.spaceEquiv.surjective ⟨v,hv⟩
  have hh := fullAction_conjugation D b' w.toAdd
  rw [hfull] at hh
  change (D.spaceEquiv w : G) = b * (D.spaceEquiv w : G) * b⁻¹ at hh
  rw [hw] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh.symm).symm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (f : LocalGeometry.InvariantFlag (.sp4 m))
    (X : Subgroup G) (z : G) (H : Subgroup G)

/-- Source 11.4.4 for every outside H in the original symplectic equality row.
The earlier geometry and independently owned Hall-faithfulness input remain explicit. -/
theorem ofFlag_sp4_equal_generation_eq_one
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHz : H ≤ Gz (ofFlag S f X z H)) : ChapterE.generationParameter H = 1 := by
  apply Nat.le_antisymm ?_ (selected_generation_spec (ofFlag S f X z H) h hH hHz).1
  change ChapterE.generationParameter H ≤ 1
  by_contra! hn
  obtain ⟨hP,n,_,hb,d,_,_,hY,hfaith,hBV,hcop⟩ :=
    ofFlag_sp4_equal_faithful_hall_order S m f X z H h he hK hlinear h1132 hcontrol hH hHz hn
  have hc : ⁅d.witness.abelianGroup.map H.subtype,f.Li 0⁆ ≤ (f.Li 0).pCoreIn 2 := by
    have hc := commutator_le.mpr (fun b hb k hk =>
      Closure.coreQuotientCentralizer_commutator (hY hb).2 hk)
    simpa only [hK,ofFlag_firstResidual] using hc
  have hfix := ofFlag_sp4_odd_section_centralizes S m f _
    (d.witness.odd.of_dvd_nat (card_map_dvd _ _)) hBV hc hcop
  have hz : d.witness.abelianGroup.map H.subtype = ⊥ := by
    rwa [inf_eq_left.mpr hfix] at hfaith
  have hB : d.witness.abelianGroup = ⊥ :=
    (map_eq_bot_iff_of_injective _ H.subtype_injective).mp hz
  have hC : d.witness.cyclicGroup = ⊥ := bot_unique (d.witness.cyclic_le.trans hB.le)
  have hc1 := d.witness.card
  rw [Subgroup.card_eq_one.mpr hC] at hc1
  have hn2 : 2 ≤ n := by omega
  have hp : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn2
  omega

/-- The original selected H has generation one, with both residual alternatives
still interpreted as O²(H). The preceding geometry is retained verbatim. -/
theorem ofFlag_sp4_equal_selected_generation_one
    (h : Comparison.EarlierGeometry (ofFlag S f X z H))
    (he : (ofFlag S f X z H).Kz = (ofFlag S f X z H).K)
    (hK : (ofFlag S f X z H).K = (ofFlag S f X z H).L₁)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ J, Hypothesis1131At D S (ofFlag S f X z H).point J →
      Proposition1132At D S (ofFlag S f X z H).point J)
    (hcontrol : LocalGeometry.WeakClosure.Generation.OddKernelNormalizer
      (T := T) (L := L) (V := V)) :
    ∃ J, J ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      J ≤ Gz (ofFlag S f X z J) ∧ SelectedResidualAlternative (ofFlag S f X z J) ∧
      ChapterE.generationParameter J = 1 := by
  obtain ⟨J,hJ,hJz,hs,_⟩ := ofFlag_equal_selected_radical_carrier S f X z H h he hK hNT h1132
  exact ⟨J,hJ,hJz,hs,ofFlag_sp4_equal_generation_eq_one S m f X z J
    ⟨h.point_mem,h.point_fixed,h.point_ne_one,h.seed_centralizes,
      h.line_component,h.point_component,h.normalizer_split⟩ he hK hlinear h1132 hcontrol hJ hJz⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation
