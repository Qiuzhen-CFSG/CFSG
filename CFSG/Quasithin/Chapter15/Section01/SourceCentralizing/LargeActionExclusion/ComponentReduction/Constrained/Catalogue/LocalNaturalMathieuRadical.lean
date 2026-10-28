module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Catalogue.LocalNaturalMathieuPlacement
public import Theory.GroupTheory.RadicalInnerNormalizer
public import Theory.GroupTheory.PRadical.NormalComponentImages
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.HeptadAutomorphisms

/-!
# Excluding the M₂₃ carrier of an original natural local escape

The selected carrier is normal in the original G₁. In the M₂₃ case its
center vanishes by the multiplier theorem, and every automorphism is inner.
Radical saturation therefore splits the original Q₁ over this carrier and
its centralizer. Consequently the full intrinsic normalizer of the
intersection Q₁ ∩ L lies in M_Z ∩ L. The radical intersection theorem then
identifies M_Z ∩ L with the normalizer of its own two-core.

The earlier ordinary source calculation identifies that same M_Z ∩ L as
the centralizer of the unique central involution of the original Sylow
S ∩ L. In native M₂₃, its two-core is the pointwise kernel of the fixed
heptad. The full normalizer of this kernel has order 40320, whereas the
involution centralizer has order 2688. This contradicts the preceding
intrinsic normalizer containment.

The actual original-marker application now leaves only the M₂₂ central
quotient and identifies the exact local image with its native affine
natural actor. It retains the full central-cover map, original cubic prime,
natural degree two, moving four-group and normal maximal selected carrier.
The covered M₂₂ exclusion, general natural Borel containment and final
15.1.20(2)/15.1.22 assembly remain open. Original 15.1.14 and whole-core A₆
reconstruction retain their existing producers.

Source: Aschbacher--Smith C.2.2(1), p.144; 15.1.18(7), 15.1.20(2),(3d),
15.1.22, pp.1092--1100; H.14.2 and GLS3 Table 5.3d for native M₂₃ geometry.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin.ChapterC Sporadic.Mathieu

private theorem m23_core_normalizer_obstruction (t : M23) (ht : orderOf t = 2)
    (hN : normalizer ((centralizer ({t} : Set M23)).pCoreIn 2 : Set M23) ≤
      centralizer ({t} : Set M23)) : False := by
  open M23Geometry in
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (involutions_isConj t involutionRepresentative ht involutionRepresentative_order)
  let a := MulAut.conj g
  have ha : a t = M23Geometry.involutionRepresentative := hg
  have hC : (centralizer ({t} : Set M23)).map a.toMonoidHom =
      centralizer ({M23Geometry.involutionRepresentative} : Set M23) := by
    rw [map_centralizer_equiv,Set.image_singleton,ha]
  have hn := map_mono (f := a.toMonoidHom) hN
  rw [map_equiv_normalizer_eq,map_pCoreIn_of_injective 2 _ _ a.injective,hC,
    M23Geometry.fixedHeptad_centralizer_core_eq M23Geometry.involutionRepresentative_order,
    M23Geometry.fixedHeptad_involutionRepresentative,
    show M23Geometry.involutionHeptad = M23Geometry.omega from rfl,
    M23Geometry.heptadPointwiseKernel_omega,M23Geometry.heptadKernelAmbient_normalizer] at hn
  have hc := card_le_of_le hn
  rw [M23Geometry.heptadStabilizer_card,M23Geometry.involutionRepresentative_centralizer_card] at hc
  omega

private theorem radical_normalizer_intersection
    {A : Type*} [Group A] [Finite A] (L R : Subgroup A) [L.Normal]
    (hR : IsPRadical 2 R) (hZ : IsPGroup 2 (center L))
    (hi : R ≤ L ⊔ centralizer (L : Set A)) :
    normalizer (((normalizer (R : Set A)).subgroupOf L).pCoreIn 2 : Set L) ≤
      (normalizer (R : Set A)).subgroupOf L := by
  let U := R.subgroupOf L
  let B := (normalizer (R : Set A)).subgroupOf L
  have he : normalizer (U : Set L) = B := by
    apply le_antisymm
    · intro x hx
      have hxN : x.val ∈ normalizer ((R ⊓ L : Subgroup A) : Set A) := by
        change x ∈ (normalizer ((R ⊓ L : Subgroup A) : Set A)).subgroupOf L
        rw [subgroupOf_normalizer_eq inf_le_right,inf_subgroupOf_right]
        exact hx
      exact radical_intersection_normalizer_le L R hR hZ hi ⟨x.property,hxN⟩
    · intro x hx
      have hxN : x.val ∈ normalizer ((R ⊓ L : Subgroup A) : Set A) :=
        inf_normalizer_le_normalizer_inf ⟨hx,le_normalizer_of_normal x.property⟩
      change x ∈ normalizer (R.subgroupOf L : Set L)
      rw [←inf_subgroupOf_right R L,←subgroupOf_normalizer_eq inf_le_right]
      exact hxN
  have hc := normal_intersection_relative_core L R hR
  rw [he] at hc
  change normalizer (B.pCoreIn 2 : Set L) ≤ B
  rw [hc]
  exact he.le

private theorem inner_radical_model_core_normalizer
    {A : Type*} [Group A] [Finite A] (L R : Subgroup A) [L.Normal]
    (hR : IsPRadical 2 R) (e : L ≃* M23) :
    normalizer (((normalizer (R : Set A)).subgroupOf L).pCoreIn 2 : Set L) ≤
      (normalizer (R : Set A)).subgroupOf L := by
  have hi : R ≤ L ⊔ centralizer (L : Set A) := by
    intro r hr
    rw [← MulAut.conjNormal_comap_innerSubgroup]
    change MulAut.conjNormal r ∈ MulAut.innerSubgroup L
    let b : MulAut M23 := e.symm.trans ((MulAut.conjNormal r).trans e)
    obtain ⟨x,hx⟩ := m23_conj_surjective b
    refine ⟨e.symm x,?_⟩
    apply MulEquiv.ext
    intro y
    apply e.injective
    have hy := DFunLike.congr_fun hx (e y)
    simpa [b,MulAut.conj_apply] using hy
  have hz : center L = ⊥ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [FixedElementary.map_center,M23Geometry.m23_center_eq_bot,Subgroup.map_bot]
  exact radical_normalizer_intersection L R hR (by rw [hz]; exact IsPGroup.of_card (n := 0) (by simp)) hi


namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Radical saturation at the original Q₁ excludes an M₂₃ central-quotient
carrier for any escaping natural member of the original local family. -/
theorem PreExclusionSource.localFamily_linearTwo_not_m23
    {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V} {p : ℕ}
    (s : d.PreExclusionSource h.normalized p) (hp : p = 3 ∨ p = 5)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfull : V = localModule T M)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G))
    {K : Subgroup G} (hK : K ∈ Chapter1.LIn d.G1 d.S)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ d.MZ) {n : ℕ} (hb : IsL2EvenBlock K n)
    (model : Nonempty ((d.L ⧸ center d.L) ≃* M23)) : False := by
  obtain ⟨hzL,_,_,_,_,_,⟨e⟩⟩ := s.localFamily_linearTwo_m23_uncovered (h := h)
    hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb model
  obtain ⟨_,_,hnL,_,_⟩ := s.localFamily_linearTwo_selected_carrier (h := h)
    hG hM hJ hu hne hmany hfull hres hK hq hout hb (by rcases hp with rfl | rfl <;> decide)
  have hL : IsComponent d.G1 (d.L.subgroupOf d.G1) := by
    rcases d.ordinary_or_constrained s.odd_core with hc | hf
    · exact hc
    · exact (hout (s.localFamily_linearTwo_le_MZ_of_constrained_carrier (h := h)
        hp hG hempty hM hJ hu hne hmany hfull hres hK hq hb hf)).elim
  let ecore := (QuotientGroup.quotientMulEquivOfEq (s.ordinary hL).center_eq.symm).trans model.some
  have hc := s.surviving_sporadic_centralizer_eq (h := h) hG hempty hM hu hL
    (name := .m23) (Or.inr (Or.inr (Or.inl rfl))) ecore
  obtain ⟨P,hP⟩ := s.component_sylow
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let ePS : P ≃* d.SL :=
    ((P : Subgroup d.L).equivMapOfInjective d.L.subtype d.L.subtype_injective).trans
      (MulEquiv.subgroupCongr hP)
  let eSP : d.SL ≃* P' := ePS.symm.trans (e.subgroupMap (P : Subgroup d.L))
  have hSLcard : Nat.card d.SL = 128 := by
    rw [Nat.card_congr eSP.toEquiv,P'.card_eq_multiplicity,m23_order]
    decide +kernel
  let : Nontrivial d.SL := Finite.one_lt_card_iff_nontrivial.mp (by rw [hSLcard]; decide)
  let : Nontrivial (center d.SL) := ((IsPGroup.of_card (p := 2) (n := 7) hSLcard)).center_nontrivial
  have hzcard : Nat.card (center d.SL) = 2 := by
    have hlo := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial (center d.SL))
    have hhi : Nat.card (center d.SL) ≤ 2 := by
      rw [Nat.card_congr (centerCongr eSP).toEquiv]
      exact m23_sylow_center_card_le_two P'
    omega
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center d.SL) 2
    (by rw [hzcard])
  have hzgen : zpowers z = (⊤ : Subgroup (center d.SL)) := by
    apply eq_of_le_of_card_ge le_top
    rw [card_top,Nat.card_zpowers,hz,hzcard]
  let f : center d.SL →* G := d.SL.subtype.comp (center d.SL).subtype
  have hcz : (center d.SL).map d.SL.subtype = zpowers (f z) := by
    have hh := congrArg (map f) hzgen
    rw [MonoidHom.map_zpowers,←MonoidHom.range_eq_map] at hh
    have hr : f.range = (center d.SL).map d.SL.subtype := by
      rw [MonoidHom.range_comp,range_subtype]
    exact hr.symm.trans hh.symm
  have hcentral : d.ML = d.L ⊓ centralizer ({f z} : Set G) := by
    rw [hc,hcz,zpowers_eq_closure,centralizer_closure]
  let L := d.L.subgroupOf d.G1
  let R := d.Q1.subgroupOf d.G1
  let : L.Normal := hnL
  let e0 : L ≃* M23 := (subgroupOfEquivOfLe d.L_component.1).trans e
  have hR := caseI_intrinsic_core_radical d.G1 d.MZ inf_le_left
    s.core_nontrivial s.core_normalizer
  have hNR : normalizer (R : Set d.G1) = d.MZ.subgroupOf d.G1 := by
    rw [show R = d.Q1.subgroupOf d.G1 from rfl,
      ←subgroupOf_normalizer_eq (d.Q1_le_MZ.trans inf_le_left)]
    ext x
    change x.val ∈ normalizer (d.Q1 : Set G) ↔ x.val ∈ d.MZ
    exact ⟨fun hx => s.core_normalizer.le ⟨x.property,hx⟩,
      fun hx => (s.core_normalizer.ge hx).2⟩
  let A := (normalizer (R : Set d.G1)).subgroupOf L
  let zL : L := ⟨⟨f z,d.L_component.1 z.val.property.2⟩,z.val.property.2⟩
  have hA : A = centralizer ({zL} : Set L) := by
    ext x
    rw [mem_centralizer_singleton_iff]
    have hx : x ∈ A ↔ x.val.val ∈ d.MZ := by
      change x.val ∈ normalizer (R : Set d.G1) ↔ _
      rw [hNR]
      rfl
    rw [hx]
    have hmem : x.val.val ∈ d.MZ ↔ x.val.val ∈ d.ML :=
      ⟨fun hx => ⟨hx,x.property⟩,fun hx => hx.1⟩
    rw [hmem,hcentral,mem_inf,mem_centralizer_singleton_iff]
    exact ⟨fun hx => Subtype.ext (Subtype.ext hx.2),fun hx =>
      ⟨x.property,congrArg (fun y : L => y.val.val) hx⟩⟩
  have hzLorder : orderOf zL = 2 := calc
    orderOf zL = orderOf (zL.val.val : G) :=
      (Subgroup.orderOf_coe zL).symm.trans (Subgroup.orderOf_coe zL.val).symm
    _ = orderOf z := (Subgroup.orderOf_coe z.val).trans (Subgroup.orderOf_coe z)
    _ = 2 := hz
  have hn := inner_radical_model_core_normalizer L R hR e0
  have hn' := map_mono (f := e0.toMonoidHom) hn
  change normalizer (A.pCoreIn 2 : Set L) ≤ A at hn
  have hmap : A.map e0.toMonoidHom = centralizer ({e0 zL} : Set M23) := by
    rw [hA,map_centralizer_equiv,Set.image_singleton]
  rw [map_equiv_normalizer_eq,map_pCoreIn_of_injective 2 _ _ e0.injective,hmap] at hn'
  exact m23_core_normalizer_obstruction (e0 zL) ((e0.orderOf_eq zL).trans hzLorder) hn'

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData

namespace CFSG.Quasithin.Chapter15.Section01
open ChapterC Section03 Section03.InitialSource ChapterA.Section05To06 MathieuCode
variable {G : Type*} [Group G] [Finite G]

/-- Every remaining natural escape in the original marked family has M₂₂
central quotient, and its exact image is the native affine natural actor.
The M₂₃ alternative is excluded using the original radical Q₁. -/
theorem PreparedChosenModule.source_preExclusion_local_natural_m22_placement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) (h : PreparedChosenModule T M V)
    (hfull : V = localModule T M)
    (m : CaseIPreExclusionMarker T M V h.normalized)
    (hp : m.prime = 3 ∨ m.prime = 5)
    (hres : (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T V : Set G)) :
    ∃ d : CaseIComponentData T M Mc V, d.Z1 = m.Z1 ∧ d.row = m.row ∧
      d.PreExclusionSource h.normalized m.prime ∧
      ∀ K ∈ Chapter1.LIn d.G1 d.S, IsQuasisimple (K ⧸ pCore 2 K) →
        ¬ K ≤ d.MZ → ∀ n : ℕ, IsL2EvenBlock K n →
          m.prime = 3 ∧ n = 2 ∧ m.movingPlane ≤ (blockU K).map K.subtype ∧
            Nat.card m.movingPlane = 4 ∧ K < d.L ∧
            d.L ∈ Chapter1.LStarIn d.G1 d.S ∧ (d.L.subgroupOf d.G1).Normal ∧
            ∃ e : (d.L ⧸ center d.L) ≃* M22,
              (((K.subgroupOf d.L).map (QuotientGroup.mk' (center d.L))).map
                e.toMonoidHom).map m22ToPairStabilizer =
                  M22ChapterH.Quintet.naturalActor.map M22Quintet.Q.subtype := by
  obtain ⟨d,hZ,hr,s,hfamily⟩ := h.source_preExclusion_local_natural_mathieu_carrier
    hG T hempty hM hmany hJ hu hne hfull m hp hres
  refine ⟨d,hZ,hr,s,?_⟩
  intro K hK hq hout n hb
  obtain ⟨hp3,hn,hW,hcard,hKL,hmax,hLn,_,_,name,hname,model⟩ :=
    hfamily K hK hq hout n hb
  refine ⟨hp3,hn,hW,hcard,hKL,hmax,hLn,?_⟩
  rcases hname with rfl | rfl
  · exact s.localFamily_linearTwo_m22_marking (h := h)
      hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb model
  · exact (s.localFamily_linearTwo_not_m23 (h := h)
      hp hG hempty hM hJ hu hne hmany hfull hres hK hq hout hb model).elim

end CFSG.Quasithin.Chapter15.Section01
