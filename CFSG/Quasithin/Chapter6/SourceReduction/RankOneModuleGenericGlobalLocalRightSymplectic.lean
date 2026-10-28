module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSymplecticGeometry
public import Theory.GroupTheory.SolvableResidual.PrimeTo
public import Theory.GroupTheory.NormalCentralQuotientAction

/-!
# Left-Cartan invariance and complete symplectic right factors

The source quotient restricted to its unique component has characteristic
kernel O₂(C). Hence the original left Cartan acts on the actual symplectic
model. Its odd order kills the action on the two parabolic classes; preservation
of the marked Borel then fixes both determinant kernels. Taking the perfect
lifts inside the component transports this invariance to the original factors.

The existing source construction supplies S-normalization, generation and the
literal Sylow intersections. Transport of its model Borel calculation and
restriction of the original odd Hall subgroup complete both RightFactor
contracts, including field four. Here S remains O₂(N_G(L) ∩ H), and neither
factor is identified with O²(H). The Chapter 12 diagram extension applies these
results to local preparation, retaining the independent original uniqueness
implication. Completion recognition remains a separate part of the global proof.
Source: Aschbacher--Smith 5.1.10--11 and 5.2.1,4, printed
pp.634--635,646,649--650 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {X : Type*} [Group X] [Finite X]
variable {F : Type} [Field F] [Finite F] [CharP F 2]

private theorem odd_preserves_symplectic_locals {D : Type*} [Group D] [Finite D]
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (a : D →* MulAut (Sp F)) (ho : Odd (Nat.card D))
    (ha : ∀ d, (borel (F := F)).map (a d).toMonoidHom = borel (F := F))
    (i : Bool) (d : D) :
    (Prime.symplecticModelLocal F i).map (a d).toMonoidHom = Prime.symplecticModelLocal F i := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show 2^1 < 2^f from Nat.pow_lt_pow_right (by decide) hf)
  let r := (parabolicClassAction hlarge).comp a
  have hc : Nat.card (Equiv.Perm (parabolicClasses hlarge)) ∣ 2 := by
    let := Fintype.ofFinite (parabolicClasses hlarge)
    rw [Nat.card_eq_fintype_card,Fintype.card_perm]
    have hh : Fintype.card (parabolicClasses hlarge) ≤ 2 := by
      simpa only [Nat.card_eq_fintype_card] using card_parabolicClasses_le_two hlarge
    simpa using Nat.factorial_dvd_factorial hh
  have hd : r d = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr ho)
      ((_root_.orderOf_dvd_natCard _).trans hc)
      ((orderOf_map_dvd r d).trans (_root_.orderOf_dvd_natCard d)))
  have hdiag := (mem_parabolicClassAction_ker_iff hlarge (a d)).mp hd
  have hU := EvenBorelTorus.FullTorusFixer.map_unipotent_of_map_borel hF (a d) (ha d)
  have hlocal := local_pair_map_of_unipotent_map hF hf (a d) hdiag hU
  cases i
  · exact hlocal.2
  · exact hlocal.1

private theorem odd_preserves_symplectic_preimages {D : Type*} [Group D] [Finite D]
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (r : X →* Sp F) (hr : Function.Surjective r) [r.ker.Characteristic]
    (a : D →* MulAut X) (ho : Odd (Nat.card D))
    (ha : ∀ d, ((borel (F := F)).comap r).map (a d).toMonoidHom = (borel (F := F)).comap r)
    (i : Bool) (d : D) :
    ((Prime.symplecticModelLocal F i).comap r).map (a d).toMonoidHom =
      (Prime.symplecticModelLocal F i).comap r := by
  let e := QuotientGroup.quotientKerEquivOfSurjective r hr
  let b : D →* MulAut (Sp F) := (MulAut.congr e).toMonoidHom.comp ((quotientAut r.ker).comp a)
  have act (z : D) (x : X) : b z (r x) = r (a z x) := by
    change e (quotientAut r.ker (a z) (e.symm (r x))) = _
    have hx : e.symm (r x) = QuotientGroup.mk' r.ker x :=
      e.symm_apply_eq.mpr rfl
    rw [hx,quotientAut_apply_mk]
    rfl
  have hb (z : D) : (borel (F := F)).map (b z).toMonoidHom = borel (F := F) := by
    have hh := congrArg (map r) (ha z)
    have hc : r.comp (a z).toMonoidHom = (b z).toMonoidHom.comp r := by
      apply MonoidHom.ext
      intro x
      exact (act z x).symm
    rwa [map_map,hc,←map_map,map_comap_eq_self_of_surjective hr] at hh
  have hl := odd_preserves_symplectic_locals hf hF b ho hb i d
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    change r (a d x) ∈ Prime.symplecticModelLocal F i
    rw [←act]
    exact hl ▸ mem_map_of_mem (b d).toMonoidHom hx
  · rw [card_map_of_injective (a d).injective]

omit [Finite X] [Finite F] [CharP F 2] in
private theorem symplectic_component_borel_preimage {M C : Subgroup X}
    (e : sourceImage M C ≃* Sp F)
    (he : (componentOverlap M C).map e.toMonoidHom = borel (F := F)) :
    (borel (F := F)).comap (e.toMonoidHom.comp ((QuotientGroup.mk' (sourceKernel M)).subgroupMap C)) =
      M.subgroupOf C := by
  ext x
  let z : sourceImage M C := ⟨QuotientGroup.mk' (sourceKernel M) x.val,x.val,x.property,rfl⟩
  change e z ∈ borel (F := F) ↔ _
  rw [←he,mem_map_equiv,e.symm_apply_apply]
  change QuotientGroup.mk' (sourceKernel M) x.val ∈ sourceImage M (M ⊓ C) ↔ x.val ∈ M
  constructor
  · rintro ⟨m,hm,hmx⟩
    have hdM := M.normalCore_le (QuotientGroup.eq_iff_div_mem.mp hmx)
    have hh := M.mul_mem (M.inv_mem hdM) hm.1
    simpa only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,mul_one] using hh
  · intro hx
    exact ⟨x.val,⟨hx,x.property⟩,rfl⟩

omit [Finite F] [CharP F 2] in
private theorem symplectic_factor_in_component {M C : Subgroup X}
    (e : sourceImage M C ≃* Sp F) (i : Bool)
    (hRC : Prime.symplecticSourceFactor M C e i ≤ C) :
    Prime.symplecticSourceFactor M C e i =
      ((solvableResidual ((Prime.symplecticModelLocal F i).comap
        (e.toMonoidHom.comp ((QuotientGroup.mk' (sourceKernel M)).subgroupMap C)))).map
          ((Prime.symplecticModelLocal F i).comap
        (e.toMonoidHom.comp ((QuotientGroup.mk' (sourceKernel M)).subgroupMap C))).subtype).map C.subtype := by
  let q := QuotientGroup.mk' (sourceKernel M)
  let j := (sourceImage M C).subtype.comp e.symm.toMonoidHom
  let P := ((Prime.symplecticModelLocal F i).map j).comap q
  let r := e.toMonoidHom.comp (q.subgroupMap C)
  let Q := (Prime.symplecticModelLocal F i).comap r
  have hQ : Q.map C.subtype = P ⊓ C := by
    ext x
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨r x,hx,congrArg Subtype.val (e.symm_apply_apply (q.subgroupMap C x))⟩,x.property⟩
    · rintro ⟨⟨y,hy,heq⟩,hx⟩
      refine ⟨⟨x,hx⟩,?_,rfl⟩
      change r ⟨x,hx⟩ ∈ Prime.symplecticModelLocal F i
      have heq' : e.symm y = q.subgroupMap C ⟨x,hx⟩ := Subtype.ext heq
      change e (q.subgroupMap C ⟨x,hx⟩) ∈ _
      rw [←heq',e.apply_symm_apply]
      exact hy
  change (solvableResidual P).map P.subtype = ((solvableResidual Q).map Q.subtype).map C.subtype
  rw [map_embedded_solvableResidual_of_hom,hQ]
  let : Group.IsPerfect ((solvableResidual P).map P.subtype) := Group.IsPerfect.map P.subtype
  apply le_antisymm
  · apply le_map_solvableResidual_of_isPerfect
    exact le_inf (map_subtype_le _) hRC
  · exact map_solvableResidual_mono inf_le_left


variable {G : Type*} [Group G] [Finite G]

/-- The odd left Cartan fixes both canonical perfect lifts in the symplectic row. -/
theorem symplectic_source_cartan_normalizes
    {T : Sylow 2 G} {L H A B : Subgroup G} {f : ℕ}
    (hTH : (T : Subgroup G) ≤ H) (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel (F := F))
    (hk : sourceKernel ((normalizer (L : Set G)).subgroupOf H) = pCore 2 H) (i : Bool)
    (hRC : Prime.symplecticSourceFactor ((normalizer (L : Set G)).subgroupOf H) C e i ≤ C) :
    A ≤ normalizer (((Prime.symplecticSourceFactor
      ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype) : Set G) := by
  let M := (normalizer (L : Set G)).subgroupOf H
  let K := C.map H.subtype
  let j : C →* G := H.subtype.comp C.subtype
  let k : C ≃* K := C.equivMapOfInjective H.subtype H.subtype_injective
  have hCK : K = residual H := congrArg (map H.subtype)
    (DiagramHall.single_component_eq_twoResidual (T.subtype hTH) hC hc).symm
  have hAK : A ≤ normalizer (K : Set G) := hCK ▸ c.left_le.trans hN
  let a : A →* MulAut C := (MulAut.congr k.symm).toMonoidHom.comp
    (K.normalizerMonoidHom.comp (inclusion hAK))
  have act (d : A) : j.comp (a d).toMonoidHom = (MulAut.conj (d : G)).toMonoidHom.comp j := by
    ext x
    change j (k.symm (K.normalizerMonoidHom ⟨d,hAK d.property⟩ (k x))) = _
    have hjk (y : K) : j (k.symm y) = (y : G) :=
      congrArg Subtype.val (k.apply_symm_apply y)
    rw [hjk]
    exact normalizerMonoidHom_apply_apply_coe K ⟨d,hAK d.property⟩ (k x)
  let r := e.toMonoidHom.comp ((QuotientGroup.mk' (sourceKernel M)).subgroupMap C)
  have hr : Function.Surjective r :=
    e.surjective.comp ((QuotientGroup.mk' (sourceKernel M)).subgroupMap_surjective C)
  have hrk : r.ker = pCore 2 C := by
    rw [pCore_subnormal_eq_comap 2 hC.subnormal]
    ext x
    change e ((QuotientGroup.mk' (sourceKernel M)).subgroupMap C x) = 1 ↔ x.val ∈ pCore 2 H
    constructor
    · intro hx
      have hz := e.injective (hx.trans e.map_one.symm)
      have hq : QuotientGroup.mk' (sourceKernel M) x.val = 1 := congrArg Subtype.val hz
      have hm := (QuotientGroup.eq_one_iff x.val).mp hq
      exact hk ▸ hm
    · intro hx
      have hm : x.val ∈ sourceKernel M := hk ▸ hx
      have hz : (QuotientGroup.mk' (sourceKernel M)).subgroupMap C x = 1 :=
        Subtype.ext ((QuotientGroup.eq_one_iff x.val).mpr hm)
      exact (congrArg e hz).trans e.map_one
  let : r.ker.Characteristic := hrk ▸ inferInstance
  have hj : Function.Injective j := H.subtype_injective.comp C.subtype_injective
  have him : ((borel (F := F)).comap r).map j = normalizer (L : Set G) ⊓ K := by
    rw [symplectic_component_borel_preimage e he]
    change (M.subgroupOf C).map (H.subtype.comp C.subtype) = _
    rw [←map_map,subgroupOf_map_subtype,Subgroup.map_inf _ _ _ H.subtype_injective,
      subgroupOf_map_subtype]
    exact inf_assoc _ _ _ |>.trans (congrArg (fun Q : Subgroup G => normalizer (L : Set G) ⊓ Q)
      (inf_eq_right.mpr (map_subtype_le C)))
  have hAM : A ≤ normalizer (normalizer (L : Set G) : Set G) :=
    ((c.left_le.trans inf_le_left).trans L.le_normalizer).trans
      (normalizer (L : Set G)).le_normalizer
  have hAI := (le_inf hAM hAK).trans inf_normalizer_le_normalizer_inf
  have ha (d : A) : ((borel (F := F)).comap r).map (a d).toMonoidHom = (borel (F := F)).comap r := by
    apply map_injective hj
    rw [map_map,act,←map_map,him]
    exact mem_normalizer_iff_map_conj_eq.mp (hAI d.property)
  have ho : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  let Q := (Prime.symplecticModelLocal F i).comap r
  have hR : (Prime.symplecticSourceFactor M C e i).map H.subtype =
      ((solvableResidual Q).map Q.subtype).map j := by
    rw [symplectic_factor_in_component e i hRC,map_map]
  intro d hd
  apply mem_normalizer_iff_map_conj_eq.mpr
  change ((Prime.symplecticSourceFactor M C e i).map H.subtype).map
    (MulAut.conj d).toMonoidHom = (Prime.symplecticSourceFactor M C e i).map H.subtype
  rw [hR,map_map,←act ⟨d,hd⟩,←map_map,map_embedded_solvableResidual_of_hom,
    odd_preserves_symplectic_preimages hf hF r hr a ho ha i ⟨d,hd⟩]


open CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

/-- Both symplectic factors satisfy the complete normalized right-factor contract,
with their original marked field and exact Borel overlap. -/
theorem symplectic_source_rightFactors
    {T : Sylow 2 G} {L H A B : Subgroup G} {f : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp4Derived F)
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = sp4DerivedBorel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e
      ((pointParabolic (F := F)).subgroupOf (Sp4Derived F))
      ((planeParabolic (F := F)).subgroupOf (Sp4Derived F))) :
    ∃ eF : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* Sp F,
      (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
        eF.toMonoidHom = borel (F := F) ∧
      ∀ i : Bool, let R := (Prime.symplecticSourceFactor
        ((normalizer (L : Set G)).subgroupOf H) C eF i).map H.subtype
        RightFactor T L H A B R ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
          R ⊔ (T : Subgroup G) = H ∧
          ChapterF.Source.borel R (sourceS L H) = normalizer (L : Set G) ⊓ R := by
  let S := T.subtype hH.1.1.2
  let M := (normalizer (L : Set G)).subgroupOf H
  obtain ⟨eF,hmark,hr⟩ := symplectic_source_original_factors_marked
    hTL hH hpar c hC hqs hc hf hF e he hmove
  let R0 := symplecticSourceFactor M C eF
  let R := fun i => (R0 i).map H.subtype
  have hST : (S : Subgroup H).map H.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hH.1.1.2
  have hSK := diagram_sourceS_intersection_residual hTL hH hpar hC hc hf
    (Or.inr ⟨F,inferInstance,inferInstance,inferInstance,by omega,hF,e,he,hmove⟩)
  let : C.Normal := DiagramHall.single_component_normal S hC hc
  refine ⟨eF,hmark,?_⟩
  intro i
  obtain ⟨hRK,hout,hgen,hquot,hcomp,hSn,hBn,P,hP⟩ := hr i
  have hRH : R i ≤ H := map_subtype_le _
  have hSR : Global.sourceS L H ⊓ R i = (T : Subgroup G) ⊓ R i := by
    calc
      _ = (Global.sourceS L H ⊓ residual H) ⊓ R i := by rw [inf_assoc,inf_eq_right.mpr hRK]
      _ = _ := by rw [hSK,inf_assoc,inf_eq_right.mpr hRK]
  let er := (R0 i).equivMapOfInjective H.subtype H.subtype_injective
  let P0 := P.mapSurjective (f := er.symm.toMonoidHom) er.symm.surjective
  have hP0 : (P0 : Subgroup (R0 i)).map (R0 i).subtype = (S : Subgroup H) ⊓ R0 i := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_inf _ _ _ H.subtype_injective,hST]
    calc
      _ = (P : Subgroup (R i)).map (R i).subtype := by
        change (((P : Subgroup (R i)).map er.symm.toMonoidHom).map (R0 i).subtype).map H.subtype = _
        simp only [map_map]
        congr 1
        ext x
        exact congrArg Subtype.val (er.apply_symm_apply x)
      _ = _ := hP.trans hSR
  let eqr := QuotientGroup.congr _ _ er (pCore_map_iso 2 er)
  have hnot0 : ¬ R0 i ≤ M := by
    intro hh
    exact hout (map_le_iff_le_comap.mpr hh)
  have hq0 : ChapterF.Source.IsRankOneModel (R0 i ⧸ pCore 2 (R0 i)) :=
    .linear f (by omega) (hquot.of_mulEquiv eqr)
  have hb0 := symplecticSourceFactor.borel_eq_overlap hf hF S (comap_mono hTL) eF hmark i hnot0 hq0 P0 hP0
  have hb : ChapterF.Source.borel (R i) (Global.sourceS L H) =
      normalizer (L : Set G) ⊓ R i := by
    have hh := congrArg (map H.subtype) hb0
    change (ChapterF.Source.borel (R0 i) (S : Subgroup H)).map H.subtype =
      (M ⊓ R0 i).map H.subtype at hh
    rw [ChapterF.Source.borel_map_of_ker_le H.subtype (R0 i) S ⟨P0,hP0⟩
      (by rw [H.ker_subtype];exact bot_le),hST,
      Subgroup.map_inf _ _ _ H.subtype_injective,subgroupOf_map_subtype] at hh
    rw [inf_assoc,inf_eq_right.mpr hRH] at hh
    change R i ⊓ normalizer ((Global.sourceS L H ⊓ R i : Subgroup G) : Set G) = _
    rw [hSR]
    exact hh
  have hCK : C.map H.subtype = residual H := congrArg (map H.subtype)
    (DiagramHall.single_component_eq_twoResidual S hC hc).symm
  have hRC : R0 i ≤ C := (map_le_map_iff_of_injective H.subtype_injective).mp
    (hRK.trans_eq hCK.symm)
  have hk := Prime.symplectic_sourceKernel_eq_twoCore S (comap_mono hTL) hC hqs hc hf hF e
  have hAn := symplectic_source_cartan_normalizes hH.1.1.2 c hN hC hc hf hF eF hmark hk i hRC
  refine ⟨⟨hRK,hout,⟨P,hP⟩,.linear f (by omega) hquot,hSn,hAn,?_⟩,hquot,hgen,hb⟩
  · let U := normalizer (L : Set G) ⊓ R i
    have hU : U ≤ Global.intersection L H := le_inf inf_le_left (inf_le_right.trans hRH)
    have hBU : B ≤ normalizer (U : Set G) :=
      (le_inf ((c.right_le.trans inf_le_left).trans (normalizer (L : Set G)).le_normalizer)
        hBn).trans inf_normalizer_le_normalizer_inf
    have hh := OddHall.hall_restrict_of_normalizes c.right_hall c.right_le hU hBU
    obtain ⟨Q,hQ⟩ := P.exists_map_subtype_eq_of_le (show U ≤ R i from inf_le_right)
      (hP.trans hSR ▸ le_inf (inf_le_left.trans hTL) inf_le_right)
    have heq := congrArg (map U.subtype) (OddHall.sylow_complement_of_hall Q hh).sup_eq_top
    have hi : B ⊓ U = B ⊓ R i := by
      dsimp [U]
      rw [←inf_assoc,inf_eq_left.mpr (c.right_le.trans inf_le_left)]
    rw [Subgroup.map_sup,hQ,hP,subgroupOf_map_subtype,hi,
      ←MonoidHom.range_eq_map,range_subtype] at heq
    rw [hb]
    exact heq.symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
