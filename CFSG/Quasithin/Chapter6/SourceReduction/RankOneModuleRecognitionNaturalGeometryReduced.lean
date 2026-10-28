module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryClosure

/-!
# A reduced transvection action on the central-line quotient

In the odd critical configuration with abelian U, the actual action on
W/<z> has a nontrivial elementary actor of order at most four. Its core
is the image of O₂(P), where P is the I-closure of the moving layer.
The available core bound is [O₂(I),U] ≤ Z_S; it does not assert that this
core fixes W/<z>.

Instead pass to W/Z_S. Since I fixes Z_S pointwise, the kernel between
the two action images has exponent two. Core transport and the proved
commutator bound therefore give a trivial two-core on the new image of P.
The endpoint intersection Z_S intersect Z' = <z> shows that the moving
actor survives with unchanged order and displacement line of order two.
The exported surjection has kernel exactly the original image’s two-core.
The quotient, conjugation formula and normal closure are all literal.

This supplies the reduced action needed for the component analysis in
6.1.19 without strengthening the earlier commutator bound. The remaining
component/amalgam argument, initial naturalness and unconditional 6.1.27
remain with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.19, printed pp.674–675.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

private theorem reduced_image_core
    {P X Y : Type*} [Group P] [Finite P] [CommGroup X] [Finite X]
    [Group Y] [Finite Y]
    (f : P →* MulAut X) (g : P →* MulAut Y) (q : X →* Y)
    (hq : Function.Surjective q)
    (he : ∀ p x, q (f p x) = g p (q x))
    (hfix : ∀ p x, x ∈ q.ker → f p x = x)
    (hexp : ∀ x : X, x ^ 2 = 1)
    (hc : ∀ p, f.rangeRestrict p ∈ pCore 2 f.range → g p = 1) :
    pCore 2 g.range = ⊥ ∧
      ∃ b : f.range →* g.range, Function.Surjective b ∧
        (∀ p, b (f.rangeRestrict p) = g.rangeRestrict p) ∧
        b.ker = pCore 2 f.range := by
  have hk : f.rangeRestrict.ker ≤ g.rangeRestrict.ker := by
    intro p hp
    apply Subtype.ext
    ext y
    obtain ⟨x,rfl⟩ := hq y
    have hh : f p = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hp)
    change g p (q x) = q x
    simpa only [hh, MulAut.one_apply] using (he p x).symm
  let b : f.range →* g.range := f.rangeRestrict.liftOfSurjective
    f.rangeRestrict_surjective ⟨g.rangeRestrict,hk⟩
  have hb (p : P) : b (f.rangeRestrict p) = g.rangeRestrict p :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ p
  have hbs : Function.Surjective b := by
    intro y
    obtain ⟨p,rfl⟩ := g.rangeRestrict_surjective y
    exact ⟨f.rangeRestrict p,hb p⟩
  have hb2 : IsPGroup 2 b.ker := by
    intro k
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨p,hp⟩ := f.rangeRestrict_surjective (k : f.range)
    have hgp : g p = 1 := by
      have hh := congrArg Subtype.val (MonoidHom.mem_ker.mp k.property)
      rw [←hp,hb] at hh
      exact hh
    have hdisp (x : X) : f p x / x ∈ q.ker := by
      change q (f p x / x) = 1
      rw [map_div,he,hgp,MulAut.one_apply,div_self']
    have hsq (x : X) : f p (f p x) = x := by
      have hh := hfix p (f p x / x) (hdisp x)
      rw [map_div] at hh
      have hm : f p (f p x) = (f p x / x) * f p x := div_eq_iff_eq_mul.mp hh
      rw [hm]
      have hh2 := hexp (f p x)
      have hx2 := hexp x
      simp only [pow_two] at hh2 hx2
      have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
      rw [div_eq_mul_inv,hxi]
      calc
        f p x * x * f p x = (f p x * f p x) * x := by ac_rfl
        _ = x := by rw [hh2,one_mul]
    change ((k : f.range) : MulAut X) ^ (2 ^ 1) = 1
    rw [←hp]
    ext x
    exact hsq x
  have hcore : pCore 2 f.range ≤ b.ker := by
    intro x hx
    obtain ⟨p,rfl⟩ := f.rangeRestrict_surjective x
    apply MonoidHom.mem_ker.mpr
    rw [hb]
    exact Subtype.ext (hc p hx)
  have hpre := b.comap_pCore_of_ker_isPGroup hbs hb2
  have hr : pCore 2 g.range = ⊥ := by
    apply bot_unique
    intro y hy
    obtain ⟨x,rfl⟩ := hbs y
    have hx : x ∈ pCore 2 f.range := hpre ▸ hy
    exact hcore hx
  exact ⟨hr,b,hbs,hb,le_antisymm (le_sSup ⟨inferInstance,hb2⟩) hcore⟩

private theorem quotient_action_kernel
    {G : Type*} [Group G] (I W Z : Subgroup G)
    (hIW : I ≤ normalizer (W : Set G)) (hIZ : I ≤ Subgroup.normalizer (Z : Set G))
    (hN : (Z.subgroupOf W).Normal) :
    let := hN
    ∀ ρ : I →* MulAut (W ⧸ Z.subgroupOf W),
    (∀ i : I, ∀ w : W,
      ρ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
        QuotientGroup.mk' (Z.subgroupOf W)
          ⟨(i : G) * (w : G) * (i : G)⁻¹,
            (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) →
    ρ.ker = (commutatorPreimage I W Z).subgroupOf I := by
  let := hN
  dsimp only
  intro ρ he
  ext i
  change ρ i = 1 ↔ (i : G) ∈ commutatorPreimage I W Z
  rw [mem_commutatorPreimage_iff I W Z hIZ]
  constructor
  · intro hi
    refine ⟨i.property,fun w hw => ?_⟩
    have hh := congrArg (fun f : MulAut (W ⧸ Z.subgroupOf W) =>
      f (QuotientGroup.mk' (Z.subgroupOf W) ⟨w,hw⟩)) hi
    rw [he] at hh
    have hz := QuotientGroup.eq_iff_div_mem.mp hh
    change (i : G) * w * (i : G)⁻¹ / w ∈ Z at hz
    simpa only [commutatorElement_def,div_eq_mul_inv] using hz
  · rintro ⟨_,hc⟩
    ext w
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) w
    rw [he]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (i : G) * (w : G) * (i : G)⁻¹ / (w : G) ∈ Z
    simpa only [commutatorElement_def,div_eq_mul_inv] using hc w w.property

open CFSG.Quasithin.ChapterE
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
namespace NaturalEscapeGraph.OddConfiguration
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)

/-- Passing to W/Z_S gives a reduced normal closure generated by the same
nontrivial transvection actor. All actions use the original conjugation maps. -/
theorem exists_reduced_transvection_action
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let Z' := Z.map (MulAut.conj d.representative).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧ Z' ≤ W ∧ E ⊓ W = Z' ∧
      ∃ (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hN : (Z.subgroupOf W).Normal),
      let := hN
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
        IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W) ∧
        let A := (E.subgroupOf I).map σ
        let J := (P.subgroupOf I).map σ
        IsElementaryAbelian 2 A ∧ 1 < Nat.card A ∧ Nat.card A ≤ 4 ∧
        commutatorAction A (W ⧸ Z.subgroupOf W) =
          (Z'.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W)) ∧
        Nat.card ((Z'.subgroupOf W).map (QuotientGroup.mk' (Z.subgroupOf W))) = 2 ∧
        commutatorAction₂ A (W ⧸ Z.subgroupOf W) = ⊥ ∧
        σ.ker = (commutatorPreimage I W Z).subgroupOf I ∧
        J = conjugateSpanBy A σ.range ∧ pCore 2 J = ⊥ ∧
        ∃ hD : ((zpowers z).subgroupOf W).Normal,
          letI := hD
          ∃ ρ : I →* MulAut (W ⧸ (zpowers z).subgroupOf W),
            (∀ i : I, ∀ w : W,
              ρ i (QuotientGroup.mk' ((zpowers z).subgroupOf W) w) =
                QuotientGroup.mk' ((zpowers z).subgroupOf W)
                  ⟨(i : G) * (w : G) * (i : G)⁻¹,
                    (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
            ∃ hPI : P ≤ I,
              let f := ρ.comp (inclusion hPI)
              let g := σ.comp (inclusion hPI)
              ∃ β : f.range →* g.range, Function.Surjective β ∧
                (∀ p, β (f.rangeRestrict p) = g.rangeRestrict p) ∧
                β.ker = pCore 2 f.range := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hEW,hIW,hD,ρ,hρ,hquot,hAe,hApos,hAupper,
      hdisp,hline,hquad,hker,hspan,hcore,hdisjoint,hAJ,hinj⟩ :=
    d.exists_involution_closure_action h hnat hE hs hNS hab
  let I := Escape.I (T : Subgroup G) L R
  let U := Escape.U (T : Subgroup G) L R
  let Z := ZS (T : Subgroup G) L R
  let W := U ⊓ conjugateSpanBy Z (centralizer ({z} : Set G))
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let Z' := Z.map (MulAut.conj d.representative).toMonoidHom
  let P := conjugateSpanBy E I
  let D := zpowers z
  let := hD
  let := hquot
  let qD := QuotientGroup.mk' (D.subgroupOf W)
  have hIZ : I ≤ Subgroup.normalizer (Z : Set G) := Subgroup.centralizer_le_normalizer _
  have hID : I ≤ Subgroup.normalizer (D : Set G) :=
    (centralizer_le (zpowers_le.mpr hz)).trans (Subgroup.centralizer_le_normalizer _)
  have hZW0 : Z ≤ W := le_inf
    ((show Z ≤ layer L R from inf_le_left).trans (Escape.layer_le_U _ _ _))
    (le_conjugateSpanBy _ _)
  have hWI : W ≤ I := inf_le_left.trans (Escape.U_centralizes_ZS h.layer_centralizes_ZS)
  let hN : (Z.subgroupOf W).Normal := normal_subgroupOf_of_le_normalizer (hWI.trans hIZ)
  let := hN
  obtain ⟨σ,hσ⟩ := exists_quotient_conjugation_action I W Z hIW hIZ hN
  have hσker := quotient_action_kernel I W Z hIW hIZ hN σ hσ
  have hDle : D ≤ Z := zpowers_le.mpr hz
  have hkerle : ρ.ker ≤ σ.ker := by
    rw [hker,hσker]
    exact subgroupOf_mono I (le_commutatorPreimage (commutatorPreimage_le I W D)
      ((commutator_commutatorPreimage_le I W D hID).trans hDle))
  let qZ := QuotientGroup.mk' (Z.subgroupOf W)
  let q : (W ⧸ D.subgroupOf W) →* (W ⧸ Z.subgroupOf W) :=
    QuotientGroup.lift (D.subgroupOf W) qZ (by
      rw [QuotientGroup.ker_mk']; exact subgroupOf_mono W hDle)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf W) y
    exact ⟨qD w,rfl⟩
  have hqeq (i : I) (x : W ⧸ D.subgroupOf W) : q (ρ i x) = σ i (q x) := by
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf W) x
    rw [hρ]
    change qZ _ = σ i (qZ w)
    rw [hσ]
  have hfix (i : I) (x : W ⧸ D.subgroupOf W) (hx : x ∈ q.ker) : ρ i x = x := by
    obtain ⟨w,rfl⟩ := QuotientGroup.mk'_surjective (D.subgroupOf W) x
    change qZ w = 1 at hx
    have hw : (w : G) ∈ Z := (QuotientGroup.eq_one_iff (N := Z.subgroupOf W) w).mp hx
    rw [hρ]
    congr 1
    apply Subtype.ext
    change (i : G) * (w : G) * (i : G)⁻¹ = w
    rw [←mem_centralizer_iff.mp i.property _ hw,mul_inv_cancel_right]
  have hPI : P ≤ I := conjugateSpanBy_le_self hEI
  let f := ρ.comp (inclusion hPI)
  let g := σ.comp (inclusion hPI)
  have hfr : f.range = (P.subgroupOf I).map ρ := by
    rw [MonoidHom.range_comp]
    congr 1
    ext i
    constructor
    · rintro ⟨p,rfl⟩; exact p.property
    · intro hi; exact ⟨⟨i,hi⟩,rfl⟩
  have hgr : g.range = (P.subgroupOf I).map σ := by
    rw [MonoidHom.range_comp]
    congr 1
    ext i
    constructor
    · rintro ⟨p,rfl⟩; exact p.property
    · intro hi; exact ⟨⟨i,hi⟩,rfl⟩
  have hcorekill : (I.pCoreIn 2).subgroupOf I ≤ σ.ker :=
    quotient_conjugation_action_kills_commutator_layer I W Z (I.pCoreIn 2)
      hN hIW ((commutator_mono inf_le_left le_rfl).trans (natural_escape_core h hnat).2) σ hσ
  have hc : ∀ p, f.rangeRestrict p ∈ pCore 2 f.range → g p = 1 := by
    intro p hp
    have hm : ρ (inclusion hPI p) ∈ ((P.subgroupOf I).map ρ).pCoreIn 2 := by
      have hh := mem_map_of_mem f.range.subtype hp
      change f p ∈ f.range.pCoreIn 2 at hh
      rwa [hfr] at hh
    rw [←hcore] at hm
    obtain ⟨i,hi,heq⟩ := hm
    have hdif : inclusion hPI p / i ∈ ρ.ker := by
      change ρ (inclusion hPI p / i) = 1
      rw [map_div,heq,div_self']
    have hi0 : σ i = 1 := hcorekill
      (pCoreIn_mono_of_normalizes hPI (le_normalizer_conjugateSpanBy E I) hi)
    have hh := MonoidHom.mem_ker.mp (hkerle hdif)
    rw [map_div,hi0,div_one] at hh
    exact hh
  obtain ⟨hred,β,hβsurj,hβ,hβker⟩ :=
    reduced_image_core f g q hq (fun p => hqeq (inclusion hPI p))
      (fun p => hfix (inclusion hPI p))
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (W ⧸ D.subgroupOf W))) hc
  rw [hgr] at hred
  have hZcard : Nat.card Z' = 4 := by
    rw [card_map_of_injective (MulAut.conj d.representative).injective]
    have hh := (hnat.sylow_intersection_geometry T h.sylow_normalizes_L).1
    rw [hn] at hh
    exact hh
  have hDle' : D ≤ Z' := by
    have hi := relIndex_mul_relIndex (⊥ : Subgroup G) (D ⊓ Z') Z' bot_le inf_le_right
    rw [relIndex_bot_left,relIndex_bot_left,hZcard,inf_comm D Z',inf_relIndex_left] at hi
    have hc : D.relIndex Z' = 2 := by
      have hh := hline
      rw [←relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hZW] at hh
      exact hh
    rw [hc] at hi
    have hmeet : Nat.card (D ⊓ Z' : Subgroup G) = 2 := by
      rw [inf_comm] at hi
      omega
    have he : D ⊓ Z' = D := eq_of_le_of_card_ge inf_le_left (by
      rw [hmeet,Nat.card_zpowers,ho])
    exact he.symm.le.trans inf_le_right
  have hinter : Z ⊓ Z' = D := by
    have hh := (d.parameter_and_intersection h hnat hE hs hNS).2
    exact (eq_of_le_of_card_ge (le_inf hDle hDle') (by
      rw [hh,Nat.card_zpowers,ho])).symm
  have hcomm : ⁅E,W⁆ ≤ Z' := by
    have hh : (⁅W,E⁆.subgroupOf W).map qD ≤ (Z'.subgroupOf W).map qD := by
      rw [←quotient_conjugation_commutatorAction_eq_image I W D E hIW hEI hD ρ hρ]
      exact hdisp.le
    have hkq : qD.ker ≤ Z'.subgroupOf W := by
      rw [QuotientGroup.ker_mk']; exact subgroupOf_mono W hDle'
    have hc : ⁅W,E⁆.subgroupOf W ≤ Z'.subgroupOf W := by
      have hh' := map_le_iff_le_comap.mp hh
      rwa [comap_map_eq_self hkq] at hh'
    have hm := map_mono (f := W.subtype) hc
    rw [map_subgroupOf_eq_of_le (le_normalizer_iff_commutator_le_left.mp (hEI.trans hIW)),
      map_subgroupOf_eq_of_le hZW,commutator_comm] at hm
    exact hm
  have hsame : σ.ker.subgroupOf (E.subgroupOf I) = ρ.ker.subgroupOf (E.subgroupOf I) := by
    apply le_antisymm
    · intro e he
      change (e : I) ∈ ρ.ker
      rw [hker]
      apply (mem_commutatorPreimage_iff I W D hID _).mpr
      refine ⟨(e : I).property,fun w hw => ?_⟩
      rw [←hinter]
      have heZ : ((e : I) : G) ∈ commutatorPreimage I W Z := by
        change (e : I) ∈ σ.ker at he
        rwa [hσker] at he
      exact ⟨(mem_commutatorPreimage_iff I W Z hIZ _).mp heZ |>.2 w hw,
        hcomm (commutator_mem_commutator e.property hw)⟩
    · exact subgroupOf_mono _ hkerle
  have hcard : Nat.card ((E.subgroupOf I).map σ) = Nat.card ((E.subgroupOf I).map ρ) := by
    rw [←relIndex_ker,←relIndex_ker]
    exact congrArg Subgroup.index hsame
  let := h.layer_elementary
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (E.subgroupOf I) := IsElementaryAbelian.subgroupOf hEI
  have hquotZ : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W) :=
    IsElementaryAbelian.of_surjective q hq
  have hlineZ : Nat.card ((Z'.subgroupOf W).map qZ) = 2 := by
    rw [←relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hZW,←inf_relIndex_left,
      ←inf_comm Z Z',hinter]
    have hh := hline
    rw [←relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hZW] at hh
    exact hh
  have hdispZ : commutatorAction ((E.subgroupOf I).map σ) (W ⧸ Z.subgroupOf W) =
      (Z'.subgroupOf W).map qZ := by
    rw [quotient_conjugation_commutatorAction_eq_image I W Z E hIW hEI hN σ hσ]
    have hh := congrArg (map q) hdisp
    rw [quotient_conjugation_commutatorAction_eq_image I W D E hIW hEI hD ρ hρ,
      map_map,map_map] at hh
    exact hh
  have hdouble : ⁅⁅W,E⁆,E⁆ ≤ Z := by
    have hh : ⁅Z',E⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
      ((hEW.ge.trans inf_le_left).trans (le_centralizer E))
    exact ((commutator_mono (by rwa [commutator_comm] : ⁅W,E⁆ ≤ Z') le_rfl).trans_eq hh).trans bot_le
  have hspanZ : (P.subgroupOf I).map σ = conjugateSpanBy ((E.subgroupOf I).map σ) σ.range := by
    have he : P.subgroupOf I = conjugateSpanBy (E.subgroupOf I) ⊤ := by
      apply map_injective I.subtype_injective
      rw [map_subgroupOf_eq_of_le hPI,map_conjugateSpanBy,map_subgroupOf_eq_of_le hEI,
        ←MonoidHom.range_eq_map,range_subtype]
    rw [he,map_conjugateSpanBy,←MonoidHom.range_eq_map]
  exact ⟨hn,z,a,hz,ho,hEI,hZW0,hZW,hEW,hIW,hN,σ,hσ,hquotZ,
    IsElementaryAbelian.map σ,(by rwa [hcard]),(by rwa [hcard]),hdispZ,hlineZ,
    quotient_conjugation_quadratic_of_double_commutator_le I W Z E hIW hEI hN hdouble σ hσ,
    hσker,hspanZ,hred,hD,ρ,hρ,hPI,β,hβsurj,hβ,hβker⟩

end NaturalEscapeGraph.OddConfiguration

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
