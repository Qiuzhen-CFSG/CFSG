module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldDegree
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalSmallGenerationParity
public import CFSG.Quasithin.Chapter6.Section02.NaturalSylowGeometry
public import Theory.SpecificGroups.SL2.OddFixedVectors
public import Theory.GroupTheory.PResidual.NormalPGroupSupplement
-- Internal continuation of the same Cartan numerical argument.
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldQrc
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldDegree

/-!
# The natural omega-span branch of small Cartan generation

The original Cartan acts freely on a nonidentity omega point. Its orbit,
with zero adjoined, exhausts the natural Sylow-fixed line, of order 2ⁿ.
Thus the literal Cartan omega-span is reduced and faithful. The two-core
of AT is its full centralizer, and the original H-intersection normalizes
O²(AT), identified with the Borel residual. This constructs source 3.1.5.

Above degree two, the original Thompson theorem makes AT normalize J(T).
The source 3.1.7 residual-Sylow argument then forces H to centralize omega:
any common normal subgroup would lie in the zero two-core of AH. This
uses the actual zero-core hypothesis, never uniqueness over the smaller AT.
The proved qrc estimate and regular cyclic-torus normalizer bound give
n ≤ 4. Parity yields two or four, discharging small Cartan generation.

The natural model on the original L-span of omega remains an explicit
branch hypothesis. Source model selection and the other module branches
remain with the full local-to-global argument. The Chapter12 extension
applies the result to the same chosen module and escaping prime pair.

Source: Aschbacher--Smith 5.1.6(2), pp.632--633, with 3.1.7, pp.575--576,
and its 5.2.2 application, p.647 (`refs/quasithin.pdf`). The two `import all`
lines deliberately continue the private numerical/Singer proofs in this
same Cartan argument, preserving their existing public boundaries.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem natural_odd_point_stabilizer
    {L U : Subgroup G} {n : ℕ} (hm : IsNaturalModule L U n)
    {x z : G} (hx : x ∈ L) (ho : Odd (orderOf x))
    (hz : z ∈ U) (hz0 : z ≠ 1) (he : x*z*x⁻¹=z) : x=1 := by
  obtain ⟨F,_,_,_,_,e,f,hf⟩ := hm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let xL : L := ⟨x,hx⟩
  have hfix : (q xL).val.mulVec (f ⟨z,hz⟩).toAdd = (f ⟨z,hz⟩).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply U.subtype_injective
    change (f.symm (Multiplicative.ofAdd ((q xL).val.mulVec (f ⟨z,hz⟩).toAdd)) : G) =
      (f.symm (f ⟨z,hz⟩) : G)
    rw [f.symm_apply_apply]
    exact (hf xL ⟨z,hz⟩).trans he
  have hq : q xL = 1 := by
    by_contra hne
    have hh := Matrix.SL2.odd_power_fixed_eq_zero (q xL) (orderOf x) ho
      (by rw [←map_pow,show xL^orderOf x=1 from Subtype.ext (pow_orderOf_eq_one x),map_one])
      hne (f ⟨z,hz⟩).toAdd hfix
    apply hz0
    exact congrArg (fun u : U => (u:G)) (f.injective (hh.trans f.map_one.symm))
  have hcore : xL ∈ pCore 2 L := (QuotientGroup.eq_one_iff xL).mp
    (e.map_eq_one_iff.mp hq)
  have hc := (pCore_isPGroup (p:=2) (G:=L)).orderOf_coprime
    ho.coprime_two_left (⟨xL,hcore⟩ : pCore 2 L)
  have hc' : Nat.Coprime (orderOf x) (orderOf x) := by
    simpa only [Subgroup.orderOf_mk,xL] using hc
  exact orderOf_eq_one_iff.mp (by simpa only [Nat.gcd_self] using hc'.gcd_eq_one)

/-- The literal full Cartan omega-span is the natural Sylow-fixed line. -/
theorem Input.natural_cartan_span
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B)
    (hm : IsNaturalModule L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n) :
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let V := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) A
    V = U ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
    Nat.card V = 2^n ∧
    A ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) ∧
    A ⊓ centralizer (V : Set G) = ⊥ := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z L
  let V := conjugateSpanBy Z A
  let C := U ⊓ centralizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)
  have hCc := (hm.sylow_intersection_geometry T h.sylow_normalizes).1
  have hDc := c.left_card h.linear h.sylow_normalizes
  change Nat.card C = 2^n at hCc
  have hZT : Z ≤ (T : Subgroup G) := fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
  have hZC : Z ≤ C := by
    intro z hz
    exact ⟨le_conjugateSpanBy Z L hz,fun t ht =>
      ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht.1⟩
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) := by
    have hr := LocalOmega.span_reduced T L (h.qtke.evenCharacteristic T)
      h.maximal_local.1 h.sylow_normalizes
    have hu := LocalOmega.span_elementary_le_sylow T L (h.qtke.evenCharacteristic T)
      h.maximal_local.1 h.sylow_normalizes
    exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
      (hu.2.trans (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right))).mp hr.normal)
  have hTinter : (T : Subgroup G) ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans inf_normalizer_le_normalizer_inf
  have hnorm : A ⊔ (T : Subgroup G) ≤ normalizer (C : Set G) := by
    apply (le_inf (sup_le ((c.left_le.trans inf_le_left).trans
      (le_normalizer_conjugateSpanBy Z L)) hTU)
      (sup_le (c.left_le.trans inf_le_right) hTinter |>.trans
        (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hVC : V ≤ C := conjugateSpanBy_le hZC (le_sup_left.trans hnorm)
  have hW0 : W ≠ ⊥ := fun he => h.noncentral (by rw [he,commutator_bot_left])
  obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot T.isPGroup' hW0 h.reduced_le_sylow
      (le_sup_right.trans (reduced_normalizes h.reduced)))
  have hzZ : (z:G) ∈ Z := by
    let := h.reduced.2.1
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨h.reduced_le_sylow z.property.1,
        elemPow_eq_one_of_isElementaryAbelian (p:=2) (z:G) z.property.1,z.property.2.2⟩
  have hz0 : (z:G) ≠ 1 := fun he => hz1 (Subtype.ext he)
  have hoA : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have hfree (x : G) (hx : x ∈ A) (he : x*(z:G)*x⁻¹=(z:G)) : x=1 := by
    have ho : Odd (orderOf x) := hoA.of_dvd_nat (by
      rw [←Subgroup.orderOf_mk x hx]
      exact orderOf_dvd_natCard _)
    exact natural_odd_point_stabilizer hm (c.left_le hx).1 ho
      (le_conjugateSpanBy Z L hzZ) hz0 he
  let orb : A → V := fun d =>
    ⟨(d:G)*(z:G)*(d:G)⁻¹,subset_closure ⟨d,d.property,z,hzZ,rfl⟩⟩
  have horb0 (d : A) : orb d ≠ 1 := by
    intro he
    apply hz0
    have hh := congrArg Subtype.val he
    change (MulAut.conj (d:G)) (z:G) = 1 at hh
    exact (MulAut.conj (d:G)).map_eq_one_iff.mp hh
  have hi : Function.Injective orb := by
    intro a b he
    have hh : (b:G)*(z:G)*(b:G)⁻¹=(a:G)*(z:G)*(a:G)⁻¹ :=
      (congrArg Subtype.val he).symm
    have hf := hfree ((a:G)⁻¹*(b:G)) (A.mul_mem (A.inv_mem a.property) b.property) (by
      calc
        (a:G)⁻¹*(b:G)*(z:G)*((a:G)⁻¹*(b:G))⁻¹ =
            (a:G)⁻¹*((b:G)*(z:G)*(b:G)⁻¹)*(a:G) := by group
        _ = (z:G) := by rw [hh]; group)
    exact Subtype.ext (inv_mul_eq_one.mp hf)
  let f : Option A → V := fun d => d.elim 1 orb
  have hfi : Function.Injective f := by
    intro a b he
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b => exact (horb0 b he.symm).elim
    | some a =>
      cases b with
      | none => exact (horb0 a he).elim
      | some b => exact congrArg some (hi he)
  have hlow := Nat.card_le_card_of_injective f hfi
  have hopt : Nat.card (Option A) = Nat.card A+1 := by
    let : Fintype A := Fintype.ofFinite A
    simp only [Nat.card_eq_fintype_card,Fintype.card_option]
  rw [hopt,hDc] at hlow
  have hp : 0 < (2:ℕ)^n := pow_pos (by decide) _
  have he : V = C := eq_of_le_of_card_ge hVC (by omega)
  change V = C ∧ Nat.card V = 2^n ∧ A ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) ∧ _
  refine ⟨he,by rw [he]; exact hCc,by rw [he]; exact hnorm,?_⟩
  apply _root_.eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  apply hfree x hx.1
  exact mul_inv_eq_iff_eq_mul.mpr ((hx.2 z (le_conjugateSpanBy Z A hzZ)).symm)

/-- The original natural Cartan omega-span is reduced in AT. -/
theorem Input.natural_cartan_span_reduced
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (c : CartanPair T L H A B)
    (hm : IsNaturalModule L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n) :
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    conjugateSpanBy Z A ∈ reducedFamily (A ⊔ (T : Subgroup G)) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let V := conjugateSpanBy Z A
  let J := A ⊔ (T : Subgroup G)
  have hg := h.natural_cartan_span c hm
  have hn : J ≤ normalizer (V : Set G) := hg.2.2.1
  have hjoin : conjugateSpanBy Z J = V := le_antisymm
    (conjugateSpanBy_le (le_conjugateSpanBy Z A) hn)
    (conjugateSpanBy_mono le_rfl le_sup_left)
  have hZT : Z ≤ (T : Subgroup G) := fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hZJ : Z ≤ J := hZT.trans le_sup_right
  have hVJ : V ≤ J := hjoin ▸ conjugateSpanBy_le_self hZJ
  have hu := LocalOmega.span_elementary_le_sylow T L (h.qtke.evenCharacteristic T)
    h.maximal_local.1 h.sylow_normalizes
  let := hu.1
  have hVU : V ≤ conjugateSpanBy Z L :=
    conjugateSpanBy_mono le_rfl (c.left_le.trans inf_le_left)
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_injective
    (inclusion hVU) (inclusion_injective hVU)
  let S := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  have hz : omegaOneCenterAmbient (S : Subgroup J) = Z.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [←omegaOneCenterAmbient_map_injective J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hZJ]
    congr 1
    exact map_subgroupOf_eq_of_le le_sup_right
  have hclosure : normalClosure (omegaOneCenterAmbient (S : Subgroup J) : Set J) = V.subgroupOf J := by
    rw [hz,normalClosure_subgroupOf_eq_conjugateSpanBy _ J hZJ,hjoin]
  let : IsElementaryAbelian 2 (V.subgroupOf J) := IsElementaryAbelian.subgroupOf hVJ
  let : IsMulCommutative (normalClosure (omegaOneCenterAmbient (S : Subgroup J) : Set J)) := by
    rw [hclosure]
    infer_instance
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient (S : Subgroup J)) :=
    omegaOneCenterAmbient_elementaryAbelian _
  have hr := isPReduced_normalClosure_of_sylow_central S
    (omegaOneCenterAmbient (S : Subgroup J))
    (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
    (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)
  rw [hclosure] at hr
  exact ⟨hVJ,inferInstance,hr.normal,hr.quotient_pCore_eq_bot⟩


private theorem cartan_residual_normalized
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hz : (A ⊔ H).pCoreIn 2 = ⊥) :
    H ⊓ normalizer (L : Set G) ≤ normalizer (residual (A ⊔ (T : Subgroup G)) : Set G) := by
  let C := localBorel T L
  let J := C ⊔ (T : Subgroup G)
  have hLH : ¬ L ≤ H := by
    intro hl
    have hAH : A ≤ H := c.left_le.trans (inf_le_left.trans hl)
    exact hH.1.1.1 (by simpa only [sup_eq_right.mpr hAH] using hz)
  have hHN : normalizer (L : Set G) ⊓ H ≤ normalizer (C : Set G) :=
    intersection_normalizes_localBorel h.linear h.sylow_normalizes hH.1.1.2 hLH
  have hTN : (T : Subgroup G) ≤ normalizer (C : Set G) :=
    (show (T : Subgroup G) ≤ normalizer (L : Set G) ⊓ H from
      le_inf h.sylow_normalizes hH.1.1.2).trans hHN
  have he : J = A ⊔ (T : Subgroup G) := by
    change C ⊔ (T : Subgroup G) = A ⊔ (T : Subgroup G)
    rw [show C = ((T : Subgroup G) ⊓ L) ⊔ A from
      (c.left_sup_intersection h.sylow_normalizes).symm]
    exact le_antisymm (sup_le (sup_le (inf_le_left.trans le_sup_right) le_sup_left) le_sup_right)
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  let : (C.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le C.le_normalizer hTN)
  have hr := pResidual_of_normal_pGroup_supplement 2 (C.subgroupOf J)
    ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype
    (by rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self])
  have hm := congrArg (map J.subtype) hr
  rw [map_embedded_pResidual,map_subgroupOf_eq_of_le le_sup_left] at hm
  have hr' : residual (A ⊔ (T : Subgroup G)) = residual C := by
    change residual C = residual J at hm
    exact he ▸ hm.symm
  rw [hr',inf_comm]
  exact hHN.trans (normalizer_le_normalizer_characteristic_image C (pResidual 2 C))

/-- Source 3.1.5 on the actual natural Cartan span, using the normalized Borel residual. -/
theorem Input.natural_cartan_qrc_hypotheses
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hm : IsNaturalModule L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hz : (A ⊔ H).pCoreIn 2 = ⊥) :
    Chapter3.QrcHypotheses T (normalizer (L : Set G))
      (A ⊔ (T : Subgroup G)) H
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) A) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let X := conjugateSpanBy Z A
  let J := A ⊔ (T : Subgroup G)
  have hg := h.natural_cartan_span c hm
  have hr := h.natural_cartan_span_reduced c hm
  let := hr.2.1
  have hJN : J ≤ normalizer (X : Set G) := reduced_normalizes hr
  have hcore := reduced_torus_centralizer hr
    (torus_join_card c h.sylow_normalizes h.linear le_rfl) hg.2.2.2
  refine ⟨le_sup_right,
    sup_le (c.left_le.trans (inf_le_left.trans L.le_normalizer)) h.sylow_normalizes,
    hH,hr.1,hJN,hr.2.1,?_,hcore,Or.inl (cartan_residual_normalized h hH c hz)⟩
  · exact Chapter3.Section02.internalActionImage_core_of_reduced J X hr.1 hJN
      (show IsPReduced 2 (X.subgroupOf J) from
        ⟨hr.2.2.choose,IsElementaryAbelian.subgroupOf hr.1,hr.2.2.choose_spec⟩)

private theorem natural_cartan_qrc_configuration
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hm : IsNaturalModule L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hz : (A ⊔ H).pCoreIn 2 = ⊥) :
    ChapterD.QRCConfiguration (A ⊔ (T : Subgroup G)) H (T : Subgroup G)
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) A) := by
  let hq := h.natural_cartan_qrc_hypotheses hH c hm hz
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  apply hq.toQRCConfiguration
  rintro ⟨N,hNc,hN,hn⟩
  have hNT : N ≤ (T : Subgroup G) := hNc.trans (hq.core_eq_centralizer ▸ inf_le_left)
  have hgen : Chapter3.generated (A ⊔ (T : Subgroup G)) H = A ⊔ H := by
    rw [Chapter3.generated_eq_sup,sup_assoc,sup_eq_right.mpr hTH]
  have hnorm : A ⊔ H ≤ normalizer (N : Set G) := by
    simpa only [hgen] using (Chapter3.normalIn_iff_le_normalizer.mp hn).2
  have hcore := le_pCoreIn_of_normalizes (T.isPGroup'.to_le hNT)
    (hNT.trans (hTH.trans le_sup_right)) hnorm
  exact hN (bot_unique (hz ▸ hcore))

/-- The source 3.1.7 common-normal argument on the actual natural span
forces H to centralize omega above degree two. -/
theorem Input.natural_cartan_omega_centralizes
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    (hm : IsNaturalModule L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hn : 2 < n) (hz : (A ⊔ H).pCoreIn 2 = ⊥) : H ≤ omegaCentralizer T := by
  have hZ : omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
    by_contra hZ
    have hjW := h.thompson_moves_of_noncentral_omega hH hZ
    obtain hJN | ⟨he,_⟩ := h.borel_thompson_or_degree_two hjW
    swap
    · omega
    let X := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) A
    let J := A ⊔ (T : Subgroup G)
    let hq := h.natural_cartan_qrc_hypotheses hH c hm hz
    let d := natural_cartan_qrc_configuration h hH c hm hz
    have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
      sSup_le fun _ hE => hE.1
    have hJcore : elementaryAbelianMaxJ (T : Subgroup G) ≤ J.pCoreIn 2 :=
      le_pCoreIn_of_normalizes (T.isPGroup'.to_le hJT) (hJT.trans le_sup_right)
        ((sup_le_sup_right c.left_le _).trans hJN)
    have hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (X : Set G) :=
      hJcore.trans (hq.core_eq_centralizer ▸ inf_le_right)
    let S := T.subtype (show (T : Subgroup G) ≤ H from hH.1.1.2)
    let Z := omegaOneCenterAmbient (S : Subgroup H)
    let U := (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) H).subgroupOf H
    have hU : IsPReduced 2 U := hq.sylowOmega_reduced (h.qtke.evenCharacteristic T)
    let := hU.normal
    have hZT : omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) :=
      fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1
    have hzmap : Z.map H.subtype = omegaOneCenterAmbient (T : Subgroup G) := by
      rw [←omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective]
      congr 1
      exact map_subgroupOf_eq_of_le hH.1.1.2
    have hZU : Z ≤ U := by
      intro z hz
      apply le_conjugateSpanBy
      exact hzmap ▸ mem_map_of_mem H.subtype hz
    have hjmap : (elementaryAbelianMaxJ (S : Subgroup H)).map H.subtype =
        elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
      congr 1
      exact map_subgroupOf_eq_of_le hH.1.1.2
    have hJn : ¬ (elementaryAbelianMaxJ (S : Subgroup H)).Normal := by
      intro hnormal
      let := hnormal
      have hnorm := (elementaryAbelianMaxJ (S : Subgroup H)).le_normalizer_map H.subtype
      rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hjmap] at hnorm
      obtain ⟨N,hNR,hN,hnN⟩ := hq.common_normal_of_thompson_normal h.maximal hJ hnorm
      exact hN (d.no_common_normal N hNR (by
        simpa only [Chapter3.generated_eq_sup] using (Chapter3.normalIn_iff_le_normalizer.mp hnN).2))
    have hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤ := by
      obtain ⟨K,⟨hK,hTK⟩,hk⟩ := Chapter3.HStar.unique_maximal_subgroup T h.sylow_normalizes hH
      have hSK : (S : Subgroup H) ≤ K := by
        intro t ht
        obtain ⟨k,hk,he⟩ := hTK ht
        exact H.subtype_injective he ▸ hk
      refine ⟨hSK.trans_lt hK.lt_top,K,⟨hSK,hK.covBy_top⟩,?_⟩
      intro C hC
      apply hk C
      exact ⟨hC.2.isCoatom,fun t ht => ⟨⟨t,hH.1.1.2 ht⟩,hC.1 ht,rfl⟩⟩
    have hj := thompson_not_centralizes_of_unique_maximal S U Z hZU
      (fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2)
      (fun hc => hZ (by rw [←hzmap]; exact map_mono hc)) hu hJn
    have hRne : J.pCoreIn 2 ≠ ⊥ := by
      intro he
      have hX : X = ⊥ := bot_unique (d.module_le_core.trans_eq he)
      have hc := (h.natural_cartan_span c hm).2.1
      change Nat.card X = 2^n at hc
      rw [hX,card_bot] at hc
      have hp : 1 < (2:ℕ)^n := Nat.one_lt_pow (by omega) (by decide)
      omega
    have hp := hstar_minimalParabolic_of_generation_gt_one h.sylow_normalizes hH hgen
    obtain ⟨N,hNR,hN,hnN⟩ := hq.common_normal_of_residual_sylow
      (Chapter3.source_common_normal_knownSimple h.qtke T) hRne
      (residual_sylow_of_reduced_module hq h.qtke hp hJ U hU hj)
    exact hN (d.no_common_normal N hNR (by
      simpa only [Chapter3.generated_eq_sup] using (Chapter3.normalIn_iff_le_normalizer.mp hnN).2))
  intro x hx z hz'
  obtain ⟨a,ha,rfl⟩ := hZ hz'
  exact (congrArg H.subtype ((mem_center_iff.mp ha) ⟨x,hx⟩)).symm

/-- The full Cartan's zero-core join gives the cubic bound on its actual
natural fixed line. No uniqueness for the smaller AT join is assumed. -/
theorem Input.natural_cartan_cubicRatio_le_two
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hm : IsNaturalModule L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hHC : H ≤ omegaCentralizer T) (hz : (A ⊔ H).pCoreIn 2 = ⊥) :
    let X := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) A
    let hq := h.natural_cartan_qrc_hypotheses hH c hm hz
    letI := hq.module_elementary
    Representation.BinaryOffender.cubicRatio (ChapterD.UniqueFactor.imageRepresentation
      (A ⊔ (T : Subgroup G)) X hq.module_normalized) ≤ 2 := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let X := conjugateSpanBy Z A
  let hq := h.natural_cartan_qrc_hypotheses hH c hm hz
  let hd := natural_cartan_qrc_configuration h hH c hm hz
  have hne : X ≠ ⊥ := by
    intro he
    have hh := (h.natural_cartan_span c hm).2.1
    change Nat.card X = 2^n at hh
    rw [he,Subgroup.card_bot] at hh
    have hp : 1 < (2:ℕ)^n := Nat.one_lt_pow (by have := h.exponent; omega) (by decide)
    omega
  have hBV : H ⊓ normalizer (L : Set G) ≤ normalizer (X : Set G) := by
    rw [inf_comm,←c.sylow_sup_right h.sylow_normalizes hH.1.1.2]
    apply sup_le (le_sup_right.trans hq.module_normalized)
    exact normalizes_conjugateSpanBy Z A B
      ((c.right_le.trans inf_le_right).trans
        (hHC.trans (Subgroup.centralizer_le_normalizer _))) c.right_normalizes_left
  exact normalized_cubicRatio_le_two hq h.qtke h.maximal hd hne hBV

/-- The natural central-omega alternative has original degree at most four. -/
theorem Input.natural_cartan_degree_le_four
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B)
    (hm : IsNaturalModule L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hHC : H ≤ omegaCentralizer T) (hz : (A ⊔ H).pCoreIn 2 = ⊥) : n ≤ 4 := by
  let X := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) A
  let J := A ⊔ (T : Subgroup G)
  let U := (T : Subgroup G) ⊓ L
  let hq := h.natural_cartan_qrc_hypotheses hH c hm hz
  let := hq.module_elementary
  have hg := h.natural_cartan_span c hm
  have hJ : J ≤ normalizer (X : Set G) := hq.module_normalized
  let f := ChapterD.UniqueFactor.actionHom A X (le_sup_left.trans hJ)
  let C := ChapterD.internalActionImage A X (le_sup_left.trans hJ)
  obtain ⟨F,_,_,_,_,⟨e⟩⟩ := c.left_equiv_units h.linear h.sylow_normalizes
  let : IsCyclic A := isCyclic_of_injective e.toMonoidHom e.injective
  let : IsCyclic C := isCyclic_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [ChapterD.UniqueFactor.actionHom_ker]
    apply _root_.eq_bot_iff.mpr
    intro a ha
    apply mem_bot.mpr
    apply Subtype.ext
    exact mem_bot.mp (hg.2.2.2 ▸ (show (a:G) ∈ A ⊓ centralizer (X : Set G) from
      ⟨a.property,ha⟩))
  have hregA := Theory.GroupAction.faithful_cyclic_binary_singer_regular f hfi
    h.exponent (c.left_card h.linear h.sylow_normalizes) hg.2.1
  have hreg : ∀ v w : X, v ≠ 1 → w ≠ 1 → ∃! a : C, a.val v = w := by
    intro v w hv hw
    obtain ⟨a,ha,hu⟩ := hregA v w hv hw
    refine ⟨f.rangeRestrict a,ha,?_⟩
    intro b hb
    obtain ⟨a',ha'⟩ := f.rangeRestrict_surjective b
    rw [←ha'] at hb ⊢
    exact congrArg f.rangeRestrict (hu a' hb)
  have hTB : (T : Subgroup G) ≤ normalizer (localBorel T L : Set G) :=
    (le_inf h.sylow_normalizes
      ((le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
        inf_normalizer_le_normalizer_inf |>.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hTN : (T : Subgroup G) ≤ normalizer ((U ⊔ A : Subgroup G) : Set G) :=
    hTB.trans (Prime.cartan_subgroup_preimage_normalized c h.sylow_normalizes h.linear le_rfl)
  have hUC : U ≤ centralizer (X : Set G) := by
    apply le_centralizer_iff.mp
    change conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) A ≤ _
    rw [hg.1]
    exact inf_le_right
  have hN : ChapterD.internalActionImage J X hJ ≤ normalizer (C : Set (MulAut X)) :=
    image_normalizes_torus hJ (inf_le_left.trans le_sup_right) le_sup_left hUC
      (sup_le (le_sup_right.trans (U ⊔ A).le_normalizer) hTN)
  have hc := Theory.GroupTheory.regular_cyclic_normalizer_cubic_card_le
    C (ChapterD.internalActionImage J X hJ)
    hreg hN (ChapterD.UniqueFactor.imageRepresentation J X hJ) (fun _ _ => rfl)
      (h.natural_cartan_cubicRatio_le_two hH c hm hHC hz)
  rw [hg.2.1] at hc
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc

/-- Parity and the literal natural action discharge the small-generation
premise in the natural omega-span branch; centralization is derived above degree two. -/
theorem Input.natural_cartan_degree_and_smallGeneration
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    (hm : IsNaturalModule L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n)
    (hz : (A ⊔ H).pCoreIn 2 = ⊥) :
    (n = 2 ∨ n = 4) ∧ CartanSmallGeneration A H n := by
  by_cases hn : n = 2
  · exact ⟨Or.inl hn,h.cartanSmallGeneration_of_degree_two_or_four hH c (Or.inl hn)⟩
  have hn2 : 2 < n := by have := h.exponent; omega
  have hHC := h.natural_cartan_omega_centralizes hH hgen c hm hn2 hz
  have hb := h.natural_cartan_degree_le_four hH c hm hHC hz
  obtain ⟨k,hk⟩ := h.cartan_even_of_zero_core hH c hz
  have he : n = 2 ∨ n = 4 := by have := h.exponent; omega
  exact ⟨he,h.cartanSmallGeneration_of_degree_two_or_four hH c he⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
