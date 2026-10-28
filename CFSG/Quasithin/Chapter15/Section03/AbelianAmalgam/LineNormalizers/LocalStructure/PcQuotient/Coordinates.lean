module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PcQuotient
public import Theory.GroupTheory.CommutingActionCoordinates
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Compatible coordinates for the original line quotient

The full action of `Y_E T_E` on the singular four-group maps `Y_E` onto
A₃. An escaping two-element `τ` acts oddly, so `⟨Y_E,τ⟩` still induces
all of S₃. Its action kernel is a two-group by 15.3.66(5).

The earlier residual argument makes `Y_E` normal in `G_E`. The source
centralizer and core identities then put both `[Y_E,C_G(E)]` and
`[τ,C_G(E)]` in the original `Q_E`. In the quotient the two images
commute and generate; their intersection is a normal two-subgroup, hence
trivial. Multiplication constructs the coordinates, retaining the actual
image of `C_G(E)` as the second factor and `⟨Y_E,τ⟩` as the first.

`markedDecompositionOfSource` feeds the resulting compatibility equations
into `markedDecompositionOfCoordinates`. Its inputs are the full-action
and kernel data of 15.3.66, the earlier core/centralizer identities, and
an escaping element in the actual `P_c`. Selecting that element remains
the Sylow movement calculation; the centralizer factor is not yet
identified with S₃. This is the initial decomposition, before the
source's temporary replacement of `G_E`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1153 (PDF p.1170), using 15.3.49 and 15.3.66.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Orthogonal
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizerImage_eq_map (E : Subgroup G) :
    centralizerImage E = ((lineC E).subgroupOf (lineNormalizer E)).map (quotientMap E) := by
  ext x
  constructor
  · rintro ⟨c,rfl⟩
    exact ⟨inclusion (centralizer_le_normalizer (E : Set G)) c, c.property, rfl⟩
  · rintro ⟨n,hn,rfl⟩
    exact ⟨⟨n,hn⟩,rfl⟩

omit [Finite G] in
private theorem quotient_images_commute (E A : Subgroup G)
    (hA : A ≤ lineNormalizer E) (hc : ⁅A,lineC E⁆ ≤ lineQ E) :
    (A.subgroupOf (lineNormalizer E)).map (quotientMap E) ≤
      centralizer (centralizerImage E : Set (lineNormalizer E ⧸ pCore 2 (lineNormalizer E))) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [centralizerImage_eq_map, ← map_commutator]
  apply (Subgroup.map_eq_bot_iff _).mpr
  rw [show (quotientMap E).ker = pCore 2 (lineNormalizer E) from QuotientGroup.ker_mk' _]
  have hm : (⁅A.subgroupOf (lineNormalizer E), (lineC E).subgroupOf (lineNormalizer E)⁆).map
      (lineNormalizer E).subtype ≤ lineQ E := by
    rw [map_commutator, map_subgroupOf_eq_of_le hA,
      map_subgroupOf_eq_of_le (centralizer_le_normalizer (E : Set G))]
    exact hc
  change _ ≤ (pCore 2 (lineNormalizer E)).map (lineNormalizer E).subtype at hm
  exact (map_le_map_iff_of_injective (lineNormalizer E).subtype_injective).mp hm

/-- A full four-group action with two-group kernel and the source mixed
commutator bound gives coordinates on the original two-core quotient. -/
theorem exists_line_quotient_coordinates (E A : Subgroup G) [IsKleinFour E]
    (hA : A ≤ lineNormalizer E)
    (hfull : Function.Surjective (lineAction E A hA))
    (hkernel : IsPGroup 2 ((lineC E).subgroupOf A))
    (hcomm : ⁅A,lineC E⁆ ≤ lineQ E) :
    ∃ e : (lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) ≃*
        Equiv.Perm (Fin 3) × centralizerImage E,
      (A.subgroupOf (lineNormalizer E)).map (e.toMonoidHom.comp (quotientMap E)) =
        (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥ ∧
      ∀ c : lineC E, e (restrictedQuotient E _ (centralizer_le_normalizer (E : Set G)) c) =
        (1,centralizerImageMap E c) := by
  let N := lineNormalizer E
  let q := quotientMap E
  let a := A.subgroupOf N
  let C := (lineC E).subgroupOf N
  let ab := a.map q
  let e0 := IsKleinFour.autEquivPermThree E
  let f0 : N →* Equiv.Perm (Fin 3) := e0.toMonoidHom.comp E.normalizerMonoidHom
  have hk0 : f0.ker = C := by
    rw [MonoidHom.ker_comp_of_injective _ _ e0.injective, E.normalizerMonoidHom_ker]
  have hfullN : Function.Surjective E.normalizerMonoidHom := by
    intro s
    obtain ⟨a,ha⟩ := hfull s
    exact ⟨inclusion hA a,ha⟩
  have hQ : pCore 2 N ≤ f0.ker := by
    rw [hk0]
    simpa only [E.normalizerMonoidHom_ker] using
      IsKleinFour.twoCore_le_ker_of_surjective E E.normalizerMonoidHom hfullN
  let f : (N ⧸ pCore 2 N) →* Equiv.Perm (Fin 3) := QuotientGroup.lift _ f0 hQ
  have hk : f.ker = centralizerImage E := by
    rw [QuotientGroup.ker_lift, hk0, centralizerImage_eq_map]
    rfl
  have hf : Function.Surjective (f.comp ab.subtype) := by
    intro s
    obtain ⟨a,ha⟩ := hfull (e0.symm s)
    refine ⟨⟨q (inclusion hA a), ⟨inclusion hA a,a.property,rfl⟩⟩, ?_⟩
    change e0 (lineAction E A hA a) = s
    rw [ha,e0.apply_symm_apply]
  have hp : IsPGroup 2 (ab ⊓ centralizerImage E : Subgroup (N ⧸ pCore 2 N)) := by
    have hQ' : q.ker ≤ C := by
      rw [show q.ker = pCore 2 N from QuotientGroup.ker_mk' _]
      exact hk0 ▸ hQ
    rw [centralizerImage_eq_map, ← map_inf_of_ker_le q a C hQ']
    apply IsPGroup.map
    have hAC : IsPGroup 2 (A ⊓ lineC E : Subgroup G) := by
      have he : ((lineC E).subgroupOf A).map A.subtype = A ⊓ lineC E := by
        rw [subgroupOf_map_subtype, inf_comm]
      rw [← he]
      exact hkernel.map A.subtype
    exact hAC.comap_of_injective N.subtype N.subtype_injective
  have hcore : pCore 2 (N ⧸ pCore 2 N) = ⊥ := by
    have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
    have hker : IsPGroup 2 q.ker := by
      rw [show q.ker = pCore 2 N from QuotientGroup.ker_mk' _]
      exact pCore_isPGroup
    have hm := congrArg (map q) (q.comap_pCore_of_ker_isPGroup hq hker)
    rw [map_comap_eq_self_of_surjective hq] at hm
    exact hm.trans ((Subgroup.map_eq_bot_iff _).mpr (by change _ ≤ (QuotientGroup.mk' (pCore 2 N)).ker; rw [QuotientGroup.ker_mk']))
  obtain ⟨e,_,hcentral,hfirst⟩ := exists_product_coordinates_of_pCore_eq_bot 2
    ab (centralizerImage E) f hk hf (quotient_images_commute E A hA hcomm) hp hcore
  refine ⟨e,?_,fun c => hcentral (centralizerImageMap E c)⟩
  rw [← map_map]
  exact hfirst
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure
variable {G : Type*} [Group G] [Finite G]

private theorem even_cube : ∀ a : Equiv.Perm (Fin 3),
    a ∈ alternatingGroup (Fin 3) → a ^ 3 = 1 := by
  simp only [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

/-- The residual and any escaping Sylow element already induce all of S₃.
This follows from the alternating residual image and the odd action of τ. -/
theorem lineTau_full_action (Y E : Subgroup G) (T : Sylow 2 G) [IsKleinFour E]
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hfull : Function.Surjective
      (lineAction E (lineY Y E ⊔ lineT T E) (lineProduct_le_normalizer Y T E)))
    (hkernel : lineS Y T E = (lineY Y E ⊔ lineT T E) ⊓ lineC E)
    (τ : G) (hτ : τ ∈ lineT T E) (hτS : τ ∉ lineS Y T E) :
    Function.Surjective (lineAction E (lineY Y E ⊔ zpowers τ)
      (sup_le ((lineY_le Y E).trans inf_le_right) ((zpowers_le.mpr hτ).trans inf_le_right))) := by
  let P := lineY Y E ⊔ lineT T E
  let A := lineY Y E ⊔ zpowers τ
  have hAP : A ≤ P := sup_le_sup_left (zpowers_le.mpr hτ) _
  let e := IsKleinFour.autEquivPermThree E
  let f : P →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp
    (lineAction E P (lineProduct_le_normalizer Y T E))
  let fA : A →* Equiv.Perm (Fin 3) := f.comp (inclusion hAP)
  have hf : Function.Surjective f := e.surjective.comp hfull
  have hres : (pResidual 2 P).map P.subtype = lineY Y E := by
    rw [← CFSG.Quasithin.Chapter15.Section03.ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
    exact Stellmacher.SectionsFiveToSeven.twoResidualIn_sup_twoGroup_eq
      (Y ⊓ lineNormalizer E) (lineT T E) (T.isPGroup'.to_le inf_le_left)
      (lineT_le_normalizer_lineY Y T E hTY)
  have hres' : pResidual 2 P = (lineY Y E).subgroupOf P := by
    apply map_injective P.subtype_injective
    rw [hres, map_subgroupOf_eq_of_le (show lineY Y E ≤ P from le_sup_left)]
  have hmap : ((lineY Y E).subgroupOf P).map f = alternatingGroup (Fin 3) := by
    rw [← hres', map_pResidual_of_surjective 2 f hf, Equiv.Perm.twoResidual_eq_alternating]
  have halt : alternatingGroup (Fin 3) ≤ fA.range := by
    intro s hs
    obtain ⟨y,hy,hfy⟩ := hmap.symm ▸ hs
    exact ⟨⟨y,mem_sup_left hy⟩,hfy⟩
  let t : P := ⟨τ,mem_sup_right hτ⟩
  have htne : f t ≠ 1 := by
    intro ht
    apply hτS
    rw [hkernel]
    refine ⟨t.property,?_⟩
    have hk : t ∈ (lineAction E P (lineProduct_le_normalizer Y T E)).ker := by
      change lineAction E P (lineProduct_le_normalizer Y T E) t = 1
      apply e.injective
      exact ht.trans (map_one e).symm
    rw [lineAction_ker] at hk
    exact hk
  have htodd : f t ∉ alternatingGroup (Fin 3) := by
    intro heven
    obtain ⟨n,hn⟩ := T.isPGroup' ⟨τ,hτ.1⟩
    have hp : f t ^ 2 ^ n = 1 := by
      rw [← map_pow]
      have ht : t ^ 2 ^ n = 1 := Subtype.ext (show τ ^ 2 ^ n = 1 from congrArg (fun x : T => (x : G)) hn)
      rw [ht,map_one]
    exact htne (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      ((by decide : Nat.Coprime 2 3).pow_left n)
      (orderOf_dvd_of_pow_eq_one hp) (orderOf_dvd_of_pow_eq_one (even_cube (f t) heven))))
  have htmem : f t ∈ fA.range := ⟨⟨τ,mem_sup_right (mem_zpowers τ)⟩,rfl⟩
  have hsurj : Function.Surjective fA := by
    apply MonoidHom.range_eq_top.mp
    apply top_unique
    intro s _
    by_cases hs : s ∈ alternatingGroup (Fin 3)
    · exact halt hs
    · have hst : s * (f t)⁻¹ ∈ alternatingGroup (Fin 3) :=
        ((alternatingGroup (Fin 3)).mul_mem_iff_of_index_two alternatingGroup.index_eq_two).mpr
          (iff_of_false hs (by simpa using htodd))
      simpa only [inv_mul_cancel_right] using fA.range.mul_mem (halt hst) htmem
  intro u
  obtain ⟨a,ha⟩ := hsurj (e u)
  exact ⟨a,e.injective ha⟩
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification
variable {G : Type*} [Group G] [Finite G]
open scoped Pointwise

/-- Construct both marked coordinate identities from the original source data.
Relative normality and both mixed commutator bounds are derived here. -/
theorem exists_quotient_coordinates_of_source (Mc Y E Z : Subgroup G) (T : Sylow 2 G) [IsKleinFour E]
    (hTMc : (T : Subgroup G) ≤ Mc) (hCMc : lineC E ≤ Mc)
    (hcore : Stellmacher.twoCoreAmbient Mc ≤ T)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hfull : Function.Surjective
      (lineAction E (lineY Y E ⊔ lineT T E) (lineProduct_le_normalizer Y T E)))
    (hkernel : lineS Y T E = (lineY Y E ⊔ lineT T E) ⊓ lineC E)
    (hZE : Z ≤ E) (hYcore : Y.pCoreIn 2 = Y ⊓ centralizer (Z : Set G))
    (τ : G) (hτ : τ ∈ linePc Mc E) (hτS : τ ∉ lineS Y T E) :
    ∃ e : (lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) ≃*
        Equiv.Perm (Fin 3) × centralizerImage E,
      ((lineY Y E ⊔ zpowers τ).subgroupOf (lineNormalizer E)).map
          (e.toMonoidHom.comp (quotientMap E)) =
        (⊤ : Subgroup (Equiv.Perm (Fin 3))).prod ⊥ ∧
      ∀ c : lineC E, e (restrictedQuotient E _ (centralizer_le_normalizer (E : Set G)) c) =
        (1,centralizerImageMap E c) := by
  have hPcT : linePc Mc E ≤ lineT T E := inf_le_inf_right _ hcore
  have hτT := hPcT hτ
  have hnot : ¬ linePc Mc E ≤ lineC E := by
    intro hc
    apply hτS
    rw [hkernel]
    exact ⟨mem_sup_right hτT,hc hτ⟩
  have hYcomm := lineY_commutator_of_noncentral_Pc Mc Y E T hcore hTY hfull hkernel hnot
  have hYn := lineY_normal_of_commutator Mc Y T E hTMc hCMc hcore hTY
    (lineNormalizer_three_factor_product Y T E hTY hfull) hYcomm
  let A := lineY Y E ⊔ zpowers τ
  let P := lineY Y E ⊔ lineT T E
  have hAP : A ≤ P := sup_le_sup_left (zpowers_le.mpr hτT) _
  have hAN : A ≤ lineNormalizer E := hAP.trans (lineProduct_le_normalizer Y T E)
  apply exists_line_quotient_coordinates E A hAN
    (lineTau_full_action Y E T hTY hfull hkernel τ hτT hτS)
  · have he : (lineC E).subgroupOf P = pCore 2 P := by
      apply map_injective P.subtype_injective
      rw [subgroupOf_map_subtype, inf_comm]
      exact hkernel.symm
    have hp : IsPGroup 2 ((lineC E).subgroupOf P) := he.symm ▸ pCore_isPGroup
    exact hp.comap_of_injective (inclusion hAP) (inclusion_injective hAP)
  · have hNQ : lineNormalizer E ≤ normalizer (lineQ E : Set G) :=
      (lineNormalizer E).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (lineNormalizer E) (pCore 2 (lineNormalizer E)))
    have hpre : A ≤ commutatorPreimage (lineNormalizer E) (lineC E) (lineQ E) := by
      apply sup_le
      · exact le_commutatorPreimage ((lineY_le Y E).trans inf_le_right)
          (lineY_commutator_lineC_le_lineQ Y E Z hZE hYcore hYn)
      · exact (zpowers_le.mpr hτ).trans (le_commutatorPreimage
          (show linePc Mc E ≤ lineNormalizer E from inf_le_right)
          (linePc_commutator_lineC_le_lineQ Mc E hCMc))
    exact (commutator_mono hpre le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hNQ)
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification
variable {G : Type*} [Group G] [Finite G]

section Source
variable (Mc Y E Z : Subgroup G) (T : Sylow 2 G) [IsKleinFour E]
    (hTMc : (T : Subgroup G) ≤ Mc) (hCMc : lineC E ≤ Mc)
    (hcore : Stellmacher.twoCoreAmbient Mc ≤ T)
    (hTY : (T : Subgroup G) ≤ normalizer (Y : Set G))
    (hfull : Function.Surjective
      (lineAction E (lineY Y E ⊔ lineT T E) (lineProduct_le_normalizer Y T E)))
    (hkernel : lineS Y T E = (lineY Y E ⊔ lineT T E) ⊓ lineC E)
    (hZE : Z ≤ E) (hYcore : Y.pCoreIn 2 = Y ⊓ centralizer (Z : Set G))
    (τ : G) (hτ : τ ∈ linePc Mc E) (hτS : τ ∉ lineS Y T E)

/-- The actual marked decomposition, with the specified escaping element.
Neither a coordinate equivalence nor either marking equation is assumed. -/
noncomputable def markedDecompositionOfSource : MarkedDecomposition Y T E := by
  let h := exists_quotient_coordinates_of_source Mc Y E Z T
    hTMc hCMc hcore hTY hfull hkernel hZE hYcore τ hτ hτS
  exact markedDecompositionOfCoordinates Y T E τ ((inf_le_inf_right _ hcore) hτ)
    h.choose h.choose_spec.1 h.choose_spec.2

/-- The construction preserves the selected element itself. -/
theorem markedDecompositionOfSource_tau :
    (markedDecompositionOfSource Mc Y E Z T hTMc hCMc hcore hTY hfull hkernel
      hZE hYcore τ hτ hτS).tau = τ := rfl

end Source
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification
