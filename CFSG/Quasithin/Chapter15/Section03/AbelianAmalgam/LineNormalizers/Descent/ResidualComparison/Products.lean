module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.ResidualComparison.Core
public import Stellmacher.TwoResidualSylowSupplement

/-!
# The two setwise products after residual collapse

The residual comparison proves `C_G(V) = C_T(V)`, so the earlier literal
factorization `M = Y C_M(V) T` becomes `M = Y T`. Since `Y` is normal in
`M`, the quotient `M/Y` is a two-group. Its restriction to `M_E` shows
that `N_Y(E)` and a Sylow two-subgroup of `M_E` generate `M_E`.
Restricting that Sylow subgroup to the normal `N_Y(E)` and applying the
two-residual supplement replaces `N_Y(E)` by the original `Y_E`.
Normalization turns the resulting join into the literal product `Y_E T_E`.

The marked geometric input is a Sylow subgroup in the image of the
original line stabilizer under the compatible orthogonal action, with
image equal to that of `T_E`. The action kernel is proved to be the
actual centralizer intersection, and the residual collapse makes it a
two-group contained in `T_E`. This lifts the marked Sylow calculation.
The already proved Sylow promotion in the original `G_E` also supplies
this marked input; no additional model calculation is needed on that route.

All conclusions are conditional on genuine earlier source inputs:
15.3.2's compatible action, 15.3.7's normality and three-factor product,
15.3.49(4), and the index-three and Sylow descent. The parent 15.3.67
assembly must supply these inputs. Neither terminal product is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1121–1122, 1142, 1152–1154, especially the descent paragraph
on p.1154 (PDF p.1171).
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent
variable {G : Type*} [Group G] [Finite G]

private theorem normal_sup_sylow (N : Subgroup G) [N.Normal]
    (P : Sylow 2 G) (hQ : IsPGroup 2 (G ⧸ N)) : N ⊔ (P : Subgroup G) = ⊤ := by
  let q := QuotientGroup.mk' N
  let U := P.mapSurjective (QuotientGroup.mk'_surjective N)
  have hU : (U : Subgroup (G ⧸ N)) = ⊤ :=
    (U.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  have hm : (P : Subgroup G).map q = ⊤ := hU
  have hc := congrArg (Subgroup.comap q) hm
  rw [comap_map_eq, Subgroup.comap_top, QuotientGroup.ker_mk'] at hc
  exact sup_comm _ _ |>.trans hc

omit [Finite G] in
private theorem quotient_two_of_product (M Y : Subgroup G) (T : Sylow 2 G)
    (hYM : Y ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hn : (Y.subgroupOf M).Normal)
    (hprod : (M : Set G) = (Y : Set G) * (T : Set G)) :
    letI := hn
    IsPGroup 2 (M ⧸ Y.subgroupOf M) := by
  let := hn
  let q := QuotientGroup.mk' (Y.subgroupOf M)
  let TM := (T : Subgroup G).subgroupOf M
  let f := q.comp TM.subtype
  have hf : Function.Surjective f := by
    intro z
    induction z using Quotient.inductionOn with | h m =>
      have hm : (m : G) ∈ (Y : Set G) * (T : Set G) := hprod ▸ m.property
      obtain ⟨y, hy, t, ht, he⟩ := hm
      refine ⟨⟨⟨t, hTM ht⟩, ht⟩, ?_⟩
      have hem : m = (⟨y, hYM hy⟩ : M) * ⟨t, hTM ht⟩ := Subtype.ext he.symm
      change q ⟨t, hTM ht⟩ = q m
      rw [hem, map_mul, show q ⟨y, hYM hy⟩ = 1 from (QuotientGroup.eq_one_iff _).mpr hy, one_mul]
  have hTM2 : IsPGroup 2 TM := T.isPGroup'.comap_subtype
  exact hTM2.of_surjective f hf

private theorem line_product_from_sylow (M Y E : Subgroup G) (T : Sylow 2 G)
    (hYM : Y ≤ M) (hTM : (T : Subgroup G) ≤ M)
    (hn : (Y.subgroupOf M).Normal)
    (hprod : (M : Set G) = (Y : Set G) * (T : Set G))
    (P : Sylow 2 (lineM M E))
    (hP : (P : Subgroup (lineM M E)).map (lineM M E).subtype = lineT (T : Subgroup G) E) :
    (lineM M E : Set G) = (lineY Y E : Set G) * (lineT (T : Subgroup G) E : Set G) := by
  let := hn
  let H := lineM M E
  let q := QuotientGroup.mk' (Y.subgroupOf M)
  let f : H →* M ⧸ Y.subgroupOf M := q.comp (inclusion inf_le_left)
  let N := f.ker
  have hQ := quotient_two_of_product M Y T hYM hTM hn hprod
  have hNQ : IsPGroup 2 (H ⧸ N) :=
    (hQ.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hNmap : N.map H.subtype = Y ⊓ lineNormalizer E := by
    ext x
    constructor
    · rintro ⟨m, hm, rfl⟩
      have hmY : inclusion (show H ≤ M from inf_le_left) m ∈ Y.subgroupOf M :=
        (QuotientGroup.eq_one_iff _).mp (show f m = 1 from hm)
      exact ⟨hmY, m.property.2⟩
    · intro hx
      refine ⟨⟨x, hYM hx.1, hx.2⟩, ?_, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mpr hx.1
  obtain ⟨S, hS⟩ := P.exists_sylow_map_eq_inf_of_normal N
  let g : N →* G := H.subtype.comp N.subtype
  have htop : (⊤ : Subgroup N).map g = Y ⊓ lineNormalizer E := by
    rw [← map_map, ← MonoidHom.range_eq_map, N.range_subtype, hNmap]
  have hres : (Stellmacher.twoResidualAmbient (⊤ : Subgroup N)).map g = lineY Y E :=
    map_twoResidualAmbient_of_subgroup_image ⊤ g _ htop
  have hSle : (S : Subgroup N).map g ≤ lineT (T : Subgroup G) E := by
    rw [← map_map, hS, map_inf _ _ _ H.subtype_injective, hP]
    exact inf_le_left
  have hcover := congrArg (Subgroup.map g) (Stellmacher.twoResidualAmbient_top_sup_sylow S)
  rw [Subgroup.map_sup, hres, htop] at hcover
  have hNle : Y ⊓ lineNormalizer E ≤ lineY Y E ⊔ lineT (T : Subgroup G) E := by
    rw [← hcover]
    exact sup_le_sup_left hSle _
  have hcoverH := congrArg (Subgroup.map H.subtype) (normal_sup_sylow N P hNQ)
  rw [Subgroup.map_sup, hNmap, hP, ← MonoidHom.range_eq_map, H.range_subtype] at hcoverH
  have heq : H = lineY Y E ⊔ lineT (T : Subgroup G) E := by
    apply le_antisymm
    · rw [← hcoverH]
      exact sup_le hNle le_sup_right
    · exact sup_le (le_inf ((lineY_le Y E).trans (inf_le_left.trans hYM))
        ((lineY_le Y E).trans inf_le_right)) (inf_le_inf_right _ hTM)
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    hTM.trans ((normal_subgroupOf_iff_le_normalizer hYM).mp hn)
  exact congrArg (fun K : Subgroup G => (K : Set G)) heq |>.trans
    (lineY_sup_lineT_product Y (T : Subgroup G) E hTY)

/-- The earlier three-factor product loses its centralizer factor after residual collapse. -/
theorem centralizer_and_whole_product (M Y V E : Subgroup G) (hEV : E ≤ V)
    (hNM : normalizer (V : Set G) ≤ M) (d : NaturalOrthogonalAction M V)
    (hi : (lineM M E).relIndex (lineNormalizer E) = 3)
    (hM : IsMaximalTwoLocal M)
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hout : ¬ lineNormalizer E ≤ M)
    (h3 : ¬ 3 ∣ Nat.card ↥(M ⊓ centralizer (V : Set G)))
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hprod : (M : Set G) =
      (Y : Set G) * (M ⊓ centralizer (V : Set G) : Set G) * (T : Set G)) :
    centralizer (V : Set G) = (T : Subgroup G) ⊓ centralizer (V : Set G) ∧
      (M : Set G) = (Y : Set G) * (T : Set G) := by
  have hC := centralizer_eq_sylow_centralizer M V E hEV hNM d hi hM hchar hout h3 T hTM
  refine ⟨hC, Set.Subset.antisymm ?_ ?_⟩
  · intro m hm
    rw [hprod] at hm
    obtain ⟨yc, ⟨y, hy, c, hc, rfl⟩, t, ht, rfl⟩ := hm
    have hcT : c ∈ (T : Subgroup G) := ((le_of_eq hC) hc.2).1
    exact ⟨y, hy, c * t, (T : Subgroup G).mul_mem hcT ht, (mul_assoc y c t).symm⟩
  · rintro m ⟨y, hy, t, ht, rfl⟩
    exact M.mul_mem (hYM hy) (hTM ht)

/-- The action of the original marked line stabilizer, restricted from the compatible action. -/
def lineAction {M V : Subgroup G} (d : NaturalOrthogonalAction M V) (E : Subgroup G) :
    lineM M E →* OrthogonalActor := d.actor.comp (inclusion inf_le_left)

omit [Finite G] in
/-- The kernel of the marked line action is the actual centralizer intersection. -/
theorem lineAction_ker {M V : Subgroup G} (d : NaturalOrthogonalAction M V) (E : Subgroup G) :
    (lineAction d E).ker = (centralizer (V : Set G)).subgroupOf (lineM M E) := by
  ext x
  change (inclusion inf_le_left x ∈ d.actor.ker) ↔ _
  rw [d.ker_actor]
  rfl

omit [Finite G] in
private theorem sylow_of_marked_action (M V E : Subgroup G)
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (hCT : centralizer (V : Set G) ≤ (T : Subgroup G))
    (S : Sylow 2 (lineAction d E).range)
    (hS : (S : Subgroup (lineAction d E).range).map (lineAction d E).range.subtype =
      ((lineT (T : Subgroup G) E).subgroupOf (lineM M E)).map (lineAction d E)) :
    ∃ P : Sylow 2 (lineM M E),
      (P : Subgroup (lineM M E)).map (lineM M E).subtype = lineT (T : Subgroup G) E := by
  let f := lineAction d E
  let TE := (lineT (T : Subgroup G) E).subgroupOf (lineM M E)
  have hker : f.rangeRestrict.ker = (centralizer (V : Set G)).subgroupOf (lineM M E) := by
    rw [MonoidHom.ker_rangeRestrict, lineAction_ker]
  have hker2 : IsPGroup 2 f.rangeRestrict.ker := by
    rw [hker]
    exact (T.isPGroup'.to_le hCT).comap_subtype
  have hkerTE : f.rangeRestrict.ker ≤ TE := by
    rw [hker]
    intro x hx
    exact ⟨hCT hx, x.property.2⟩
  have him : TE.map f.rangeRestrict = (S : Subgroup f.range) := by
    apply Subgroup.map_injective f.range.subtype_injective
    rw [map_map, MonoidHom.subtype_comp_rangeRestrict]
    exact hS.symm
  have hrange : (S : Subgroup f.range) ≤ f.rangeRestrict.range := by
    rw [MonoidHom.range_eq_top.mpr f.rangeRestrict_surjective]
    exact le_top
  let P := S.comapOfKerIsPGroup f.rangeRestrict hker2 hrange
  have hP : (P : Subgroup (lineM M E)) = TE := by
    change (S : Subgroup f.range).comap f.rangeRestrict = TE
    rw [← him, comap_map_eq_self hkerTE]
  refine ⟨P, ?_⟩
  rw [hP]
  exact map_subgroupOf_eq_of_le (show lineT (T : Subgroup G) E ≤ lineM M E from
    inf_le_inf_right _ hTM)

/-- Lift the marked Sylow calculation through the actual action kernel and prove `M_E = Y_E T_E`.
The marked input concerns only the image of the original stabilizer under `d.actor`. -/
theorem line_product_of_marked_action (M Y V E : Subgroup G) (hEV : E ≤ V)
    (hNM : normalizer (V : Set G) ≤ M) (d : NaturalOrthogonalAction M V)
    (hi : (lineM M E).relIndex (lineNormalizer E) = 3)
    (hM : IsMaximalTwoLocal M)
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hout : ¬ lineNormalizer E ≤ M)
    (h3 : ¬ 3 ∣ Nat.card ↥(M ⊓ centralizer (V : Set G)))
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hnY : (Y.subgroupOf M).Normal)
    (hprod : (M : Set G) =
      (Y : Set G) * (M ⊓ centralizer (V : Set G) : Set G) * (T : Set G))
    (S : Sylow 2 (lineAction d E).range)
    (hS : (S : Subgroup (lineAction d E).range).map (lineAction d E).range.subtype =
      ((lineT (T : Subgroup G) E).subgroupOf (lineM M E)).map (lineAction d E)) :
    (lineM M E : Set G) = (lineY Y E : Set G) * (lineT (T : Subgroup G) E : Set G) := by
  obtain ⟨hC, hMT⟩ := centralizer_and_whole_product M Y V E hEV hNM d hi hM hchar
    hout h3 T hTM hYM hprod
  have hCT : centralizer (V : Set G) ≤ (T : Subgroup G) := (le_of_eq hC).trans inf_le_left
  obtain ⟨P, hP⟩ := sylow_of_marked_action M V E d T hTM hCT S hS
  exact line_product_from_sylow M Y E T hYM hTM hnY hMT P hP

/-- The Sylow subgroup already obtained in the original `G_E` supplies the marked action input. -/
theorem marked_sylow_of_original_sylow (M V E : Subgroup G)
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype =
      lineT (T : Subgroup G) E) :
    ∃ S : Sylow 2 (lineAction d E).range,
      (S : Subgroup (lineAction d E).range).map (lineAction d E).range.subtype =
        ((lineT (T : Subgroup G) E).subgroupOf (lineM M E)).map (lineAction d E) := by
  let H := lineM M E
  let N := lineNormalizer E
  let i : H →* N := inclusion inf_le_right
  have hUr : (U : Subgroup N) ≤ i.range := by
    intro u hu
    have huT : (u : G) ∈ lineT (T : Subgroup G) E :=
      hU ▸ mem_map_of_mem N.subtype hu
    exact ⟨⟨u, hTM huT.1, u.property⟩, rfl⟩
  let P := U.comapOfInjective i (inclusion_injective inf_le_right) hUr
  have hPi : (P : Subgroup H).map i = (U : Subgroup N) := map_comap_eq_self hUr
  have hP : (P : Subgroup H).map H.subtype = lineT (T : Subgroup G) E := by
    have hm := congrArg (Subgroup.map N.subtype) hPi
    rw [map_map, hU] at hm
    exact hm
  have hP' : (P : Subgroup H) = (lineT (T : Subgroup G) E).subgroupOf H := by
    rw [← hP, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
  let f := lineAction d E
  let S := P.mapSurjective f.rangeRestrict_surjective
  refine ⟨S, ?_⟩
  change ((P : Subgroup H).map f.rangeRestrict).map f.range.subtype = _
  rw [map_map, MonoidHom.subtype_comp_rangeRestrict, hP']

/-- The source Sylow promotion discharges the marked action input to the terminal line product. -/
theorem line_product_of_original_sylow (M Y V E : Subgroup G) (hEV : E ≤ V)
    (hNM : normalizer (V : Set G) ≤ M) (d : NaturalOrthogonalAction M V)
    (hi : (lineM M E).relIndex (lineNormalizer E) = 3)
    (hM : IsMaximalTwoLocal M)
    (hchar : centralizer (pCore 2 M : Set M) ≤ pCore 2 M)
    (hout : ¬ lineNormalizer E ≤ M)
    (h3 : ¬ 3 ∣ Nat.card ↥(M ⊓ centralizer (V : Set G)))
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M) (hYM : Y ≤ M)
    (hnY : (Y.subgroupOf M).Normal)
    (hprod : (M : Set G) =
      (Y : Set G) * (M ⊓ centralizer (V : Set G) : Set G) * (T : Set G))
    (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype =
      lineT (T : Subgroup G) E) :
    (lineM M E : Set G) = (lineY Y E : Set G) * (lineT (T : Subgroup G) E : Set G) := by
  obtain ⟨S, hS⟩ := marked_sylow_of_original_sylow M V E d T hTM U hU
  exact line_product_of_marked_action M Y V E hEV hNM d hi hM hchar hout h3 T hTM
    hYM hnY hprod S hS

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent
