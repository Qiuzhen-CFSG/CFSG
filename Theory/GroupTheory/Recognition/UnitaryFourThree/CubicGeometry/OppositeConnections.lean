module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.LocalDiameter
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.OppositeAdjacency
/-!
# The opposite-to-opposite adjacency formula in the marked normalizer

The displaced plane [V,z] has order nine. An actor centralizing z and
preserving V exchanges the two cubic axes, so [V,z] lies in both odd
kernels. It therefore fixes every line through the second axis. Its free
orbit on an opposite cubic exhausts the other nine points of such a line.
The complement is transitive on the four common neighbors of an opposite
pair. Hence Y and Y^d are adjacent precisely when d is nonidentity and
some K-conjugate of d lies in [V,z]. All groups and maps are the original
ones. Source: Aschbacher, Sporadic Groups (1994),45.11, pp.248–249.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

theorem otherAxis_conjugator_in_centralizer :
    ∃g∈centralizer z,g∈normalizer (c.V:Set G) ∧ c.W.conjBy g=c.otherAxis := by
  let d := h.toCentralizerHypothesis.factorData
  obtain ⟨R⟩ := h.exists_rootPair
  obtain ⟨m, E, hE, htE, ht, hs, hN, htB, htC⟩ :=
    R.exists_positioned_reflected_marking h c.X (h.cubic_sylow_image_card P) (map_subtype_le _)
  have hA : c.actors.A.map (MulAut.conj m.t).toMonoidHom = c.actors.A := by
    rw [c.actors_eq]
    exact mem_normalizer_iff_map_conj_eq.mp m.t_normalizes
  have hmap : c.W.map (MulAut.conj m.t).toMonoidHom ≤ c.actors.A ⊓
      Subgroup.centralizer (d.leftCore : Set G) := by
    refine le_inf ((map_mono (zpowers_le.mpr c.actors.x.property)).trans_eq hA) ?_
    have hWC : c.W ≤ Subgroup.centralizer (d.rightCore : Set G) :=
      zpowers_le.mpr c.actors.x_centralizes
    rintro a ⟨w, hw, rfl⟩ b hb
    have hb' : b ∈ d.rightCore.map (MulAut.conj m.t).toMonoidHom := htC.symm ▸ hb
    obtain ⟨v, hv, rfl⟩ := hb'
    simpa only [MulEquiv.coe_toMonoidHom, ← map_mul] using
      congrArg (MulAut.conj m.t) (hWC hw v hv)
  rw [c.otherAxis_fixed] at hmap
  have he : c.W.map (MulAut.conj m.t).toMonoidHom = c.otherAxis :=
    eq_of_le_of_card_ge hmap (by
      rw [card_map_of_injective (MulAut.conj m.t).injective, c.otherAxis_card, c.line_card])
  exact ⟨m.t, mem_centralizer_singleton_iff.mpr m.zt_commute.symm.eq,
    CubicNormalizer.normalizer_normalizes_oddKernel c.X m.t_normalizes, he⟩


omit [Finite G] in
theorem displacement_le_odd : ⁅c.V,zpowers z⁆≤c.D :=
  (le_sup_left.trans c.intersection.ge).trans inf_le_right

theorem displacement_card : Nat.card (⁅c.V,zpowers z⁆:Subgroup G)=9 := by
  let V := c.V
  let E := ⁅V,zpowers z⁆
  let : IsElementaryAbelian 3 V := c.kernel_elementary
  have hn : zpowers z≤normalizer (V:Set G) := zpowers_le.mpr c.involution_normalizes_kernel
  have hEV : E≤V := le_normalizer_iff_commutator_le_left.mp hn
  have hXV : c.X≤V := CubicNormalizer.le_oddKernel c.X (h.cubic_sylow_image_card P)
    (h.toCentralizerHypothesis.cubic_centralizer c.X (h.cubic_sylow_image_card P) (map_subtype_le _))
  have hVX : V⊓Subgroup.centralizer (zpowers z:Set G)=c.X := by
    rw [Subgroup.zpowers_eq_closure,Subgroup.centralizer_closure]
    exact h.toCentralizerHypothesis.cubic_oddKernel_fixed c.X (h.cubic_sylow_image_card P) (map_subtype_le _)
  have hcop : Nat.Coprime (Nat.card (zpowers z)) (Nat.card V) := by
    rw [Nat.card_zpowers,h.involution,c.kernel_card]
    decide
  have hgen : V=E⊔c.X := by
    simpa only [hVX] using eq_commutator_sup_centralizer_of_solvable_coprime V (zpowers z) hn
      (Group.isSolvable_of_comm fun x y=>IsMulCommutative.is_comm.comm x y) hcop
  have hdis : Disjoint E c.X := by
    simpa only [hVX] using commutator_disjoint_centralizer_of_coprime V (zpowers z) hn hcop
  have hXE : c.X≤normalizer (E:Set G) :=
    ((hXV.trans V.le_centralizer).trans (centralizer_le hEV)).trans (Subgroup.centralizer_le_normalizer _)
  have hh := card_sup_eq_mul_of_normalizes_of_disjoint E c.X hXE hdis
  rw [←hgen,c.kernel_card,h.cubic_sylow_image_card P] at hh
  change Nat.card E=9
  omega

theorem displacement_fixes_otherAxis_line {L:Subgroup G} (hL:L∈c.linesThrough c.otherAxis) :
    ⁅c.V,zpowers z⁆≤normalizer (L:Set G) := by
  obtain ⟨g,hgz,hgV,hgW⟩ := c.otherAxis_conjugator_in_centralizer
  have hz : g*z*g⁻¹=z := mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hgz)
  have he : (⁅c.V,zpowers z⁆).conjBy g=⁅c.V,zpowers z⁆ := by
    change (⁅c.V,zpowers z⁆).map (MulAut.conj g).toMonoidHom=_
    rw [Subgroup.map_commutator,MonoidHom.map_zpowers]
    change ⁅c.V.conjBy g,zpowers (g*z*g⁻¹)⁆=_
    have hgV' : c.V.conjBy g=c.V := mem_normalizer_iff_map_conj_eq.mp hgV
    rw [hgV',hz]
  have hED : ⁅c.V,zpowers z⁆≤c.D.conjBy g := he ▸ map_mono c.displacement_le_odd
  have hL' : L.conjBy g⁻¹∈c.linesThrough c.W := by
    refine ⟨c.line_conjugate_mem hL.1 g⁻¹,?_⟩
    have hh := map_mono (f:=(MulAut.conj g⁻¹).toMonoidHom) hL.2
    change c.otherAxis.conjBy g⁻¹≤L.conjBy g⁻¹ at hh
    rwa [←hgW,conjBy_inv] at hh
  have hh := map_mono (f:=(MulAut.conj g).toMonoidHom) (c.odd_fixes_incident_line hL')
  rw [map_equiv_normalizer_eq] at hh
  change c.D.conjBy g≤normalizer ((L.conjBy g⁻¹).conjBy g:Set G) at hh
  rw [conjBy_inv'] at hh
  exact hED.trans hh


theorem opposite_same_line_iff_mem_displacement {Y L:Subgroup G}
    (hYL:Y≤c.oppositeFactor) (hY:Nat.card Y=3) (hne:Y≠c.W)
    (hL:L∈c.lines) (hIL:c.otherAxis≤L) (hYL':Y≤L)
    (d:G) (hd:d∈c.D) : Y.conjBy d≤L ↔ d∈⁅c.V,zpowers z⁆ := by
  classical
  let A := ⁅c.V,zpowers z⁆
  have hAD : A≤c.D := c.displacement_le_odd
  have hAL : A≤normalizer (L:Set G) := c.displacement_fixes_otherAxis_line ⟨hL,hIL⟩
  have hnon (a:G) (ha:a∈c.D) : Y.conjBy a≠c.otherAxis := by
    intro he
    have hh := c.opposite_cubic_conjugate_distance_two hYL hY hne a ha
    have hi : c.collinearity.Adj ⟨c.W,c.point_mem⟩
        ⟨Y.conjBy a,c.point_conjugate_mem (c.cubic_in_oppositeFactor_is_point hYL hY) a⟩ := by
      change Y.conjBy a∈c.neighbors c.W
      rw [he]
      exact c.otherAxis_neighbor
    exact (c.collinearity.edist_eq_two_iff.mp hh).2.1 hi
  let f (a:A) : c.otherPoints c.otherAxis L :=
    ⟨Y.conjBy a.val,⟨c.point_conjugate_mem (c.cubic_in_oppositeFactor_is_point hYL hY) a.val,
      (map_mono hYL').trans_eq (mem_normalizer_iff_map_conj_eq.mp (hAL a.property))⟩,
      hnon a.val (hAD a.property)⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun v:c.D=>(v:G)) (c.opposite_odd_conjugation_injective hYL hY hne
      (a₁:=⟨a.val,hAD a.property⟩) (a₂:=⟨b.val,hAD b.property⟩) (congrArg Subtype.val he))
  have hc : Nat.card (c.otherPoints c.otherAxis L)≤Nat.card A := by
    rw [c.otherPoints_card c.otherAxis_is_point hL hIL,c.displacement_card]
  have hs := (hf.bijective_of_nat_card_le hc).2
  constructor
  · intro hdl
    obtain ⟨a,ha⟩ := hs ⟨Y.conjBy d,⟨c.point_conjugate_mem (c.cubic_in_oppositeFactor_is_point hYL hY) d,hdl⟩,
      hnon d hd⟩
    have he : a.val=d := congrArg (fun v:c.D=>(v:G)) (c.opposite_odd_conjugation_injective hYL hY hne
      (a₁:=⟨a.val,hAD a.property⟩) (a₂:=⟨d,hd⟩) (congrArg Subtype.val ha))
    exact he ▸ a.property
  · intro ha
    exact (f ⟨d,ha⟩).property.1.2

theorem opposite_common_neighbor_complement_conjugate {Y U:Subgroup G}
    (hYL:Y≤c.oppositeFactor) (hY:Nat.card Y=3) (hne:Y≠c.W)
    (hK:c.K≤normalizer (Y:Set G))
    (hUW:U∈c.neighbors c.W) (hUY:U∈c.neighbors Y) :
    ∃k∈c.K,U=c.otherAxis.conjBy k := by
  obtain ⟨hU,hneUW,L,hL,hWL,hUL⟩ := hUW
  obtain ⟨k,hk,he⟩ := c.complement_incident_line ⟨hL,hWL⟩
  have hw : c.W.conjBy k=c.W := mem_normalizer_iff_map_conj_eq.mp (c.complement_le hk).2
  have hy : Y.conjBy k=Y := mem_normalizer_iff_map_conj_eq.mp (hK hk)
  have hWIk := c.neighbor_conjugate c.otherAxis_neighbor k
  rw [hw] at hWIk
  have hYI : c.otherAxis∈c.neighbors Y := c.collinearity.adj_symm
    (show c.collinearity.Adj ⟨c.otherAxis,c.otherAxis_is_point⟩
      ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩ from c.opposite_cubic_common_neighbor hYL hY hne)
  have hYIk := c.neighbor_conjugate hYI k
  rw [hy] at hYIk
  have he' := c.common_neighbors_on_line_unique ⟨c.W,c.point_mem⟩
    ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩ ⟨U,hU⟩
    ⟨c.otherAxis.conjBy k,c.point_conjugate_mem c.otherAxis_is_point k⟩
    (c.opposite_cubic_not_collinear hYL hY hne) (fun h=>hne (congrArg Subtype.val h).symm)
    ⟨⟨hU,hneUW,L,hL,hWL,hUL⟩,hUY⟩
    ⟨hWIk,hYIk⟩ ⟨hL,hWL⟩ hUL (he.symm ▸ map_mono c.otherAxis_le_kernel)
  exact ⟨k,hk,congrArg Subtype.val he'⟩


theorem opposite_adj_iff_displacement_conjugate {Y:Subgroup G}
    (hYL:Y≤c.oppositeFactor) (hY:Nat.card Y=3) (hne:Y≠c.W)
    (hK:c.K≤normalizer (Y:Set G)) (d:G) (hd:d∈c.D) :
    Y.conjBy d∈c.neighbors Y ↔ d≠1 ∧ ∃k∈c.K,k⁻¹*d*k∈⁅c.V,zpowers z⁆ := by
  have hkD (k:G) (hk:k∈c.K) : k⁻¹*d*k∈c.D := by
    have hn := CubicLine.normalizer_normalizes_oddKernel c.W (c.complement_le (c.K.inv_mem hk)).2
    have hh := (mem_normalizer_iff.mp hn d).mp hd
    simpa only [inv_inv] using hh
  have he (k:G) (hk:k∈c.K) : Y.conjBy (k⁻¹*d*k)=(Y.conjBy d).conjBy k⁻¹ := by
    have hy : Y.conjBy k=Y := mem_normalizer_iff_map_conj_eq.mp (hK hk)
    rw [conjBy_mul,conjBy_mul,hy]
  constructor
  · intro ha
    have hd1 : d≠1 := by intro hd1; exact ha.2.1 (hd1 ▸ conjBy_one Y)
    obtain ⟨-,hneYD,L,hL,hYL',hYdL⟩ := ha
    let Yp : c.points := ⟨Y,c.cubic_in_oppositeFactor_is_point hYL hY⟩
    obtain ⟨U,hUL⟩ := c.distance_two_common_neighbor_on_each_line
      (c.opposite_cubic_distance_two hYL hY hne) ⟨L,hL,hYL'⟩
    obtain ⟨k,hk,hUk⟩ := c.opposite_common_neighbor_complement_conjugate hYL hY hne hK
      U.property.1 U.property.2
    have hIki : U.val.val.conjBy k⁻¹=c.otherAxis := by rw [hUk,conjBy_inv]
    have hYki : Y.conjBy k⁻¹=Y := mem_normalizer_iff_map_conj_eq.mp (hK (c.K.inv_mem hk))
    have hIL : c.otherAxis≤L.conjBy k⁻¹ := hIki ▸ map_mono hUL
    have hYL'' : Y≤L.conjBy k⁻¹ := hYki ▸ map_mono hYL'
    have hYdL' : Y.conjBy (k⁻¹*d*k)≤L.conjBy k⁻¹ := by rw [he k hk]; exact map_mono hYdL
    exact ⟨hd1,k,hk,(c.opposite_same_line_iff_mem_displacement hYL hY hne
      (c.line_conjugate_mem hL k⁻¹) hIL hYL'' _ (hkD k hk)).mp hYdL'⟩
  · rintro ⟨hd1,k,hk,hdk⟩
    obtain ⟨-,hneYI,L,hL,hIL,hYL'⟩ := c.opposite_cubic_common_neighbor hYL hY hne
    have hYdL := (c.opposite_same_line_iff_mem_displacement hYL hY hne hL hIL hYL'
      _ (hkD k hk)).mpr hdk
    have hne' : Y.conjBy (k⁻¹*d*k)≠Y := by
      intro hh
      have hid : k⁻¹*d*k=1 := congrArg (fun a:c.D=>(a:G))
        (c.opposite_odd_conjugation_injective hYL hY hne
          (a₁:=⟨k⁻¹*d*k,hkD k hk⟩) (a₂:=1) (hh.trans (conjBy_one Y).symm))
      have hd' := congrArg (fun x:G=>k*x*k⁻¹) hid
      simp only [mul_assoc,mul_inv_cancel,mul_one,mul_inv_cancel_left] at hd'
      exact hd1 hd'
    have ha : Y.conjBy (k⁻¹*d*k)∈c.neighbors Y :=
      ⟨c.point_conjugate_mem (c.cubic_in_oppositeFactor_is_point hYL hY) _,hne',L,hL,hYL',hYdL⟩
    have hh := c.neighbor_conjugate ha k
    rw [he k hk,conjBy_inv'] at hh
    have hy : Y.conjBy k=Y := mem_normalizer_iff_map_conj_eq.mp (hK hk)
    rwa [hy] at hh
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration


