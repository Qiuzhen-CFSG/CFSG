module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.BinaryThree.FixedLayer
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# Saturated points of the binary-three module with zero fixed kernel

When C_[V,L](L) is trivial, the literal natural coordinates identify the moved
factor with the binary three-space. Transitivity of SL₃(2) carries a nonidentity
half-Sylow-fixed vector to the original opposite point. Local Sylow saturation
then bounds the half-Sylow's order by that of C_T(v). The original two-component
action supplies the reverse containment, proving C_T(v)=N_T(L).

The final application supplies PointSylowControl from the separate normalizer
bound of source 10.2.5, owned by qt-d-10-nona5-half-sylow-unique. It neither assumes
that bound as part of the module marking nor changes the selected point.
Source: Aschbacher--Smith, 10.2.9, zero-kernel subcase of 10.1.1(3), printed p.750.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original component is transitive on the nonidentity moved vectors. -/
theorem moved_transitive_of_zero_kernel (hmodel : BinaryThreeNatural D)
    (hzero : sourceMovedFixed D = ⊥)
    {u v : G} (hu : u ∈ ⁅D.fullModule,L⁆) (hv : v ∈ ⁅D.fullModule,L⁆)
    (hune : u ≠ 1) (hvne : v ≠ 1) :
    ∃ l ∈ L, (MulAut.conj l) u = v := by
  obtain ⟨e,⟨c⟩⟩ := hmodel
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hinj : Function.Injective c.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [c.kernel_eq]
    change (sourceMovedFixed D).subgroupOf ⁅D.fullModule,L⁆ = ⊥
    rw [hzero,bot_subgroupOf]
  let W : Subgroup G := ⁅D.fullModule,L⁆
  let a : W := ⟨u,hu⟩
  let b : W := ⟨v,hv⟩
  have ha : (c.coordinates a).toAdd ≠ 0 := by
    intro h
    have hh := (c.coordinates_eq_one_iff a).mp h
    exact hune (mem_bot.mp (hzero ▸ hh))
  have hb : (c.coordinates b).toAdd ≠ 0 := by
    intro h
    have hh := (c.coordinates_eq_one_iff b).mp h
    exact hvne (mem_bot.mp (hzero ▸ hh))
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three _ _ ha hb
  obtain ⟨l,hl⟩ := hπ g
  refine ⟨l,l.property,?_⟩
  have hh := c.equivariant l a
  change _ = specialLinearNatural 3 (π l) (c.coordinates a).toAdd at hh
  rw [hl,specialLinearNatural_apply,hg] at hh
  exact congrArg Subtype.val (hinj (Multiplicative.toAdd.injective hh))

/-- Conjugation transports natural transitivity to the specified opposite factor. -/
theorem partner_transitive_of_zero_kernel (hmodel : BinaryThreeNatural D)
    (hzero : sourceMovedFixed D = ⊥) (t : G)
    {u v : G} (hu : u ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hune : u ≠ 1) (hvne : v ≠ 1) :
    ∃ l ∈ L.map (MulAut.conj t).toMonoidHom, (MulAut.conj l) u = v := by
  obtain ⟨a,ha,rfl⟩ := hu
  obtain ⟨b,hb,rfl⟩ := hv
  have hane : a ≠ 1 := fun h => hune (by simp [h])
  have hbne : b ≠ 1 := fun h => hvne (by simp [h])
  obtain ⟨l,hl,hab⟩ := moved_transitive_of_zero_kernel D hmodel hzero ha hb hane hbne
  refine ⟨(MulAut.conj t) l, mem_map_of_mem (MulAut.conj t).toMonoidHom hl, ?_⟩
  change (t*l*t⁻¹)*(t*a*t⁻¹)*(t*l*t⁻¹)⁻¹ = t*b*t⁻¹
  have hh := congrArg (MulAut.conj t) hab
  simpa only [MulAut.conj_apply,map_mul,map_inv,MulEquiv.coe_toMonoidHom] using hh


/-- A conjugate of the half-Sylow fixes every nonzero opposite natural point. -/
theorem half_sylow_conjugate_fixes_point_of_zero_kernel
    (hmodel : BinaryThreeNatural D) (hzero : sourceMovedFixed D = ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hvne : v ≠ 1) :
    ∃ m ∈ D.maximalLocal,
      (((T : Subgroup G) ⊓ normalizer (L : Set G)).map (MulAut.conj m).toMonoidHom) ≤
        centralizer ({v} : Set G) := by
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let W := ⁅D.fullModule,L⁆
  let B := L.map (MulAut.conj t).toMonoidHom
  let U := W.map (MulAut.conj t).toMonoidHom
  have hSM : S ≤ D.maximalLocal := inf_le_left.trans (le_normalizer_componentOrbit L T)
  have hSB : S ≤ normalizer (B : Set G) :=
    (le_inf inf_le_right hSM).trans (source_nonnormal_component_normalizer_fixes_opposite
      D (fun hn => htn (hn ht)) ht htn)
  have hmap : U = ⁅D.fullModule,B⁆ := by
    dsimp [U,W,B]
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht))]
  have hSU : S ≤ normalizer (U : Set G) := by
    rw [hmap]
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule (hSM hs)),
      mem_normalizer_iff_map_conj_eq.mp (hSB hs)]
  have hS : IsPGroup 2 S := T.isPGroup'.to_le inf_le_left
  let : IsElementaryAbelian 2 W := source_original_full_moved_elementary D
  have hU : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 W).map _
  let : Nontrivial U := (nontrivial_iff_ne_bot U).mpr (by
    intro h
    exact hvne (mem_bot.mp (h ▸ hv)))
  let ρ : S →* MulAut U := U.normalizerMonoidHom.comp (inclusion hSU)
  let : MulDistribMulAction S U := MulDistribMulAction.compHom U ρ
  have hdiv : 2 ∣ Nat.card U := by
    obtain ⟨n,hn,he⟩ := hU.nontrivial_iff_card.mp inferInstance
    rw [he]
    exact dvd_pow_self _ (by omega)
  obtain ⟨u,hu,hune⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point U hdiv
    (show (1 : U) ∈ MulAction.fixedPoints S U from fun s => smul_one s)
  have huS : S ≤ centralizer ({(u:G)} : Set G) := by
    intro s hs
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg Subtype.val (hu ⟨s,hs⟩)
    change s*(u:G)*s⁻¹=(u:G) at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hune' : (u:G) ≠ 1 := fun h => hune (Subtype.ext h.symm)
  obtain ⟨b,hb,hbu⟩ := partner_transitive_of_zero_kernel D hmodel hzero t u.property hv hune' hvne
  have hBM : B ≤ D.maximalLocal := by
    exact (map_mono ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp
        (D.maximalLocal.le_normalizer (le_normalizer_componentOrbit L T ht)))
  refine ⟨b,hBM hb,?_⟩
  rintro _ ⟨s,hs,rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  have hh := congrArg (MulAut.conj b) (mem_centralizer_singleton_iff.mp (huS hs))
  simpa only [map_mul,hbu,MulEquiv.coe_toMonoidHom] using hh

/-- Local saturation preserves the original point and forces its Sylow centralizer
onto the whole half-Sylow when the binary natural kernel vanishes. -/
theorem point_sylow_eq_half_sylow_of_zero_kernel
    (hmodel : BinaryThreeNatural D) (hzero : sourceMovedFixed D = ⊥)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hvne : v ≠ 1)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G))) :
    (T : Subgroup G) ⊓ centralizer ({v} : Set G) =
      (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  let S := (T : Subgroup G) ⊓ normalizer (L : Set G)
  let R := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  have hfixed : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
    rw [fixed_layer_eq_moved_kernels D ht htn hcross,hzero,Subgroup.map_bot,sup_bot_eq]
  have hv0 : v ∉ centralizer (localOrbit T L : Set G) := by
    intro hc
    exact hvne (mem_bot.mp (hfixed ▸
      (show v ∈ D.fullModule ⊓ centralizer (localOrbit T L : Set G) from
        ⟨partner_le_fullModule D ht hv,hc⟩)))
  have hRS : R ≤ S := le_inf inf_le_left
    ((inf_le_inf (le_normalizer_componentOrbit L T) le_rfl).trans
      (source_nonnormal_element_centralizer_stabilizes D (fun hn => htn (hn ht))
        (hcross hv) hv0))
  obtain ⟨m,hm,hfix⟩ := half_sylow_conjugate_fixes_point_of_zero_kernel D hmodel hzero ht htn hv hvne
  let Q := S.map (MulAut.conj m).toMonoidHom
  have hQM : Q ≤ D.maximalLocal :=
    (map_mono (show S ≤ D.maximalLocal from
      inf_le_left.trans (le_normalizer_componentOrbit L T))).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal.le_normalizer hm))
  obtain ⟨g,_,hg⟩ := ChapterB.exists_conjugate_le_relative_sylow _ _ Q hs
    ((T.isPGroup'.to_le inf_le_left).map (MulAut.conj m).toMonoidHom) (le_inf hQM hfix)
  apply eq_of_le_of_card_ge hRS
  have hc := card_le_of_le hg
  rw [card_map_of_injective (MulAut.conj g).injective] at hc
  change Nat.card (S.map (MulAut.conj m).toMonoidHom) ≤ Nat.card R at hc
  rwa [card_map_of_injective (MulAut.conj m).injective] at hc

/-- The zero-kernel branch of the literal source point alternative. The bound on
N_G(T₁) is the separate source 10.2.5 input. -/
theorem point_case_of_zero_kernel
    (hmodel : BinaryThreeNatural D) (hzero : sourceMovedFixed D = ⊥)
    (hN : normalizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G) ≤ D.maximalLocal)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G))
    {v : G} (hv : v ∈ (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom)
    (hvne : v ≠ 1)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (D.maximalLocal ⊓ centralizer ({v} : Set G))) : BinaryThreePointCase D v :=
  Or.inl ⟨point_sylow_eq_half_sylow_of_zero_kernel D hmodel hzero ht htn hcross hv hvne hs,hN⟩

/-- Actual point-control application for the zero-kernel row, including all
nonidentity opposite points. The only separate input is source 10.2.5. -/
theorem pointSylowControl_of_zero_kernel
    (hmodel : BinaryThreeNatural D) (hzero : sourceMovedFixed D = ⊥)
    (hN : normalizer (((T : Subgroup G) ⊓ normalizer (L : Set G)) : Set G) ≤ D.maximalLocal)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hcross : (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)) :
    PointSylowControl D t := by
  intro v hv hvne _ hs
  have he := point_sylow_eq_half_sylow_of_zero_kernel D hmodel hzero ht htn hcross hv hvne hs
  constructor
  · change normalizer (↑((T : Subgroup G) ⊓ centralizer ({v} : Set G)) : Set G) ≤ _
    rw [he]
    exact hN
  · rw [he]
    exact inf_le_right

end CFSG.Quasithin.Chapter10.PointControl.Selection.BinaryThree
