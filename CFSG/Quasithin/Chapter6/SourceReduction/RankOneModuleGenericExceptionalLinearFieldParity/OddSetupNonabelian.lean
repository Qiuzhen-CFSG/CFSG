module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupGeometry
public import CFSG.Quasithin.ChapterG.Section02.RankOneHigherFields.Assembly
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFixedSpacesLines
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.PCoreImage

/-!
# The nonabelian normalizer span in the odd-exponent argument

The literal point normalizer acts on the chosen natural module. A nonabelian
span has nontrivial image in LT/O₂(LT). The original quotient marking, its
conjugation formula and the Sylow fixed field-line construct every G.2.3
hypothesis. Thus the two-conjugate group is LU, its two-core is the product of
the two marked intersections, and its elementary middle layer contains V.

If this two-core lies in the point-normalizer core, G.2.2 puts its commutators
with U in the point. Conjugating that bound and using I = ⟨U,Uˡ⟩ puts [I,O₂(I)]
in V. The product formula then forces O₂(I) = U ∩ Uˡ. Consequently O₂(L) is
elementary abelian and [O₂(L),L] = V. This collapse uses no quotient-module
recognition premise. The core containment and the exclusion of this block
configuration remain source obligations of qt-d-1222-linear-field-parity,
alongside 5.1.16(2) and the global TI construction.

Source: Aschbacher–Smith, 5.1.17, printed pp.640–641, using G.2.2–3,
printed pp.332–334 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
open ChapterG.Section02.RankOneHigherFields
open RankOneRecognition.ConjugateFixedSpaces
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

/-- G.2 with the full normalizer of the literal point Ω₁Z(T) ∩ V. -/
@[expose] def normalizerSetup (T : Sylow 2 G) (L V : Subgroup G) : ChapterG.Section02.Setup G :=
  .mk V (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ V) L T
    (normalizer ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ V : Subgroup G) : Set G))

private theorem fundamental_core_centralizes
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ centralizer (D.moduleSubgroup : Set G) := by
  simpa only [Chapter3.Section02.localJoin,componentOrbit_sup] using D.core_centralizes_module

/-- The original L/O₂(L) marking descends to the actual L-image in LT/O₂(LT). -/
theorem fundamental_star_kernel
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hnat : IsNaturalModule L D.moduleSubgroup n) :
    (starProjection (normalizerSetup T L D.moduleSubgroup)).ker = pCore 2 L := by
  let E := normalizerSetup T L D.moduleSubgroup
  have hm : L.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer hTL)
  have hcentral : L ⊓ centralizer (D.moduleSubgroup : Set G) = L.pCoreIn 2 := by
    obtain ⟨F,_,_,_,_,hm⟩ := hnat
    exact hm.centralizer_eq_core (Representation.specialLinearNatural_injective 2)
  ext l
  have he : l ∈ (starProjection E).ker ↔
      inclusion (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) l ∈
        pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
    change starProjection E l = 1 ↔ _
    rw [← Subtype.val_inj]
    exact QuotientGroup.eq_one_iff _
  rw [he]
  constructor
  · intro hl
    have hc : (l : G) ∈ L ⊓ centralizer (D.moduleSubgroup : Set G) :=
      ⟨l.property,fundamental_core_centralizes D (mem_map_of_mem _ hl)⟩
    rw [hcentral] at hc
    exact (mem_map_iff_mem L.subtype_injective).mp hc
  · intro hl
    have hc := hm (mem_map_of_mem L.subtype hl)
    exact (mem_map_iff_mem (L ⊔ (T : Subgroup G)).subtype_injective).mp hc

/-- A trivial starred span would centralize its seed and hence be abelian. -/
theorem fundamental_nonabelian_star
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hnon : ¬ IsMulCommutative (normalizerSetup T L D.moduleSubgroup).U) :
    (normalizerSetup T L D.moduleSubgroup).star
      (normalizerSetup T L D.moduleSubgroup).U ≠ ⊥ := by
  let E := normalizerSetup T L D.moduleSubgroup
  have hg := fundamental_g2_normalizer h hH c hodd hK hnf D hnat
  change E.Hypothesis at hg
  intro hz
  apply hnon
  apply (conjugateSpanBy_commutative_iff E.V E.H).mpr
  apply le_centralizer_iff.mp
  intro u hu
  let x : E.LT := ⟨u,mem_sup_right (hg.U_normal_in_T.1 hu)⟩
  have hx : QuotientGroup.mk' (pCore 2 E.LT) x ∈ E.star E.U :=
    mem_map_of_mem _ (show x ∈ E.U.subgroupOf E.LT from hu)
  rw [hz,mem_bot] at hx
  exact fundamental_core_centralizes D (mem_map_of_mem E.LT.subtype
    ((QuotientGroup.eq_one_iff x).mp hx))

/-- Construct the natural marking and field-line hypotheses on the actual span. -/
theorem fundamental_nonabelian_marking
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hnon : ¬ IsMulCommutative (normalizerSetup T L D.moduleSubgroup).U)
    {l : G} (hl : l ∈ L) (hlout : l ∉ (normalizerSetup T L D.moduleSubgroup).G₁) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F),
      Nonempty (Hypothesis (normalizerSetup T L D.moduleSubgroup) F n l) := by
  let E := normalizerSetup T L D.moduleSubgroup
  have hg := fundamental_g2_normalizer h hH c hodd hK hnf D hnat
  change E.Hypothesis at hg
  have hnL : L ≤ normalizer (D.moduleSubgroup : Set G) := by
    obtain ⟨F,_,_,_,_,hm⟩ := hnat
    exact hm.normalizes
  have hspanle : E.VL ≤ D.moduleSubgroup := conjugateSpanBy_le hg.point_le hnL
  have hspan : E.VL = E.V := by
    rcases hnat.invariant_subgroup E.VL hspanle
      (le_normalizer_conjugateSpanBy E.V₁ L) with hz | he
    · exact (hg.point_ne_bot (bot_unique ((le_conjugateSpanBy E.V₁ L).trans_eq hz))).elim
    · exact he
  have hne := fundamental_nonabelian_star h hH c hodd hK hnf D hnat hnon
  have hk := fundamental_star_kernel D h.sylow_normalizes hnat
  have hpoint : E.V₁ = D.moduleSubgroup ⊓ centralizer ((T : Subgroup G) ⊓ L : Set G) :=
    fundamental_point_eq_sylow_fixed D h.sylow_normalizes h.linear hodd
  have hcard := fundamental_point_card D h.sylow_normalizes h.linear hodd hnat
  change Nat.card E.V₁ = 2 ^ n at hcard
  obtain ⟨F,_,_,_,hF,e,f,hf⟩ := hnat
  change ∀ (x : L) (v : D.moduleSubgroup), (f.symm (Multiplicative.ofAdd
    ((e (QuotientGroup.mk' (pCore 2 L) x)).val *ᵥ (f v).toAdd)) : G) =
      (x : G) * (v : G) * (x : G)⁻¹ at hf
  let q : L →* E.star L := starProjection E
  change q.ker = pCore 2 L at hk
  let e₀ : (L ⧸ pCore 2 L) ≃* E.star L :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q (starProjection_surjective E))
  let em : E.star L ≃* SL(2,F) := e₀.symm.trans e
  have hem (x : L) : em (starProjection E x) = e (QuotientGroup.mk' (pCore 2 L) x) := by
    apply congrArg e
    change e₀.symm (q x) = QuotientGroup.mk' (pCore 2 L) x
    apply e₀.injective
    rw [e₀.apply_symm_apply]
    rfl
  let P := sylowSpace (T : Subgroup G) e
  have hP : P.toAddSubgroup = coordinateSpace f E.V₁ := by
    rw [hpoint]
    exact AddSubgroup.ext (mem_sylowSpace_iff (T : Subgroup G) e f hf)
  have hc : Nat.card P = Nat.card F := by
    change Nat.card P.toAddSubgroup = Nat.card F
    rw [hP,coordinateSpace_card f hg.point_le,hF,hcard]
  have hd : Module.finrank F P = 1 := by
    apply Nat.pow_right_injective (Finite.one_lt_card (α := F))
    change Nat.card F ^ Module.finrank F P = Nat.card F ^ 1
    rw [← Module.natCard_eq_pow_finrank,hc,pow_one]
  have hequiv (x : L) (v w : D.moduleSubgroup)
      (hw : (w : G) = (x : G) * (v : G) * (x : G)⁻¹) :
      (f w).toAdd = (em (starProjection E x)).val *ᵥ (f v).toAdd := by
    rw [hem]
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    simpa only [ofAdd_toAdd,f.symm_apply_apply] using hw.trans (hf x v).symm
  have hmem (v : D.moduleSubgroup) : (v : G) ∈ E.V₁ ↔ (f v).toAdd ∈ P := by
    change (v : G) ∈ E.V₁ ↔ (f v).toAdd ∈ P.toAddSubgroup
    rw [hP]
    simp
  exact ⟨F,inferInstance,inferInstance,⟨{
    setup := hg
    exponent_gt_one := h.exponent
    field_card := hF
    span_eq := hspan
    model := em
    coordinates := f
    equivariant := fun x v => hequiv x v _ rfl
    point := P
    point_dimension := hd
    point_mem := hmem
    star_U_ne_bot := hne
    g_mem := hl
    g_not_normalizing := hlout }⟩⟩

/-- The actual nonabelian branch supplies the generated group and its three layers. -/
theorem fundamental_nonabelian_geometry
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hnon : ¬ IsMulCommutative (normalizerSetup T L D.moduleSubgroup).U)
    {l : G} (hl : l ∈ L) (hlout : l ∉ (normalizerSetup T L D.moduleSubgroup).G₁) :
    let E := normalizerSetup T L D.moduleSubgroup
    E.I l = L ⊔ E.U ∧
      E.S l = E.W l ⊔ ChapterG.Section02.Setup.conjugate (E.W l) l ∧
      E.V ≤ E.S₂ l ∧ E.S₂ l ≤ E.S l ∧
      IsElementaryAbelian 2 (E.S₂ l) ∧ ⁅E.S₂ l,E.I l⁆ ≤ E.V ∧
      E.V ≤ centralizer (E.S l : Set G) ∧
      L ⊔ (T : Subgroup G) ≤ normalizer (E.S l : Set G) := by
  let E := normalizerSetup T L D.moduleSubgroup
  obtain ⟨F,_,_,⟨d⟩⟩ := fundamental_nonabelian_marking h hH c hodd hK hnf D hnat hnon hl hlout
  have hg := fundamental_g2_normalizer h hH c hodd hK hnf D hnat
  change E.Hypothesis at hg
  have hut := hg.U_normal_in_T.1
  have hphi := hg.frattini_U_le_point
  obtain ⟨hv,hs,_,_,_,hc,hcomm,he⟩ := d.series hut hphi
  exact ⟨d.I_eq_LU hut hphi,d.S_eq_WProduct_of_source hut hphi,hv,hs,he,hcomm,hc,
    (d.LT_normalizes_I_of_star hut (d.star_I_eq_star_L hut hphi).ge).trans
      (normalizer_le_normalizer_characteristic_image (E.I l) (pCore 2 (E.I l)))⟩

/-- If the generated two-core lies in the point-normalizer core, the middle
layer collapses and the original L-core is elementary with natural commutator. -/
theorem fundamental_nonabelian_core_collapse
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hodd : Odd n)
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (D : Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T L)
    (hnat : IsNaturalModule L D.moduleSubgroup n)
    (hnon : ¬ IsMulCommutative (normalizerSetup T L D.moduleSubgroup).U)
    {l : G} (hl : l ∈ L) (hlout : l ∉ (normalizerSetup T L D.moduleSubgroup).G₁)
    (hcore : (normalizerSetup T L D.moduleSubgroup).S l ≤
      (normalizerSetup T L D.moduleSubgroup).QH) :
    let E := normalizerSetup T L D.moduleSubgroup
    E.S l = E.S₂ l ∧ IsElementaryAbelian 2 (L.pCoreIn 2) ∧
      ⁅L.pCoreIn 2,L⁆ = D.moduleSubgroup := by
  let E := normalizerSetup T L D.moduleSubgroup
  obtain ⟨F,_,_,⟨d⟩⟩ := fundamental_nonabelian_marking h hH c hodd hK hnf D hnat hnon hl hlout
  have hg := fundamental_g2_normalizer h hH c hodd hK hnf D hnat
  change E.Hypothesis at hg
  have hut := hg.U_normal_in_T.1
  have hphi := hg.frattini_U_le_point
  have hstar := d.star_I_eq_star_L hut hphi
  obtain ⟨hv,hs,_,_,_,hc,hcomm,he⟩ := d.series hut hphi
  have hUS : ⁅E.U,E.S l⁆ ≤ E.V :=
    ((commutator_mono le_rfl hcore).trans hg.commutator_U_core_le_point).trans hg.point_le
  have hIg : l ∈ E.I l := d.g_mem_I hut hphi
  have hSmap : (E.S l).map (MulAut.conj l⁻¹).toMonoidHom = E.S l :=
    mem_normalizer_iff_map_conj_eq.mp (Hypothesis.I_normalizes_core (D := E) (g := l) ((E.I l).inv_mem hIg))
  have hVmap : E.V.map (MulAut.conj l⁻¹).toMonoidHom = E.V :=
    mem_normalizer_iff_map_conj_eq.mp (d.I_normalizes hut ((E.I l).inv_mem hIg))
  have hUgS : ⁅ChapterG.Section02.Setup.conjugate E.U l,E.S l⁆ ≤ E.V := by
    have hh := map_mono (f := (MulAut.conj l⁻¹).toMonoidHom) hUS
    rwa [map_commutator,hSmap,hVmap] at hh
  have hIV : E.I l ≤ normalizer (E.V : Set G) := d.I_normalizes hut
  have hIS : ⁅E.I l,E.S l⁆ ≤ E.V := by
    have hh : E.I l ≤ commutatorPreimage (E.I l) (E.S l) E.V :=
      sup_le (le_commutatorPreimage le_sup_left hUS) (le_commutatorPreimage le_sup_right hUgS)
    exact (commutator_mono hh le_rfl).trans
      (commutator_commutatorPreimage_le _ _ _ hIV)
  have hSU : E.S l ≤ E.U := by
    rw [d.S_eq_WProduct_of_source hut hphi]
    apply sup_le inf_le_left
    rintro x ⟨w,hw,rfl⟩
    change l⁻¹ * w * l⁻¹⁻¹ ∈ E.U
    have hh := commutator_le.mp hIS l⁻¹ ((E.I l).inv_mem hIg) w hw.2
    have hhU : ⁅l⁻¹,w⁆ ∈ E.U := (le_conjugateSpanBy E.V E.H) hh
    simpa only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one] using E.U.mul_mem hhU hw.1
  have hcollapse : E.S l = E.S₂ l := by
    apply le_antisymm _ hs
    apply le_inf hSU
    have hh := map_mono (f := (MulAut.conj l⁻¹).toMonoidHom) hSU
    rwa [hSmap] at hh
  have hLI := d.L_le_I hut hphi
  have hLS : L.pCoreIn 2 ≤ E.S l :=
    pCoreIn_mono_of_normalizes hLI (by
      rw [d.I_eq_LU hut hphi]
      exact sup_le L.le_normalizer (hut.trans h.sylow_normalizes))
  have heS : IsElementaryAbelian 2 (E.S l) := hcollapse.symm ▸ he
  let := heS
  have hVl : E.V ≤ L.pCoreIn 2 := by
    have hh := D.module_le_orbitCore
    have horbit : Chapter3.Section02.localOrbit T L = L :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl h.sylow_normalizes)
        (le_componentOrbit _ _)
    rwa [horbit] at hh
  refine ⟨hcollapse,IsElementaryAbelian.of_injective (inclusion hLS) (inclusion_injective hLS),?_⟩
  apply le_antisymm
  · exact (commutator_mono (hLS.trans_eq hcollapse) hLI).trans hcomm
  · rw [fundamental_cartan_commutator D h.sylow_normalizes h.linear h.exponent c hnat]
    exact commutator_mono hVl (c.left_le.trans inf_le_left)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
