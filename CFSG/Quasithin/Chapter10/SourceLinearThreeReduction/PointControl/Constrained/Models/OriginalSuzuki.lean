module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.SuzukiPairCentralizer
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Constrained.Models.OriginalSemisimple
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Excluding the original constrained Suzuki branch

The two actual Suzuki component images have zero common fixed space on the
full module. Every nonzero pair submodule has degree at least twelve. The
original crossed moved subgroups are disjoint, so the full degree is at least
twenty-four. The component-orbit centralizer cannot have an FF-offender:
its offender subgroup is normal in the irreducible full actor, and the full
B.5 classification contradicts these degree bounds and Suzuki multiplicities.

The local action kernel comparison now extends Thompson centralization to
D.fullModule. Consequently J(C_T(v)) = J(T), completing preparation of the
literal VI. The already proved containing-action classification forces three
to divide the original quotient order, contrary to the Suzuki order formula.
No Suzuki natural marking, later generation bound or small-offender theorem
is used. The full module, local module, VI and exact quotient kernels stay
distinct throughout.

Source: Aschbacher--Smith 10.1.1--2, 10.2.9 and B.5.6,
printed pp.741--742,751 and105; refs/quasithin.pdf.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter10.PointControl.Constrained
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open Chapter3.Section02 ChapterB.SourceInduction ChapterB.InternalThompsonAction
open Selection.ModuleChoice BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L} {t v : G} {I : Subgroup G}

private theorem Context.suzuki_full_degree (c : Context D t v I)
    (m : ℕ) (hm : 0 < m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) :
    letI := (source_full_module_reduced D).elementary
    24 ≤ Module.finrank (ZMod 2) (Additive (D.fullModule.subgroupOf D.maximalLocal)) := by
  let W := ⁅D.fullModule,L⁆
  let W' := W.map (MulAut.conj t).toMonoidHom
  let := source_original_full_moved_elementary D
  let : Nontrivial W := (nontrivial_iff_ne_bot W).mpr (source_full_moved_ne_bot D)
  let : Fact (0 < m) := ⟨hm⟩
  obtain ⟨ρ,s,_,_,hz⟩ := c.original_quotient_semisimple e
  have hf : Function.Injective ρ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker inferInstance with h | h
    · exact (MonoidHom.ker_eq_bot_iff ρ).mp h
    · have hall : ρ.invariants = ⊤ := by
        apply top_unique
        intro w _ a
        have hh : ρ a = 1 := h.ge (mem_top a)
        rw [hh,Module.End.one_apply]
      exact (top_ne_bot (α := Submodule (ZMod 2) (Additive W)) (hall.symm.trans hz)).elim
  have hd := Suzuki.finrank_ge (by omega : 1 ≤ m) ρ hf
  change 4 * (2*m+1) ≤ Module.finrank (ZMod 2) (Additive W) at hd
  have hW : 2^12 ≤ Nat.card W := by
    have hc : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
      rw [←Nat.card_congr (Additive.toMul : Additive W ≃ W),
        Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    rw [hc]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hW'V : W' ≤ D.fullModule := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hWV
    exact hh.trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T c.escaping.t_mem)))
  let := D.fullModule_elementary (source_module_nonsolvable_uniqueness D)
  have hn : W' ≤ normalizer (W : Set G) :=
    (hW'V.trans (D.fullModule.le_centralizer.trans (centralizer_le hWV))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hdis : Disjoint W W' := disjoint_iff.mpr
    (bot_unique ((inf_le_inf_left W c.escaping.crossed).trans_eq c.moved_fixed_eq_bot))
  have hc := card_sup_eq_mul_of_normalizes_of_disjoint W W' hn hdis
  have he : Nat.card W' = Nat.card W :=
    (Nat.card_congr ((MulAut.conj t).subgroupMap W).toEquiv).symm
  have hbound : 2^24 ≤ Nat.card D.fullModule := by
    have hle := Nat.card_le_card_of_injective (inclusion (sup_le hWV hW'V))
      (inclusion_injective (sup_le hWV hW'V))
    rw [hc,he] at hle
    calc
      2^24 = (2^12)*(2^12) := by norm_num
      _ ≤ Nat.card W * Nat.card W := Nat.mul_le_mul hW hW
      _ ≤ Nat.card D.fullModule := hle
  let U := D.fullModule.subgroupOf D.maximalLocal
  let := (source_full_module_reduced D).elementary
  have hcard : Nat.card D.fullModule = 2 ^ Module.finrank (ZMod 2) (Additive U) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe
      (D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer)).toEquiv]
    change Nat.card U = _
    rw [←Nat.card_congr (Additive.toMul : Additive U ≃ U),
      Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  rw [hcard] at hbound
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbound

/-- The original pair's centralizer has no FF-offender on the full module.
The two Suzuki components, their common fixed space and the full action are
retained; no individual Suzuki constituent is substituted for the full module. -/
theorem Context.suzuki_full_centralizer_not_ff (c : Context D t v I)
    (m : ℕ) (hm : 0 < m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) :
    let U := D.fullModule.subgroupOf D.maximalLocal
    letI := (source_full_module_reduced D).normal
    letI := (source_full_module_reduced D).elementary
    let q := actionMk U
    let X := ((localOrbit T L).subgroupOf D.maximalLocal).map q
    ¬ IsFFModule ((action U).comp (centralizer (X : Set (ActionQuotient U))).subtype) := by
  dsimp only
  let M := D.maximalLocal
  let R := localOrbit T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let Q := ActionQuotient U
  let q := actionMk U
  let ρ := action U
  let X := (R.subgroupOf M).map q
  let C := centralizer (X : Set Q)
  let N := offenderSubgroup (ρ.comp C.subtype)
  let f := C.subtype.comp N.subtype
  let A := L.subgroupOf M
  let S := A.map q
  let tM : M := ⟨t,le_normalizer_componentOrbit L T c.escaping.t_mem⟩
  let K := S.map (MulAut.conj (q tM)).toMonoidHom
  have hnon : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun h => c.escaping.t_not_normalizes (h c.escaping.t_mem)
  have hLM : L ≤ M := (le_componentOrbit L T).trans R.le_normalizer
  have hpair : R = L ⊔ L.map (MulAut.conj t).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1 hnon)
      inf_le_right c.escaping.t_mem c.escaping.t_not_normalizes
  have hLtM : L.map (MulAut.conj t).toMonoidHom ≤ M :=
    (le_sup_right.trans hpair.ge).trans R.le_normalizer
  have hmap : (A.map (MulAut.conj tM).toMonoidHom).map q = K := by
    dsimp only [K,S]
    rw [map_map,map_map]
    congr 1
  have hsub : (L.map (MulAut.conj t).toMonoidHom).subgroupOf M =
      A.map (MulAut.conj tM).toMonoidHom := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le hLtM,map_map,
      show M.subtype.comp (MulAut.conj tM).toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp M.subtype from rfl,
      ←map_map,map_subgroupOf_eq_of_le hLM]
  have hX : X = S ⊔ K := by
    change (R.subgroupOf M).map q = _
    rw [hpair,subgroupOf_sup hLM hLtM,Subgroup.map_sup,hsub,hmap]
  obtain ⟨a⟩ := full_action_original_component_equiv D hnon
  let eS : S ≃* SuzukiMatrixGroup m := a.trans e
  let eK : K ≃* SuzukiMatrixGroup m := ((MulAut.conj (q tM)).subgroupMap S).symm.trans eS
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect R := isPerfect_iSup_conjugates L T
  let : Group.IsPerfect (R.subgroupOf M) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe R.le_normalizer).symm.toMonoidHom)
    (subgroupOfEquivOfLe R.le_normalizer).symm.surjective
  let : Group.IsPerfect X := Group.IsPerfect.map q
  let : Group.IsPerfect (S ⊔ K : Subgroup Q) := hX ▸ inferInstance
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : X.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let : C.Normal := inferInstance
  have hfix : fixedSpace ρ X = ⊥ := by
    apply bot_unique
    intro z hz
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    apply c.full_fixed_eq_bot.le
    refine ⟨z.toMul.property,?_⟩
    intro r hr
    let rM : M := ⟨r,R.le_normalizer hr⟩
    have hh := hz ⟨q rM,mem_map_of_mem q hr⟩
    have hact := action_apply U rM z
    exact mul_inv_eq_iff_eq_mul.mp
      ((congrArg (fun x : M => (x : G)) hact).symm.trans
        (congrArg (fun x : Additive U => ((x.toMul : M) : G)) hh))
  have hfix' : fixedSpace ρ (S ⊔ K) = ⊥ := hX ▸ hfix
  have hf := action_faithful U
  have hi := quiet_full_action_irreducible D c.many c.minimal c.local_thompson_fixed
  let cover : SQTKQuotient KnownSimple.IsKnownSimple Q := {
    Cover := M
    kernel := centralizer (U : Set M)
    sqtk := D.simpleQTKE.twoLocal_sqtk
      (source_module_nonsolvable_uniqueness D).normalizer_maximal.1
    equiv := MulEquiv.refl Q }
  intro hff
  have hcore := normal_subgroup_twoCore_eq_bot C hu.quotient_pCore_eq_bot
  obtain ⟨B,hB⟩ := (isFFModule_iff_exists_bestOffender (ρ.comp C.subtype)).mp hff
  have hffN : IsFFModule ((ρ.comp C.subtype).comp N.subtype) :=
    ⟨B.subgroupOf N,(hB.isOffender _).subgroupOf _ (hB.le_offenderSubgroup _)⟩
  have hrange : f.range = N.map C.subtype := by
    rw [MonoidHom.range_comp,range_subtype]
  let : f.range.Normal := hrange.symm ▸ normal_restriction_offender_image ρ C
  have hzN := normal_restriction_offender_fixed_eq_bot ρ hf hi C
    (offenderSubgroup_ne_bot_of_ff _ hff)
  exact SuzukiCentralizer.no_ff_of_normal_commuting_suzuki_pair ρ hf hi S K hm eS eK hfix'
    (SuzukiCentralizer.pair_submodule_degree ρ S K hm eS eK hfix') (c.suzuki_full_degree m hm e)
    f (C.subtype_injective.comp N.subtype_injective)
    (by rintro _ ⟨x,rfl⟩; rw [←hX]; exact x.val.property)
    (offenderSubgroup_twoCore _ hcore) ((cover.subgroup C).subgroup N)
    (offenderSubgroup_restrict_eq_top _) hzN hffN

/-- Suzuki centralizes the full Thompson subgroup without any module marking. -/
theorem Context.full_thompson_fixed_of_suzuki (c : Context D t v I)
    (m : ℕ) (hm : 0 < m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G) := by
  have hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    fun h => c.escaping.t_not_normalizes (h c.escaping.t_mem)
  have hno := c.suzuki_full_centralizer_not_ff m hm e
  let M := D.maximalLocal
  let R := localOrbit T L
  let H := localJoin T L
  let U := D.fullModule.subgroupOf M
  let hu := source_full_module_reduced D
  let := hu.normal
  let := hu.elementary
  let Q := M ⧸ centralizer (U : Set M)
  let q := ChapterB.InternalThompsonAction.actionMk U
  let ρ := ChapterB.InternalThompsonAction.action U
  let X := (R.subgroupOf M).map q
  let C := centralizer (X : Set Q)
  let S := D.ambientSylow
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup M)).map M.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective]
    exact congrArg elementaryAbelianMaxJ
      (map_subgroupOf_eq_of_le (le_normalizer_componentOrbit L T))
  have hJC : (elementaryAbelianMaxJ (S : Subgroup M)).map q ≤ C := by
    rintro _ ⟨j,hj,rfl⟩
    have hjG : (j : G) ∈ elementaryAbelianMaxJ (T : Subgroup G) := by
      rw [←hJmap]
      exact mem_map_of_mem M.subtype hj
    have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
      sSup_le fun _ hA => hA.1
    have hjT : (j : G) ∈ (T : Subgroup G) := hJT hjG
    have hjH : (j : G) ∈ H := (show (T : Subgroup G) ≤ H from le_sup_right) hjT
    apply local_kernel_full_image_le_centralizer D hn (⟨j,hjH⟩ : H)
    intro v hv
    exact Subtype.ext (c.local_thompson_fixed hjG v hv)
  have hfix : elementaryAbelianMaxJ (S : Subgroup M) ≤ centralizer (U : Set M) := by
    apply sSup_le
    intro E hE
    by_contra hEC
    have hn' : ¬ E ≤ q.ker := by
      simpa only [q,ChapterB.InternalThompsonAction.actionMk,QuotientGroup.ker_mk'] using hEC
    have hEU : U ≤ (S : Subgroup M) :=
      (IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normal S
    have he : IsOffender ρ (E.map q) :=
      NormalElementaryQuotient.maxElementary_isOffender U q
        (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
        (S : Subgroup M) E hEU hE hn'
    have hEC' : E.map q ≤ C := (map_mono (le_sSup hE)).trans hJC
    exact hno ⟨(E.map q).subgroupOf C,he.subgroupOf ρ hEC'⟩
  rw [←hJmap]
  rintro _ ⟨x,hx,rfl⟩ v hv
  have hVM : D.fullModule ≤ M := D.fullModule_le_orbit.trans R.le_normalizer
  exact congrArg M.subtype (hfix hx ⟨v,hVM hv⟩ hv)


/-- The actual Suzuki quotient is excluded on the original reduced VI.
The full-module Thompson equality supplies the previously missing preparation. -/
theorem Context.no_original_suzuki (c : Context D t v I)
    (m : ℕ) (hm : 0 < m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m) : False := by
  have hp := c.prepared_of_centralizer_of_thompson_eq c.orbit_centralizer_le
    (c.thompson_eq_of_fullModule_centralized (c.full_thompson_fixed_of_suzuki m hm e))
  apply c.no_prepared_of_three_free _ hp
  rw [Nat.card_congr e.toEquiv]
  exact suzukiMatrixGroup_three_free m hm

end CFSG.Quasithin.Chapter10.PointControl.Constrained
