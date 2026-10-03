module
public import Stellmacher.SectionEight.LemmaEightOne
public import Stellmacher.QuotientModuleOffenderFixedPoints
public import Stellmacher.SectionOne.OneSevenFixedSpaceFixer
public import Stellmacher.SectionOne.OneSevenSubgroupSupportLine
public import Stellmacher.SectionOne.OneSevenFixedSupportLineControl

/-!
# A controlled noncentral four-element factor in the initial center

In the graph-local Section Eight context, use the exact quotient-module
witness from (8.1) and its one-seven factor product decomposition. Select a canonical factor whose four-element support
is moved by the opposite-center image. The unconditional pointwise-fixer
identity turns every subgroup of the Sylow centralizing the original fixed
space into the one-J subgroup. The support-line theorem then bounds its action
on the selected support by the full opposite-center commutator, which maps to
`[Z_a,Z_{a'}]` and hence lies in `Z_{a'}`. The selected support also has a nonzero order-two commutator line contained
in the opposite center. Every initial-stabilizer subgroup centralizing that
center fixes this line. The unrestricted support-line fixer theorem then
bounds its commutator with the same selected support by the opposite center.
Thus both source (8) Sylow-fixed-space control and source (9) initial-group
centralizer control hold for a single genuine one-seven support; arbitrary
order-four subgroups are not substituted. The two local theorems retain the
supplied witness and the same selected subgroup. The original canonical
statements are exact wrappers through `ctx.toLocalContext`.

This is the controlled selection used in Stellmacher (8.4), Journal of Algebra
190 (1997), pp.39--40, refs/files/stellmacher-n-group.pdf. The old
`eight_four_noncentral_four` theorem is unchanged.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
open scoped commutatorElement

public theorem eight_four_centralizer_controlled_noncentral_four_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    ∃ A : Subgroup H, A ≤ ZAt ctx.Γ ctx.criticalPath.a ∧ Nat.card A = 4 ∧
      ⁅A,ZAt ctx.Γ ctx.criticalPath.a'⁆ ≠ ⊥ ∧
      (∀ T : Subgroup H, T ≤ S → ⁅T,w.oneJFixedPoints S⁆ = ⊥ →
        ⁅T,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a') ∧
      (∀ T : Subgroup H, T ≤ GAt ctx.Γ ctx.criticalPath.a →
        ⁅T,ZAt ctx.Γ ctx.criticalPath.a'⁆ = ⊥ →
        ⁅T,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a') := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let h := ctx.sectionSeven
  let P := GAt Γ cp.a
  let V := ZAt Γ cp.a
  let Y := ZAt Γ cp.a'
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom V w.action
  let Sb := (S.subgroupOf P).map w.projection
  let J := SectionOne.oneJ (V := V) Sb
  let K := (Y.subgroupOf P).map w.projection
  have hfirst := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hfirst
  have h74 := lemma_seven_four h Γ cp
  have hYP : Y ≤ P := h74.reverse_containment.1
  have hSP : S ≤ P := cp.S_le_edge_stabilizers.trans inf_le_left
  have hpos := cp.length_pos
  let last := cp.path ⟨cp.length-1,by omega⟩
  have hlastadj : Γ.adjacent cp.a' last := by
    have he := cp.path_adj ⟨cp.length-1,by omega⟩
    have hi : (⟨cp.length-1,by omega⟩ : Fin cp.length).succ =
        ⟨cp.length,Nat.lt_succ_self _⟩ := by apply Fin.ext; dsimp; omega
    rw [hi,cp.path_end] at he
    exact Γ.adjacent_symm he
  have hlast := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr hlastadj
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor h Γ hlast
  have hnotcentral : ¬ Y ≤ Subgroup.centralizer (V : Set H) := by
    intro hc
    apply ctx.commutator_ne
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc
  have hlocal := local_quotient_hypotheses h Γ cp.a hfirst w Y hYP hnotcentral
  obtain ⟨_, U, hU⟩ := (SevenSix.edge_sylow_data h Γ cp).1
  have hUS : (U : Subgroup P) = S.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSP]
    exact hU
  let Ub := U.mapSurjective w.surjective
  have hUb : (Ub : Subgroup w.X) = Sb := by
    change (U : Subgroup P).map w.projection = _
    rw [hUS]
  have hKJ : K ≤ J := le_sSup (eight_five_offender_local ctx w).1
  let E := SectionOne.oneSevenGenerated (G := w.X) (V := V)
  let Factors := SectionOne.oneSevenFactors (G := w.X) (V := V)
  obtain ⟨hEnormal,hprod,_⟩ := SectionOne.oneSeven_global_product hlocal Ub
  change IsInternalDirectProduct E Factors at hprod
  let _ : E.Normal := hEnormal
  have hJid : J = (Ub : Subgroup w.X) ⊓ E := by
    simpa only [hUb] using (SectionOne.oneSeven_global_identification hlocal Ub).1
  let I := {D : Subgroup w.X // D ∈ Factors}
  let n := Fintype.card I
  let eI : Fin n ≃ I := (Fintype.equivFin I).symm
  let Df : Fin n → Subgroup w.X := fun i => (eI i).val
  have hDi (i : Fin n) : Df i ∈ Factors := (eI i).property
  have hinj : Function.Injective Df := by intro i j he; exact eI.injective (Subtype.ext he)
  have hDf (i) : SectionOne.IsOneSevenFactor (V := V) (Df i) :=
    (SectionOne.mem_oneSevenFactors_iff _).mp (hDi i)
  have hgen : E = ⨆ i : Fin n, Df i := by
    rw [hprod.1]
    apply le_antisymm
    · apply iSup_le
      intro D
      obtain ⟨i,rfl⟩ := eI.surjective D
      exact le_iSup Df i
    · apply iSup_le
      intro i
      exact le_iSup (fun D : I => (D : Subgroup w.X)) (eI i)
  have hfamily : IsInternalDirectProductFamily E Df := by
    refine ⟨hgen,?_,?_⟩
    · intro i j hij
      exact hprod.2.2.1 (Df i) (hDi i) (Df j) (hDi j) (fun he => hij (hinj he))
    · intro i j hij
      exact hprod.2.2.2 (Df i) (hDi i) (Df j) (hDi j) (fun he => hij (hinj he))
  have hDN (i) : ((Df i).subgroupOf E).Normal := hprod.2.1 (Df i) (hDi i)
  let Vf := fun i => commutatorAction (Df i) V
  have hVprod := SectionOne.oneSevenFactor_module_product hlocal Df hDf hinj E hgen
  have hVgen : FixedPoints.subgroup E V ⊔ (⨆ i, Vf i) = ⊤ := by
    simpa only [iSup_option] using hVprod.1.symm
  have hKE : K ≤ E := hKJ.trans (hJid ▸ inf_le_right)
  have hmove : ∃ i : Fin n, ∃ k ∈ K, ∃ v ∈ Vf i, k • v ≠ v := by
    by_contra! hall
    have hfixed : (⊤ : Subgroup V) ≤ FixedPoints.subgroup K V := by
      rw [← hVgen]
      apply sup_le
      · intro v hv k
        exact hv ⟨k,hKE k.property⟩
      · apply iSup_le
        intro i v hv k
        exact hall i k k.property v hv
    have hbot : commutatorAction K V = ⊥ := by
      rw [commutatorAction_eq_closure]
      apply le_bot_iff.mp
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨k,v,rfl⟩
      have hv := hfixed (Subgroup.mem_top v) k
      change v⁻¹ * (k • v) = 1
      rw [hv,inv_mul_cancel]
    have hm := w.commutatorAction_image_map_subtype Y hYP
    dsimp only at hm
    rw [show commutatorAction K V = ⊥ from hbot,Subgroup.map_bot] at hm
    exact ctx.commutator_ne hm.symm
  obtain ⟨i,hi⟩ := hmove
  let A : Subgroup H := (Vf i).map V.subtype
  have hA : A ≤ V := Subgroup.map_subtype_le _
  have hAnon : ⁅A,Y⁆ ≠ ⊥ := by
    intro hc
    obtain ⟨k,hk,v,hv,hkv⟩ := hi
    obtain ⟨y,hy,rfl⟩ := hk
    apply hkv
    apply Subtype.ext
    change ((w.action (w.projection y)) v : H) = (v : H)
    rw [w.action_compatible]
    have hcomm : (y : H) * (v : H) = (v : H) * (y : H) :=
      Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
        (Subgroup.mem_map_of_mem V.subtype hv)) y hy
    rw [hcomm,mul_assoc,mul_inv_cancel,mul_one]
  refine ⟨A,hA,?_,hAnon,?_⟩
  · rw [Subgroup.card_map_of_injective V.subtype_injective]
    exact (hDf i).2.2.1
  constructor
  ·
    intro T hTS hTF
    have hTP : T ≤ P := hTS.trans hSP
    have hTbarJ : (T.subgroupOf P).map w.projection ≤ J := by
      have hfixer := SectionOne.oneSeven_fixedSpace_fixer_eq_oneJ_unconditional hlocal Ub
      rw [hUb] at hfixer
      change _ ≤ SectionOne.oneJ (V := V) Sb
      rw [← hfixer]
      rintro t ⟨y,hy,rfl⟩
      rw [mem_fixingSubgroup_iff]
      intro v hv
      apply Subtype.ext
      change ((w.action (w.projection y)) v : H) = (v : H)
      rw [w.action_compatible]
      have hvF : (v : H) ∈ w.oneJFixedPoints S := Subgroup.mem_map_of_mem V.subtype hv
      have hyC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hTF hy
      have heq : (v : H) * (y : H) = (y : H) * (v : H) :=
        Subgroup.mem_centralizer_iff.mp hyC v hvF
      rw [← heq,mul_assoc,mul_inv_cancel,mul_one]
    have hcontrol := SectionOne.oneSevenFactor_subgroup_support_line_control hlocal Ub E Df
      hfamily hinj hDf hDN i K (hKJ.trans hJid.le) hi
    have hRY : ⁅V,Y⁆ ≤ Y := Subgroup.le_normalizer_iff_commutator_le_right.mp
      ((h74.first_containment.1.trans h74.first_containment.2).trans (stabilizer_le_normalizer_z Γ cp.a'))
    apply Subgroup.commutator_le.mpr
    intro t ht a ha
    obtain ⟨v,hv,rfl⟩ := ha
    let tP : P := ⟨t,hTP ht⟩
    have htJ : w.projection tP ∈ (Ub : Subgroup w.X) ⊓ E :=
      hJid ▸ hTbarJ (Subgroup.mem_map_of_mem w.projection ht)
    have hdelta := hcontrol (w.projection tP) htJ v hv
    have hm := Subgroup.mem_map_of_mem V.subtype hdelta
    rw [w.commutatorAction_image_map_subtype Y hYP] at hm
    have heq : ((v⁻¹ * ((w.projection tP) • v) : V) : H) = ⁅t,(v : H)⁆ := by
      change (v : H)⁻¹ * ((w.action (w.projection tP)) v : H) = ⁅t,(v : H)⁆
      rw [w.action_compatible]
      have hcomm : (v : H)⁻¹ * (t * (v : H) * t⁻¹) =
          (t * (v : H) * t⁻¹) * (v : H)⁻¹ := by
        have he := congrArg (fun z : V => (z : H))
          ((IsMulCommutative.is_comm (M := V)).comm v⁻¹ ((w.action (w.projection tP)) v))
        simpa only [Subgroup.coe_mul,Subgroup.coe_inv,w.action_compatible] using he
      rw [hcomm]
      rfl
    exact hRY (heq ▸ hm)
  · intro T hTP hTY
    let R := commutatorSubgroup K V (Vf i)
    let R0 := commutatorAction (↥((Ub : Subgroup w.X) ⊓ Df i)) V
    have hline := SectionOne.oneSevenFactor_sylow_line_control hlocal Ub E Df
      hfamily hinj hDf hDN i
    have hR0card : Nat.card R0 = 2 := hline.1
    have hRR : R ≤ R0 := by
      apply (Subgroup.closure_le _).mpr
      rintro z ⟨k,v,hv,rfl⟩
      exact hline.2.2.1 k (hKJ.trans hJid.le k.property) v hv
    have hRne : R ≠ ⊥ := by
      intro he
      obtain ⟨k,hk,v,hv,hne⟩ := hi
      have hm : v⁻¹*(k•v)∈R := Subgroup.subset_closure ⟨⟨k,hk⟩,v,hv,rfl⟩
      rw [he] at hm
      exact hne (inv_mul_eq_one.mp hm).symm
    have hRcard : Nat.card R = 2 := by
      have hbig := (Subgroup.one_lt_card_iff_ne_bot R).mpr hRne
      have hle := Nat.card_le_card_of_injective (Subgroup.inclusion hRR) (Subgroup.inclusion_injective hRR)
      omega
    have hRU : R ≤ Vf i := hRR.trans hline.2.1
    have hRfull : R ≤ commutatorAction K V := by
      apply Subgroup.closure_mono
      rintro z ⟨k,v,hv,rfl⟩
      exact ⟨k,v,Subgroup.mem_top _,rfl⟩
    have hRY : R.map V.subtype ≤ Y := by
      have hh := Subgroup.map_mono (f := V.subtype) hRfull
      rw [w.commutatorAction_image_map_subtype Y hYP] at hh
      exact hh.trans (Subgroup.le_normalizer_iff_commutator_le_right.mp
        ((h74.first_containment.1.trans h74.first_containment.2).trans (stabilizer_le_normalizer_z Γ cp.a')))
    apply Subgroup.commutator_le.mpr
    intro t ht a ha
    obtain ⟨v,hv,rfl⟩ := ha
    let tP : P := ⟨t,hTP ht⟩
    have htfix : ∀r∈R,(w.projection tP) • r = r := by
      intro r hr
      apply Subtype.ext
      change ((w.action (w.projection tP)) r : H) = (r : H)
      rw [w.action_compatible]
      have htr := Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hTY ht) r
        (hRY (Subgroup.mem_map_of_mem V.subtype hr))
      rw [← htr,mul_assoc,mul_inv_cancel,mul_one]
    have hd := SectionOne.oneSevenFactor_fixed_line_control hlocal (Df i) (hDf i)
      R hRU hRcard (w.projection tP) htfix v hv
    have hm := hRY (Subgroup.mem_map_of_mem V.subtype hd)
    have heq : ((v⁻¹ * ((w.projection tP) • v) : V) : H) = ⁅t,(v : H)⁆ := by
      change (v : H)⁻¹ * ((w.action (w.projection tP)) v : H) = ⁅t,(v : H)⁆
      rw [w.action_compatible]
      have hc := congrArg (fun z : V => (z : H))
        ((IsMulCommutative.is_comm (M := V)).comm v⁻¹ ((w.action (w.projection tP)) v))
      change (v : H)⁻¹ * (t * (v : H) * t⁻¹) = (t * (v : H) * t⁻¹) * (v : H)⁻¹
      simpa only [Subgroup.coe_mul,Subgroup.coe_inv,w.action_compatible] using hc
    exact heq ▸ hm

public theorem eight_four_controlled_noncentral_four_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    ∃ A : Subgroup H, A ≤ ZAt ctx.Γ ctx.criticalPath.a ∧ Nat.card A = 4 ∧
      ⁅A,ZAt ctx.Γ ctx.criticalPath.a'⁆ ≠ ⊥ ∧
      ∀ T : Subgroup H, T ≤ S → ⁅T,w.oneJFixedPoints S⁆ = ⊥ →
        ⁅T,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a' := by
  obtain ⟨A,hA,hcard,hcomm,hfixed,_hcentral⟩ :=
    eight_four_centralizer_controlled_noncentral_four_local ctx w
  exact ⟨A,hA,hcard,hcomm,hfixed⟩

/-- The canonical context keeps the original witness and controlled selection. -/
public theorem eight_four_centralizer_controlled_noncentral_four
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    ∃ A : Subgroup H, A ≤ ZAt ctx.Γ ctx.criticalPath.a ∧ Nat.card A = 4 ∧
      ⁅A,ZAt ctx.Γ ctx.criticalPath.a'⁆ ≠ ⊥ ∧
      (∀ T : Subgroup H, T ≤ S → ⁅T,w.oneJFixedPoints S⁆ = ⊥ →
        ⁅T,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a') ∧
      (∀ T : Subgroup H, T ≤ GAt ctx.Γ ctx.criticalPath.a →
        ⁅T,ZAt ctx.Γ ctx.criticalPath.a'⁆ = ⊥ →
        ⁅T,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a') := by
  exact eight_four_centralizer_controlled_noncentral_four_local ctx.toLocalContext w

/-- The canonical context keeps the original witness and controlled selection. -/
public theorem eight_four_controlled_noncentral_four
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a)) :
    ∃ A : Subgroup H, A ≤ ZAt ctx.Γ ctx.criticalPath.a ∧ Nat.card A = 4 ∧
      ⁅A,ZAt ctx.Γ ctx.criticalPath.a'⁆ ≠ ⊥ ∧
      ∀ T : Subgroup H, T ≤ S → ⁅T,w.oneJFixedPoints S⁆ = ⊥ →
        ⁅T,A⁆ ≤ ZAt ctx.Γ ctx.criticalPath.a' := by
  exact eight_four_controlled_noncentral_four_local ctx.toLocalContext w

end Stellmacher.SectionEight
