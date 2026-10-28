module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.Cosets
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.AmbientGeneration
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.LinearFactors
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.AlignedMarking
public import Theory.Mathieu.M23.QuasithinGeometry.SourceRecognition.AdjacentPairs
public import Theory.GroupTheory.Recognition.QuasithinM23.ParabolicOvergroups
public import Theory.GroupAction.OrbitFamilyEquivalence
public import Theory.Mathieu.M23.QuasithinGeometry.StandardSystem
public import Theory.GroupTheory.GraphUniquenessSystem.CosetConstruction

/-!
# The source edge fixer in the actual coset action

Use the marked triple to select an edge reversal lying in the original left
local normalizer. The native adjacent-pair intersection has order 192 after
lifting through the heptad kernel. Divisibility excludes both source T and K;
the proved parabolic overgroup alternatives then identify the ambient edge
fixer with the original L. The same construction proves vertex generation.
Source: Aschbacher--Smith 5.2.19--5.2.20, printed pp.656--657.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Sporadic.Mathieu.M23Geometry GraphUniquenessSystem
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem map_inf_subgroupOf (J : Subgroup G) (U : Subgroup J) (V : Subgroup G) :
    (U ⊓ V.subgroupOf J).map J.subtype = U.map J.subtype ⊓ V := by
  ext g
  constructor
  · rintro ⟨u,⟨hu,hv⟩,rfl⟩
    exact ⟨⟨u,hu,rfl⟩,hv⟩
  · rintro ⟨⟨u,hu,rfl⟩,hv⟩
    exact ⟨u,⟨hu,hv⟩,rfl⟩

/-- Original source 5.2.19(3–4), the setwise part of 5.2.20(3), and 5.2.22: the four-set
local and all its actual coset stabilizers use one marking. -/
theorem Preparation.linear_exceptional_coset_edge_geometry
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hKJ : residual H < J)
    : ∃ (ζ : J ≃* heptadStabilizer) (I : Subgroup J) (t : J),
      (pCore 2 J).map ζ.toMonoidHom = heptadKernel ∧
      ((residual H).subgroupOf J).map ζ.toMonoidHom =
        (fixingSubgroup (Equiv.Perm (Fin 7)) ({5,6} : Set (Fin 7))).comap heptadAction ∧
      (H.subgroupOf J).map ζ.toMonoidHom = pairStabilizer.subgroupOf heptadStabilizer ∧
      ((normalizer (L : Set G)).subgroupOf J).map ζ.toMonoidHom =
        (MulAction.stabilizer (Equiv.Perm (Fin 7)) ({4,5,6} : Set (Fin 7))).comap heptadAction ∧
      I.map ζ.toMonoidHom = fourStabilizer.subgroupOf heptadStabilizer ∧ t ∈ I ∧
      let x0 := ((1 : G) : G ⧸ (L ⊔ H : Subgroup G))
      let y0 := t • x0
      t • y0 = x0 ∧ x0 ≠ y0 ∧
      (∀ a b : J, a • x0 = b • x0 ↔ ζ a • x.val = ζ b • x.val) ∧
      ζ t • x.val = y.val ∧
      (I ⊓ MulAction.stabilizer J x0).map ζ.toMonoidHom =
        fourPairStabilizer.subgroupOf heptadStabilizer ∧
      (I ⊓ edgeFixer J x0 y0).map ζ.toMonoidHom =
        fourTwoPairStabilizer.subgroupOf heptadStabilizer ∧
      (I ⊓ edgeStabilizer J x0 y0).map ζ.toMonoidHom =
        fourEdgeStabilizer.subgroupOf heptadStabilizer ∧
      edgeFixer G x0 y0 = L ∧
      L ⊔ (I.map J.subtype ⊓ (L ⊔ H)) = L ⊔ H ∧
      (I.map J.subtype ⊓ edgeStabilizer G x0 y0) ⊔
        (I.map J.subtype ⊓ MulAction.stabilizer G x0) = I.map J.subtype ∧
      I.map J.subtype ⊔ (L ⊔ H) = ⊤ := by
  obtain ⟨ζ,hcore,hKmark,hHmark,hMmark⟩ :=
    d.linear_exceptional_aligned_heptad_marking h hH hp F hm hF he hJ hKJ
  have hinter := d.linear_exceptional_pair_intersection h hH hp F hm hF he hJ hKJ
  have hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G) := by
    intro hK
    exact hKJ.ne (hK.2 J hJ.1 hKJ.le).symm
  obtain ⟨hTJ,hHJ,_,_,_,_,_,_⟩ := d.linear_exceptional_local h hH hp F hm hF he hJ hKJ
  let x0 := ((1 : G) : G ⧸ (L ⊔ H : Subgroup G))
  have hstab : MulAction.stabilizer J x0 = H.subgroupOf J := by
    ext j
    change (j:G) ∈ MulAction.stabilizer G x0 ↔ (j:G) ∈ H
    rw [MulAction.stabilizer_quotient]
    constructor
    · intro hj
      exact hinter ▸ (show (j:G) ∈ (L ⊔ H) ⊓ J from ⟨hj,j.property⟩)
    · exact fun hj => mem_sup_right hj
  have hstabmap : (MulAction.stabilizer J x0).map ζ.toMonoidHom =
      MulAction.stabilizer heptadStabilizer x.val := by rw [hstab,hHmark]; rfl
  let e := MulAction.orbitEquivOfStabilizerMap ζ x0 x.val hstabmap
  have horbit : ∀ j : J, (e ⟨j • x0,MulAction.mem_orbit _ j⟩).val = ζ j • x.val :=
    MulAction.orbitEquivOfStabilizerMap_apply ζ x0 x.val hstabmap
  have heq (a b : J) : a • x0 = b • x0 ↔ ζ a • x.val = ζ b • x.val := by
    constructor
    · intro hh
      have hh' := congrArg (fun v => (e v).val) (show
        (⟨a • x0,MulAction.mem_orbit _ a⟩ : MulAction.orbit J x0) =
        ⟨b • x0,MulAction.mem_orbit _ b⟩ from Subtype.ext hh)
      simpa only [horbit] using hh'
    · intro hh
      have hh' : e ⟨a • x0,MulAction.mem_orbit _ a⟩ =
          e ⟨b • x0,MulAction.mem_orbit _ b⟩ := Subtype.ext (by simpa only [horbit] using hh)
      exact congrArg Subtype.val (e.injective hh')
  obtain ⟨tbar,htx,hty⟩ := fourStabilizer_exists_swap
  let tj : heptadStabilizer := ⟨tbar,fourStabilizer_le tbar.property⟩
  let t := ζ.symm tj
  let y0 := t • x0
  have htM : (t : G) ∈ normalizer (L : Set G) := by
    have hn : ζ t ∈ ((normalizer (L : Set G)).subgroupOf J).map ζ.toMonoidHom := by
      rw [hMmark]
      change heptadAction (ζ t) • ({4,5,6} : Set (Fin 7)) = {4,5,6}
      rw [show ζ t = tj from ζ.apply_symm_apply tj]
      exact heptad_edge_swap_stabilizes_triple tj htx hty
    rw [mem_map_equiv] at hn
    rw [ζ.symm_apply_apply] at hn
    exact hn
  have htx' : ζ t • x.val = y.val := by
    rw [show ζ t = tj from ζ.apply_symm_apply tj]
    exact congrArg Subtype.val htx
  have hty' : ζ t • y.val = x.val := by
    rw [show ζ t = tj from ζ.apply_symm_apply tj]
    exact congrArg Subtype.val hty
  have hswap : t • y0 = x0 := by
    have hh := (heq (t*t) 1).mpr (by rw [map_mul,mul_smul,htx',hty',map_one,one_smul])
    simpa only [y0,mul_smul,one_smul] using hh
  have hne : x0 ≠ y0 := by
    intro hh
    have hh' := (heq 1 t).mp (by simpa only [one_smul] using hh)
    rw [map_one,one_smul,htx'] at hh'
    exact x_adj_y.ne (Subtype.ext hh')
  have hxx (a : J) : a • x0 = x0 ↔ ζ a • x.val = x.val := by
    simpa only [map_one,one_smul] using heq a 1
  have hxy (a : J) : a • x0 = y0 ↔ ζ a • x.val = y.val := by
    simpa only [htx'] using heq a t
  have hyx (a : J) : a • y0 = x0 ↔ ζ a • y.val = x.val := by
    simpa only [map_mul,mul_smul,htx',map_one,one_smul] using heq (a*t) 1
  have hyy (a : J) : a • y0 = y0 ↔ ζ a • y.val = y.val := by
    simpa only [map_mul,mul_smul,htx'] using heq (a*t) t
  let I := (fourStabilizer.subgroupOf heptadStabilizer).comap ζ.toMonoidHom
  have hI : I.map ζ.toMonoidHom = fourStabilizer.subgroupOf heptadStabilizer :=
    Subgroup.map_comap_eq_self_of_surjective ζ.surjective _
  have htI : t ∈ I := by
    change ((ζ t : heptadStabilizer) : Sporadic.Mathieu.M23) ∈ fourStabilizer
    rw [show ζ t = tj from ζ.apply_symm_apply tj]
    exact tbar.property
  have hpoint : (MulAction.stabilizer J x0).map ζ.toMonoidHom =
      pairStabilizer.subgroupOf heptadStabilizer := by
    ext g
    rw [mem_map_equiv]
    change ζ.symm g • x0 = x0 ↔ (g : Sporadic.Mathieu.M23) • x.val = x.val
    have hh := hxx (ζ.symm g)
    rw [ζ.apply_symm_apply] at hh
    exact hh
  have hfix : (edgeFixer J x0 y0).map ζ.toMonoidHom =
      (pairStabilizer ⊓ MulAction.stabilizer Sporadic.Mathieu.M23 y.val).subgroupOf
        heptadStabilizer := by
    ext g
    rw [mem_map_equiv]
    change (ζ.symm g • x0 = x0 ∧ ζ.symm g • y0 = y0) ↔ _
    rw [hxx,hyy,ζ.apply_symm_apply]
    rfl
  have hLfix : L ≤ edgeFixer G x0 y0 := by
    intro g hg
    refine ⟨?_,?_⟩
    · change g ∈ MulAction.stabilizer G x0
      rw [MulAction.stabilizer_quotient]
      exact mem_sup_left hg
    · change g ∈ MulAction.stabilizer G ((t:G) • x0)
      rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj,mem_map_equiv,
        MulAction.stabilizer_quotient]
      apply mem_sup_left
      have hn := (mem_normalizer_iff.mp ((normalizer (L : Set G)).inv_mem htM) g).mp hg
      simpa only [MulAut.conj_symm_apply,inv_inv] using hn
  have hfixcard : Nat.card (edgeFixer J x0 y0) = 192 := by
    rw [←card_map_of_injective (f := ζ.toMonoidHom) ζ.injective,hfix]
    exact heptad_adjacent_pair_fixer_card
  have hgeom := d.linear_nonmaximal_factor_geometry h hH hp F hm hF he hnonmax
  have hTcard := (d.linear_nonmaximal_core_geometry h hH hp F hm hF he hnonmax).2.2.2.2.2.2.2.1
  have hnoT : ¬ (T : Subgroup G) ≤ edgeFixer G x0 y0 := by
    intro hh
    have hd := card_dvd_of_le (subgroupOf_mono J hh)
    change Nat.card ((T : Subgroup G).subgroupOf J) ∣ Nat.card (edgeFixer J x0 y0) at hd
    rw [Nat.card_congr (subgroupOfEquivOfLe hTJ).toEquiv,hTcard,hfixcard] at hd
    norm_num at hd
  have hnoK : ¬ residual H ≤ edgeFixer G x0 y0 := by
    intro hh
    have hd := card_dvd_of_le (subgroupOf_mono J hh)
    change Nat.card ((residual H).subgroupOf J) ∣ Nat.card (edgeFixer J x0 y0) at hd
    rw [Nat.card_congr (subgroupOfEquivOfLe hKJ.le).toEquiv,hgeom.2.2.2.1,hfixcard] at hd
    norm_num at hd
  have hsourcefix : edgeFixer G x0 y0 = L := by
    have hle : edgeFixer G x0 y0 ≤ L ⊔ H := by
      change MulAction.stabilizer G x0 ⊓ _ ≤ _
      rw [MulAction.stabilizer_quotient]
      exact inf_le_left
    rcases d.linear_nonmaximal_overgroup_alternatives h hH hp F hm hF he hnonmax
      (edgeFixer G x0 y0) hLfix hle with heq | heq | hc
    · exact heq
    · exact (hnoT (heq ▸ le_sup_right)).elim
    · exact (hnoK (le_sup_right.trans hc)).elim
  have hedge : (edgeStabilizer J x0 y0).map ζ.toMonoidHom =
      (MulAction.stabilizer Sporadic.Mathieu.M23
        ({x.val,y.val} : Finset (Finset (Fin 23)))).subgroupOf heptadStabilizer := by
    ext g
    rw [mem_map_equiv]
    change ((ζ.symm g • x0 = x0 ∧ ζ.symm g • y0 = y0) ∨
      (ζ.symm g • x0 = y0 ∧ ζ.symm g • y0 = x0)) ↔ _
    rw [hxx,hxy,hyx,hyy,ζ.apply_symm_apply]
    change _ ↔ (g : Sporadic.Mathieu.M23) •
      ({x.val,y.val} : Finset (Finset (Fin 23))) = {x.val,y.val}
    change (( (g : Sporadic.Mathieu.M23) • x.val = x.val ∧
      (g : Sporadic.Mathieu.M23) • y.val = y.val) ∨
      ((g : Sporadic.Mathieu.M23) • x.val = y.val ∧
      (g : Sporadic.Mathieu.M23) • y.val = x.val)) ↔ _
    rw [Finset.smul_finset_insert,Finset.smul_finset_singleton]
    conv_rhs => rw [← Finset.coe_inj, Finset.coe_pair, Finset.coe_pair,
      Set.pair_eq_pair_iff]
  have hxI : (I ⊓ MulAction.stabilizer J x0).map ζ.toMonoidHom =
      fourPairStabilizer.subgroupOf heptadStabilizer := by
    rw [map_inf _ _ _ ζ.injective,hI,hpoint]
    rfl
  have hxyI : (I ⊓ edgeFixer J x0 y0).map ζ.toMonoidHom =
      fourTwoPairStabilizer.subgroupOf heptadStabilizer := by
    rw [map_inf _ _ _ ζ.injective,hI,hfix]
    ext g
    change (g.val ∈ fourStabilizer ∧ g.val ∈ pairStabilizer ∧
      g.val ∈ MulAction.stabilizer Sporadic.Mathieu.M23 y.val) ↔
      ((g.val ∈ fourStabilizer ∧ g.val ∈ pairStabilizer) ∧
      g.val ∈ MulAction.stabilizer Sporadic.Mathieu.M23 y.val)
    exact and_assoc.symm
  have hedgeI : (I ⊓ edgeStabilizer J x0 y0).map ζ.toMonoidHom =
      fourEdgeStabilizer.subgroupOf heptadStabilizer := by
    rw [map_inf _ _ _ ζ.injective,hI,hedge]
    rfl
  have hIxN : ¬ I ⊓ MulAction.stabilizer J x0 ≤ (normalizer (L : Set G)).subgroupOf J := by
    intro hh
    have hh' := map_mono hh (f := ζ.toMonoidHom)
    rw [hxI,hMmark] at hh'
    exact fourPair_not_le_marked_overgroups.2 hh'
  have hIxK : ¬ I ⊓ MulAction.stabilizer J x0 ≤ (residual H).subgroupOf J := by
    intro hh
    have hh' := map_mono hh (f := ζ.toMonoidHom)
    rw [hxI,hKmark] at hh'
    exact fourPair_not_le_marked_overgroups.1 hh'
  let C := L ⊔ residual H
  have hCX : C ≤ L ⊔ H := sup_le le_sup_left ((map_subtype_le _).trans le_sup_right)
  have hCG : ChapterF.Source.generated ![L,residual H] (sourceS L H) = C := by
    have hP := d.linear_nonmaximal_parabolic_eq h hH hp F hm hF he hnonmax
    rw [←ChapterF.Source.parabolics_generate,hP 0,hP 1]
    rfl
  have hCT := (d.linear_nonmaximal_extension_geometry h hH hp F hm hF he hnonmax).1
  change ChapterF.Source.generated ![L,residual H] (sourceS L H) ⊓ (T : Subgroup G) = _ at hCT
  rw [hCG] at hCT
  have hCJ : C ⊓ J = residual H := by
    apply le_antisymm _ (le_inf le_sup_right hKJ.le)
    intro g hg
    have hgH : g ∈ H := hinter ▸ (show g ∈ (L ⊔ H) ⊓ J from ⟨hCX hg.1,hg.2⟩)
    have hgprod : g ∈ (residual H : Set G) * ((T : Subgroup G) : Set G) := by
      rw [←coe_mul_of_right_le_normalizer_left (residual H) (T : Subgroup G)
        (hH.1.1.2.trans (le_normalizer_residual H)),residual_sup_sylow T H hH.1.1.2]
      exact hgH
    obtain ⟨k,hk,t',ht',rfl⟩ := hgprod
    have htC : t' ∈ C := by
      have hh := C.mul_mem (C.inv_mem (mem_sup_right hk)) hg.1
      simpa only [inv_mul_cancel_left] using hh
    have htS : t' ∈ sourceS L H := hCT ▸ (show t' ∈ C ⊓ (T : Subgroup G) from ⟨htC,ht'⟩)
    have htK : t' ∈ residual H := d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he 1 htS
    exact (residual H).mul_mem hk htK
  have hVgen : L ⊔ (I.map J.subtype ⊓ (L ⊔ H)) = L ⊔ H := by
    let R := L ⊔ (I.map J.subtype ⊓ (L ⊔ H))
    have hRX : R ≤ L ⊔ H := sup_le le_sup_left inf_le_right
    have hIxR : I ⊓ MulAction.stabilizer J x0 ≤ R.subgroupOf J := by
      rintro j ⟨hj,hjx⟩
      apply mem_sup_right
      refine ⟨⟨j,hj,rfl⟩,?_⟩
      change (j:G) ∈ MulAction.stabilizer G x0 at hjx
      rwa [MulAction.stabilizer_quotient] at hjx
    have hRN : ¬ R ≤ normalizer (L : Set G) :=
      fun hh => hIxN (hIxR.trans (subgroupOf_mono J hh))
    rcases d.linear_nonmaximal_overgroup_alternatives h hH hp F hm hF he hnonmax
      R le_sup_left hRX with hr | hr | hCR
    · exact (hRN (hr ▸ L.le_normalizer)).elim
    · exact (hRN (hr ▸ sup_le L.le_normalizer h.sylow_normalizes)).elim
    · have hCne : C ≠ R := by
        intro hh
        have hixC : I ⊓ MulAction.stabilizer J x0 ≤ C.subgroupOf J := hh.symm ▸ hIxR
        apply hIxK
        intro j hj
        exact hCJ ▸ (show (j:G) ∈ C ⊓ J from ⟨hixC hj,j.property⟩)
      have hidx : C.relIndex (L ⊔ H) = 2 := by
        have hh := relIndex_mul_relIndex (⊥ : Subgroup G) C (L ⊔ H) bot_le hCX
        simp only [relIndex_bot_left] at hh
        rw [hgeom.2.2.2.2,
          (d.linear_nonmaximal_extension_geometry h hH hp F hm hF he hnonmax).2] at hh
        omega
      have hc := relIndex_mul_relIndex C R (L ⊔ H) hCR hRX
      rw [hidx] at hc
      have hprime : (C.relIndex R * R.relIndex (L ⊔ H)).Prime := hc ▸ Nat.prime_two
      rcases Nat.prime_mul_iff.mp hprime with ⟨_,hR⟩ | ⟨_,hC⟩
      · exact le_antisymm hRX (relIndex_eq_one.mp hR)
      · exact (hCne (le_antisymm hCR (relIndex_eq_one.mp hC))).elim
  have hgen : (I ⊓ edgeStabilizer J x0 y0) ⊔ (I ⊓ MulAction.stabilizer J x0) = I := by
    apply Subgroup.map_injective (f := ζ.toMonoidHom) ζ.injective
    rw [Subgroup.map_sup,hedgeI,hxI,hI,←subgroupOf_sup
      (show fourEdgeStabilizer ≤ heptadStabilizer from inf_le_left.trans fourStabilizer_le)
      (show fourPairStabilizer ≤ heptadStabilizer from inf_le_left.trans fourStabilizer_le),
      sup_comm,fourStabilizer_generated]
  have hHJ := (d.linear_exceptional_local h hH hp F hm hF he hJ hKJ).2.1
  obtain ⟨_,_,_,_,_,_,hmaxH⟩ := d.linear_exceptional_pair_marking h hH hp F hm hF he hJ hKJ
  have hs : MulAction.stabilizer J x0 = H.subgroupOf J :=
    Subgroup.map_injective ζ.injective (hpoint.trans hHmark.symm)
  have htop : I ⊔ H.subgroupOf J = ⊤ := by
    apply (hmaxH.ne_iff_eq_top (show H.subgroupOf J ≤ I ⊔ H.subgroupOf J from le_sup_right)).mp
    intro heq
    have htH : t ∈ H.subgroupOf J := heq ▸ (mem_sup_left htI : t ∈ I ⊔ H.subgroupOf J)
    rw [←hs] at htH
    exact hne (show t • x0 = x0 from htH).symm
  have hJgen : I.map J.subtype ⊔ H = J := by
    have hh := congrArg (Subgroup.map J.subtype) htop
    rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hHJ,← MonoidHom.range_eq_map,range_subtype] at hh
  have hamb : I.map J.subtype ⊔ (L ⊔ H) = ⊤ := by
    rw [sup_left_comm,hJgen]
    exact d.linear_exceptional_ambient_generation h hH hp F hm hF he hJ hKJ
  refine ⟨ζ,I,t,hcore,hKmark,hHmark,hMmark,hI,htI,hswap,hne,heq,htx',hxI,hxyI,hedgeI,hsourcefix,hVgen,?_,hamb⟩
  have hh := congrArg (Subgroup.map J.subtype) hgen
  rw [Subgroup.map_sup] at hh
  have h₁ : edgeStabilizer J x0 y0 = (edgeStabilizer G x0 y0).subgroupOf J := rfl
  have h₂ : MulAction.stabilizer J x0 = (MulAction.stabilizer G x0).subgroupOf J := rfl
  rw [h₁,h₂,map_inf_subgroupOf,map_inf_subgroupOf] at hh
  exact hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
