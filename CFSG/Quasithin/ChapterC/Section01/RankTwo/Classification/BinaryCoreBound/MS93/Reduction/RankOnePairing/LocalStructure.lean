module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Source
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Parabolics.Residual
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# Local structure for the binary MS93 rank-one pairing

The common Sylow of the Borel preimage is Sylow in M, since the model Borel
has index 21. Its intersection with the preimage of a model radical is the
selected core. Frattini's argument shows that its local normalizer covers
the model parabolic. Normality and Sylow maximality then identify the
selected subgroup with the actual local two-core. These arguments retain
the full extension kernel E; they do not identify E with Q = O₂(E).

Finite surjections preserve the two ordered residuals defining L. Their
images generate SL₃(2), and the nonsupplement clause (A) gives M = LQ.
The kernel normalizes the residual generators, so L is normal. The same
clause, together with Q lying in both local normalizers, proves generation
of M by those normalizers. For a two-group kernel they are the full
parabolic preimages.

Finally, natural coordinates and the full image of L give irreducibility
for actual invariant subgroups of Z. The nontrivial intersection of a
normal subgroup of a finite two-group with its center then gives Z ≤ C_M(Q).
These are local prerequisites for (1.7), not the complete pairing theorem.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (A) on p.828, notation on pp.829,832, and (1.7) on pp.847--848.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing

private theorem map_primeToResidual_surjective {G H : Type*} [Group G] [Finite G]
    [Group H] (f : G →* H) (hf : Function.Surjective f) :
    (primeToResidual 2 G).map f = primeToResidual 2 H := by
  apply le_antisymm (map_primeToResidual_le f hf)
  let : ((primeToResidual 2 G).map f).Normal := Normal.map inferInstance f hf
  exact primeToResidual_le _ ((primeToResidual_index_coprime (G := G) 2).coprime_dvd_right
    ((primeToResidual 2 G).index_map_dvd hf))

private theorem map_localResidual {G H : Type*} [Group G] [Finite G] [Group H]
    (P : Subgroup G) (f : G →* H) :
    (localResidual P).map f = localResidual (P.map f) := by
  calc
    _ = ((primeToResidual 2 P).map (f.subgroupMap P)).map (P.map f).subtype := by
      rw [localResidual, map_map, map_map]
      rfl
    _ = _ := by
      rw [map_primeToResidual_surjective _ (f.subgroupMap_surjective P)]
      rfl

private theorem rankOne_eq_embedded (G : Type*) [Group G] [Finite G] (P : Subgroup G) :
    rankOne P = (pResidual 2 (localResidual P)).map (localResidual P).subtype :=
  map_embedded_pResidual 2 (primeToResidual 2 P) P.subtype

private theorem map_rankOne {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]
    (P : Subgroup G) (f : G →* H) :
    (rankOne P).map f = rankOne (P.map f) := by
  rw [rankOne_eq_embedded, map_embedded_pResidual, map_localResidual]
  exact (rankOne_eq_embedded _ _).symm

private theorem id_kernel_two : IsPGroup 2 (MonoidHom.id SL).ker := by
  intro x
  refine ⟨0, ?_⟩
  apply Subtype.ext
  change (x : SL) ^ (2 ^ 0) = 1
  simpa only [pow_zero, pow_one, MonoidHom.mem_ker, MonoidHom.id_apply] using x.property

private theorem model_pResidual_top : pResidual 2 SL = ⊤ := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank
    (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup SL := Matrix.PSL3Two.equiv.isSimpleGroup
  rcases (inferInstance : (pResidual 2 SL).Normal).eq_bot_or_eq_top with hb | ht
  · obtain ⟨n, hn⟩ := (isPGroup_quotient_pResidual (G := SL) 2).exists_card_eq
    rw [← index_eq_card, hb, index_bot, Matrix.PSL3Two.card_SL] at hn
    have hd : 3 ∣ 2 ^ n := hn ▸ (by decide : 3 ∣ 168)
    have := (show Nat.Prime 3 by decide).dvd_of_dvd_pow hd
    norm_num at this
  · exact ht

variable {M : Type*} [Group M] [Finite M]

/-- The ordered residual generators cover the marked simple quotient. -/
theorem component_map (π : M →* SL) (hπ : Function.Surjective π) (g : SL) :
    (component π g).map π = ⊤ := by
  unfold component
  rw [Subgroup.map_sup, map_rankOne, map_rankOne]
  have hm (i : Bool) : (parabolic π g i).map π = modelParabolic g i := by
    exact map_comap_eq_self (by rw [π.range_eq_top_of_surjective hπ]; exact le_top)
  rw [hm, hm]
  have hh := rankOne_parabolic_generation (MonoidHom.id SL) Function.surjective_id
    id_kernel_two g
  simpa only [parabolic, comap_id, model_pResidual_top] using hh

omit [Finite M] in
private theorem parabolic_normalizes_rankOne (P : Subgroup M) :
    P ≤ normalizer (rankOne P : Set M) := by
  exact P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P
    ((pResidual 2 (primeToResidual 2 P)).map (primeToResidual 2 P).subtype))

omit [Finite M] in
/-- The kernel normalizes both ordered residual generators. -/
theorem kernel_normalizes_component (π : M →* SL) (g : SL) :
    π.ker ≤ normalizer (component π g : Set M) := by
  have h (i : Bool) : π.ker ≤ parabolic π g i := by
    intro x hx
    change π x ∈ modelParabolic g i
    rw [MonoidHom.mem_ker.mp hx]
    exact one_mem _
  exact (le_inf ((h false).trans (parabolic_normalizes_rankOne _))
    ((h true).trans (parabolic_normalizes_rankOne _))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- Clause (A) reduces the extension to the component and its two-core. -/
theorem component_sup_extensionCore (e : Extension (M := M)) :
    component e.projection e.flag ⊔ extensionCore e.projection = ⊤ := by
  have he := congrArg (fun K : Subgroup SL => K.comap e.projection)
    (component_map e.projection e.base.surjective e.flag)
  rw [comap_map_eq, comap_top] at he
  have hker := e.base.no_supplement (component e.projection e.flag) le_sup_left
  apply top_unique
  rw [← he]
  exact sup_le le_sup_left hker

/-- Normality is derived from the genuine nonsupplement clause (A). -/
theorem component_normal (e : Extension (M := M)) :
    (component e.projection e.flag).Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← component_sup_extensionCore e]
  exact sup_le (component e.projection e.flag).le_normalizer
    ((extensionCore_le_kernel _).trans (kernel_normalizes_component _ _))

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing

open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing
variable {M : Type*} [Group M] [Finite M]

omit [Finite M] in
private theorem borel_index (e : Extension (M := M)) : e.borel.index = 21 := by
  rw [e.borel_eq, borelPreimage, index_comap_of_surjective _ e.base.surjective]
  change (modelBorel e.flag).index = 21
  have h := (modelBorel e.flag).index_mul_card
  rw [card_modelBorel, Matrix.PSL3Two.card_SL] at h
  omega

/-- The chosen Sylow of the Borel preimage is also an ambient Sylow.
Its underlying subgroup is definitionally the specified `commonSylow`. -/
@[expose] noncomputable def ambientSylow (e : Extension (M := M)) : Sylow 2 M :=
  (e.sylow.isPGroup'.map e.borel.subtype).toSylow (by
    rw [index_map_subtype, borel_index]
    exact Nat.Prime.not_dvd_mul (by decide) e.sylow.not_dvd_index (by decide))

@[simp] theorem coe_ambientSylow (e : Extension (M := M)) :
    (ambientSylow e : Subgroup M) = commonSylow e := rfl

omit [Finite M] in
private theorem commonSylow_le_parabolic (e : Extension (M := M)) (i : Bool) :
    commonSylow e ≤ parabolic e.projection e.flag i := by
  apply (map_subtype_le _).trans
  rw [e.borel_eq]
  exact comap_mono (modelParabolic_borel_le e.flag i)

private theorem modelCore_le_borel (g : SL) (i : Bool) :
    (pCore 2 (modelParabolic g i)).map (modelParabolic g i).subtype ≤ modelBorel g := by
  have hB : (modelBorelSylow g : Subgroup SL) ≤ modelParabolic g i := by
    rw [coe_modelBorelSylow]
    exact modelParabolic_borel_le g i
  have hh := pCoreIn_le_sylow (p := 2) (modelParabolic g i) ((modelBorelSylow g).subtype hB)
  change (pCore 2 (modelParabolic g i)).map (modelParabolic g i).subtype ≤
    ((modelBorelSylow g : Subgroup SL).subgroupOf (modelParabolic g i)).map
      (modelParabolic g i).subtype at hh
  rwa [map_subgroupOf_eq_of_le hB, coe_modelBorelSylow] at hh


private theorem commonSylow_map (e : Extension (M := M)) :
    (commonSylow e).map e.projection = modelBorel e.flag := by
  have hle : (commonSylow e).map e.projection ≤ modelBorel e.flag := by
    apply map_le_iff_le_comap.mpr
    rw [← borelPreimage, ← e.borel_eq]
    exact map_subtype_le _
  let T := (ambientSylow e).mapSurjective e.base.surjective
  have hB : IsPGroup 2 (modelBorel e.flag) := by
    rw [← coe_modelBorelSylow]
    exact (modelBorelSylow e.flag).isPGroup'
  exact (T.is_maximal' hB hle).symm

/-- The selected subgroup covers the actual model radical. -/
theorem selectedCore_map (e : Extension (M := M)) (i : Bool) :
    (selectedCore e i).map e.projection =
      (pCore 2 (modelParabolic e.flag i)).map (modelParabolic e.flag i).subtype := by
  apply le_antisymm
  · exact map_le_iff_le_comap.mpr inf_le_right
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (show x ∈ (commonSylow e).map e.projection by
      rw [commonSylow_map]; exact modelCore_le_borel e.flag i hx)
    exact ⟨y, ⟨hy, hx⟩, rfl⟩

omit [Finite M] in
private theorem parabolic_normalizes_radicalPreimage (e : Extension (M := M)) (i : Bool) :
    parabolic e.projection e.flag i ≤ normalizer
      (((pCore 2 (modelParabolic e.flag i)).map
        (modelParabolic e.flag i).subtype).comap e.projection : Set M) := by
  have hn := (modelParabolic e.flag i).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  exact (comap_mono hn).trans (le_normalizer_comap _)

omit [Finite M] in
/-- The common Sylow normalizes each selected radical. -/
theorem commonSylow_le_localParabolic (e : Extension (M := M)) (i : Bool) :
    commonSylow e ≤ localParabolic e i := by
  exact le_inf (commonSylow_le_parabolic e i)
    ((le_inf (commonSylow e).le_normalizer
      ((commonSylow_le_parabolic e i).trans
        (parabolic_normalizes_radicalPreimage e i))).trans inf_normalizer_le_normalizer_inf)

/-- The extension core lies in both actual local normalizers. -/
theorem extensionCore_le_localParabolic (e : Extension (M := M)) (i : Bool) :
    extensionCore e.projection ≤ localParabolic e i :=
  ((extensionCore_isPGroup _).le_sylow_of_normal (ambientSylow e)).trans
    (commonSylow_le_localParabolic e i)

omit [Finite M] in
private theorem selectedCore_le_parabolic (e : Extension (M := M)) (i : Bool) :
    selectedCore e i ≤ parabolic e.projection e.flag i :=
  inf_le_left.trans (commonSylow_le_parabolic e i)

omit [Finite M] in
/-- Relative normality of the selected core uses precisely its local normalizer. -/
theorem selectedCore_normal (e : Extension (M := M)) (i : Bool) :
    ((selectedCore e i).subgroupOf (localParabolic e i)).Normal :=
  normal_subgroupOf_of_le_normalizer inf_le_right

omit [Finite M] in
private theorem radicalPreimage_le_parabolic (e : Extension (M := M)) (i : Bool) :
    ((pCore 2 (modelParabolic e.flag i)).map
      (modelParabolic e.flag i).subtype).comap e.projection ≤
      parabolic e.projection e.flag i := comap_mono (map_subtype_le _)

/-- Frattini's argument for the selected Sylow in the radical preimage. -/
theorem localParabolic_sup_radicalPreimage (e : Extension (M := M)) (i : Bool) :
    localParabolic e i ⊔
      ((pCore 2 (modelParabolic e.flag i)).map
        (modelParabolic e.flag i).subtype).comap e.projection =
      parabolic e.projection e.flag i := by
  let P := parabolic e.projection e.flag i
  let R := ((pCore 2 (modelParabolic e.flag i)).map
    (modelParabolic e.flag i).subtype).comap e.projection
  have hRP : R ≤ P := radicalPreimage_le_parabolic e i
  let : (R.subgroupOf P).Normal :=
    normal_subgroupOf_of_le_normalizer (parabolic_normalizes_radicalPreimage e i)
  let S := (ambientSylow e).subtype (commonSylow_le_parabolic e i)
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal (R.subgroupOf P)
  have hsel : (T : Subgroup (R.subgroupOf P)).map (R.subgroupOf P).subtype =
      (selectedCore e i).subgroupOf P := by
    rw [hT, subgroupOf_map_subtype]
    rfl
  have hfr := congrArg (fun K : Subgroup P => K.map P.subtype) T.normalizer_sup_eq_top
  rw [Subgroup.map_sup, hsel, ← subgroupOf_normalizer_eq (selectedCore_le_parabolic e i),
    subgroupOf_map_subtype, map_subgroupOf_eq_of_le hRP,
    ← MonoidHom.range_eq_map, range_subtype] at hfr
  simpa only [localParabolic, inf_comm] using hfr

/-- The actual local normalizer maps onto its marked model parabolic. -/
theorem localParabolic_map (e : Extension (M := M)) (i : Bool) :
    (localParabolic e i).map e.projection = modelParabolic e.flag i := by
  have hr : (((pCore 2 (modelParabolic e.flag i)).map
      (modelParabolic e.flag i).subtype).comap e.projection).map e.projection =
      (pCore 2 (modelParabolic e.flag i)).map (modelParabolic e.flag i).subtype :=
    map_comap_eq_self_of_surjective e.base.surjective _
  have hp : (parabolic e.projection e.flag i).map e.projection =
      modelParabolic e.flag i := map_comap_eq_self_of_surjective e.base.surjective _
  have h := congrArg (fun K : Subgroup M => K.map e.projection)
    (localParabolic_sup_radicalPreimage e i)
  rw [Subgroup.map_sup, hr, hp] at h
  have hsel : selectedCore e i ≤ localParabolic e i :=
    le_inf (selectedCore_le_parabolic e i) (selectedCore e i).le_normalizer
  rw [← selectedCore_map e i, sup_eq_left.mpr (map_mono hsel)] at h
  exact h

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing

open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing
variable {M : Type*} [Group M] [Finite M]

/-- The selected Sylow radical is exactly the two-core of the local normalizer. -/
theorem selectedCore_eq_localCore (e : Extension (M := M)) (i : Bool) :
    selectedCore e i = localCore (localParabolic e i) := by
  have hsel : selectedCore e i ≤ localParabolic e i :=
    le_inf (selectedCore_le_parabolic e i) (selectedCore e i).le_normalizer
  apply le_antisymm
  · exact le_pCoreIn_of_normalizes
      ((ambientSylow e).isPGroup'.to_le inf_le_left) hsel inf_le_right
  · have hS : localCore (localParabolic e i) ≤ commonSylow e := by
      have hh := pCoreIn_le_sylow (p := 2) (localParabolic e i)
        ((ambientSylow e).subtype (commonSylow_le_localParabolic e i))
      change localCore (localParabolic e i) ≤
        ((commonSylow e).subgroupOf (localParabolic e i)).map (localParabolic e i).subtype at hh
      rwa [map_subgroupOf_eq_of_le (commonSylow_le_localParabolic e i)] at hh
    apply le_inf hS
    let f : localParabolic e i →* modelParabolic e.flag i :=
      (e.projection.comp (localParabolic e i).subtype).codRestrict _ (fun x => x.property.1)
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, hx, he⟩ := (show (y : SL) ∈ (localParabolic e i).map e.projection by
        rw [localParabolic_map]; exact y.property)
      exact ⟨⟨x, hx⟩, Subtype.ext he⟩
    have hn : ((pCore 2 (localParabolic e i)).map f).Normal := Normal.map inferInstance f hf
    have hcore : (pCore 2 (localParabolic e i)).map f ≤ pCore 2 (modelParabolic e.flag i) :=
      le_sSup ⟨hn, pCore_isPGroup.map f⟩
    rintro x ⟨a, ha, rfl⟩
    exact mem_map_of_mem (modelParabolic e.flag i).subtype (hcore (mem_map_of_mem f ha))

/-- The local core has precisely the model radical as its image. -/
theorem localCore_map (e : Extension (M := M)) (i : Bool) :
    (localCore (localParabolic e i)).map e.projection =
      (pCore 2 (modelParabolic e.flag i)).map (modelParabolic e.flag i).subtype := by
  rw [← selectedCore_eq_localCore, selectedCore_map]

private theorem model_primeToResidual_top (g : SL) (i : Bool) :
    primeToResidual 2 (modelParabolic g i) = ⊤ := by
  have hs : primeToResidual 2 (Equiv.Perm (Fin 4)) = ⊤ := by
    apply top_unique
    intro x _
    refine Equiv.Perm.swap_induction_on x (primeToResidual 2 _).one_mem ?_
    intro y a b _ hy
    apply (primeToResidual 2 _).mul_mem _ hy
    apply mem_primeToResidual_of_pow (n := 1)
    simp [pow_two]
  let f := modelParabolicEquivSymmetric g i
  apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
  rw [map_primeToResidual, hs, map_top_of_surjective _ f.surjective]

/-- The untilded local residual also covers the whole model parabolic. -/
theorem localResidual_map (e : Extension (M := M)) (i : Bool) :
    (localResidual (localParabolic e i)).map e.projection = modelParabolic e.flag i := by
  rw [map_localResidual, localParabolic_map, localResidual, model_primeToResidual_top,
    ← MonoidHom.range_eq_map, range_subtype]

/-- The actual two local normalizers generate M, using clause (A). -/
theorem localParabolic_generation (e : Extension (M := M)) :
    localParabolic e false ⊔ localParabolic e true = ⊤ := by
  let F := localParabolic e false ⊔ localParabolic e true
  have hm : F.map e.projection = ⊤ := by
    rw [Subgroup.map_sup, localParabolic_map, localParabolic_map, modelParabolic_generation]
  have hs : F ⊔ e.projection.ker = ⊤ := by
    have hh := congrArg (fun K : Subgroup SL => K.comap e.projection) hm
    simpa only [comap_map_eq, comap_top] using hh
  have hQ : extensionCore e.projection ≤ F :=
    (extensionCore_le_localParabolic e false).trans le_sup_left
  have hE : e.projection.ker ≤ F := by
    have hh := e.base.no_supplement F (by rw [hs]; exact le_top)
    rwa [sup_eq_left.mpr hQ] at hh
  exact (sup_eq_left.mpr hE).symm.trans hs

/-- For a two-group kernel the source local normalizer is the full parabolic. -/
theorem localParabolic_eq_parabolic (e : Extension (M := M))
    (hk : IsPGroup 2 e.projection.ker) (i : Bool) :
    localParabolic e i = parabolic e.projection e.flag i := by
  let P := parabolic e.projection e.flag i
  let R := ((pCore 2 (modelParabolic e.flag i)).map
    (modelParabolic e.flag i).subtype).comap e.projection
  have hRP : R ≤ P := radicalPreimage_le_parabolic e i
  let : (R.subgroupOf P).Normal :=
    normal_subgroupOf_of_le_normalizer (parabolic_normalizes_radicalPreimage e i)
  have hp : IsPGroup 2 R :=
    (pCore_isPGroup.map (modelParabolic e.flag i).subtype).comap_of_ker_isPGroup e.projection hk
  have hRS : R ≤ commonSylow e := by
    have hp' : IsPGroup 2 (R.subgroupOf P) := hp.comap_subtype
    have hh : R.subgroupOf P ≤
        ((ambientSylow e).subtype (commonSylow_le_parabolic e i) : Subgroup P) :=
      hp'.le_sylow_of_normal _
    intro x hx
    exact hh (show (⟨x, hRP hx⟩ : P) ∈ R.subgroupOf P from hx)
  have he : selectedCore e i = R := inf_eq_right.mpr hRS
  unfold localParabolic
  rw [he]
  exact inf_eq_left.mpr (parabolic_normalizes_radicalPreimage e i)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing

open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem natural_reachable : ∀ v : Fin 3 → ZMod 2, v ≠ 0 →
    ∃ g : SL, g.val.mulVec ![1, 0, 0] = v := by
  decide +kernel

private theorem natural_transitive (v w : Fin 3 → ZMod 2) (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : SL, g.val.mulVec v = w := by
  obtain ⟨a, ha⟩ := natural_reachable v hv
  obtain ⟨b, hb⟩ := natural_reachable w hw
  refine ⟨b * a⁻¹, ?_⟩
  change (b * a⁻¹) • v = w
  change a • ![1, 0, 0] = v at ha
  change b • ![1, 0, 0] = w at hb
  rw [← ha, mul_smul, inv_smul_smul, hb]

variable {M : Type*} [Group M]

/-- Natural coordinates and a full acting image give actual subgroup irreducibility. -/
theorem NaturalFactor.irreducible {π : M →* SL} {L Z : Subgroup M}
    (n : NaturalFactor π L Z ⊥) (hπ : L.map π = ⊤)
    (D : Subgroup M) (hDZ : D ≤ Z) (hLD : L ≤ normalizer (D : Set M)) :
    D = ⊥ ∨ D = Z := by
  rcases D.bot_or_exists_ne_one with hb | ⟨x, hx, hxne⟩
  · exact Or.inl hb
  right
  apply le_antisymm hDZ
  intro y hy
  by_cases hyne : y = 1
  · simpa only [hyne] using D.one_mem
  let xZ : Z := ⟨x, hDZ hx⟩
  let yZ : Z := ⟨y, hy⟩
  have hxcoord : (n.coordinates xZ).toAdd ≠ 0 := by
    intro h
    have hc : n.coordinates xZ = n.coordinates 1 := by
      simpa using congrArg Multiplicative.ofAdd h
    exact hxne (congrArg Subtype.val (n.equivOfBot.injective hc))
  have hycoord : (n.coordinates yZ).toAdd ≠ 0 := by
    intro h
    have hc : n.coordinates yZ = n.coordinates 1 := by
      simpa using congrArg Multiplicative.ofAdd h
    exact hyne (congrArg Subtype.val (n.equivOfBot.injective hc))
  obtain ⟨g, hg⟩ := natural_transitive _ _ hxcoord hycoord
  obtain ⟨l, hl, he⟩ := (show n.marking.symm g ∈ L.map π by rw [hπ]; trivial)
  let c : Z := ⟨l * x * l⁻¹, le_normalizer_iff.mp n.normalized l hl x (hDZ hx)⟩
  have hc : c = yZ := by
    apply n.equivOfBot.injective
    have h := n.action l hl xZ c rfl
    rw [he, n.marking.apply_symm_apply, hg] at h
    exact congrArg Multiplicative.ofAdd h
  have hval : l * x * l⁻¹ = y := congrArg Subtype.val hc
  exact hval ▸ le_normalizer_iff.mp hLD l hl x hx

namespace SourceData
variable [Finite M] {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M}
    [Z.Normal] [W.Normal] (d : SourceData e i Z W X)
include d

/-- Every L-invariant subgroup of the source natural Z is zero or all of Z. -/
theorem natural_irreducible (D : Subgroup M) (hDZ : D ≤ Z)
    (hLD : component e.projection e.flag ≤ normalizer (D : Set M)) :
    D = ⊥ ∨ D = Z :=
  d.natural.irreducible (component_map _ e.base.surjective _) D hDZ hLD

/-- The source natural subgroup Z centralizes the whole extension two-core Q. -/
theorem z_le_centralizer_extensionCore :
    Z ≤ centralizer (extensionCore e.projection : Set M) := by
  let Q := extensionCore e.projection
  have hZQ : Z ≤ Q := d.z_le.trans d.x_le
  by_cases hZ : Z = ⊥
  · rw [hZ]
    exact bot_le
  have hZQne : Z.subgroupOf Q ≠ ⊥ := by
    intro h
    have hh := congrArg (fun H : Subgroup Q => H.map Q.subtype) h
    rw [map_subgroupOf_eq_of_le hZQ, Subgroup.map_bot] at hh
    exact hZ hh
  have hmeet := center_inf_ne_bot_of_normal (extensionCore_isPGroup e.projection)
    (Z.subgroupOf Q) hZQne
  let C := (center Q).map Q.subtype
  have hD : Z ⊓ C ≠ ⊥ := by
    intro h
    apply hmeet
    apply (map_eq_bot_iff_of_injective _ Q.subtype_injective).mp
    rw [Subgroup.map_inf _ _ _ Q.subtype_injective, map_subgroupOf_eq_of_le hZQ,
      inf_comm, h]
  have hn : component e.projection e.flag ≤ normalizer ((Z ⊓ C : Subgroup M) : Set M) := by
    rw [normalizer_eq_top]
    exact le_top
  have he : Z ⊓ C = Z := (d.natural_irreducible _ inf_le_left hn).resolve_left hD
  have hZC : Z ≤ C := he ▸ inf_le_right
  rintro z hz q hq
  obtain ⟨c, hc, rfl⟩ := hZC hz
  exact congrArg Subtype.val ((mem_center_iff.mp hc) ⟨q, hq⟩)

end SourceData
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing
