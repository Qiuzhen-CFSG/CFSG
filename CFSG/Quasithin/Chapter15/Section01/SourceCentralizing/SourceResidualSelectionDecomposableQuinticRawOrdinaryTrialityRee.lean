module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticRawHigherG2Local
public import Theory.SpecificGroups.ReeF4.ParabolicResiduals
public import Theory.SpecificGroups.ReeF4.CubicRank
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.CubicOrder

/-! The actual higher-field Ree component is excluded by its two native
parabolic residuals. The Suzuki residual is three-free, whereas escape
would give an original FF image whose order is divisible by three. The
linear residual has a nonshort PSL2 core and is placed by the proved raw
theorem. Native generation then contradicts the original component's escape. -/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ClassificationModels ChapterC.C27Source
open ReeF4 ReeF4.LargeLocalSeeds ReeF4.Parabolics
variable {G : Type*} [Group G] [Finite G]

private theorem raw_ree_normal
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G))
      (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    (m : ℕ) (e : L ≃* ReeF4.Model m) :
    (L.subgroupOf (centralizer (Z1 : Set G))).Normal := by
  let := h.elementary
  have hsq : IsSQTK KnownSimple.IsKnownSimple (centralizer (Z1 : Set G)) := caseI_centralizer_sqtk hG Z1 hZne
    ((IsElementaryAbelian.isPGroup 2 V).to_le (hZ.trans inf_le_left))
  let ec : L.subgroupOf (centralizer (Z1 : Set G)) ≃* L := subgroupOfEquivOfLe hLG
  have hR : 2 ≤ primeRank 3 (L.subgroupOf (centralizer (Z1 : Set G))) := by
    rw [primeRank_equiv 3 (ec.trans e)]
    exact CubicRank.model m
  have hZtwo : IsPGroup 2 (center L) := by
    rw [hcenter]
    exact pCore_isPGroup
  have hZ := hZtwo.of_equiv (centerCongr ec.symm)
  obtain ⟨k,hk⟩ := hZ.exists_card_eq
  have hc : Nat.Coprime 3 (Nat.card (center (L.subgroupOf (centralizer (Z1 : Set G))))) := by
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  exact hL.normal_of_coprime_center_primeRank 3 hc (by
    have hh := hsq.stronglyQuasithin 3 Nat.prime_three (by decide)
    omega)

private theorem raw_ree_sylow_marking
    {S L : Subgroup G} (hSylL : Chapter1.IsSylowIn 2 (S ⊓ L) L)
    (m : ℕ) (e : L ≃* ReeF4.Model m) :
    ∃ e' : L ≃* ReeF4.Model m,
      ((S ⊓ L).subgroupOf L).map e'.toMonoidHom = Parabolics.unipotent m := by
  obtain ⟨Q,hQ⟩ := hSylL
  have hQL : (Q : Subgroup L) = (S ⊓ L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le (show (S ⊓ L) ≤ L from inf_le_right)]
    exact hQ
  obtain ⟨U,hU⟩ := ConverseParabolics.exists_sylow_eq_unipotent m
  rw [ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.unipotent_eq_rootUnipotent] at hU
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ReeF4.Model m) Q' U
  refine ⟨e.trans (MulAut.conj g),?_⟩
  rw [←hQL]
  change (Q : Subgroup L).map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
  rw [←map_map]
  change (Q' : Subgroup (ReeF4.Model m)).map (MulAut.conj g).toMonoidHom = _
  rw [←hU,←hg,Sylow.coe_subgroup_smul,pointwise_smul_def]
  rfl

private theorem raw_ree_residuals
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M V Z1 L : Subgroup G} (h : PreparedChosenModule T M V)
    (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G))
      (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    (hSylG : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hSylL : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (m : ℕ) (hm : 1 ≤ m) (model : Chapter1.Section02.LocalModels.IsReeF4At L m) :
    ∃ B K : Side → Subgroup G,
      (∀ a, B a ≤ L) ∧
      (∀ a, ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ≤ normalizer (B a : Set G)) ∧
      (∀ a, (solvableResidual (B a)).map (B a).subtype = K a) ∧
      (∀ a, K a ∈ Chapter1.LIn (centralizer (Z1 : Set G))
        ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))) ∧
      (∀ a, generalizedFitting (K a) = pCore 2 (K a)) ∧
      (∀ a, IsQuasisimple (K a ⧸ pCore 2 (K a))) ∧
      (¬3 ∣ Nat.card (K .suzuki)) ∧
      (¬ChapterC.IsShort (K .linear)) ∧
      ClassicalGroup.IsPSL (K .linear ⧸ pCore 2 (K .linear)) 2 (2^(2*m+1)) ∧
      K .suzuki ⊔ K .linear = L := by
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  obtain ⟨D,⟨e₀⟩⟩ := model
  obtain ⟨e,he⟩ := raw_ree_sylow_marking hSylL m (e₀.trans D.modelEquiv)
  have hnL : S ≤ normalizer (L : Set G) := (show S ≤ centralizer (Z1 : Set G) from inf_le_right).trans
    ((normal_subgroupOf_iff_le_normalizer hLG).mp
      (raw_ree_normal hG T h hZ hZne hLG hL hcenter m e))
  let f := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := L.subtype_injective.comp e.symm.injective
  have hr : f.range = L := by rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,
    ←MonoidHom.range_eq_map,range_subtype]
  have hU : (Parabolics.unipotent m).map f = (S ⊓ L) := by
    rw [←he,map_map]
    have hh : f.comp e.toMonoidHom = L.subtype := by ext x; simp [f]
    rw [hh,map_subgroupOf_eq_of_le (show (S ⊓ L) ≤ L from inf_le_right)]
  let B := fun a => (Parabolics.parabolic m a).map f
  let K := fun a => (localFactor m a).map f
  let α : S →* MulAut (ReeF4.Model m) := (MulAut.congr e).toMonoidHom.comp
    (L.normalizerMonoidHom.comp (inclusion hnL))
  have heq (a : S) (l : L) :
      e (L.normalizerMonoidHom (inclusion hnL a) l) = α a (e l) := by simp [α]
  have hnSL : S ≤ normalizer ((S ⊓ L) : Set G) :=
    (le_inf S.le_normalizer hnL).trans inf_normalizer_le_normalizer_inf
  have hUi (a : S) : (Parabolics.unipotent m).map (α a).toMonoidHom = Parabolics.unipotent m := by
    have hh := EquivariantLift.map_invariant L e.toMonoidHom hnL α heq (D := S ⊓ L) hnSL a
    rwa [he] at hh
  have hpow (a : S) : ∃ n : ℕ, α a ^ (2^n) = 1 := by
    obtain ⟨n,hn⟩ := (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)) a
    exact ⟨n,by rw [←map_pow,hn,map_one]⟩
  have hBi (a : Side) (t : S) :
      (Parabolics.parabolic m a).map (α t).toMonoidHom = Parabolics.parabolic m a := by
    have hi : ∀ x, x ∈ ConverseParabolics.unipotent m ↔ α t x ∈ ConverseParabolics.unipotent m := by
      rw [ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.unipotent_eq_rootUnipotent]
      intro x
      have hx := (mem_map_iff_mem (f := (α t).toMonoidHom) (α t).injective
        (K := Parabolics.unipotent m) (x := x)).symm
      rw [hUi t] at hx
      exact hx
    have hh := ConverseParabolics.parabolic_invariant_of_twoPower hm (α t) (hpow t) hi a
    rw [ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic] at hh
    ext x
    rw [mem_map_equiv]
    simpa only [MulEquiv.apply_symm_apply] using hh ((α t).symm x)
  have hBn (a : Side) : S ≤ normalizer (B a : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    obtain ⟨y,hy,rfl⟩ := hx
    let t₀ : S := ⟨t,ht⟩
    refine ⟨α t₀ y,hBi a t₀ ▸ mem_map_of_mem (α t₀).toMonoidHom hy,?_⟩
    change (e.symm (e (L.normalizerMonoidHom (inclusion hnL t₀) (e.symm y))) : G) = _
    rw [e.symm_apply_apply]
    rfl
  have hres (a : Side) : (solvableResidual (B a)).map (B a).subtype = K a := by
    rw [←map_embedded_solvableResidual_of_hom,parabolic_solvableResidual_map hm a]
  have hKn (a : Side) : S ≤ normalizer (K a : Set G) := by
    rw [←hres a]
    exact (hBn a).trans (normalizer_le_normalizer_characteristic_image (B a) (solvableResidual (B a)))
  have hKL (a : Side) : K a ≤ L := hr ▸ map_le_range f _
  let ek (a : Side) : localFactor m a ≃* K a := (localFactor m a).equivMapOfInjective f hf
  let eq (a : Side) := QuotientGroup.congr _ _ (ek a) (pCore_map_iso 2 (ek a))
  have hq (a : Side) : IsQuasisimple (K a ⧸ pCore 2 (K a)) := by
    let := localFactor_quotient_quasisimple hm a
    exact IsQuasisimple.of_mulEquiv (eq a)
  have hfit (a : Side) : generalizedFitting (K a) = pCore 2 (K a) := by
    rw [←map_generalizedFitting_equiv (ek a),←pCore_map_iso 2 (ek a),localFactor_generalizedFitting hm a]
  have hfamily (a : Side) : K a ∈ Chapter1.LIn (centralizer (Z1 : Set G)) S := by
    let := OuterLocal.localFactor_perfect hm a
    let : Group.IsPerfect (K a) := Group.IsPerfect.ofSurjective (f := (ek a).toMonoidHom) (ek a).surjective
    let := hq a
    apply Chapter1.mem_LIn_of_normalized_perfect hSylG
      ((hKL a).trans hLG) (hKn a)
    intro hz
    have hz' : pCore 2 (K a) = ⊥ := (map_eq_bot_iff_of_injective _ (K a).subtype_injective).mp hz
    have hh := congrArg (Subgroup.map (ek a).symm.toMonoidHom) hz'
    rw [pCore_map_iso,Subgroup.map_bot] at hh
    exact localFactor_core_ne_bot hm a hh
  refine ⟨B,K,(fun _ => hr ▸ map_le_range f _),hBn,hres,hfamily,hfit,hq,?_,?_,?_,?_⟩
  · rw [←Nat.card_congr (ek .suzuki).toEquiv]
    exact suzukiLocalFactor_three_free hm
  · intro hs
    have hs' := hs.of_mulEquiv (ek .linear).symm
    exact linearLocalFactor_core_triple hm (commutator_eq_bot_iff_le_centralizer.mpr hs'.central)
  · exact ⟨CoefficientField m,inferInstance,inferInstance,field_card m,
      ⟨(eq .linear).symm.trans (linearLocalQuotientEquiv m)⟩⟩
  · change (localFactor m .suzuki).map f ⊔ (localFactor m .linear).map f = L
    rw [←Subgroup.map_sup,localFactor_sup_eq_top,←MonoidHom.range_eq_map,hr]

private theorem raw_three_free_local_le_marked
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 K : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hK : K ∈ Chapter1.LIn (centralizer (Z1 : Set G))
      ((T : Subgroup G) ⊓ centralizer (Z1 : Set G)))
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hf : generalizedFitting K = pCore 2 K)
    (hthree : ¬3 ∣ Nat.card K) : K ≤ centralizer (Z1 : Set G) ⊓ Mc := by
  by_contra hout
  let S := (T : Subgroup G) ⊓ centralizer (Z1 : Set G)
  have houtM : ¬K ≤ M := by
    intro hKM
    let : Group.IsPerfect (K.subgroupOf (K ⊔ S)) := hK.2.1.perfect
    let i : K.subgroupOf (K ⊔ S) ≃* K := subgroupOfEquivOfLe le_sup_left
    let : Group.IsPerfect K := Group.IsPerfect.ofSurjective (f := i.toMonoidHom) i.surjective
    exact hout (le_inf hK.1
      ((perfect_subgroup_centralizes_localModule hG T hempty hM hKM).trans
        (localModule_centralizer_le_partner T M hu)))
  let H := K ⊔ (S ⊓ normalizer (K : Set G))
  let W := normalClosure ((centralInvolutions T).subgroupOf H : Set H)
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let I := (K.subgroupOf H).map q
  obtain ⟨hr,_,_,_,_,hIJ,⟨c⟩⟩ :=
    h.raw_component_normalizer_source hG T hM hJ hu hZ hZne hK hq hf hout houtM
  let := hr.elementary
  have hm : StarModels.Model I :=
    StarModels.model_of_source _ (subgroupOfEquivOfLe hIJ).symm c
  have hd := hm.three_dvd.trans
    (card_dvd_of_surjective (q.subgroupMap (K.subgroupOf H))
      (q.subgroupMap_surjective (K.subgroupOf H)))
  rw [Nat.card_congr (subgroupOfEquivOfLe (show K ≤ H from le_sup_left)).toEquiv] at hd
  exact hthree hd

/-- Exclude the higher-field Ree row on the original ordinary component.
Both native residuals are placed using actual raw normalizer sources. -/
theorem PreparedChosenModule.raw_ordinary_not_higherRee
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V Z1 L : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hZ : Z1 ≤ thompsonFixed T V) (hZne : Z1 ≠ ⊥)
    (hLG : L ≤ centralizer (Z1 : Set G))
    (hL : IsComponent (centralizer (Z1 : Set G))
      (L.subgroupOf (centralizer (Z1 : Set G))))
    (hcenter : center L = pCore 2 L)
    (hSylG : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer (Z1 : Set G))
      (centralizer (Z1 : Set G)))
    (hSylL : Chapter1.IsSylowIn 2 (((T : Subgroup G) ⊓ centralizer (Z1 : Set G)) ⊓ L) L)
    (hout : ¬L ≤ centralizer (Z1 : Set G) ⊓ Mc) (m : ℕ) (hm : 1 ≤ m) :
    ¬Chapter1.Section02.LocalModels.IsReeF4At L m := by
  intro model
  obtain ⟨B,K,_,_,_,hfamily,hfit,hquasi,hthree,hshort,hquot,hgen⟩ :=
    raw_ree_residuals hG T h hZ hZne hLG hL hcenter hSylG hSylL m hm model
  have hs := raw_three_free_local_le_marked hG T hempty hM hJ hu h hZ hZne
    (hfamily .suzuki) (hquasi .suzuki) (hfit .suzuki) hthree
  have hl := h.raw_nonshort_pslTwo_le_marked hG T hempty hM hJ hu hZ hZne
    (hfamily .linear) (hfit .linear) hshort (2*m+1) (by omega) hquot
  exact hout (hgen ▸ sup_le hs hl)

end CFSG.Quasithin.Chapter15.Section01
