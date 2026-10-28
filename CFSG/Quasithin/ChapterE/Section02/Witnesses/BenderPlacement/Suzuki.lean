module
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.Suzuki.Source
public import Theory.GroupTheory.NormalCoreTwoClosedTransport.General
public import Theory.SpecificGroups.Suzuki.NormalSupplement
public import CFSG.Quasithin.ChapterE.Section02.Structure.NormalBender

/-!
# Placement and the original Suzuki normal-Bender witness

The actual normal Suzuki supplement equals H, and the original elementary V
lies in the center of its prescribed Sylow intersection. The concrete Suzuki
pair is then carried through the same inclusion K → H. The original unique
maximal subgroup pulls back to the Borel by the proved normal-Bender source
calculation. Thus neither placement nor a model witness is an input, and the
result retains the original V, internal conjugator and maximal intersection.

Source: Aschbacher–Smith E.2.7, printed p.218, normal Bender case.
-/

@[expose] public section
noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
variable {H : Type*} [Group H] [Finite H]

structure SuzukiWitness (T : Sylow 2 H) (M V : Subgroup H) (m : ℕ) where
  pair : QuotientLift.Pair T M V
  outside : (pair.conjugator : H) ∉ M
  normalizer_eq : M.subgroupOf pair.subgroup = normalizer (pair.sylow : Set pair.subgroup)
  core_eq_bot : (M.subgroupOf pair.subgroup).normalCore = ⊥
  parameter : ℕ
  positive : 0 < parameter
  degree_dvd : 2 * parameter + 1 ∣ 2 * m + 1
  equiv : pair.subgroup ≃* SuzukiMatrixGroup parameter
  borel_eq : (M.subgroupOf pair.subgroup).map equiv.toMonoidHom =
    normalizer ((pair.sylow : Subgroup pair.subgroup).map equiv.toMonoidHom : Set (SuzukiMatrixGroup parameter))
  borel_conjugate : ∃ c : SuzukiMatrixGroup parameter,
    (M.subgroupOf pair.subgroup).map equiv.toMonoidHom =
      (SuzukiBorelSubgroup parameter).map (MulAut.conj c).toMonoidHom

theorem suzuki_pair_map {G D : Type*} [Group G] [Group D]
    (f : G →* D) (V : Subgroup G) (g : G) :
    (V ⊔ V.map (MulAut.conj g).toMonoidHom).map f =
      V.map f ⊔ (V.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_sup, map_map, map_map]
  congr 2
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, map_mul, map_inv]

noncomputable def SuzukiWitness.map_model {m : ℕ}
    {S : Sylow 2 (SuzukiMatrixGroup m)} {W : Subgroup (SuzukiMatrixGroup m)}
    (w : Suzuki.SourceWitness S W)
    (f : SuzukiMatrixGroup m →* H) (hf : Function.Injective f)
    (T : Sylow 2 H) (M : Subgroup H)
    (hT : (T : Subgroup H).comap f = S)
    (hM : M.comap f = normalizer (S : Set (SuzukiMatrixGroup m))) :
    SuzukiWitness T M (W.map f) m := by
  let I := w.subgroup.map f
  let e : w.subgroup ≃* I := w.subgroup.equivMapOfInjective f hf
  have hmap (A : Subgroup H) (B : Subgroup (SuzukiMatrixGroup m)) (hAB : A.comap f = B) :
      (B.subgroupOf w.subgroup).map e.toMonoidHom = A.subgroupOf I := by
    have hc : (A.subgroupOf I).comap e.toMonoidHom = B.subgroupOf w.subgroup := by
      ext x
      change f x ∈ A ↔ (x : SuzukiMatrixGroup m) ∈ B
      exact SetLike.ext_iff.mp hAB (x : SuzukiMatrixGroup m)
    rw [← hc, map_comap_eq_self_of_surjective e.surjective]
  have hV := hmap (W.map f) W (comap_map_eq_self_of_injective hf W)
  have hS := hmap (T : Subgroup H) S hT
  have hB := hmap M (normalizer (S : Set (SuzukiMatrixGroup m))) hM
  let g := e w.conjugator
  let P := w.sylow.mapSurjective (f := e.toMonoidHom) e.surjective
  have hPe : (P : Subgroup I) = (w.sylow : Subgroup w.subgroup).map e.toMonoidHom := rfl
  have hS0 : (w.sylow : Subgroup w.subgroup) = (S : Subgroup _).subgroupOf w.subgroup := by
    apply Subgroup.map_injective w.subgroup.subtype_injective
    rw [w.sylow_eq,subgroupOf_map_subtype]
  have hP : (P : Subgroup I) = (T : Subgroup H).subgroupOf I := by rw [hPe,hS0,hS]
  have hgen : (W.map f).subgroupOf I ⊔
      ((W.map f).subgroupOf I).map (MulAut.conj g).toMonoidHom = ⊤ := by
    have hh := congrArg (Subgroup.map e.toMonoidHom) w.generate
    rw [suzuki_pair_map,hV,map_top_of_surjective _ e.surjective] at hh
    exact hh
  have hcore : (M.subgroupOf I).normalCore = ⊥ := by
    have hm : (M.subgroupOf I).comap e.toMonoidHom =
        (normalizer (S : Set (SuzukiMatrixGroup m))).subgroupOf w.subgroup := by
      rw [← hB,comap_map_eq_self_of_injective e.injective]
    have hh := normalCore_comap_of_surjective e.toMonoidHom e.surjective (M.subgroupOf I)
    rw [hm,w.core_eq_bot] at hh
    have hi := congrArg (Subgroup.map e.toMonoidHom) hh
    rw [Subgroup.map_bot,map_comap_eq_self_of_surjective e.surjective] at hi
    exact hi.symm
  have hclosed : ∃ R : Sylow 2 (M.subgroupOf I).normalCore,
      (R : Subgroup (M.subgroupOf I).normalCore).Normal := by
    rw [hcore]
    exact ⟨default,inferInstance⟩
  let pair : QuotientLift.Pair T M (W.map f) :=
    ⟨I,map_mono w.le,g,hgen,P,by rw [hP,subgroupOf_map_subtype],hclosed⟩
  let d := e.symm.trans w.equiv
  have hd : d.toMonoidHom.comp e.toMonoidHom = w.equiv.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact congrArg w.equiv (e.symm_apply_apply x)
  refine ⟨pair,?_,?_,hcore,w.parameter,w.positive,w.degree_dvd,d,?_,?_⟩
  · intro hg
    apply w.outside
    exact (SetLike.ext_iff.mp hM (w.conjugator : SuzukiMatrixGroup m)).mp hg
  · change M.subgroupOf I = normalizer (P : Set I)
    rw [← hB,w.normalizer_eq]
    change (normalizer ((w.sylow : Subgroup w.subgroup) : Set w.subgroup)).map _ = _
    rw [map_normalizer_eq_of_bijective _ e.bijective]
    rfl
  · change (M.subgroupOf I).map d.toMonoidHom = _
    rw [← hB,Subgroup.map_map,hd,w.borel_eq]
    change _ = normalizer ((P : Subgroup I).map d.toMonoidHom : Set (SuzukiMatrixGroup w.parameter))
    rw [hPe,Subgroup.map_map,hd]
  · change ∃ c, (M.subgroupOf I).map d.toMonoidHom = _
    rw [← hB,Subgroup.map_map,hd]
    exact w.borel_conjugate

/-- The normal Suzuki branch with the original unique maximal subgroup.
The stronger placement argument does not need normality of V or V ≤ O₂(M). -/
theorem source_suzuki (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (K : Subgroup H) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hcore : pCore 2 H = ⊥)
    {m : ℕ} (hm : 0 < m) (e : K ≃* SuzukiMatrixGroup m)
    (V : Subgroup H) [IsElementaryAbelian 2 V]
    (hVT : V ≤ T) (hrank : 1 < primeRank 2 V) :
    V ≤ K ∧ Nonempty (SuzukiWitness T (ChapterB.minimalParabolicMax T hP) V m) := by
  obtain ⟨hVK,S,hS,hVZ⟩ :=
    suzuki_normal_sylow_supplement_placement K T hgen hcore hm e V hVT
  let M := ChapterB.minimalParabolicMax T hP
  have hMK : M.subgroupOf K = normalizer (S : Set K) := by
    have h := (Structure.source_normal_bender_conclusions T hP K hgen
      (.suzuki m (by omega) ⟨e⟩)).1
    rw [← hS] at h
    exact h
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let W := (V.subgroupOf K).map e.toMonoidHom
  let : IsElementaryAbelian 2 (V.subgroupOf K) := IsElementaryAbelian.subgroupOf hVK
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map e.toMonoidHom
  have hWQ : W ≤ (Q : Subgroup (SuzukiMatrixGroup m)) := by
    apply map_mono
    rw [hS]
    exact comap_mono hVT
  have hWr : 1 < primeRank 2 W := by
    rw [← primeRank_congr 2 ((V.subgroupOf K).equivMapOfInjective e.toMonoidHom e.injective),
      primeRank_congr 2 (subgroupOfEquivOfLe hVK)]
    exact hrank
  obtain ⟨w⟩ := Suzuki.source_witness_of_le_sylow hm Q W hWQ hWr
  let f : SuzukiMatrixGroup m →* H := K.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := K.subtype_injective.comp e.symm.injective
  have hTf : (T : Subgroup H).comap f = Q := by
    change ((T : Subgroup H).subgroupOf K).comap e.symm.toMonoidHom = _
    rw [← hS]
    exact comap_equiv_eq_map_symm e.symm (S : Subgroup K)
  have hMf : M.comap f = normalizer (Q : Set (SuzukiMatrixGroup m)) := by
    change (M.subgroupOf K).comap e.symm.toMonoidHom = _
    rw [hMK]
    change (normalizer ((S : Subgroup K) : Set K)).comap e.symm.toMonoidHom = _
    rw [comap_normalizer_eq_of_surjective (f := e.symm.toMonoidHom)
      (S : Subgroup K) e.symm.surjective]
    have heS : (S : Subgroup K).comap e.symm.toMonoidHom = (Q : Subgroup _) :=
      comap_equiv_eq_map_symm e.symm (S : Subgroup K)
    rw [heS]
    rfl
  have hWV : W.map f = V := by
    change ((V.subgroupOf K).map e.toMonoidHom).map f = _
    rw [map_map]
    have he : f.comp e.toMonoidHom = K.subtype := by
      ext x
      exact congrArg Subtype.val (e.symm_apply_apply x)
    rw [he,map_subgroupOf_eq_of_le hVK]
  have result := SuzukiWitness.map_model w f hf T M hTf hMf
  rw [hWV] at result
  exact ⟨hVK,⟨result⟩⟩

end CFSG.Quasithin.ChapterE.Witnesses.BenderPlacement
