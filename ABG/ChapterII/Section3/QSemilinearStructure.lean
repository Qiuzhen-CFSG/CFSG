module
public import ABG.ChapterII.Section3.QLinearSylowTransfer
public import GorensteinWalter.PGammaL2FullLinearRestriction
public import ABG.ChapterII.Section3.QConstituentMatrixModel
public import ABG.ChapterII.Section3.QSylowExtensionData
public import ABG.ChapterII.Section3.UnitaryPrescribedCoefficientLift
public import ABG.ChapterII.Section3.LinearSemilinearLift
public import ABG.ChapterII.Section3.UnitarySemilinearLift
public import ABG.ChapterII.Section3.QSemilinearStructureStatement
public import Theory.GroupTheory.SemilinearComplementCentralizer
public import Theory.SpecificGroups.GL2.FaithfulModelCentralizer
public import ABG.ChapterII.Section3.QSemilinearStructureTransport
public import ABG.ChapterII.Section2.QGroupEquiv
public import Mathlib.Algebra.Group.Shrink

/-!
# The full semilinear structure of core-free Q-groups

For a finite enlarged Q-group H with trivial odd core and a prescribed normal
SL2(F) subgroup over an odd finite field, this proves ABG II.3 Proposition 3.
The conclusion gives H=LE with L normal, L0 contained in L, E cyclic of odd
order and disjoint from L, an injective map to the actual GammaL2 or GammaU2,
the exact determinant-level image of L, pure coefficient images for E, and
E equal to the ambient odd core of a Sylow-two centralizer in H. Both matrix
alternatives are retained, including fields of orders three and nine.

First work over a canonical Galois field. The source Sylow geometry and the
projective decomposition retain the same Sylow R, normal SL2 identification,
and map f. Restrict f to L and express its pure field image through the actual
complement E. Choose unitary coordinates for this prescribed odd actor before
recognizing L as a matrix determinant level. The linear and unitary lifting
theorems derive action agreement from projective compatibility, fixed Sylow
subgroups and the absence of index-two subgroups in SL2. The latter works
uniformly at q=3. The faithful matrix centralizer theorem and Q-group Sylow
noncommutativity identify the complement as the claimed odd core. Finally
transport the complete structure through finite-field uniqueness and a finite
universe reduction; this preserves every image and the centralizer equality.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article pp24-28,
`page-025.tex` through `page-029.tex`. The final either-model conclusion is
unrestricted, as in the source proposition; the inconsistent early congruence
choice in its proof is not imposed on the result.
-/

namespace ABG
open GorensteinWalter Matrix.GeneralLinearGroup

private theorem projective_actor
    {H F : Type*} [Group H] [Field F]
    (L E : Subgroup H) [L.Normal] (hcomp : L.IsComplement' E)
    (f : H →* PGammaL2 F) (hker : f.ker ≤ L)
    (φ : L →* PGL2 F) (hfL : ∀ l : L, f l = SemidirectProduct.inl (φ l))
    (hE : E.map f ≤ (SemidirectProduct.inr : (F ≃+* F) →* PGammaL2 F).range) :
    ∃ c : E →* (F ≃+* F), Function.Injective c ∧
      ∃ fE : H →* PGL2 F ⋊[(pgl2FieldAut F).comp c] E,
        (∀ l : L, fE l = SemidirectProduct.inl (φ l)) ∧
        (∀ e : E, fE e = SemidirectProduct.inr e) := by
  classical
  let c := (SemidirectProduct.rightHom : PGammaL2 F →* (F ≃+* F)).comp
    (f.comp E.subtype)
  have hfE (e : E) : f e = SemidirectProduct.inr (c e) := by
    obtain ⟨a, ha⟩ := hE (Subgroup.mem_map_of_mem f e.property)
    have hright := congrArg (fun z : PGammaL2 F => z.right) ha
    change a = c e at hright
    exact ha.symm.trans (congrArg SemidirectProduct.inr hright)
  have hc : Function.Injective c := by
    apply (MonoidHom.ker_eq_bot_iff c).mp
    apply bot_unique
    intro e he
    have hf : (e : H) ∈ f.ker := by
      change f e = 1
      rw [hfE, show c e = 1 from he, map_one]
    have hle : (e : H) ∈ L ⊓ E := ⟨hker hf, e.property⟩
    have heq : (e : H) = 1 := by
      rw [hcomp.disjoint.eq_bot] at hle
      exact hle
    exact Subtype.ext heq
  let γ := L.normalizerMonoidHom.comp
    (Subgroup.inclusion (L.normalizer_eq_top ▸ (le_top : E ≤ ⊤)))
  let β := (pgl2FieldAut F).comp c
  have hγ (e : E) (l : L) : (γ e l : H) = e * l * (e : H)⁻¹ := rfl
  have hφ (e : E) : φ.comp (γ e).toMonoidHom = (β e).toMonoidHom.comp φ := by
    apply DFunLike.ext
    intro l
    apply SemidirectProduct.inl_injective (φ := pgl2FieldAut F)
    change SemidirectProduct.inl (φ (γ e l)) = SemidirectProduct.inl (β e (φ l))
    rw [← hfL, hγ, map_mul, map_mul, map_inv, hfE, hfL]
    simpa only [β, MonoidHom.comp_apply, map_inv] using
      (SemidirectProduct.inl_aut (φ := pgl2FieldAut F) (c e) (φ l)).symm
  let k := SemidirectProduct.mulEquivSubgroup hcomp
  let j : L ⋊[γ] E →* PGL2 F ⋊[β] E :=
    SemidirectProduct.map φ (MonoidHom.id E) hφ
  refine ⟨c, hc, j.comp k.symm.toMonoidHom, ?_, ?_⟩
  · intro l
    have hk : k.symm l = SemidirectProduct.inl l := by
      apply k.injective
      rw [k.apply_symm_apply]
      simp [k]
    change j (k.symm l) = _
    rw [hk]
    exact SemidirectProduct.map_inl _ _ _ _
  · intro e
    have hk : k.symm e = SemidirectProduct.inr e := by
      apply k.injective
      rw [k.apply_symm_apply]
      simp [k]
    change j (k.symm e) = _
    rw [hk]
    exact SemidirectProduct.map_inr _ _ _ _

private theorem model_sylow_centralizer
    {H D F : Type*} [Group H] [Finite H] [Group D] [Finite D] [Field F]
    (hH : IsQGroup H) (L : Subgroup H) (hL : Odd L.index) (e : L ≃* D)
    (j : D →* GL (Fin 2) F) (hj : Function.Injective j)
    (m : ℕ) (hlevel : j.range ≤ determinantTwoPower F m)
    (T : Sylow 2 D) : IsPGroup 2 (Subgroup.centralizer (T : Set D)) := by
  apply isPGroup_centralizer_of_injective_determinant_model j hj m hlevel
  intro hT
  let S := T.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let eT : T ≃* S := (T : Subgroup D).equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  apply qGroup_odd_index_sylow_not_isMulCommutative hH L hL S
  exact ⟨⟨fun a b => eT.symm.injective (by
    rw [map_mul, map_mul]
    exact hT.is_comm.comm _ _)⟩⟩

private theorem qGroup_semilinear_structure_galois
    {H : Type} [Group H] [Finite H] (hH : IsQGroup H)
    (hcore : pPrimeCore 2 H = ⊥) (L0 : Subgroup H) [L0.Normal]
    (p d : ℕ) [Fact p.Prime] (hp : Odd p) (hd : d ≠ 0)
    (eL0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p d)) :
    qSemilinearStructureConclusion L0 (GaloisField p d) := by
  classical
  let K := GaloisField p d
  let : Finite (K ≃+* K) :=
    Finite.of_injective (fun e : K ≃+* K => (e : K → K)) DFunLike.coe_injective
  let : Finite (GaloisField p (2 * d) ≃+* GaloisField p (2 * d)) :=
    Finite.of_injective (fun e : GaloisField p (2 * d) ≃+* GaloisField p (2 * d) =>
      (e : GaloisField p (2 * d) → GaloisField p (2 * d))) DFunLike.coe_injective
  have hKc : Nat.card K = p ^ d := GaloisField.card p d hd
  have hK : IsOddPrimePower (Nat.card K) := ⟨p, d, Fact.out, hp, by omega, hKc⟩
  have hKo : Odd (Nat.card K) := by rw [hKc]; exact hp.pow
  obtain ⟨R, n, hn, hfield, hgeo⟩ :=
    qGroup_sylow_normal_sl2_extension_data hH hcore L0 K hK eL0
  let Z := subgroupCenter (R : Subgroup H)
  have hZc : Z ≤ Subgroup.center H := by
    have h := qGroup_eq_oddCore_mul_sylowCenterCentralizer hH R
    rw [hcore, bot_sup_eq] at h
    exact Subgroup.centralizer_eq_top_iff_subset.mp h
  let : Z.Normal := ⟨fun x hx g => by
    have hh := Subgroup.mem_center_iff.mp (hZc hx) g
    simpa only [hh, mul_inv_cancel_right] using hx⟩
  obtain ⟨_, hZcyc, hZne, hZtwo, f, L, E, hfker, hLN, hL0L, hcomp, hEcyc,
      hEodd, hLmap, hL0map, hEmap, hindex, hcomm, hRL, hLsup, hindexeq, hfcore⟩ :=
    qGroup_projective_linear_complement_with_sylow hH hcore R Z rfl L0 K hK eL0
  let : L.Normal := hLN
  have hLi : Odd L.index := hcomp.symm.index_eq_card ▸ hEodd
  have hZL : Z ≤ L := (Subgroup.map_subtype_le _).trans hRL
  have hlinear : L.map f ≤ pGammaL2PGLRange K := hLmap ▸ inf_le_right
  obtain ⟨φ, hφ, hφker⟩ := exists_pgl2_restriction_of_linear_layer f L hlinear
  have hφkerZ : φ.ker = Z.subgroupOf L := by rw [hφker, hfker]
  have hφtwo : IsPGroup 2 φ.ker :=
    hZtwo.of_equiv ((Subgroup.subgroupOfEquivOfLe hZL).symm.trans
      (MulEquiv.subgroupCongr hφkerZ.symm))
  have hφc : φ.ker.map L.subtype ≤ Subgroup.center H := by
    rw [hφkerZ, Subgroup.map_subgroupOf_eq_of_le hZL]
    exact hZc
  let M := L0.subgroupOf L
  let e0 : M ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (Subgroup.subgroupOfEquivOfLe hL0L).trans eL0
  have hφ0 (x : M) : φ x.val = Matrix.ProjectiveSpecialLinearGroup.toPGL
      (sl2ProjectiveProjection K (e0 x)) := by
    apply SemidirectProduct.inl_injective (φ := pgl2FieldAut K)
    rw [← hφ]
    exact hfcore ⟨x.val.val, x.property⟩
  have hi : (φ.ker ⊔ M).index ∣ 2 := by
    rw [hφkerZ, ← Subgroup.subgroupOf_sup hZL hL0L]
    exact hindex
  have hEpure : E.map f ≤ (SemidirectProduct.inr : (K ≃+* K) →* PGammaL2 K).range := by
    rw [hEmap]
    exact Subgroup.map_le_range _ _
  obtain ⟨c, hc, fE, hfEL, hfEE⟩ := projective_actor L E hcomp f (hfker ▸ hZL) φ hφ hEpure
  obtain ⟨cQ, eSU, hcQ, hcoeff⟩ := exists_unitary_coordinates_for_odd_actor hEodd p d hp hd c hc
  obtain ⟨m, hmodel⟩ := qGroup_constituent_matrix_model_with_level hH hcore L0 p d hp hd
    eL0 eSU R n hn (by simpa only [hKc] using hfield) hgeo L hRL hL0L
    f hfker hlinear hL0map hfcore hindexeq
  refine ⟨L, E, hLN, hL0L, hcomp, hEcyc, hEodd, ?_⟩
  rcases hmodel with ⟨hdiv, eL, heL⟩ | ⟨hdiv, eL, heL⟩
  · have hdivK : 2 ^ m ∣ Nat.card K - 1 := hKc ▸ hdiv
    obtain ⟨F, hF, _, _, hFL, hFE⟩ :=
      exists_linear_semilinear_embedding_of_core_equiv hK L E hcomp hEodd c hc φ hφtwo hφc
        M e0 hφ0 hi m hdivK eL (fun x => heL ⟨x.val.val, x.property⟩) fE hfEL hfEE
    refine ⟨Or.inl ⟨m, F, hF, hdivK, hFL, hFE⟩, ?_⟩
    apply Subgroup.exists_oddCore_sylowCentralizer_of_semilinear_model
      (coefficientAction K) (determinantTwoPower K m) L E hcomp hEodd F hF hFL hFE
    · intro A hA
      exact exists_sylow_fixed_by_odd_coefficient_subgroup K hKo A hA m hdivK
    · exact model_sylow_centralizer hH L hLi eL (determinantTwoPower K m).subtype
        (determinantTwoPower K m).subtype_injective m (by rw [Subgroup.range_subtype])
  · obtain ⟨F, hF, _, _, hFL, hFE⟩ :=
      exists_unitary_semilinear_embedding_of_core_equiv p d hp hd L E hcomp hEodd c cQ hcQ
        φ hφtwo hφc M e0 hφ0 hi m hdiv eSU hcoeff eL
        (fun x => heL ⟨x.val.val, x.property⟩) fE hfEL hfEE
    refine ⟨Or.inr ⟨p, d, Fact.out, hp, hd, hKc, m, F, hF, hdiv, hFL, hFE⟩, ?_⟩
    apply Subgroup.exists_oddCore_sylowCentralizer_of_semilinear_model
      (GU2CoefficientAction p d hd) (SU2Level p d hd m) L E hcomp hEodd F hF hFL hFE
    · intro A hA
      exact exists_unitary_sylow_fixed_by_odd_coefficient_subgroup p d hp hd A hA m hdiv
    · let j := (unitaryForm 2 p d hd).unitarySubgroup.subtype.comp (SU2Level p d hd m).subtype
      apply model_sylow_centralizer hH L hLi eL j
        ((unitaryForm 2 p d hd).unitarySubgroup.subtype_injective.comp
          (SU2Level p d hd m).subtype_injective) m
      rintro x ⟨a, rfl⟩
      exact a.property

universe u

/-- ABG II.3 Proposition 3: the complete semilinear structure of a core-free Q-group. -/
public theorem qGroup_semilinear_structure
    {H : Type u} [Group H] [Finite H]
    (hQ : IsQGroup H) (hcore : pPrimeCore 2 H = ⊥)
    (L0 : Subgroup H) [L0.Normal]
    (F : Type u) [Field F] [Finite F] (hF : IsOddPrimePower (Nat.card F))
    (e0 : L0 ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    qSemilinearStructureConclusion L0 F := by
  classical
  obtain ⟨p, d, hp, hpodd, hd, hcard⟩ := hF
  let : Fact p.Prime := ⟨hp⟩
  have hd0 : d ≠ 0 := by omega
  let := Fintype.ofFinite F
  let := Fintype.ofFinite (GaloisField p d)
  let eF : GaloisField p d ≃+* F := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, GaloisField.card p d hd0] using hcard.symm)
  let H' := Shrink.{0} H
  let eH : H' ≃* H := Shrink.mulEquiv.{0} (α := H)
  let : Finite H' := Finite.of_injective eH eH.injective
  let L0' : Subgroup H' := L0.map eH.symm.toMonoidHom
  have hLn : L0'.Normal := (inferInstance : L0.Normal).map _ eH.symm.surjective
  let : L0'.Normal := hLn
  have hQ' : IsQGroup H' := (isQGroup_iff_of_mulEquiv eH).mpr hQ
  have hcore' : pPrimeCore 2 H' = ⊥ := by
    have hmap := pPrimeCore_map_iso 2 eH.symm
    rw [hcore, Subgroup.map_bot] at hmap
    exact hmap.symm
  let e0' : L0' ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p d) :=
    (eH.symm.subgroupMap L0).symm.trans (e0.trans (sl2RingEquiv eF.symm))
  have hcanonical := qGroup_semilinear_structure_galois hQ' hcore' L0' p d hpodd hd0 e0'
  have hresult := qSemilinearStructureConclusion_transport eH eF hcanonical
  have hL0 : L0'.map eH.toMonoidHom = L0 := by
    change (L0.map eH.symm.toMonoidHom).map eH.toMonoidHom = L0
    rw [Subgroup.map_map]
    have hid : eH.toMonoidHom.comp eH.symm.toMonoidHom = MonoidHom.id H := by
      ext x
      exact eH.apply_symm_apply x
    rw [hid, Subgroup.map_id]
  rwa [hL0] at hresult

end ABG
