module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalFieldFour
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# Excluding the normal-core unitary field-four overcomponent

A cubic scalar in the fixed field gives an actual diagonal element in the
whole U₄(4) flag overlap. Its action multiplies the central Heisenberg
coordinate by the square of that scalar, so it moves a central element of
the point two-core. Restricting the compatible parabolic isomorphisms to
their solvable residuals transports the same core and center to the original
K = O²(H). The degree-two extension uses the already proved index-two
reduction and then includes the reduced overlap into the original one.

For a proper maximal local overcomponent J normalizing Q = O₂(K), the
previous core equality and quotient sieve give O₂(J) = Q and quotient A₇
or its triple cover at q = 4. The whole N_G(K) normalizes J. Quasithinness
bounds the three-rank of N_G(J), forcing every cubic there into J. Since
J is perfect, it centralizes its elementary core center of order four,
contradicting the constructed cubic. Thus the normal-core field-four branch
is eliminated without assuming a torus actor or an overcomponent action.

The remaining unitary obstruction is genuine nonnormality of Q in J;
this module does not assert that it is impossible. The companion gives the
literal Chapter12 normalizer application. Other maximality rows, exhaustive
F.1.12 comparison, original uniqueness and ambient recognition remain with
the same global assembly.
Source: Aschbacher–Smith 5.2.8, printed pp.652–653, and F.1.12(I)(6),
pp.263–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourSylow UnitaryFourPointLocal
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFourCenter
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
  (σ : F ≃+* F) (hσ : Function.Involutive σ)

private def torusElement (a : Fˣ) : borelSU F (form F σ hσ) := by
  let d : Fin 4 → F := ![(a:F), (a:F)⁻¹, σ a, (σ a)⁻¹]
  have hd : (Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_diagonal]
    simp [d, Fin.prod_univ_succ]
  let g : SU F (form F σ hσ) :=
    ⟨GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d) (by rw [hd]; exact one_ne_zero),
      by
        change (form F σ hσ).conjTranspose (Matrix.diagonal d) * gram F *
          Matrix.diagonal d = gram F
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
            Fin.sum_univ_succ, d, hσ (a:F)],
      Units.ext hd⟩
  exact ⟨g,(mem_borel_iff_triangular F σ hσ g).mpr
    (Matrix.blockTriangular_diagonal d)⟩

private def torusHom : Fˣ →* borelSU F (form F σ hσ) where
  toFun a := torusElement F σ hσ a
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change Matrix.diagonal ![1,1⁻¹,σ 1,(σ 1)⁻¹] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change Matrix.diagonal ![((a*b:Fˣ):F),(a*b:Fˣ)⁻¹,σ (a*b:Fˣ),(σ (a*b:Fˣ))⁻¹] =
      Matrix.diagonal ![(a:F),(a:F)⁻¹,σ a,(σ a)⁻¹] *
        Matrix.diagonal ![(b:F),(b:F)⁻¹,σ b,(σ b)⁻¹]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_comm]

omit [CharP F 2] in
private theorem torusHom_injective : Function.Injective (torusHom F σ hσ) := by
  intro a b h
  exact Units.ext (congrArg (fun x : borelSU F (form F σ hσ) => x.val.val.val 0 0) h)

private theorem central_moved (a : Fˣ) (ha : a ≠ 1) (hfix : σ (a:F) = a) :
    ¬ Commute (torusElement F σ hσ a).val
      (centralElement F σ hσ 1).val.val := by
  intro hc
  have hh := congrArg (fun g : SU F (form F σ hσ) => g.val.val 0 3) hc.eq
  change (Matrix.diagonal ![(a:F),(a:F)⁻¹,σ a,(σ a)⁻¹] *
      radicalMatrix F σ ⟨0,0,1,_⟩) 0 3 =
    (radicalMatrix F σ ⟨0,0,1,_⟩ *
      Matrix.diagonal ![(a:F),(a:F)⁻¹,σ a,(σ a)⁻¹]) 0 3 at hh
  simp [Matrix.diagonal_mul,Matrix.mul_diagonal,radicalMatrix,hfix] at hh
  have hsq : (a:F)^2 = 1 := by
    calc (a:F)^2 = (a:F) * (a:F) := pow_two _
         _ = (a:F) * (a:F)⁻¹ := congrArg ((a:F) * ·) hh
         _ = 1 := mul_inv_cancel₀ a.ne_zero
  have hone : (a:F) = 1 := frobenius_inj F 2 (by simpa only [frobenius_def,one_pow] using hsq)
  exact ha (Units.ext hone)

open CFSG.Quasithin.ChapterF.GreenBook.LieModels.UnitaryFour

private theorem field_actor (hnt : ∃ u, σ u ≠ u)
    (hcard : Nat.card (FixedBy.subfield F σ) = 4) :
    ∃ x : SU F (form F σ hσ), x ∈ borelSU F (form F σ hσ) ∧
      orderOf x = 3 ∧ ∃ z : center (radical F σ hσ),
        ¬ Commute x z.val.val.val := by
  obtain ⟨a,ha⟩ : ∃ a : (FixedBy.subfield F σ)ˣ, orderOf a = 3 := by
    apply exists_prime_orderOf_dvd_card' 3
    rw [Nat.card_units,hcard]
  let f : (FixedBy.subfield F σ)ˣ →* Fˣ :=
    Units.map (FixedBy.subfield F σ).subtype.toMonoidHom
  have hf : Function.Injective f := Units.map_injective Subtype.val_injective
  let t := torusHom F σ hσ
  let c := centralElement F σ hσ 1
  have hc : c ∈ center (radical F σ hσ) :=
    (mem_center_radical_iff F σ hσ hnt c).mpr ⟨rfl,rfl⟩
  refine ⟨(t (f a)).val,(t (f a)).property,?_,⟨c,hc⟩,?_⟩
  · calc
      orderOf (t (f a)).val = orderOf (t (f a)) :=
        orderOf_injective (borelSU F (form F σ hσ)).subtype
          (borelSU F (form F σ hσ)).subtype_injective (t (f a))
      _ = orderOf (f a) := orderOf_injective t (torusHom_injective F σ hσ) (f a)
      _ = orderOf a := orderOf_injective f hf a
      _ = 3 := ha
  · exact central_moved F σ hσ (f a)
      (fun hh => by have := hf (hh.trans (map_one f).symm); simp [this] at ha)
      (a.val.property)

omit [Field F] [Finite F] [CharP F 2] in
private theorem model_actor :
    ∃ x : MatrixGroup 2 (Nat.le_succ 1), x ∈ overlapMatrix 2 (Nat.le_succ 1) ∧
      orderOf x = 3 ∧ ∃ z : center (PointLocal.Radical 2 (Nat.le_succ 1)),
        ¬ Commute x z.val.val.val :=
  field_actor (MatrixField 2) (fieldConj 2) (fieldConj_involutive 2 (Nat.le_succ 1))
    (PointLocal.fieldConj_nontrivial 2 (Nat.le_succ 1))
    (PointLocal.fixedField_card 2 (Nat.le_succ 1))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFourCenter

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFourCenter
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]

private theorem not_point_of_elementary_core {L P : Subgroup G}
    [IsElementaryAbelian 2 (pCore 2 L)]
    (hr : (solvableResidual P).map P.subtype = L)
    (e : P ≃* pointParabolic 2 (Nat.le_succ 1)) : False := by
  let a : solvableResidual P ≃* L :=
    ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr hr)
  let b : solvableResidual (pointParabolic 2 (Nat.le_succ 1)) ≃* PointLocal.ProjectiveLocal 2 (Nat.le_succ 1) :=
    ((solvableResidual (pointParabolic 2 (Nat.le_succ 1))).equivMapOfInjective
      (pointParabolic 2 (Nat.le_succ 1)).subtype (pointParabolic 2 (Nat.le_succ 1)).subtype_injective).trans
      (MulEquiv.subgroupCongr (PointLocal.pointParabolic_solvableResidual 2 (Nat.le_succ 1) (by decide)))
  let c := a.symm.trans (e.solvableResidualEquiv.trans b)
  let cq := (c.subgroupMap (pCore 2 L)).trans (MulEquiv.subgroupCongr (pCore_map_iso 2 c))
  let : IsElementaryAbelian 2 (pCore 2 (PointLocal.ProjectiveLocal 2 (Nat.le_succ 1))) :=
    IsElementaryAbelian.of_injective cq.symm.toMonoidHom cq.symm.injective
  exact PointLocal.projectiveTwoCore_commutator_ne_bot 2 (Nat.le_succ 1)
    ((commutator_eq_bot_iff _).mpr inferInstance)

private theorem pair_center_moved {P₀ P₁ K : Subgroup G}
    (hr : (solvableResidual P₁).map P₁.subtype = K)
    (he : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups P₀ (P₀ ⊓ P₁) P₁ inf_le_left inf_le_right)
      (amalgam 2 (Nat.le_succ 1)).reverse) :
    ∃ x : G, x ∈ P₀ ⊓ P₁ ∧ orderOf x = 3 ∧
      ∃ z ∈ centerIn (K.pCoreIn 2), ¬ Commute x z := by
  let e := he.trans (projectIso 2 (Nat.le_succ 1)).symm.reverse
  let f : P₁ →* MatrixGroup 2 (Nat.le_succ 1) :=
    (pointParabolicMatrix 2 (Nat.le_succ 1)).subtype.comp e.right.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.right.injective
  have hKP : K ≤ P₁ := hr ▸ map_subtype_le _
  have hK0 : K.subgroupOf P₁ = solvableResidual P₁ := by
    apply Subgroup.map_injective P₁.subtype_injective
    rw [map_subgroupOf_eq_of_le hKP,hr]
  have hmapK : (K.subgroupOf P₁).map f = PointLocal.MatrixLocal 2 (Nat.le_succ 1) := by
    rw [hK0,show f = (pointParabolicMatrix 2 (Nat.le_succ 1)).subtype.comp e.right.toMonoidHom from rfl,
      ←Subgroup.map_map,map_solvableResidual_eq e.right.toMonoidHom e.right.surjective]
    exact PointLocal.pointParabolicMatrix_solvableResidual 2 (Nat.le_succ 1) (by decide)
  have hmapQ : ((K.pCoreIn 2).subgroupOf P₁).map f =
      (PointLocal.MatrixLocal 2 (Nat.le_succ 1)).pCoreIn 2 := by
    rw [←pCoreIn_subgroupOf 2 K P₁ hKP,map_pCoreIn_of_injective 2 _ f hf,hmapK]
  have hQP : K.pCoreIn 2 ≤ P₁ := (map_subtype_le _).trans hKP
  obtain ⟨y,hy,ho,z,hmove⟩ := model_actor
  let x : (P₀ ⊓ P₁ : Subgroup G) := e.middle.symm ⟨y,hy⟩
  have hfx : f ⟨x.val,x.property.2⟩ = y := by
    have hh := e.right_commutes x
    rw [show e.middle x = ⟨y,hy⟩ from e.middle.apply_symm_apply _] at hh
    exact congrArg Subtype.val hh
  have hz : z.val.val.val ∈ centerIn ((PointLocal.MatrixLocal 2 (Nat.le_succ 1)).pCoreIn 2) := by
    change z.val.val.val ∈ centerIn ((pCore 2 (PointLocal.MatrixLocal 2 (Nat.le_succ 1))).map
      (PointLocal.MatrixLocal 2 (Nat.le_succ 1)).subtype)
    rw [←PointLocal.radical_eq_twoCore 2 (Nat.le_succ 1),centerIn_eq_map_center,
      ←map_embeddedCenter _ _ (PointLocal.MatrixLocal 2 (Nat.le_succ 1)).subtype_injective]
    exact ⟨z.val.val,⟨z.val,z.property,rfl⟩,rfl⟩
  obtain ⟨w,hw,hwz⟩ := (show z.val.val.val ∈ ((K.pCoreIn 2).subgroupOf P₁).map f from
    hmapQ.symm ▸ hz.1)
  have hwc : w.val ∈ centerIn (K.pCoreIn 2) := by
    refine ⟨hw,?_⟩
    intro q hq
    have hqf : f ⟨q,hQP hq⟩ ∈ (PointLocal.MatrixLocal 2 (Nat.le_succ 1)).pCoreIn 2 :=
      hmapQ ▸ mem_map_of_mem f (show (⟨q,hQP hq⟩:P₁) ∈ (K.pCoreIn 2).subgroupOf P₁ from hq)
    have hc := hz.2 _ hqf
    rw [←hwz,←map_mul,←map_mul] at hc
    exact congrArg Subtype.val (hf hc)
  refine ⟨x.val,x.property,?_,w.val,hwc,?_⟩
  · exact (orderOf_injective P₁.subtype P₁.subtype_injective ⟨x.val,x.property.2⟩).trans
      ((orderOf_injective f hf ⟨x.val,x.property.2⟩).symm.trans (by rw [hfx,ho]))
  · intro hc
    apply hmove
    rw [←hfx,←hwz]
    exact (show Commute (⟨x.val,x.property.2⟩:P₁) w from Subtype.ext hc.eq).map f

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.UnitaryFourCenter

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]

/-- The original whole unitary overlap contains a cubic moving the center
of the original right core, also in the degree-two extension. -/
theorem Preparation.unitary_four_center_moved
    {κ : GroupClass} {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input κ T L W n) (hTH : (T : Subgroup G) ≤ H)
    (hp : Group.IsPerfect (residual H))
    (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam 2 (Nat.le_succ 1))) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam 2 (Nat.le_succ 1)).reverse)) ∨
      (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam 2 (Nat.le_succ 1))) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam 2 (Nat.le_succ 1)).reverse))) :
    ∃ x : G, x ∈ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ∧
      orderOf x = 3 ∧ x ∈ normalizer (residual H : Set G) ∧
      ∃ z ∈ centerIn ((residual H).pCoreIn 2), ¬ Commute x z := by
  let : IsElementaryAbelian 2 (pCore 2 L) :=
    (d.unitary_core_structure h hTH hp 2 (Nat.le_succ 1) he).2.2.1
  have hpair (S : Subgroup G)
      (hr : ∀ i : Fin 2, (solvableResidual (ChapterF.Source.parabolic ![L,residual H] S i)).map
        (ChapterF.Source.parabolic ![L,residual H] S i).subtype = ![L,residual H] i)
      (he : Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,residual H] S)
        (amalgam 2 (Nat.le_succ 1))) ∨ Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] S) (amalgam 2 (Nat.le_succ 1)).reverse)) :
      ∃ x : G, x ∈ ChapterF.Source.parabolic ![L,residual H] S 0 ⊓
          ChapterF.Source.parabolic ![L,residual H] S 1 ∧ orderOf x = 3 ∧
        ∃ z ∈ centerIn ((residual H).pCoreIn 2), ¬ Commute x z := by
    rcases he with he | he
    · obtain ⟨e⟩ := he
      exact (UnitaryFourCenter.not_point_of_elementary_core (L := L) (hr 0) e.left).elim
    · obtain ⟨e⟩ := he
      exact UnitaryFourCenter.pair_center_moved (hr 1) e
  have hx : ∃ x : G, x ∈ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1 ∧ orderOf x = 3 ∧
      ∃ z ∈ centerIn ((residual H).pCoreIn 2), ¬ Commute x z := by
    rcases he with he | he
    · exact hpair _ (d.parabolic_residuals h hTH hp) he
    · obtain ⟨x,hx,ho,hz⟩ := hpair _
        (d.reduced_parabolic_residuals h hTH hp (.unitaryExtension 2 (Nat.le_succ 1) he))
        (d.unitaryExtension_reduced_amalgam h hTH hp 2 (by decide) he)
      have hle (i : Fin 2) : ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) i ≤
          ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i := by
        rw [d.reduced_source_parabolics h hTH hp (.unitaryExtension 2 (Nat.le_succ 1) he) i]
        exact map_subtype_le _
      exact ⟨x,⟨hle 0 hx.1,hle 1 hx.2⟩,ho,hz⟩
  obtain ⟨x,hx,ho,hz⟩ := hx
  exact ⟨x,hx,ho,((normal_subgroupOf_iff_le_normalizer
    (show residual H ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
      from le_sup_left.trans le_sup_left)).mp
        ((d.hypothesisF11 h hTH).local_normal_in_parabolic 1)) hx.2,hz⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
section Unitary
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ) (hm : 1 ≤ m)
  (he : (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (amalgam m hm).reverse)) ∨
    (Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (Extension.amalgam m hm).reverse)))
include d h hH hp m hm he

/-- The alternating field-four overcomponent is impossible: the original
cubic moves the center of its equal core, whereas every normalizer cubic
must fix that center. Thus only the genuinely nonnormal-core case remains. -/
theorem Preparation.unitary_maximal_or_nonnormal_core :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) ∨
      ∃ J ∈ Chapter1.LStar G (T : Subgroup G), residual H < J ∧
        ¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G) := by
  rcases d.unitary_maximal_or_alternating_obstruction h hH hp m hm he with hmax |
    ⟨J,hJ,hKJ,hn | ⟨hm2,_,hc,hs⟩⟩
  · exact .inl hmax
  · exact .inr ⟨J,hJ,hKJ,hn⟩
  subst m
  exfalso
  obtain ⟨_,_,_,_,_,hzK,_,_,heK,_⟩ := d.unitary_core_structure h hH.1.1.2 hp 2 hm he
  let e : pCore 2 J ≃* pCore 2 (residual H) :=
    ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).trans
      ((MulEquiv.subgroupCongr hc).trans
        ((pCore 2 (residual H)).equivMapOfInjective (residual H).subtype
          (residual H).subtype_injective).symm)
  let := heK
  let : IsElementaryAbelian 2 (center (pCore 2 J)) :=
    IsElementaryAbelian.of_injective (centerCongr e).toMonoidHom (centerCongr e).injective
  have hz : Nat.card (center (pCore 2 J)) = 4 :=
    (Nat.card_congr (centerCongr e).toEquiv).trans hzK
  have hf := he.elim (d.unitary_local_structure h hH.1.1.2 hp 2 hm)
    (d.unitaryExtension_local_structure h hH.1.1.2 hp 2 hm)
  have hK := residual_binary_mem_local hH.1.1 hp hf.1 hf.2.2.2.2
  have hnormal : J ≤ normalizer ((residual H).pCoreIn 2 : Set G) :=
    hc ▸ J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hNJ := (d.maximal_overcomponent_core_of_normal h hH.1.1.2 hp
    (he.elim (.unitary 2 hm) (.unitaryExtension 2 hm)) hK hJ hKJ.le hnormal).2
  obtain ⟨x,_,ho,hxN,z,hzQ,hmove⟩ := d.unitary_four_center_moved h hH.1.1.2 hp he
  exact hmove (maximal_seven_cubic_centralizes_core_center h.qtke hJ
    ((hH.1.1.2.trans (le_normalizer_residual H)).trans hNJ) hz hs (hNJ hxN) ho z (hc.symm ▸ hzQ))

/-- The original unitary normalizer pair satisfies the 5.3 local conditions
unless a maximal overcomponent fails to normalize the original two-core.
The field-four exclusions, common Sylow and enlarged cores are discharged. -/
theorem Preparation.unitary_normalizer_or_nonnormal_core :
    Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∨
      ∃ J ∈ Chapter1.LStar G (T : Subgroup G), residual H < J ∧
        ¬ J ≤ normalizer ((residual H).pCoreIn 2 : Set G) := by
  rcases d.unitary_maximal_or_nonnormal_core h hH hp m hm he with hmax | hh
  · left
    have hc : ConcreteAmalgamComparison
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) :=
      he.elim (.unitary m hm) (.unitaryExtension m hm)
    exact d.normalizer_local_conditions h hH hmax rfl
      (d.common_sylow_of_comparison h hH.1.1.2 hp hc)
      (d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp hc)
  · exact .inr hh
end Unitary
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
