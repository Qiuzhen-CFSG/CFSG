module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFullFactorAction
public import Theory.GroupTheory.PGroup.NormalChain
public import Theory.GroupTheory.GeneralizedFitting.CubicResidualOrder
public import Theory.Alternating.Aut
public import Theory.SpecificGroups.SymmetricTwoResidual

/-!
# Cubic normalization of the full marked factors

The original two-residual action and cubic residual normalization recover
the full S₃, L₃(2), and S₅ factors in N_G(Z_S)/O₂(N_G(Z_S)). For the symmetric
rows, two subnormal candidates with the same residual lie in a common
extension of that residual inside its normalizer. The normalizer contains
O²(I), hence is subnormal in the core-free centralizer image. The extension
has trivial two-core. Self-centralization of its residual and Aut(C₃) or
Aut(A₅) bound its order by six or 120, identifying both candidates. The
L₃(2) factor is already its own residual.

Apply the reconstruction to conjugation by each ambient cubic, restricting
to the same original centralizer image. The product image and the full
preimages in N_G(Z_S) are normalized as well. These full preimages explicitly
retain O₂(N_G(Z_S)); no normalization of a smaller lift inside P is inferred.

The Chapter 12 application preserves the literal W/Z_S action, both maps,
kernel identities, and product coordinates. This supplies the full quotient
factor action in Aschbacher–Smith 6.1.19, printed p.675. Single-factor reduction,
the parabolic/amalgam contradiction, initial 6.1.4–5, and the remaining escape
geometry stay with qt-d-1222-rankone-recognition-natural, the owner of
unconditional 6.1.27.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFullFactor
variable {A : Type*} [Group A] [Finite A]

private theorem subnormal_of_residual_le (K : Subgroup A) (hK : pResidual 2 A ≤ K) :
    K.IsSubnormal := by
  let q := QuotientGroup.mk' (pResidual 2 A)
  have hh := ((isPGroup_quotient_pResidual (G:=A) 2).subgroup_isSubnormal (K.map q)).comap q
  simpa only [comap_map_eq,q,QuotientGroup.ker_mk',sup_eq_left.mpr hK] using hh

private theorem subnormal_core_zero (hc : pCore 2 A = ⊥)
    (K : Subgroup A) (hK : K.IsSubnormal) : pCore 2 K = ⊥ := by
  rw [pCore_subnormal_eq_comap 2 hK,hc]
  exact (MonoidHom.ker_eq_bot_iff K.subtype).mpr K.subtype_injective

private theorem subnormal_two_le_core (K : Subgroup A) (hK : K.IsSubnormal)
    (hp : IsPGroup 2 K) : K ≤ pCore 2 A := by
  have ht : pCore 2 K = ⊤ := top_unique (le_sSup ⟨inferInstance,hp.to_subgroup ⊤⟩)
  have hh := pCoreIn_le_of_subnormal 2 hK
  change (pCore 2 K).map K.subtype ≤ _ at hh
  rwa [ht,←MonoidHom.range_eq_map,range_subtype] at hh

/-- Two subnormal subgroups with the same two-residual fit in one core-free
extension of that residual when the ambient two-residual normalizes it. -/
private theorem common_extension (X Y : Subgroup A)
    (hX : X.IsSubnormal) (hY : Y.IsSubnormal) (hc : pCore 2 A = ⊥)
    (he : (pResidual 2 X).map X.subtype = (pResidual 2 Y).map Y.subtype)
    (hn : pResidual 2 A ≤ normalizer ((pResidual 2 X).map X.subtype : Set A)) :
    ∃ J : Subgroup A, X ≤ J ∧ Y ≤ J ∧ pCore 2 J = ⊥ ∧
      (pResidual 2 J).map J.subtype = (pResidual 2 X).map X.subtype := by
  let D := (pResidual 2 X).map X.subtype
  let K := normalizer (D : Set A)
  have hK : K.IsSubnormal := subnormal_of_residual_le K hn
  have hDK : D ≤ K := D.le_normalizer
  have hXK : X ≤ K := (X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pResidual 2 X)))
  have hYK : Y ≤ K := by
    change Y ≤ normalizer ((pResidual 2 X).map X.subtype : Set A)
    rw [he]
    exact Y.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image Y (pResidual 2 Y))
  let D' := D.subgroupOf K
  let : D'.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let q := QuotientGroup.mk' D'
  let J' := (pCore 2 (K ⧸ D')).comap q
  let J := J'.map K.subtype
  have hD'J : D' ≤ J' := fun x hx => by
    change q x ∈ pCore 2 (K ⧸ D')
    rw [show q x=1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hDJ : D ≤ J := by
    have hh := map_mono (f:=K.subtype) hD'J
    change (D.subgroupOf K).map K.subtype ≤ J at hh
    rwa [map_subgroupOf_eq_of_le hDK] at hh
  have hIJ (Z : Subgroup A) (hZK : Z ≤ K) (hZ : Z.IsSubnormal)
      (hr : (pResidual 2 Z).map Z.subtype = D) : Z ≤ J := by
    let f := q.comp (inclusion hZK)
    have hk : pResidual 2 Z ≤ f.ker := by
      intro z hz
      apply (QuotientGroup.eq_one_iff _).mpr
      change (z:A) ∈ D
      rw [←hr]
      exact mem_map_of_mem Z.subtype hz
    let fq := QuotientGroup.lift (pResidual 2 Z) f hk
    have hp : IsPGroup 2 f.range := by
      have heq : fq.range = f.range := by
        have hh := congrArg MonoidHom.range
          (show fq.comp (QuotientGroup.mk' (pResidual 2 Z)) = f from rfl)
        rwa [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
          ←MonoidHom.range_eq_map] at hh
      exact heq ▸ (isPGroup_quotient_pResidual (G:=Z) 2).of_surjective
        fq.rangeRestrict fq.rangeRestrict_surjective
    have hfn : f.range.IsSubnormal := by
      have hh := hZ.subgroupOf.map (QuotientGroup.mk'_surjective D')
      have hf : f.range = (Z.subgroupOf K).map q := by
        rw [MonoidHom.range_comp]
        congr 1
        ext z
        constructor
        · rintro ⟨w,hw⟩
          change (z:A) ∈ Z
          have hh : (w:A) = (z:A) := congrArg Subtype.val hw
          exact hh ▸ w.property
        · intro hz; exact ⟨⟨z,hz⟩,rfl⟩
      rwa [hf]
    have hm := subnormal_two_le_core f.range hfn hp
    intro z hz
    exact ⟨⟨z,hZK hz⟩,hm ⟨⟨z,hz⟩,rfl⟩,rfl⟩
  have hXJ : X ≤ J := hIJ X hXK hX rfl
  have hYJ : Y ≤ J := hIJ Y hYK hY he.symm
  have hJn : J.IsSubnormal := (inferInstance : J'.Normal).isSubnormal.trans' hK
  have hr : (pResidual 2 J).map J.subtype = D := by
    apply le_antisymm
    · let e : J' ≃* J := J'.equivMapOfInjective K.subtype K.subtype_injective
      have hq : pResidual 2 J' ≤ (q.comp J'.subtype).ker := by
        let f := (q.comp J'.subtype).codRestrict (pCore 2 (K ⧸ D')) (fun x => x.property)
        exact fun x hx => congrArg Subtype.val (pResidual_le_ker_of_isPGroup 2 f pCore_isPGroup hx)
      rw [←map_pResidual_of_surjective 2 e.toMonoidHom e.surjective,map_map]
      rintro _ ⟨x,hx,rfl⟩
      change (x.val:A) ∈ D
      exact (QuotientGroup.eq_one_iff (N:=D') x.val).mp (hq hx)
    · exact (show D = (pResidual 2 X).map X.subtype from rfl) ▸
        embedded_pResidual_mono 2 hXJ
  exact ⟨J,hXJ,hYJ,subnormal_core_zero hc J hJn,hr⟩

private theorem card_le_of_alternating_residual
    (hc : pCore 2 A = ⊥) (e : pResidual 2 A ≃* alternatingGroup (Fin 5)) :
    Nat.card A ≤ 120 := by
  let D := pResidual 2 A
  have hz : center D = ⊥ := by
    apply eq_bot_iff.mpr
    intro z hz
    have he : e z ∈ center (alternatingGroup (Fin 5)) :=
      (centerCongr e ⟨z,hz⟩).property
    rw [alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 5))] at he
    exact e.map_eq_one_iff.mp he
  let f : A →* MulAut D := MulAut.conjNormal
  have hk : f.ker = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hxD : x ∈ D := centralizer_pResidual_le_of_pCore_eq_bot hc
      (by simpa only [f,MulAut.conjNormal_ker_eq_centralizer] using hx)
    have hxc : (⟨x,hxD⟩ : D) ∈ center D := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact (show x ∈ centralizer (D : Set A) from by
        simpa only [f,MulAut.conjNormal_ker_eq_centralizer] using hx) y y.property
    exact congrArg Subtype.val (hz.le hxc)
  have h := Nat.card_le_card_of_injective f ((MonoidHom.ker_eq_bot_iff f).mp hk)
  have hcard : Nat.card (MulAut D) = 120 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    let a : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
      MulEquiv.ofBijective _ (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
        5 (by decide) (by decide))
    rw [←Nat.card_congr a.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm]
    rfl
  exact h.trans_eq hcard

private def residualEquiv {B : Type*} [Group B] (e : A ≃* B) :
    pResidual 2 A ≃* pResidual 2 B :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr
    (map_pResidual_of_surjective 2 e.toMonoidHom e.surjective))

private def residualEquivOfImage (X Y : Subgroup A)
    (he : (pResidual 2 X).map X.subtype = (pResidual 2 Y).map Y.subtype) :
    pResidual 2 X ≃* pResidual 2 Y :=
  ((pResidual 2 X).equivMapOfInjective X.subtype X.subtype_injective).trans
    ((MulEquiv.subgroupCongr he).trans
      ((pResidual 2 Y).equivMapOfInjective Y.subtype Y.subtype_injective).symm)

/-- The full S₃ or S₅ is recovered from its two-residual inside a core-free
ambient group, provided the ambient two-residual normalizes the factor. -/
theorem symmetric_eq_of_residual_eq (X Y : Subgroup A)
    (hX : X.IsSubnormal) (hY : Y.IsSubnormal) (hc : pCore 2 A = ⊥)
    (he : (pResidual 2 X).map X.subtype = (pResidual 2 Y).map Y.subtype)
    (hn : pResidual 2 A ≤ normalizer (X : Set A))
    (hm : Nonempty (X ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (X ≃* Equiv.Perm (Fin 5)))
    (hcard : Nat.card X = Nat.card Y) : X = Y := by
  obtain ⟨J,hXJ,hYJ,hcJ,hrJ⟩ := common_extension X Y hX hY hc he
    (hn.trans (normalizer_le_normalizer_characteristic_image X (pResidual 2 X)))
  have hb : Nat.card J ≤ Nat.card X := by
    rcases hm with h3 | h5
    · obtain ⟨e⟩ := h3
      have hr : Nat.card (pResidual 2 J) = 3 := by
        rw [Nat.card_congr (residualEquivOfImage J X hrJ).toEquiv,
          Nat.card_congr (residualEquiv e).toEquiv]
        exact Theory.SpecificGroups.SymmetricThree.CubicSelection.residual_card
      have hh := card_le_six_of_core_free_cubic_residual hcJ hr
      simpa only [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,
        Fintype.card_fin,show Nat.factorial 3 = 6 from rfl,show Nat.factorial 5 = 120 from rfl] using hh
    · obtain ⟨e⟩ := h5
      let f := (residualEquivOfImage J X hrJ).trans ((residualEquiv e).trans
        (MulEquiv.subgroupCongr (Equiv.Perm.twoResidual_eq_alternating (Fin 5))))
      have hh := card_le_of_alternating_residual hcJ f
      simpa only [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,
        Fintype.card_fin,show Nat.factorial 3 = 6 from rfl,show Nat.factorial 5 = 120 from rfl] using hh
  exact (eq_of_le_of_card_ge hXJ hb).trans
    (eq_of_le_of_card_ge hYJ (hcard ▸ hb)).symm

/-- An actual automorphism fixing the residual fixes a full marked factor.
The O² action hypothesis is used to reconstruct the full symmetric rows. -/
theorem fixed_of_residual_fixed (X : Subgroup A) (hX : X.IsSubnormal)
    (hc : pCore 2 A = ⊥) (hn : pResidual 2 A ≤ normalizer (X : Set A))
    (hm : Nonempty (X ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (X ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
      Nonempty (X ≃* Equiv.Perm (Fin 5)))
    (e : MulAut A)
    (he : ((pResidual 2 X).map X.subtype).map e.toMonoidHom =
      (pResidual 2 X).map X.subtype) : X.map e.toMonoidHom = X := by
  rcases hm with h3 | hlin | h5
  · exact (symmetric_eq_of_residual_eq X (X.map e.toMonoidHom) hX
      (hX.map e.surjective) hc ((map_embedded_pResidual 2 X e.toMonoidHom).symm.trans he).symm
      hn (Or.inl h3) (card_map_of_injective e.injective).symm).symm
  · obtain ⟨f⟩ := hlin
    let E := f.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)).symm
    let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :=
      Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup X := E.isSimpleGroup
    let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
      (f:=E.symm.toMonoidHom) E.symm.surjective
    have hle : solvableResidual X ≤ pResidual 2 X := by
      apply le_sInf
      rintro D ⟨hD,hp⟩
      let := hD
      let : Group.IsNilpotent (X ⧸ D) := hp.isNilpotent
      exact solvableResidual_le_of_solvable_quotient D
    have hr : pResidual 2 X = ⊤ := top_unique
      ((solvableResidual_eq_top (G:=X)) ▸ hle)
    simpa only [hr,←MonoidHom.range_eq_map,range_subtype] using he
  · exact (symmetric_eq_of_residual_eq X (X.map e.toMonoidHom) hX
      (hX.map e.surjective) hc ((map_embedded_pResidual 2 X e.toMonoidHom).symm.trans he).symm
      hn (Or.inr h5) (card_map_of_injective e.injective).symm).symm

/-- Restrict the reconstruction to the original normal subgroup, then return
to the ambient conjugation action. -/
theorem normalizes_of_normalizes_residual
    (I X : Subgroup A) (hI : I.Normal) (hXI : X ≤ I)
    (hX : X.IsSubnormal) (hc : pCore 2 I = ⊥)
    (hn : (pResidual 2 I).map I.subtype ≤ normalizer (X : Set A))
    (hm : Nonempty (X ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (X ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
      Nonempty (X ≃* Equiv.Perm (Fin 5)))
    (c : A) (hd : c ∈ normalizer ((pResidual 2 X).map X.subtype : Set A)) :
    c ∈ normalizer (X : Set A) := by
  let := hI
  let α : MulAut I := MulAut.conjNormal c
  let X' := X.subgroupOf I
  let D' := (pResidual 2 X').map X'.subtype
  have hDX : D'.map I.subtype = (pResidual 2 X).map X.subtype := by
    rw [map_embedded_pResidual,map_subgroupOf_eq_of_le hXI]
  have hcomp : I.subtype.comp α.toMonoidHom =
      (MulAut.conj c).toMonoidHom.comp I.subtype := rfl
  have hfix : D'.map α.toMonoidHom = D' := by
    apply map_injective I.subtype_injective
    rw [map_map,hcomp,←map_map,hDX]
    exact mem_normalizer_iff_map_conj_eq.mp hd
  have hact : pResidual 2 I ≤ normalizer (X' : Set I) := by
    rw [←subgroupOf_normalizer_eq hXI]
    exact fun x hx => hn (mem_map_of_mem I.subtype hx)
  have hmodels : Nonempty (X' ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (X' ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
      Nonempty (X' ≃* Equiv.Perm (Fin 5)) := by
    rcases hm with h3 | hlin | h5
    · obtain ⟨e⟩ := h3
      exact Or.inl ⟨(subgroupOfEquivOfLe hXI).trans e⟩
    · obtain ⟨e⟩ := hlin
      exact Or.inr (Or.inl ⟨(subgroupOfEquivOfLe hXI).trans e⟩)
    · obtain ⟨e⟩ := h5
      exact Or.inr (Or.inr ⟨(subgroupOfEquivOfLe hXI).trans e⟩)
  have hh := fixed_of_residual_fixed X' hX.subgroupOf hc hact hmodels α hfix
  have hh := congrArg (map I.subtype) hh
  rw [map_map,hcomp,←map_map,map_subgroupOf_eq_of_le hXI] at hh
  exact mem_normalizer_iff_map_conj_eq.mpr hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFullFactor

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterG.Section06
universe v
/-- The original residual action and cubic residual normalization reconstruct
every full factor inside the same ambient quotient. -/
theorem SmallTransvectionProductModel.cubic_normalizes_full_preimages
    {B V : Type v} {H N : Type*}
    [Group B] [Finite B] [AddCommGroup V] [Module (ZMod 2) V]
    [Group H] [Finite H] [Group N] [Finite N]
    {ρ : Representation (ZMod 2) B V} (product : SmallTransvectionProductModel ρ)
    (φ : H →* B) (hφ : Function.Bijective φ)
    (j : H →* N) (hj : Function.Injective j) (hjn : j.range.IsSubnormal)
    (Q : Subgroup N) (hQ : Q.Normal) (hcore : pCore 2 Q = ⊥)
    (hjQ : j.range ≤ Q)
    (hact : ∀ K ∈ product.factors,
      (pResidual 2 Q).map Q.subtype ≤ normalizer ((K.comap φ).map j : Set N))
    (hres : ∀ K ∈ product.factors, ∀ c : N, c^3=1 →
      c ∈ normalizer ((((pResidual 2 (K.comap φ)).map (K.comap φ).subtype).map j) : Set N)) :
    ∀ K ∈ product.factors, ∀ c : N, c^3=1 →
      c ∈ normalizer ((K.comap φ).map j : Set N) := by
  intro K hK c hc
  let X := (K.comap φ).map j
  have hKn : K.Normal := by
    obtain ⟨t,_,rfl,_⟩ := product.marked K hK
    infer_instance
  let := hKn
  have hX : X.IsSubnormal := by
    have hh := ((inferInstance : (K.comap φ).Normal).isSubnormal.map
      j.rangeRestrict_surjective).trans' hjn
    simpa only [map_map,MonoidHom.subtype_comp_rangeRestrict] using hh
  have hXQ : X ≤ Q := (map_le_range _ _).trans hjQ
  let eH : K.comap φ ≃* K := MulEquiv.ofBijective (φ.subgroupComap K)
    ⟨fun x y he => Subtype.ext (hφ.1 (congrArg Subtype.val he)),
      φ.subgroupComap_surjective_of_surjective K hφ.2⟩
  let eX : X ≃* K := ((K.comap φ).equivMapOfInjective j hj).symm.trans eH
  have hm : Nonempty (X ≃* Equiv.Perm (Fin 3)) ∨
      Nonempty (X ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
      Nonempty (X ≃* Equiv.Perm (Fin 5)) := by
    obtain ⟨U,hmodel⟩ := product.small K hK
    rcases hmodel with ⟨e,_,_⟩ | ⟨e,_,_⟩ | ⟨e,_,_⟩
    · exact Or.inl ⟨eX.trans (e.trans ((BinaryLinear.OuterCyclic.slEquivLinear 2).symm.trans
        (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)))⟩
    · exact Or.inr (Or.inl ⟨eX.trans e⟩)
    · exact Or.inr (Or.inr ⟨eX.trans e⟩)
  apply NaturalFullFactor.normalizes_of_normalizes_residual Q X hQ hXQ hX hcore
    (hact K hK) hm c
  have hh := hres K hK c hc
  rwa [map_embedded_pResidual] at hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition


namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe v
/-- Factorwise normalization preserves the whole original product image. -/
theorem SmallTransvectionProductModel.normalizes_range_of_full_factors
    {B V : Type v} {H N : Type*}
    [Group B] [AddCommGroup V] [Module (ZMod 2) V] [Group H] [Group N]
    {ρ : Representation (ZMod 2) B V} (product : SmallTransvectionProductModel ρ)
    (φ : H →* B) (hφ : Function.Bijective φ) (j : H →* N)
    (c : N) (hc : ∀ K ∈ product.factors,
      c ∈ normalizer ((K.comap φ).map j : Set N)) :
    c ∈ normalizer (j.range : Set N) := by
  let e := MulEquiv.ofBijective φ hφ
  have he (K : Subgroup B) : K.comap φ = K.map e.symm.toMonoidHom :=
    comap_equiv_eq_map_symm e K
  have hjoin : (⨆ K : {K // K ∈ product.factors}, (K.val.comap φ).map j) = j.range := by
    simp_rw [he,←Subgroup.map_iSup]
    rw [product.join_eq,map_top_of_surjective _ e.symm.surjective,
      ←MonoidHom.range_eq_map]
  rw [←hjoin]
  exact iInf_normalizer_le_normalizer_iSup _
    (mem_iInf.mpr fun K => hc K.val K.property)

/-- Normalization in the actual quotient lifts to its full preimage. This
explicitly retains the ambient two-core in the lifted subgroup. -/
theorem quotient_normalizes_full_preimage
    {N : Type*} [Group N] (H : Subgroup (N ⧸ pCore 2 N)) (c : N)
    (hc : QuotientGroup.mk' (pCore 2 N) c ∈ normalizer (H : Set (N ⧸ pCore 2 N))) :
    c ∈ normalizer (H.comap (QuotientGroup.mk' (pCore 2 N)) : Set N) := by
  apply mem_normalizer_iff.mpr
  intro x
  change QuotientGroup.mk' (pCore 2 N) x ∈ H ↔
    QuotientGroup.mk' (pCore 2 N) (c*x*c⁻¹) ∈ H
  simp only [map_mul,map_inv]
  exact mem_normalizer_iff.mp hc _

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Classical
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe v
open CFSG.Quasithin.ChapterE
variable {G : Type v} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
namespace NaturalEscapeGraph.OddConfiguration
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d

/-- Every ambient cubic normalizes every full factor. All actions, residuals,
covering maps and product coordinates retain the original W/Z_S witness. -/
theorem exists_ambient_cubic_full_product
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let N := Escape.H (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N) (hIN : I ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      let := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        let := hX
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Bijective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧ g.ker = pCore 2 P ∧
          closure {x : P ⧸ pCore 2 P | x ^ 2 = 1} = ⊤ ∧
          let θ := Representation.ofElementaryAbelianAction
            (A := g.range) (G := W ⧸ Z.subgroupOf W) (p := 2)
          ∃ product : SmallTransvectionProductModel θ,
            (∀ K ∈ product.factors, FactorResidualLift φ j
              ((I.subgroupOf N).map (QuotientGroup.mk' (pCore 2 N))) K ∧
              ∀ c : N ⧸ pCore 2 N, c^3=1 →
                c ∈ Subgroup.normalizer ((((pResidual 2 (K.comap φ)).map
                  (K.comap φ).subtype).map j) : Set (N ⧸ pCore 2 N))) ∧
            (∀ K ∈ product.factors,
              ((pResidual 2 I).map (inclusion hIN)).map (QuotientGroup.mk' (pCore 2 N)) ≤
                Subgroup.normalizer ((K.comap φ).map j : Set (N ⧸ pCore 2 N)) ∧
              (pResidual 2 I).map I.subtype ≤ Subgroup.normalizer
                ((((K.comap φ).comap (QuotientGroup.mk' (pCore 2 P))).map P.subtype) : Set G)) ∧
            (∀ K ∈ product.factors, ∀ c : N ⧸ pCore 2 N, c^3=1 →
              c ∈ Subgroup.normalizer ((K.comap φ).map j : Set (N ⧸ pCore 2 N))) ∧
            (∀ c : N ⧸ pCore 2 N, c^3=1 →
              c ∈ Subgroup.normalizer (j.range : Set (N ⧸ pCore 2 N))) ∧
            (∀ K ∈ product.factors, ∀ c : N, c^3=1 →
              c ∈ Subgroup.normalizer (((K.comap φ).map j).comap
                (QuotientGroup.mk' (pCore 2 N)) : Set N)) ∧
            ∃ e : (∀ K : {K // K ∈ product.factors}, K.val) ≃* (P ⧸ pCore 2 P),
              (∀ x, φ (e x) = product.productEquiv x) ∧
              (∀ K : {K // K ∈ product.factors}, ∀ a : P ⧸ pCore 2 P,
                a ∈ K.val.comap φ ↔ ∃ x : K.val,
                  e (Function.update 1 K x) = a) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hgen,product,hres,hact,e,he,hcoords⟩ :=
    d.exists_ambient_full_factor_action h hnat hE hs hNS hab
  let I := Escape.I (T : Subgroup G) L R
  let N := Escape.H (T : Subgroup G) L R
  let E := (layer L R).map (MulAut.conj a).toMonoidHom
  let P := conjugateSpanBy E I
  let q := QuotientGroup.mk' (pCore 2 N)
  let Q := (I.subgroupOf N).map q
  let : (I.subgroupOf N).Normal :=
    normal_subgroupOf_centralizer_normalizer (ZS (T : Subgroup G) L R : Set G)
  let : Q.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hcore : pCore 2 Q = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : Q.Normal).isSubnormal,
      pCore_quotient_pCore_eq_bot]
    exact (MonoidHom.ker_eq_bot_iff Q.subtype).mpr Q.subtype_injective
  have hjQ : j.range ≤ Q := by
    rintro _ ⟨p,rfl⟩
    obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 P) p
    rw [hje]
    exact mem_map_of_mem q (show inclusion hPN p ∈ I.subgroupOf N from hPI p.property)
  have hresI : (pResidual 2 Q).map Q.subtype =
      ((pResidual 2 I).map (inclusion hIN)).map q := by
    have hf : (I.subgroupOf N).map q = (⊤ : Subgroup I).map (q.comp (inclusion hIN)) := by
      ext x
      constructor
      · rintro ⟨i,hi,rfl⟩
        exact ⟨⟨i,hi⟩,mem_top _,rfl⟩
      · rintro ⟨i,_,rfl⟩
        exact ⟨inclusion hIN i,i.property,rfl⟩
    let f := q.comp (inclusion hIN)
    have hfQ : f.range = Q := by
      rw [MonoidHom.range_eq_map]
      exact hf.symm
    have hh := map_embedded_pResidual 2 (⊤ : Subgroup I) f
    have ht : (pResidual 2 (⊤ : Subgroup I)).map (⊤ : Subgroup I).subtype =
        pResidual 2 I :=
      map_pResidual_of_surjective 2 (topEquiv (G:=I)).toMonoidHom (topEquiv (G:=I)).surjective
    rw [ht,←MonoidHom.range_eq_map,hfQ] at hh
    exact hh.symm.trans (map_map _ _ _).symm
  let := hZ
  let := hX
  have hfull := product.cubic_normalizes_full_preimages φ hφ j hj hjn Q
    inferInstance hcore hjQ (fun K hK => by rw [hresI]; exact (hact K hK).1)
    (fun K hK => (hres K hK).2)
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hgen,product,hres,hact,hfull,?_,?_,e,he,hcoords⟩
  · intro c hc
    exact product.normalizes_range_of_full_factors φ hφ j c (fun K hK => hfull K hK c hc)
  · intro K hK c hc
    exact quotient_normalizes_full_preimage _ c (hfull K hK _ (by rw [←map_pow,hc,map_one]))

end NaturalEscapeGraph.OddConfiguration
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
