module
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder.FixedEndpoint
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.SylowKernelCore
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation

/-!
# The compatible binary fixed pair and normal two-kernels

The six-letter parabolic recognition, transported through the actual polar
representation, identifies the two residual cores in Sp4(2). Both lie in
the common Borel and generate D8 with nontrivial intersection. An isomorphism
of the full amalgam carries both cores through its single middle map, so
this conclusion holds in every faithful realization of the fixed pair.
The full endpoint cores are elementary abelian, excluding containment of
either residual four-group in the opposite endpoint core.

Minimality of a residual core then forces it to avoid any two-subgroup
normalized by both endpoints. The central half-turn calculation in D8
extends this to the whole join when the kernel is normal there.

Source: Aschbacher--Smith F.4.37, printed p.293 of refs/quasithin.pdf.
Chapter6's SymplecticExtensionOrder.FixedPair applies these results to the
original fixed endpoints and the actual conjugate full-normalizer quotient.
The further placement in its PSL2(4) section is a separate obligation.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder

private theorem map_core {X Y : Type*} [Group X] [Group Y]
    (e : X ≃* Y) (L : Subgroup X) :
    (L.pCoreIn 2).map e.toMonoidHom = (L.map e.toMonoidHom).pCoreIn 2 := by
  let eL : L ≃* L.map e.toMonoidHom := e.subgroupMap L
  rw [pCoreIn,pCoreIn,←pCore_map_iso 2 eL,map_map,map_map]
  rfl

private theorem residual_core_le_sylow {X : Type*} [Group X]
    (P : Subgroup X) (S : Sylow 2 P) :
    ((pResidual 2 P).map P.subtype).pCoreIn 2 ≤ (S : Subgroup P).map P.subtype :=
  (pCoreIn_mono_of_normalizes (map_subtype_le _) (le_normalizer_embedded_pResidual 2 P)).trans
    (pCoreIn_le_sylow P S)

private theorem residual_pair_transport {X : Type*} [Group X] [Finite X]
    (e : X ≃* Theory.SpecificGroups.SymmetricSix.S6)
    (S : Sylow 2 X) (P Q : Subgroup X)
    (hSP : (S : Subgroup X) ≤ P) (hSQ : (S : Subgroup X) ≤ Q)
    (hiP : (S : Subgroup X).relIndex P=3) (hiQ : (S : Subgroup X).relIndex Q=3)
    (hgen : P ⊔ Q=⊤) :
    let U := ((pResidual 2 P).map P.subtype).pCoreIn 2
    let V := ((pResidual 2 Q).map Q.subtype).pCoreIn 2
    Nonempty (↥(U ⊔ V) ≃* DihedralGroup 4) ∧ U ⊓ V≠⊥ := by
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hgen' : P.map e.toMonoidHom ⊔ Q.map e.toMonoidHom=⊤ := by
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ e.surjective]
  obtain ⟨_,_,_,_,hj,hint⟩ :=
    Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.residual_pair_recognition
      S' (P.map e.toMonoidHom) (Q.map e.toMonoidHom) (map_mono hSP) (map_mono hSQ)
      ((relIndex_map_map_of_injective _ _ e.injective).trans hiP)
      ((relIndex_map_map_of_injective _ _ e.injective).trans hiQ) hgen'
  dsimp only at hj hint ⊢
  rw [←map_embedded_pResidual 2 P e.toMonoidHom,
    ←map_embedded_pResidual 2 Q e.toMonoidHom,←map_core e,←map_core e,
    ←Subgroup.map_sup] at hj
  rw [←map_embedded_pResidual 2 P e.toMonoidHom,
    ←map_embedded_pResidual 2 Q e.toMonoidHom,←map_core e,←map_core e,
    ←Subgroup.map_inf _ _ e.toMonoidHom e.injective] at hint
  refine ⟨⟨(e.subgroupMap _).trans hj.some⟩,?_⟩
  intro hh
  exact hint (by rw [hh,Subgroup.map_bot])

/-- The two residual cores in the binary matrix parabolics lie in their
whole common Borel and generate the actual dihedral group of order eight. -/
theorem binary_residual_core_pair :
    let P := pointParabolic (F := ZMod 2)
    let Q := planeParabolic (F := ZMod 2)
    let U := ((pResidual 2 P).map P.subtype).pCoreIn 2
    let V := ((pResidual 2 Q).map Q.subtype).pCoreIn 2
    U ≤ borel ∧ V ≤ borel ∧
      Nonempty (↥(U ⊔ V) ≃* DihedralGroup 4) ∧ U ⊓ V≠⊥ := by
  let S := unipotentSylow (F := ZMod 2) (n := 1) (by norm_num) (by decide)
  have hSP : (S : Subgroup (Sp (ZMod 2))) ≤ pointParabolic :=
    unipotent_le_borel.trans inf_le_left
  have hSQ : (S : Subgroup (Sp (ZMod 2))) ≤ planeParabolic :=
    unipotent_le_borel.trans inf_le_right
  have hS : Nat.card S=16 := by
    change Nat.card (unipotent (F := ZMod 2))=16
    rw [card_unipotent]
    norm_num
  have hi (P : Subgroup (Sp (ZMod 2))) (hSP : (S : Subgroup (Sp (ZMod 2)))≤P)
      (hP : Nat.card P=48) : (S : Subgroup (Sp (ZMod 2))).relIndex P=3 := by
    have hc := ((S : Subgroup (Sp (ZMod 2))).subgroupOf P).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hSP).toEquiv,hS,hP] at hc
    change ((S : Subgroup (Sp (ZMod 2))).subgroupOf P).index=3
    omega
  have hcP : Nat.card (pointParabolic (F := ZMod 2))=48 := by
    rw [Nat.card_congr Binary.pointParabolicZModEquivProd.toEquiv]
    norm_num [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_perm]
  have hcQ : Nat.card (planeParabolic (F := ZMod 2))=48 := by
    rw [Nat.card_congr Binary.planeParabolicZModEquivProd.toEquiv]
    norm_num [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_perm]
  have hU := residual_core_le_sylow pointParabolic (S.subtype hSP)
  have hV := residual_core_le_sylow planeParabolic (S.subtype hSQ)
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSP] at hU
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSQ] at hV
  exact ⟨hU.trans unipotent_le_borel,hV.trans unipotent_le_borel,
    residual_pair_transport Binary.symmetricSixEquiv.symm S _ _ hSP hSQ
      (hi _ hSP hcP) (hi _ hSQ hcQ) parabolics_sup_eq_top⟩

private theorem middle_image {X Y : Type*} [Group X] [Group Y]
    {P B : Subgroup X} {R C : Subgroup Y} (hBP : B≤P) (hCR : C≤R)
    (e : P ≃* R) (b : B ≃* C)
    (he : ∀ x : B, e (inclusion hBP x)=inclusion hCR (b x))
    (A : Subgroup P) (K : Subgroup Y) (hKC : K≤C)
    (hA : A.map (R.subtype.comp e.toMonoidHom)=K) :
    A.map P.subtype=(K.subgroupOf C).map (B.subtype.comp b.symm.toMonoidHom) := by
  let β := B.subtype.comp b.symm.toMonoidHom
  have hval (p : P) (u : C) (hp : (e p).val=u.val) : β u=p.val := by
    have hh := he (b.symm u)
    rw [b.apply_symm_apply] at hh
    have hh' : e (inclusion hBP (b.symm u))=e p :=
      hh.trans (Subtype.ext hp.symm)
    exact congrArg Subtype.val (e.injective hh')
  apply le_antisymm
  · rintro x ⟨p,hp,rfl⟩
    have hk : (e p).val∈K := hA ▸ mem_map_of_mem _ hp
    exact ⟨⟨(e p).val,hKC hk⟩,hk,hval p _ rfl⟩
  · rintro x ⟨u,hu,rfl⟩
    obtain ⟨p,hp,he⟩ := (show u.val∈A.map (R.subtype.comp e.toMonoidHom) by
      rw [hA]; exact hu)
    exact (hval p u he) ▸ mem_map_of_mem P.subtype hp

private theorem residual_core_middle_image {X Y : Type*} [Group X] [Group Y]
    {P B : Subgroup X} {R C : Subgroup Y} (hBP : B≤P) (hCR : C≤R)
    (e : P ≃* R) (b : B ≃* C)
    (he : ∀ x : B, e (inclusion hBP x)=inclusion hCR (b x))
    (hKC : ((pResidual 2 R).map R.subtype).pCoreIn 2≤C) :
    ((pResidual 2 P).map P.subtype).pCoreIn 2=
      ((((pResidual 2 R).map R.subtype).pCoreIn 2).subgroupOf C).map
        (B.subtype.comp b.symm.toMonoidHom) := by
  rw [←map_pCoreIn_of_injective 2 (pResidual 2 P) P.subtype P.subtype_injective]
  apply middle_image hBP hCR e b he _ _ hKC
  rw [←map_map,map_core e,map_pResidual 2 e,
    map_pCoreIn_of_injective 2 (pResidual 2 R) R.subtype R.subtype_injective]

/-- A compatible binary symplectic amalgam transports both residual cores
through its one common Borel map, hence also their dihedral join. -/
theorem binary_amalgam_residual_core_pair {X : Type*} [Group X]
    {P B Q : Subgroup X} {hBP : B≤P} {hBQ : B≤Q}
    (e : Theory.GroupTheory.RankTwoAmalgam.Iso
      (Theory.GroupTheory.RankTwoAmalgam.ofSubgroups P B Q hBP hBQ)
      (SourceNormalizerExtension.diagram (ZMod 2))) :
    let U := ((pResidual 2 P).map P.subtype).pCoreIn 2
    let V := ((pResidual 2 Q).map Q.subtype).pCoreIn 2
    U≤B ∧ V≤B ∧ Nonempty (↥(U⊔V)≃*DihedralGroup 4) ∧ U⊓V≠⊥ := by
  let P₀ := pointParabolic (F := ZMod 2)
  let Q₀ := planeParabolic (F := ZMod 2)
  let U₀ := ((pResidual 2 P₀).map P₀.subtype).pCoreIn 2
  let V₀ := ((pResidual 2 Q₀).map Q₀.subtype).pCoreIn 2
  obtain ⟨hU,hV,⟨j⟩,hi⟩ := binary_residual_core_pair
  let β := B.subtype.comp e.middle.symm.toMonoidHom
  have hβ : Function.Injective β := B.subtype_injective.comp e.middle.symm.injective
  have hUl := residual_core_middle_image (C := borel (F := ZMod 2)) hBP inf_le_left e.left e.middle e.left_commutes hU
  have hVr := residual_core_middle_image (C := borel (F := ZMod 2)) hBQ inf_le_right e.right e.middle e.right_commutes hV
  dsimp only
  rw [hUl,hVr]
  have hB (A : Subgroup (borel (F := ZMod 2))) : A.map β≤B := by
    rintro x ⟨a,ha,rfl⟩
    exact (e.middle.symm a).property
  refine ⟨hB _,hB _,?_,?_⟩
  · rw [←Subgroup.map_sup]
    let J := U₀.subgroupOf borel ⊔ V₀.subgroupOf borel
    have hJ : J.map (borel (F := ZMod 2)).subtype=U₀⊔V₀ := by
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hU,map_subgroupOf_eq_of_le hV]
    exact ⟨(J.equivMapOfInjective β hβ).symm.trans
      (((J.equivMapOfInjective _ (borel (F := ZMod 2)).subtype_injective).trans
        (MulEquiv.subgroupCongr hJ)).trans j)⟩
  · rw [←Subgroup.map_inf _ _ β hβ]
    intro hh
    have h0 := (map_eq_bot_iff_of_injective _ hβ).mp hh
    apply hi
    have hh' := congrArg (fun K : Subgroup (borel (F := ZMod 2)) =>
      K.map (borel (F := ZMod 2)).subtype) h0
    rw [Subgroup.map_inf _ _ _ (borel (F := ZMod 2)).subtype_injective,
      map_subgroupOf_eq_of_le hU,map_subgroupOf_eq_of_le hV,Subgroup.map_bot] at hh'
    exact hh'

private theorem core_commutative_of_product {X : Type*} [Group X]
    (e : X ≃* Equiv.Perm (Fin 2) × Equiv.Perm (Fin 4)) :
    IsMulCommutative (pCore 2 X) := by
  let a := (e.subgroupMap (pCore 2 X)).trans (MulEquiv.subgroupCongr
    ((pCore_map_iso 2 e).trans SymmetricSix.DuadCalculation.productCore_eq.symm))
  refine ⟨⟨fun x y => a.injective ?_⟩⟩
  simp only [map_mul]
  exact IsMulCommutative.is_comm.comm (a x) (a y)

private theorem core_image_commutative {X : Type*} [Group X] (P : Subgroup X)
    (hc : IsMulCommutative (pCore 2 P)) : IsMulCommutative (P.pCoreIn 2) := by
  let a : pCore 2 P ≃* P.pCoreIn 2 :=
    (pCore 2 P).equivMapOfInjective P.subtype P.subtype_injective
  refine ⟨⟨fun x y => a.symm.injective ?_⟩⟩
  simpa only [map_mul] using hc.is_comm.comm (a.symm x) (a.symm y)

private theorem dihedral_pair_not_le {X : Type*} [Group X]
    (U V K : Subgroup X) (hVK : V≤K) (hc : IsMulCommutative K)
    (e : (U⊔V : Subgroup X) ≃* DihedralGroup 4) : ¬ U≤K := by
  intro hUK
  let j := inclusion (sup_le hUK hVK)
  let a := j.comp e.symm.toMonoidHom
  have ha : Function.Injective a := (inclusion_injective (sup_le hUK hVK)).comp e.symm.injective
  apply DihedralGroup.not_commutative (by decide : 4≠1) (by decide : 4≠2)
  refine ⟨⟨fun x y => ha ?_⟩⟩
  simp only [map_mul]
  exact hc.is_comm.comm (a x) (a y)

/-- Neither residual four-group lies in the opposite full endpoint core.
The reason is the noncommutative D8 join and the elementary endpoint cores. -/
theorem binary_amalgam_residual_core_noncontainment {X : Type*} [Group X]
    {P B Q : Subgroup X} {hBP : B≤P} {hBQ : B≤Q}
    (e : Theory.GroupTheory.RankTwoAmalgam.Iso
      (Theory.GroupTheory.RankTwoAmalgam.ofSubgroups P B Q hBP hBQ)
      (SourceNormalizerExtension.diagram (ZMod 2))) :
    ¬ ((pResidual 2 P).map P.subtype).pCoreIn 2 ≤ Q.pCoreIn 2 ∧
    ¬ ((pResidual 2 Q).map Q.subtype).pCoreIn 2 ≤ P.pCoreIn 2 := by
  obtain ⟨_,_,⟨j⟩,_⟩ := binary_amalgam_residual_core_pair e
  have hP := core_image_commutative P
    (core_commutative_of_product (e.left.trans Binary.pointParabolicZModEquivProd))
  have hQ := core_image_commutative Q
    (core_commutative_of_product (e.right.trans Binary.planeParabolicZModEquivProd))
  have hU := pCoreIn_mono_of_normalizes (p := 2) (map_subtype_le (pResidual 2 P))
    (le_normalizer_embedded_pResidual 2 P)
  have hV := pCoreIn_mono_of_normalizes (p := 2) (map_subtype_le (pResidual 2 Q))
    (le_normalizer_embedded_pResidual 2 Q)
  exact ⟨dihedral_pair_not_le _ _ _ hV hQ j,
    dihedral_pair_not_le _ _ _ hU hP ((MulEquiv.subgroupCongr (sup_comm _ _)).trans j)⟩

/-- Minimality of one residual core and its failure to lie in the opposite
endpoint core force avoidance of every two-subgroup normalized by both endpoints. -/
theorem residual_core_disjoint_of_minimal {X : Type*} [Group X]
    (P R Q : Subgroup X) (hQ : IsPGroup 2 Q)
    (hnP : P≤normalizer (Q : Set X)) (hnR : R≤normalizer (Q : Set X))
    (hmin : ∀ A : Subgroup (pResidual 2 P), A.Normal → A≤pCore 2 (pResidual 2 P) →
      A=⊥ ∨ A=pCore 2 (pResidual 2 P))
    (hle : ((pResidual 2 P).map P.subtype).pCoreIn 2≤R)
    (hnot : ¬ ((pResidual 2 P).map P.subtype).pCoreIn 2≤R.pCoreIn 2) :
    Disjoint (((pResidual 2 P).map P.subtype).pCoreIn 2) Q := by
  let E := pResidual 2 P
  let θ : E →* X := P.subtype.comp E.subtype
  have hU : ((pResidual 2 P).map P.subtype).pCoreIn 2=
      (pCore 2 E).map θ := by
    rw [←map_pCoreIn_of_injective 2 (pResidual 2 P) P.subtype P.subtype_injective]
    exact map_map _ _ _
  have hN : (Q.comap θ).Normal := ⟨fun x hx g => by
    change θ (g*x*g⁻¹)∈Q
    rw [map_mul,map_mul,map_inv]
    exact (hnP g.val.property (θ x)).mp hx⟩
  let := hN
  let N := pCore 2 E ⊓ Q.comap θ
  have hNbot : N=⊥ := by
    rcases hmin N inferInstance inf_le_left with hh | hh
    · exact hh
    have hUQ : ((pResidual 2 P).map P.subtype).pCoreIn 2≤Q := by
      rw [hU]
      rintro x ⟨a,ha,rfl⟩
      exact (show a∈N from hh.symm ▸ ha).2
    apply False.elim
    apply hnot
    have hQR : Q⊓R≤R.pCoreIn 2 := le_pCoreIn_of_normalizes
      (hQ.to_le inf_le_left) inf_le_right
      ((le_inf hnR R.le_normalizer).trans inf_normalizer_le_normalizer_inf)
    exact (le_inf hUQ hle).trans hQR
  rw [hU]
  apply disjoint_def.mpr
  rintro x ⟨a,ha,rfl⟩ hx
  have haN : a∈N := ⟨ha,hx⟩
  have ha1 : a=1 := by simpa only [hNbot,mem_bot] using haN
  rw [ha1,map_one]

private theorem dihedral_halfturn_word : ∀ x : DihedralGroup 4, x≠1 →
    x=DihedralGroup.r 2 ∨ x*x=DihedralGroup.r 2 ∨
      ∃ g : DihedralGroup 4, g*x*g⁻¹*x⁻¹=DihedralGroup.r 2 := by decide +kernel

private theorem dihedral_halfturn_mem (N : Subgroup (DihedralGroup 4))
    (hn : N.Normal) (hN : N≠⊥) : DihedralGroup.r 2∈N := by
  obtain ⟨x,hx,hx1⟩ := (bot_or_exists_ne_one N).resolve_left hN
  rcases dihedral_halfturn_word x hx1 with hh | hh | ⟨g,hh⟩
  · exact hh ▸ hx
  · exact hh ▸ N.mul_mem hx hx
  · exact hh ▸ N.mul_mem (hn.conj_mem x hx g) (N.inv_mem hx)

/-- In D8 every nontrivial normal subgroup contains the central half-turn.
Thus a normal kernel disjoint from one nontrivial normal subgroup is trivial. -/
theorem dihedral_normal_disjoint_eq_bot {X : Type*} [Group X]
    (e : X≃*DihedralGroup 4) (U N : Subgroup X)
    (hU : U.Normal) (hN : N.Normal) (hU0 : U≠⊥) (hd : Disjoint U N) : N=⊥ := by
  by_contra hN0
  let := hU
  let := hN
  have hmap (A : Subgroup X) (hA : A≠⊥) : A.map e.toMonoidHom≠⊥ := by
    intro hh
    exact hA ((map_eq_bot_iff_of_injective _ e.injective).mp hh)
  have hu := dihedral_halfturn_mem (U.map e.toMonoidHom)
    (Subgroup.Normal.map hU e.toMonoidHom e.surjective) (hmap U hU0)
  have hn := dihedral_halfturn_mem (N.map e.toMonoidHom)
    (Subgroup.Normal.map hN e.toMonoidHom e.surjective) (hmap N hN0)
  have hh := disjoint_def.mp hd (mem_map_equiv.mp hu) (mem_map_equiv.mp hn)
  have hh' := congrArg e hh
  simp only [e.apply_symm_apply,map_one] at hh'
  exact (by decide : (DihedralGroup.r 2 : DihedralGroup 4)≠1) hh'

end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
