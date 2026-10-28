module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryResidualCore
public import Theory.GroupTheory.ElementaryThompsonNormalizerControl
public import Stellmacher.ElementaryAbelianMaxJWeakClosure
public import Theory.GroupTheory.PCoreOvergroup
public import CFSG.Quasithin.Chapter1.Section01Overgroups

/-!
# Sylow placement for the actual paired binary plane

The full natural–dual automizer preserves paired planes, including under
outer operators exchanging the axes. Thompson normalizer control puts a
Sylow subgroup of the plane centralizer into the original maximal local.
Conjugating there supplies a paired plane U for which the literal C_T(U)
is Sylow in C_G(U). No assertion of Sylow placement for an arbitrary plane
is needed.

For this placement, C_{LT}(U)=O²(C_L(U))C_T(U). Minimal escape and the
Thompson Frattini argument then give H=J(H)L₀T₀. The chosen-module
application, including O₂(H)<Q and characteristic two for H∩M, is in
NonFFSourceDoubledBinarySylow. Constrainedness of H and ambient containment
remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith 3.2.10(1,8), 7.7.2–6, printed pp.583,704–705.
-/

open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySylow
open ChapterE BinaryLinearThree NaturalDual DoubledBinaryPlanes DoubledBinaryLocalCore

private theorem dual_pairing (g : BinaryLinearThree.Group) (v : Vector)
    (f : Module.Dual (ZMod 2) Vector) : W.dual g f (W g v) = f v := by
  change f (W g⁻¹ (W g v)) = f v
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

private def dotSwap : Space ≃ₗ[ZMod 2] Space :=
  (LinearEquiv.prodComm _ _ _).trans
    ((dotProductEquiv (ZMod 2) (Fin 3)).symm.prodCongr
      (dotProductEquiv (ZMod 2) (Fin 3)))

private theorem dot_intertwine (g : BinaryLinearThree.Group) (v : Vector) :
    dotProductEquiv (ZMod 2) (Fin 3) (W (AutomorphismAction.graph g) v) =
      W.dual g (dotProductEquiv (ZMod 2) (Fin 3) v) := by
  apply LinearMap.ext
  intro w
  change dotProduct (Matrix.mulVec g⁻¹.val.transpose v) w = dotProduct v (Matrix.mulVec g⁻¹.val w)
  rw [← Matrix.vecMul_transpose,Matrix.dotProduct_mulVec,Matrix.transpose_transpose]

private theorem dotSwap_covariance (g : BinaryLinearThree.Group) (x : Space) :
    dotSwap (action g x) = action (AutomorphismAction.graph g) (dotSwap x) := by
  apply Prod.ext
  · change (dotProductEquiv (ZMod 2) (Fin 3)).symm (W.dual g x.2) =
      W (AutomorphismAction.graph g) ((dotProductEquiv (ZMod 2) (Fin 3)).symm x.2)
    apply (dotProductEquiv (ZMod 2) (Fin 3)).injective
    rw [LinearEquiv.apply_symm_apply,dot_intertwine,LinearEquiv.apply_symm_apply]
  · change dotProductEquiv (ZMod 2) (Fin 3) (W g x.1) =
      W.dual (AutomorphismAction.graph g) (dotProductEquiv (ZMod 2) (Fin 3) x.1)
    simpa only [AutomorphismAction.graph_graph] using dot_intertwine (AutomorphismAction.graph g) x.1

private theorem graph_pairing (v : Vector) (f : Module.Dual (ZMod 2) Vector) :
    dotProductEquiv (ZMod 2) (Fin 3) v ((dotProductEquiv (ZMod 2) (Fin 3)).symm f) = f v := by
  have he := congrArg (fun a : Module.Dual (ZMod 2) Vector => a v)
    ((dotProductEquiv (ZMod 2) (Fin 3)).apply_symm_apply f)
  change dotProduct v ((dotProductEquiv (ZMod 2) (Fin 3)).symm f) = f v
  rw [dotProduct_comm]
  exact he

private theorem pairedPlane_span (v : Vector) (f : Module.Dual (ZMod 2) Vector) :
    pairedPlane v f = Submodule.span (ZMod 2) {(v,0),(0,f)} := by
  apply le_antisymm
  · rw [pairedPlane_le_iff]
    exact ⟨Submodule.subset_span (by simp),Submodule.subset_span (by simp)⟩
  · rw [Submodule.span_le,Set.insert_subset_iff,Set.singleton_subset_iff]
    exact (pairedPlane_le_iff v f _).mp le_rfl

private theorem ambientPlane_coordinates
    {G : Type*} [_root_.Group G] (W₀ : Subgroup G) [IsElementaryAbelian 2 W₀]
    (E : Additive W₀ ≃ₗ[ZMod 2] Space) (v : Vector) (f : Module.Dual (ZMod 2) Vector) :
    ambientPlane W₀ E v f = ambientSubmodule W₀ ((pairedPlane v f).comap E.toLinearMap) := by
  let U := (pairedPlane v f).comap E.toLinearMap
  have hp := (pairedPlane_le_iff v f (pairedPlane v f)).mp le_rfl
  apply le_antisymm
  · rw [ambientPlane_le_iff]
    constructor
    · refine ⟨(E.symm (v,0)).toMul,?_,rfl⟩
      change E (E.symm (v,0)) ∈ pairedPlane v f
      rw [E.apply_symm_apply]
      exact hp.1
    · refine ⟨(E.symm (0,f)).toMul,?_,rfl⟩
      change E (E.symm (0,f)) ∈ pairedPlane v f
      rw [E.apply_symm_apply]
      exact hp.2
  · let Z := (moduleSubgroup W₀).symm ((ambientPlane W₀ E v f).subgroupOf W₀)
    have hg := (ambientPlane_le_iff W₀ E v f (ambientPlane W₀ E v f)).mp le_rfl
    have hz : pairedPlane v f ≤ Z.map E.toLinearMap := by
      rw [pairedPlane_le_iff]
      exact ⟨⟨E.symm (v,0),hg.1,E.apply_symm_apply _⟩,
        ⟨E.symm (0,f),hg.2,E.apply_symm_apply _⟩⟩
    rintro x ⟨w,hw,rfl⟩
    change E (Additive.ofMul w) ∈ pairedPlane v f at hw
    have hm := hz hw
    rw [Submodule.mem_map_equiv,E.symm_apply_apply] at hm
    exact hm

private theorem pairedPlane_operator
    (a : MulAut BinaryLinearThree.Group) (c : Space ≃ₗ[ZMod 2] Space)
    (hc : ∀ g x, c (action g x) = action (a g) (c x))
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1) :
    ∃ v' f', f' v' = 1 ∧ (pairedPlane v f).map c.toLinearMap = pairedPlane v' f' := by
  have hi (g : BinaryLinearThree.Group) (u : Vector) (h : Module.Dual (ZMod 2) Vector) :
      (pairedPlane u h).map (action g) = pairedPlane (W g u) (W.dual g h) := by
    simp only [pairedPlane_span, Submodule.map_span]
    simp only [Set.image_insert_eq, Set.image_singleton]
    change Submodule.span (ZMod 2) {(W g u,W.dual g 0),(W g 0,W.dual g h)} = _
    rw [map_zero,map_zero]
  by_cases ha : a ∈ MulAut.innerSubgroup BinaryLinearThree.Group
  · obtain ⟨g,rfl⟩ := inner_operator a c hc ha
    exact ⟨W g v,W.dual g f,(dual_pairing g v f).trans hfv,hi g v f⟩
  · obtain ⟨g,hg⟩ := AutomorphismAction.outer_eq_inner_graph a ha
    have he : c = dotSwap.trans (innerOperator g) := implementing_unique a c _ hc (by
      intro k x
      change innerOperator g (dotSwap (action k x)) = action (a k) (innerOperator g (dotSwap x))
      rw [dotSwap_covariance,innerOperator_covariance,hg]
      rfl)
    rw [he]
    refine ⟨W g ((dotProductEquiv (ZMod 2) (Fin 3)).symm f),
      W.dual g ((dotProductEquiv (ZMod 2) (Fin 3)) v),?_,?_⟩
    · rw [dual_pairing,graph_pairing,hfv]
    · have hs : (pairedPlane v f).map dotSwap.toLinearMap =
          pairedPlane ((dotProductEquiv (ZMod 2) (Fin 3)).symm f)
            ((dotProductEquiv (ZMod 2) (Fin 3)) v) := by
        simp only [pairedPlane_span,Submodule.map_span]
        simp only [Set.image_insert_eq,Set.image_singleton]
        change Submodule.span (ZMod 2)
          {((dotProductEquiv (ZMod 2) (Fin 3)).symm 0,(dotProductEquiv (ZMod 2) (Fin 3)) v),
           ((dotProductEquiv (ZMod 2) (Fin 3)).symm f,(dotProductEquiv (ZMod 2) (Fin 3)) 0)} = _
        rw [map_zero,map_zero]
        exact congrArg (Submodule.span (ZMod 2)) (Set.pair_comm _ _)
      change (pairedPlane v f).map ((action g).comp dotSwap.toLinearMap) = _
      rw [Submodule.map_comp,hs,hi]

/-- The full normalizer preserves the actual family of paired planes. -/
theorem pairedPlane_normalizer_invariant
    {G : Type*} [_root_.Group G] (W₀ : Subgroup G) [IsElementaryAbelian 2 W₀]
    (E : Additive W₀ ≃ₗ[ZMod 2] Space) (a : Automizer W₀ ≃* MulAut BinaryLinearThree.Group)
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (action g (E w)))) =
      action (a b g) (E (automizerRepresentation W₀ b w)))
    (n : normalizer (W₀ : Set G)) (v : Vector) (f : Module.Dual (ZMod 2) Vector)
    (hfv : f v = 1) :
    ∃ v' f', f' v' = 1 ∧
      (ambientPlane W₀ E v f).map (MulAut.conj (n : G)).toMonoidHom =
        ambientPlane W₀ E v' f' := by
  let b := W₀.normalizerMonoidHom.rangeRestrict n
  let ρ := automizerRepresentation W₀
  let c := E.symm.trans ((LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom b)).trans E)
  have hc (g : BinaryLinearThree.Group) (x : Space) : c (action g x) = action (a b g) (c x) := by
    change E (ρ b (E.symm (action g x))) = action (a b g) (E (ρ b (E.symm x)))
    simpa only [E.apply_symm_apply] using hcov b g (E.symm x)
  obtain ⟨v',f',hfv',he⟩ := pairedPlane_operator (a b) c hc v f hfv
  refine ⟨v',f',hfv',?_⟩
  rw [ambientPlane_coordinates W₀ E v f,ambientPlane_coordinates W₀ E v' f',← he]
  apply le_antisymm
  · rintro _ ⟨x,⟨w,hw,rfl⟩,rfl⟩
    refine ⟨(ρ b (Additive.ofMul w)).toMul,?_,rfl⟩
    change E (ρ b (Additive.ofMul w)) ∈ (pairedPlane v f).map c.toLinearMap
    exact ⟨E (Additive.ofMul w),hw,by
      change E (ρ b (E.symm (E (Additive.ofMul w)))) = _
      rw [E.symm_apply_apply]⟩
  · rintro _ ⟨w,hw,rfl⟩
    obtain ⟨x,hx,hex⟩ := hw
    let w₀ := (E.symm x).toMul
    have hact : ρ b (Additive.ofMul w₀) = Additive.ofMul w := E.injective hex
    refine ⟨(w₀ : G),⟨w₀,?_,rfl⟩,?_⟩
    · change E (E.symm x) ∈ pairedPlane v f
      rwa [E.apply_symm_apply]
    · exact congrArg (fun z : Additive W₀ => (z.toMul : G)) hact

/-- Every two-overgroup of the original Thompson group has the same Thompson group. -/
theorem thompson_eq_of_overgroup
    {G : Type*} [_root_.Group G] [Finite G] (T : Sylow 2 G)
    (S : Subgroup G) (hp : IsPGroup 2 S)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ S) :
    elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) := by
  obtain ⟨R,hSR⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G R T
  let e := MulAut.conj g
  have hRmap : (R : Subgroup G).map e.toMonoidHom = (T : Subgroup G) := by
    have hs := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul] at hs
    exact hs
  have hstable := elementaryAbelianMaxJ_map_eq_of_le (T : Subgroup G) e
    ((map_mono (hJ.trans hSR)).trans_eq hRmap)
  have he : elementaryAbelianMaxJ (R : Subgroup G) = elementaryAbelianMaxJ (T : Subgroup G) := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [← elementaryAbelianMaxJ_map_equiv e (R : Subgroup G),hRmap,hstable]
  exact (elementaryAbelianMaxJ_eq_of_intermediate (R : Subgroup G) S (he.symm ▸ hJ) hSR).trans he

private theorem map_centralizer_eq {G : Type*} [_root_.Group G]
    (e : G ≃* G) (U : Subgroup G) :
    (centralizer (U : Set G)).map e.toMonoidHom = centralizer (U.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x,?_,e.apply_symm_apply x⟩
  intro u hu
  apply e.injective
  simpa only [map_mul,e.apply_symm_apply] using hx (e u) (mem_map_of_mem _ hu)

private theorem sylow_map_centralizer {G : Type*} [_root_.Group G] [Finite G]
    (U : Subgroup G) (S : Sylow 2 (centralizer (U : Set G))) (e : G ≃* G) :
    ∃ P : Sylow 2 (centralizer (U.map e.toMonoidHom : Set G)),
      (P : Subgroup _).map (centralizer (U.map e.toMonoidHom : Set G)).subtype =
        ((S : Subgroup _).map (centralizer (U : Set G)).subtype).map e.toMonoidHom := by
  let C := centralizer (U : Set G)
  let C' := centralizer (U.map e.toMonoidHom : Set G)
  let f : C ≃* C' := (C.equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_centralizer_eq e U))
  let P := S.mapSurjective (f := f.toMonoidHom) f.surjective
  refine ⟨P,?_⟩
  change ((S : Subgroup C).map f.toMonoidHom).map C'.subtype = _
  rw [map_map,map_map]
  rfl

/-- A paired plane can be chosen so its literal T-centralizer is Sylow in
its full ambient centralizer. Only the source Thompson control is needed. -/
theorem exists_pairedPlane_sylow
    {G : Type*} [_root_.Group G] [Finite G]
    (W₀ M : Subgroup G) (T : Sylow 2 G) [IsElementaryAbelian 2 W₀]
    (hTM : (T : Subgroup G) ≤ M) (hMW : M ≤ normalizer (W₀ : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W₀ : Set G))
    (hNJ : normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ M)
    (E : Additive W₀ ≃ₗ[ZMod 2] Space) (a : Automizer W₀ ≃* MulAut BinaryLinearThree.Group)
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (action g (E w)))) =
      action (a b g) (E (automizerRepresentation W₀ b w))) :
    ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector, f v = 1 ∧
      ∃ P : Sylow 2 (centralizer (ambientPlane W₀ E v f : Set G)),
        (P : Subgroup _).map (centralizer (ambientPlane W₀ E v f : Set G)).subtype =
          (T : Subgroup G) ⊓ centralizer (ambientPlane W₀ E v f : Set G) := by
  let v : Vector := Pi.single 0 1
  let f : Module.Dual (ZMod 2) Vector := LinearMap.proj 0
  have hfv : f v = 1 := by simp [f,v]
  let U := ambientPlane W₀ E v f
  let C := centralizer (U : Set G)
  let Q := (T : Subgroup G) ⊓ centralizer (W₀ : Set G)
  have hQC : Q ≤ C := inf_le_right.trans (centralizer_le (ambientPlane_le_orbit W₀ E v f))
  have hp : IsPGroup 2 Q := T.isPGroup'.to_le inf_le_left
  obtain ⟨S,hQS⟩ := (hp.comap_subtype (K := C)).exists_le_sylow
  let R := (S : Subgroup C).map C.subtype
  have hJR : elementaryAbelianMaxJ (T : Subgroup G) ≤ R := by
    intro x hx
    have hQx : x ∈ Q := ⟨(show elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) from sSup_le fun _ hA => hA.1) hx,hJ hx⟩
    exact mem_map_of_mem C.subtype (hQS (show (⟨x,hQC hQx⟩ : C) ∈ Q.subgroupOf C from hQx))
  have hRM : R ≤ M := by
    have he := thompson_eq_of_overgroup T R (S.isPGroup'.map C.subtype) hJR
    exact R.le_normalizer.trans ((normalizer_le_normalizer_elementaryAbelianMaxJ R).trans
      (he.symm ▸ hNJ))
  obtain ⟨A,hRA⟩ := ((S.isPGroup'.map C.subtype).comap_subtype (K := M)).exists_le_sylow
  obtain ⟨m,hm⟩ := MulAction.exists_smul_eq M A (T.subtype hTM)
  let e := MulAut.conj (m : G)
  have hRT : R.map e.toMonoidHom ≤ (T : Subgroup G) := by
    rintro _ ⟨x,hx,rfl⟩
    have hh : (MulAut.conj m) (⟨x,hRM hx⟩ : M) ∈ (T.subtype hTM : Subgroup M) := by
      rw [← hm]
      exact mem_map_of_mem (MulAut.conj m).toMonoidHom (hRA hx)
    exact hh
  obtain ⟨v',f',hfv',hU'⟩ := pairedPlane_normalizer_invariant W₀ E a hcov
    ⟨m,hMW m.property⟩ v f hfv
  obtain ⟨P,hP⟩ := sylow_map_centralizer U S e
  have hP' := inf_eq_sylow_map P T.isPGroup' (hP.trans_le hRT)
  refine ⟨v',f',hfv',?_⟩
  change U.map e.toMonoidHom = ambientPlane W₀ E v' f' at hU'
  rw [← hU']
  exact ⟨P,hP'.symm⟩

/-- A Sylow overgroup's core lies in the core of the smaller local base. -/
theorem core_le_of_sylow_base
    {G : Type*} [_root_.Group G] [Finite G] {B H : Subgroup G}
    (S : Sylow 2 H) (hSB : (S : Subgroup H).map H.subtype ≤ B) (hBH : B ≤ H) :
    H.pCoreIn 2 ≤ B.pCoreIn 2 := by
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H)
    ((pCoreIn_le_sylow H S).trans hSB)
    (hBH.trans (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))

/-- Minimal escape and the Thompson Frattini argument give the actual
source generation H = J(H)B. -/
theorem minimal_escape_generation
    {G : Type*} [_root_.Group G] [Finite G] (T : Sylow 2 G) (U B M H : Subgroup G)
    (hH : H ∈ Chapter3.HStar B M) (hHC : H ≤ centralizer (U : Set G))
    (hp : IsPGroup 2 U) (hU : U ≠ ⊥) (hUB : U ≤ B)
    (S : Sylow 2 H) (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hJS : elementaryAbelianMaxJ (T : Subgroup G) ≤ (S : Subgroup H).map H.subtype)
    (hNJ : normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ M) :
    H = elementaryAbelianMaxJ H ⊔ B := by
  have hBH : B ≤ H := hH.1.1.2
  have hSH : elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) ≤ elementaryAbelianMaxJ H := by
    have hh := map_mono (f := H.subtype) (elementaryAbelianMaxJ_sylow_le_top S)
    rw [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      ← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective,
      ← MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have he : elementaryAbelianMaxJ ((S : Subgroup H).map H.subtype) =
      elementaryAbelianMaxJ (T : Subgroup G) :=
    elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G) _ hJS hST
  have hout : ¬ elementaryAbelianMaxJ H ≤ M := by
    intro hj
    apply hH.1.2
    exact le_of_thompson_normalizer_control H M (elementaryAbelianMaxJ H) S
      (H.le_normalizer.trans (normalizer_le_normalizer_elementaryAbelianMaxJ H)) hj hSH (he.symm ▸ hNJ)
  let X := elementaryAbelianMaxJ H ⊔ B
  have hXH : X ≤ H := sup_le (sSup_le fun _ hA => hA.1) hBH
  have hUX : U ≤ X := hUB.trans le_sup_right
  have hcore : U ≤ X.pCoreIn 2 := le_pCoreIn_of_normalizes hp hUX
    ((hXH.trans hHC).trans (Subgroup.centralizer_le_normalizer _))
  apply le_antisymm _ hXH
  apply hH.2 ?_ hXH
  refine ⟨⟨?_,fun x hx => (le_sup_right : B ≤ X) hx⟩,fun hXM => hout (le_sup_left.trans hXM)⟩
  intro hz
  exact hU (le_bot_iff.mp (hz ▸ hcore))

/-- Restrict an actual Sylow image to an intermediate overgroup. -/
theorem sylow_between
    {G : Type*} [_root_.Group G] {H C : Subgroup G} (hHC : H ≤ C)
    (S : Sylow 2 C) (hSH : (S : Subgroup C).map C.subtype ≤ H) :
    ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = (S : Subgroup C).map C.subtype := by
  have hs : (S : Subgroup C) ≤ (inclusion hHC).range := by
    intro x hx
    exact ⟨⟨x,hSH (mem_map_of_mem C.subtype hx)⟩,rfl⟩
  let P := S.comapOfInjective (inclusion hHC) (inclusion_injective hHC) hs
  refine ⟨P,?_⟩
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact mem_map_of_mem C.subtype hy
  · rintro ⟨y,hy,rfl⟩
    exact ⟨⟨y,hSH (mem_map_of_mem C.subtype hy)⟩,hy,rfl⟩

/-- For the placed plane, the full centralizer in LT equals the original
residual/Sylow base L₀T₀. -/
theorem localBase_eq_centralizer
    {G : Type*} [_root_.Group G] [Finite G] (L U : Subgroup G) (T : Sylow 2 G)
    (hTN : (T : Subgroup G) ≤ normalizer (L : Set G))
    (S : Sylow 2 (centralizer (U : Set G)))
    (hS : (S : Subgroup _).map (centralizer (U : Set G)).subtype =
      (T : Subgroup G) ⊓ centralizer (U : Set G)) :
    localBase L (T : Subgroup G) U = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) := by
  let J := L ⊔ (T : Subgroup G)
  let K := J ⊓ centralizer (U : Set G)
  let LJ := L.subgroupOf J
  let SJ := T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)
  let R := (pResidual 2 K).map K.subtype
  let _ : LJ.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTN)
  have hgen : LJ ⊔ (SJ : Subgroup J) = ⊤ := by
    apply map_injective J.subtype_injective
    rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left),
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right),
      ← MonoidHom.range_eq_map,range_subtype]
  have hres : pResidual 2 J ≤ LJ := sInf_le ⟨inferInstance,
    isPGroup_quotient_of_sup_eq_top LJ (SJ : Subgroup J) SJ.isPGroup' hgen⟩
  have hRL : R ≤ L := by
    rintro _ ⟨x,hx,rfl⟩
    exact hres ((map_pResidual_le 2 (inclusion (show K ≤ J from inf_le_left)))
      (mem_map_of_mem _ hx))
  have hRLC : R ≤ L ⊓ centralizer (U : Set G) :=
    le_inf hRL ((map_subtype_le _).trans inf_le_right)
  have hR : R = localResidual L U := by
    apply le_antisymm
    · have hp := (pResidual_eq_top_iff 2 R).mpr (isPPerfect_embedded_pResidual 2 K)
      have hh := embedded_pResidual_mono 2 hRLC
      rw [hp,← MonoidHom.range_eq_map,range_subtype] at hh
      exact hh
    · exact embedded_pResidual_mono 2
        (inf_le_inf_right _ (show L ≤ J from le_sup_left))
  obtain ⟨P,hP⟩ := sylow_between (show K ≤ centralizer (U : Set G) from inf_le_right) S
    (hS.trans_le (inf_le_inf_right _ (show (T : Subgroup G) ≤ J from le_sup_right)))
  have he := congrArg (fun A : Subgroup K => A.map K.subtype) (pResidual_sup_sylow_eq_top P)
  rw [Subgroup.map_sup,hP,hS,← MonoidHom.range_eq_map,range_subtype] at he
  change R ⊔ ((T : Subgroup G) ⊓ centralizer (U : Set G)) = K at he
  rw [hR] at he
  exact he

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySylow
