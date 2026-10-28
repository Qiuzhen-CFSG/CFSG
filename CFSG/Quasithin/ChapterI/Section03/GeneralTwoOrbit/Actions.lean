module

public import CFSG.Quasithin.ChapterI.Section03.GeneralTwoOrbit
public import CFSG.Quasithin.ChapterI.Section03.GeneralTwoOrbit.Quotient
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# GLS II 5.22 for arbitrary finite two-group actions

Apply the internal two-subgroup theorem in the actual action semidirect product.
The original fixed subgroup embeds normally in the actor centralizer, as the
kernel of its right-coordinate map. The selected two-component lies in the
base group because its perfect image in the two-group actor is trivial. The
base embedding identifies its actor orbit with the original automorphism orbit
and reflects the relative normal-closure equality.

Normality in the source two-layer gives both subnormal closures. Restriction
retains the seed in the literal fixed subgroup of the orbit product. That
product is its own two-layer, so the odd-central quotient theorem applies to
every invariant normal subgroup of its actual O_{2',2}.

`proposition522` proves all four clauses of GLS II, Chapter B, Proposition 5.22,
with only the genuine universal GLS 5.17 input explicit. S₂ is discharged in
the internal theorem. The semidirect-product coordinate calculations follow
the same literal maps as `PStar.RadicalActionReduction`; no fixed-point
surjectivity for central even kernels or projection to a covering factor is used.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.GeneralTwoOrbit
universe u v
variable {G : Type u} {A : Type v} [Group G] [Group A] [MulDistribMulAction A G]

local notation "SD" => G ⋊[MulDistribMulAction.toMulAut A G] A
local notation "actor" => MonoidHom.range (SemidirectProduct.inr : A →* SD)
local notation "CSD" => centralizer (actor : Set SD)

private theorem inl_mem_actor_centralizer_iff (g : G) :
    (SemidirectProduct.inl g : SD) ∈ CSD ↔ g ∈ fixedPointSubgroup A G := by
  constructor
  · intro hg a
    have he := congrArg SemidirectProduct.left
      (mem_centralizer_iff.mp hg (SemidirectProduct.inr a) ⟨a, rfl⟩)
    simpa only [SemidirectProduct.mul_left, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, one_mul, map_one, MulAut.one_apply, mul_one,
      MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply] using he
  · intro hg
    apply mem_centralizer_iff.mpr
    rintro _ ⟨a, rfl⟩
    apply SemidirectProduct.ext
    · simpa only [SemidirectProduct.mul_left, SemidirectProduct.left_inr,
        SemidirectProduct.right_inr, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, one_mul, map_one, MulAut.one_apply, mul_one,
      MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
        using hg a
    · simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inr,
        SemidirectProduct.right_inl, mul_one, one_mul]

private def fixedPointInl : fixedPointSubgroup A G →* CSD :=
  ((SemidirectProduct.inl : G →* SD).comp (fixedPointSubgroup A G).subtype).codRestrict _
    (fun x => (inl_mem_actor_centralizer_iff (x : G)).mpr x.property)

private theorem fixedPointInl_injective :
    Function.Injective (fixedPointInl (G := G) (A := A)) := by
  intro x y h
  apply Subtype.ext
  exact SemidirectProduct.inl_injective (congrArg Subtype.val h)

private theorem centralizer_right_mem_center (x : CSD) : (x : SD).right ∈ center A := by
  apply mem_center_iff.mpr
  intro a
  have he := congrArg SemidirectProduct.right
    (mem_centralizer_iff.mp x.property (SemidirectProduct.inr a) ⟨a, rfl⟩)
  simpa only [SemidirectProduct.mul_right, SemidirectProduct.right_inr] using he

private def centralizerRight : CSD →* center A :=
  ((SemidirectProduct.rightHom : SD →* A).comp (CSD).subtype).codRestrict _
    centralizer_right_mem_center

private theorem fixedPointInl_range_eq_ker :
    (fixedPointInl (G := G) (A := A)).range = centralizerRight.ker := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    apply Subtype.ext
    rfl
  · intro hx
    have hr : (x : SD).right = 1 := congrArg Subtype.val hx
    have he : (SemidirectProduct.inl (x : SD).left : SD) = x :=
      SemidirectProduct.ext rfl hr.symm
    have hf : (x : SD).left ∈ fixedPointSubgroup A G := by
      apply (inl_mem_actor_centralizer_iff _).mp
      rw [he]
      exact x.property
    exact ⟨⟨(x : SD).left, hf⟩, Subtype.ext he⟩


/-- The product of one actual orbit under the given external action. -/
@[expose] def actionOrbit (J : Subgroup G) : Subgroup G :=
  ⨆ a : A, J.map (MulDistribMulAction.toMulAut A G a).toMonoidHom

private theorem map_actionOrbit_inl (J : Subgroup G) :
    (actionOrbit (A := A) J).map (SemidirectProduct.inl : G →* SD) =
      componentOrbit (J.map (SemidirectProduct.inl : G →* SD)) actor := by
  let i : G →* SD := SemidirectProduct.inl
  have hm (a : A) : (J.map (MulDistribMulAction.toMulAut A G a).toMonoidHom).map i =
      (J.map i).map (MulAut.conj (SemidirectProduct.inr a : SD)).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    change (SemidirectProduct.inl ((MulDistribMulAction.toMulAut A G a) x) : SD) =
      SemidirectProduct.inr a * SemidirectProduct.inl x * (SemidirectProduct.inr a)⁻¹
    simpa only [map_inv] using
      (SemidirectProduct.inl_aut (φ := MulDistribMulAction.toMulAut A G) a x)
  change (⨆ a : A, J.map (MulDistribMulAction.toMulAut A G a).toMonoidHom).map i = _
  rw [Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup_le fun a => ?_
    rw [hm]
    exact le_iSup (fun b : actor => (J.map i).map (MulAut.conj (b : SD)).toMonoidHom)
      ⟨SemidirectProduct.inr a, ⟨a, rfl⟩⟩
  · refine iSup_le ?_
    rintro ⟨_, a, rfl⟩
    rw [← hm]
    exact le_iSup (fun a : A =>
      (J.map (MulDistribMulAction.toMulAut A G a).toMonoidHom).map i) a

section Finite
variable [Finite G] [Finite A]
local instance : Finite SD := Finite.of_equiv (G × A) SemidirectProduct.equivProd.symm

/-- The internal source theorem applies to external actions through the real
semidirect product. The resulting orbit and normal closure are in the original G. -/
theorem exists_action_orbit_normalClosure
    (balance : OrdinaryBalance.TwoLayerCentralizerBalance.{max u v}) (hA : IsPGroup 2 A)
    (I : Subgroup (fixedPointSubgroup A G)) (hI : I.IsTwoComponent) :
    ∃ J : Subgroup G, J.IsTwoComponent ∧
      let D := I.map (fixedPointSubgroup A G).subtype
      let X := actionOrbit (A := A) J
      D ≤ X ∧ componentOrbit D X = X := by
  let i : G →* SD := SemidirectProduct.inl
  let j := fixedPointInl (G := G) (A := A)
  have hjn : j.range.Normal := by
    rw [fixedPointInl_range_eq_ker]
    infer_instance
  let : Group.IsSolvable j.ker := by
    rw [j.ker_eq_bot fixedPointInl_injective]
    infer_instance
  have hIs : (I.map j).IsTwoComponent :=
    map_twoComponent_of_subnormal_range_solvable_kernel hI j hjn.isSubnormal
  have hactor : IsPGroup 2 actor := hA.of_surjective
    (SemidirectProduct.inr : A →* SD).rangeRestrict (MonoidHom.rangeRestrict_surjective _)
  obtain ⟨K, hK, hIK, hgen, _, _, _, _, _⟩ :=
    exists_orbit_and_closures balance actor hactor (I.map j) hIs
  let D := I.map (fixedPointSubgroup A G).subtype
  have hD : (I.map j).map (CSD).subtype = D.map i := by
    rw [map_map, map_map]
    rfl
  rw [hD] at hIK hgen
  let : Group.IsNilpotent A := hA.isNilpotent
  let := hK.1.perfect
  have hKr : K ≤ (SemidirectProduct.rightHom : SD →* A).ker := by
    apply (Subgroup.map_eq_bot_iff K).mp
    let : Group.IsPerfect (K.map (SemidirectProduct.rightHom : SD →* A)) := Group.IsPerfect.map _
    by_contra he
    let : Nontrivial (K.map (SemidirectProduct.rightHom : SD →* A)) :=
      (nontrivial_iff_ne_bot _).mpr he
    exact Group.IsPerfect.not_isSolvable (K.map (SemidirectProduct.rightHom : SD →* A)) inferInstance
  have hKi : K ≤ i.range := by
    rwa [← SemidirectProduct.range_inl_eq_ker_rightHom] at hKr
  let e : G ≃* i.range := MonoidHom.ofInjective SemidirectProduct.inl_injective
  let J := (K.subgroupOf i.range).map e.symm.toMonoidHom
  have hJ : J.IsTwoComponent := (hK.subgroupOf hKi).map_equiv e.symm
  have hJi : J.map i = K := by
    change ((K.subgroupOf i.range).map e.symm.toMonoidHom).map i = K
    rw [map_map]
    have he : i.comp e.symm.toMonoidHom = i.range.subtype := by
      apply MonoidHom.ext
      intro x
      exact congrArg Subtype.val (e.apply_symm_apply x)
    rw [he, map_subgroupOf_eq_of_le hKi]
  have hX : (actionOrbit (A := A) J).map i = componentOrbit K actor := by
    rw [map_actionOrbit_inl, hJi]
  refine ⟨J, hJ, ?_, ?_⟩
  · apply (map_le_map_iff_of_injective (f := i) SemidirectProduct.inl_injective).mp
    rw [hX]
    exact hIK
  · apply (map_injective (f := i) SemidirectProduct.inl_injective)
    rw [map_componentOrbit, hX]
    exact hgen

omit [Finite G] [Finite A] in
/-- The orbit product is invariant under the original action. -/
theorem actionOrbit_invariant (J : Subgroup G) : IsInvariant A G (actionOrbit (A := A) J) := by
  let X := actionOrbit (A := A) J
  have hs (a : A) : ∀ x ∈ X, a • x ∈ X := by
    intro x hx
    induction hx using iSup_induction' with
    | hp b x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      apply (le_iSup (fun b : A => J.map (MulDistribMulAction.toMulAut A G b).toMonoidHom)
        (a * b))
      refine ⟨y, hy, ?_⟩
      exact mul_smul a b y
    | h1 => simpa only [smul_one] using X.one_mem
    | hmul x y _ _ hx hy => simpa only [smul_mul'] using X.mul_mem hx hy
  exact ⟨fun a x => ⟨hs a x, fun hx => by simpa only [inv_smul_smul] using hs a⁻¹ _ hx⟩⟩

omit [Finite G] [Finite A] in
/-- All orbit factors lie in the source layer. -/
theorem actionOrbit_le_twoLayer {J : Subgroup G} (hJ : J.IsTwoComponent) :
    actionOrbit (A := A) J ≤ twoComponentLayer G :=
  iSup_le fun a => (hJ.map_equiv (MulDistribMulAction.toMulAut A G a)).le_twoComponentLayer

omit [Finite A] in
/-- The source layer normalizes the full orbit product. -/
theorem twoLayer_le_normalizer_actionOrbit {J : Subgroup G} (hJ : J.IsTwoComponent) :
    twoComponentLayer G ≤ normalizer (actionOrbit (A := A) J : Set G) := by
  have hLC : twoComponentLayer G ≤ cComponentLayer G :=
    sSup_le fun K hK => le_cComponentLayer hK.1
  exact hLC.trans ((le_iInf fun a : A => cComponentLayer_le_normalizer
    (hJ.1.map_equiv (MulDistribMulAction.toMulAut A G a))).trans
      (iInf_normalizer_le_normalizer_iSup _))

omit [Finite A] in
/-- Every actor orbit of two-components is subnormal in the original group. -/
theorem actionOrbit_subnormal {J : Subgroup G} (hJ : J.IsTwoComponent) :
    (actionOrbit (A := A) J).IsSubnormal :=
  (normal_subgroupOf_of_le_normalizer (twoLayer_le_normalizer_actionOrbit hJ)).isSubnormal.trans
    (actionOrbit_le_twoLayer hJ) (inferInstance : (twoComponentLayer G).Normal).isSubnormal

omit [Finite G] [Finite A] in
/-- The orbit product is generated by its intrinsic two-components. -/
theorem actionOrbit_twoLayer_eq_top {J : Subgroup G} (hJ : J.IsTwoComponent) :
    twoComponentLayer (actionOrbit (A := A) J) = ⊤ := by
  let X := actionOrbit (A := A) J
  apply top_unique
  apply (map_le_map_iff_of_injective X.subtype_injective).mp
  rw [← MonoidHom.range_eq_map, range_subtype]
  refine iSup_le fun a => ?_
  have ha : J.map (MulDistribMulAction.toMulAut A G a).toMonoidHom ≤ X :=
    le_iSup (fun a : A => J.map (MulDistribMulAction.toMulAut A G a).toMonoidHom) a
  have hh := map_mono (f := X.subtype)
    ((hJ.map_equiv (MulDistribMulAction.toMulAut A G a)).subgroupOf ha).le_twoComponentLayer
  rwa [map_subgroupOf_eq_of_le ha] at hh

omit [Finite G] [Finite A] in
private theorem twoComponent_comap_injective {H : Type*} [Group H]
    (f : H →* G) (hf : Function.Injective f) {J : Subgroup G}
    (hJ : J.IsTwoComponent) (hle : J ≤ f.range) : (J.comap f).IsTwoComponent := by
  let e : H ≃* f.range := MonoidHom.ofInjective hf
  have h := (hJ.subgroupOf hle).map_equiv e.symm
  have he : (J.subgroupOf f.range).map e.symm.toMonoidHom = J.comap f := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change f (e.symm y) ∈ J
      have hh : f (e.symm y) = (y : G) := congrArg Subtype.val (e.apply_symm_apply y)
      rw [hh]
      exact hy
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
  rwa [he] at h

omit [Finite G] [Finite A] in
/-- The fixed-subgroup inclusion uses the original subtype homomorphism. -/
@[expose] def orbitFixedInclusion (X : Subgroup G) [IsInvariant A G X] :
    fixedPointSubgroup A X →* fixedPointSubgroup A G :=
  FixedPoints.mapHom X.subtype (fun _ _ => rfl)

omit [Finite G] [Finite A] in
/-- Restriction to the actual orbit fixed subgroup preserves the seed component. -/
theorem seed_in_actionOrbit_fixed
    (X : Subgroup G) [IsInvariant A G X]
    (I : Subgroup (fixedPointSubgroup A G)) (hI : I.IsTwoComponent)
    (hIX : I.map (fixedPointSubgroup A G).subtype ≤ X) :
    (I.comap (orbitFixedInclusion (A := A) X)).IsTwoComponent ∧
      (I.comap (orbitFixedInclusion (A := A) X)).map (orbitFixedInclusion X) = I := by
  let f := orbitFixedInclusion (A := A) X
  have hf : Function.Injective f := by
    intro x y h
    have hv : (((x : fixedPointSubgroup A X) : X) : G) =
        (((y : fixedPointSubgroup A X) : X) : G) :=
      congrArg (fun z : fixedPointSubgroup A G => (z : G)) h
    exact Subtype.ext (Subtype.ext hv)
  have hIr : I ≤ f.range := by
    intro x hx
    refine ⟨⟨⟨x, hIX (mem_map_of_mem _ hx)⟩, ?_⟩, rfl⟩
    intro a
    exact Subtype.ext (x.property a)
  exact ⟨twoComponent_comap_injective f hf hI hIr, map_comap_eq_self hIr⟩

/-- The full GLS II 5.22 for an arbitrary finite two-group action. All four
clauses use the original orbit, subgroup embeddings and quotient maps. The only
earlier-source premise is the genuine universal GLS 5.17 bound. -/
theorem proposition522
    (balance : OrdinaryBalance.TwoLayerCentralizerBalance.{max u v}) (hA : IsPGroup 2 A)
    (I : Subgroup (fixedPointSubgroup A G)) (hI : I.IsTwoComponent) :
    ∃ J : Subgroup G, J.IsTwoComponent ∧
      ∃ hX : IsInvariant A G (actionOrbit (A := A) J),
        let := hX
        let X := actionOrbit (A := A) J
        let D := I.map (fixedPointSubgroup A G).subtype
        let I₀ := I.comap (orbitFixedInclusion (A := A) X)
        D ≤ X ∧ componentOrbit D X = X ∧
        componentOrbit D (twoComponentLayer G) = X ∧
        IsLeast {M : Subgroup G | D ≤ M ∧ M.IsSubnormal} X ∧
        IsLeast {M : Subgroup G | D ≤ M ∧ M ≤ twoComponentLayer G ∧
          (M.subgroupOf (twoComponentLayer G)).IsSubnormal} X ∧
        I₀.IsTwoComponent ∧ I₀.map (orbitFixedInclusion X) = I ∧
        ∀ (N : Subgroup X) [N.Normal] (hN : IsInvariant A X N),
          N ≤ oddTwoCore X →
            letI : MulDistribMulAction A (X ⧸ N) := quotientMulDistribMulAction N hN
            (I₀.map (FixedPoints.quotientMap N hN)).IsTwoComponent := by
  obtain ⟨J, hJ, hIJ, hgen⟩ := exists_action_orbit_normalClosure balance hA I hI
  let X := actionOrbit (A := A) J
  let D := I.map (fixedPointSubgroup A G).subtype
  let hX := actionOrbit_invariant (A := A) J
  let := hX
  obtain ⟨hI₀, hmap⟩ := seed_in_actionOrbit_fixed X I hI hIJ
  have hXL : X ≤ twoComponentLayer G := actionOrbit_le_twoLayer hJ
  have hsub : X.IsSubnormal := actionOrbit_subnormal hJ
  have hmin (M : Subgroup G) (hDM : D ≤ M) (hM : M.IsSubnormal) : X ≤ M :=
    le_subnormal_of_self_normalClosure hgen hM hDM
  have hgenL : componentOrbit D (twoComponentLayer G) = X := by
    apply le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ hIJ
      (twoLayer_le_normalizer_actionOrbit hJ))
    exact hgen.ge.trans (iSup_le fun x =>
      le_iSup (fun l : twoComponentLayer G => D.map (MulAut.conj (l : G)).toMonoidHom)
        ⟨x, hXL x.property⟩)
  refine ⟨J, hJ, hX, hIJ, hgen, hgenL,
    ⟨⟨hIJ, hsub⟩, fun M hM => hmin M hM.1 hM.2⟩,
    ⟨⟨hIJ, hXL, hsub.subgroupOf⟩, ?_⟩, hI₀, hmap, ?_⟩
  · intro M hM
    exact hmin M hM.1 (hM.2.2.trans hM.2.1
      (inferInstance : (twoComponentLayer G).Normal).isSubnormal)
  · intro N _ hN hNcore
    exact map_fixed_twoComponent_oddTwoCore_quotient (actionOrbit_twoLayer_eq_top hJ)
      hA N hN hNcore hI₀

end Finite
end CFSG.Quasithin.ChapterI.GeneralTwoOrbit
