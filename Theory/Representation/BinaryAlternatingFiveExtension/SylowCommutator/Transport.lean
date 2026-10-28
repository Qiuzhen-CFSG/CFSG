module
public import Theory.Representation.BinaryAlternatingFiveExtension.SylowCommutator
public import Theory.GroupTheory.CompatibleRestriction

/-!
# Marked affine Sylow transport for the cyclic displacement line

Conjugacy of Sylow subgroups preserves the normal translation group in the
binary affine symmetric-five model. Its coordinate Sylow comparison therefore
retains that group, even though no particular outer involution is marked by
the comparison. The exact identity `[Q,f] = <t>` and the order of `t` are
then sufficient to transport the dihedral-product centralizer to any
injective ambient realization.

Source: the local calculation in Aschbacher--Smith F.4.37 and F.5.3,
printed pp.293 and 300--301.
-/

@[expose] public noncomputable section
namespace BinaryPermutation.AlternatingFiveExtension.SylowCommutator
open Subgroup SylowModel
open scoped commutatorElement Pointwise

def translations : Subgroup Model := (SemidirectProduct.inl : V →* Model).range

instance : translations.Normal := by
  dsimp [translations]
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

theorem coordinates_surjective : Function.Surjective coordinates := by
  intro v
  let a := coreCoordinates.symm v
  refine ⟨fun i => if i = 1 then a.1 else a.2,?_⟩
  change coreCoordinates ((if (1:Bit) = 1 then a.1 else a.2),
    (if (Multiplicative.ofAdd 1:Bit) = 1 then a.1 else a.2)) = v
  simp only [ite_true,show (Multiplicative.ofAdd 1:Bit) ≠ 1 by decide,ite_false]
  exact coreCoordinates.apply_symm_apply v

theorem embedding_base (v : V4) : embedding (baseMap v) = SemidirectProduct.inl (coordinates v) := by
  apply SemidirectProduct.ext
  · rfl
  · change actor (1 : Actor) = 1
    exact map_one actor

theorem map_base : baseMap.range.map embedding = translations := by
  apply le_antisymm
  · rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    exact ⟨coordinates v,embedding_base v |>.symm⟩
  · rintro _ ⟨v,rfl⟩
    obtain ⟨u,rfl⟩ := coordinates_surjective v
    exact ⟨baseMap u,⟨u,rfl⟩,embedding_base u⟩

theorem embedding_mem_translations_iff (x : PlaneWreath) :
    embedding x ∈ translations ↔ x ∈ baseMap.range := by
  rw [←map_base]
  exact mem_map_iff_mem embedding_injective

/-- Sylow conjugacy retains the original translation group. -/
theorem exists_marked_sylow_equiv (S : Sylow 2 Model) :
    ∃ e : S ≃* PlaneWreath,
      (translations.subgroupOf S).map e.toMonoidHom = baseMap.range := by
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq Model S SylowModel.standardSylow
  have hmap : (S : Subgroup Model).map (MulAut.conj a).toMonoidHom = embedding.range := by
    change ((a • S : Sylow 2 Model) : Subgroup Model) = embedding.range
    rw [ha]
    rfl
  let e : S ≃* PlaneWreath := ((MulAut.conj a).subgroupMap S).trans
    ((MulEquiv.subgroupCongr hmap).trans (MonoidHom.ofInjective embedding_injective).symm)
  have he (x : S) : embedding (e x) = MulAut.conj a x.val := by
    exact congrArg Subtype.val ((MonoidHom.ofInjective embedding_injective).apply_symm_apply
      ((MulEquiv.subgroupCongr hmap) ((MulAut.conj a).subgroupMap S x)))
  have hmem (x : S) : e x ∈ baseMap.range ↔ x.val ∈ translations := by
    rw [←embedding_mem_translations_iff,he]
    change a * x.val * a⁻¹ ∈ translations ↔ x.val ∈ translations
    exact (mem_normalizer_iff.mp (show a∈normalizer (translations : Set Model) by
      rw [normalizer_eq_top]; trivial) x.val).symm
  refine ⟨e,?_⟩
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hmem x).mpr hx
  · intro hy
    exact ⟨e.symm y,(hmem (e.symm y)).mp (by simpa using hy),e.apply_symm_apply y⟩

variable {G : Type*} [Group G]

/-- A marked Sylow equivalence transports the cyclic displacement argument. -/
theorem centralizer_of_marked_equiv (T Q : Subgroup G) (hQT : Q ≤ T)
    (e : T ≃* PlaneWreath) (he : (Q.subgroupOf T).map e.toMonoidHom = baseMap.range)
    (f t : G) (hf : f ∈ T) (ht : t ∈ Q) (ho : orderOf t = 2)
    (hc : ⁅Q,zpowers f⁆ = zpowers t) :
    Nonempty ((T ⊓ centralizer ({t} : Set G) : Subgroup G) ≃*
      DihedralGroup 4 × DihedralGroup 4) := by
  let fT : T := ⟨f,hf⟩
  let tT : T := ⟨t,hQT ht⟩
  have hcomm : ⁅Q.subgroupOf T,zpowers fT⁆ = zpowers tT := by
    apply map_injective T.subtype_injective
    rw [map_commutator,subgroupOf_map_subtype,inf_eq_left.mpr hQT,MonoidHom.map_zpowers,MonoidHom.map_zpowers]
    exact hc
  have hcomm' := congrArg (fun U : Subgroup T => U.map e.toMonoidHom) hcomm
  rw [map_commutator,he,MonoidHom.map_zpowers,MonoidHom.map_zpowers] at hcomm'
  obtain ⟨u,hu⟩ : e tT ∈ baseMap.range := by
    rw [←he]
    exact mem_map_of_mem _ ht
  have huo : orderOf (baseMap u) = 2 := by
    rw [hu, e.orderOf_eq]
    exact (orderOf_injective T.subtype T.subtype_injective tT).symm.trans ho
  change ⁅baseMap.range,zpowers (e fT)⁆ = zpowers (e tT) at hcomm'
  rw [←hu] at hcomm'
  obtain ⟨d⟩ := centralizer_of_cyclic_base_commutator (e fT) u huo hcomm'
  let c : centralizer ({tT} : Set T) ≃*
      (T ⊓ centralizer ({t} : Set G) : Subgroup G) := {
    toFun x := ⟨x.val.val,x.val.property,
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩
    invFun x := ⟨⟨x.val,x.property.1⟩,mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2))⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  refine ⟨c.symm.trans ((Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e tT).trans ?_)⟩
  exact (MulEquiv.subgroupCongr (congrArg (fun x => centralizer ({x} : Set PlaneWreath)) hu.symm)).trans d


theorem exists_marked_sylow_embedding_equiv (j : Model →* G) (hj : Function.Injective j)
    (S : Sylow 2 Model) :
    ∃ e : ((S : Subgroup Model).map j) ≃* PlaneWreath,
      ((translations.map j).subgroupOf ((S : Subgroup Model).map j)).map
        e.toMonoidHom = baseMap.range := by
  obtain ⟨e,he⟩ := exists_marked_sylow_equiv S
  let d := (S : Subgroup Model).equivMapOfInjective j hj
  have hQ : ((translations.map j).subgroupOf ((S : Subgroup Model).map j)).map
      d.symm.toMonoidHom = translations.subgroupOf S := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨v,hv,hvy⟩ := hy
      have hd : j (d.symm y).val = y.val := congrArg Subtype.val (d.apply_symm_apply y)
      change (d.symm y).val ∈ translations
      rw [hj (hd.trans hvy.symm)]
      exact hv
    · intro hx
      refine ⟨d x,?_,d.symm_apply_apply x⟩
      exact ⟨x.val,hx,rfl⟩
  have hmark : ((translations.map j).subgroupOf ((S : Subgroup Model).map j)).map
      (d.symm.trans e).toMonoidHom = baseMap.range := by
    change ((translations.map j).subgroupOf ((S : Subgroup Model).map j)).map
      (e.toMonoidHom.comp d.symm.toMonoidHom) = _
    rw [←map_map,hQ,he]
  exact ⟨d.symm.trans e,hmark⟩

theorem centralizer_of_affine_sylow_embedding (j : Model →* G) (hj : Function.Injective j)
    (S : Sylow 2 Model) (hQS : translations ≤ (S : Subgroup Model))
    (f t : G) (hf : f ∈ (S : Subgroup Model).map j)
    (ht : t ∈ translations.map j) (ho : orderOf t = 2)
    (hc : ⁅translations.map j,zpowers f⁆ = zpowers t) :
    Nonempty ((((S : Subgroup Model).map j) ⊓ centralizer ({t} : Set G) : Subgroup G) ≃*
      DihedralGroup 4 × DihedralGroup 4) := by
  obtain ⟨e,he⟩ := exists_marked_sylow_embedding_equiv j hj S
  exact centralizer_of_marked_equiv _ _ (map_mono hQS) e he f t hf ht ho hc

end BinaryPermutation.AlternatingFiveExtension.SylowCommutator
