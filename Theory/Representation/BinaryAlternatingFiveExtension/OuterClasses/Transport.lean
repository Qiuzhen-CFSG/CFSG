module
public import Theory.Representation.BinaryAlternatingFiveExtension.OuterClasses

/-!
# Affine Sylow transport of the outer two-class table

An actual Sylow conjugacy in the affine plane preserves translations and
permutation parity. The coordinate two-class calculation therefore retains
conjugators in that same affine group. The cyclic commutator, graph-centralizer
order and central root are transported structurally.

Source application: the outer-coset cover in Aschbacher--Smith F.4.37, p.293.
-/

@[expose] public noncomputable section
namespace BinaryPermutation.AlternatingFiveExtension.OuterClasses
open SylowModel SylowCommutator Subgroup
open scoped Pointwise commutatorElement

private theorem exists_coordinate_conjugacy (S : Sylow 2 Model) :
    ∃ (a : Model) (e : S ≃* PlaneWreath),
      (translations.subgroupOf S).map e.toMonoidHom = baseMap.range ∧
      ∀ x : S, embedding (e x) = (MulAut.conj a) x.val := by
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
  refine ⟨a,e,?_,he⟩
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hmem x).mpr hx
  · intro hy
    exact ⟨e.symm y,(hmem (e.symm y)).mp (by simpa using hy),e.apply_symm_apply y⟩

/-- Sylow conjugacy transports the outer two-class calculation in the full affine plane. -/
theorem outer_classes_in_sylow (S : Sylow 2 Model) (f z t : S)
    (hf : orderOf f=2) (ht : orderOf t=2) (htV : t.val∈translations)
    (hc : ⁅translations.subgroupOf S,zpowers f⁆=zpowers t)
    (hcard : Nat.card (centralizer ({f} : Set S))=32)
    (hz : z∈center S) (hz1 : z≠1)
    (x : S) (hx : x*x=1) (hxodd : x.val.right ∉ alternatingGroup (Fin 5)) :
    IsConj f.val x.val ∨ IsConj (f.val*z.val) x.val := by
  obtain ⟨a,e,he,hcomp⟩ := exists_coordinate_conjugacy S
  have hcomm := congrArg (fun U : Subgroup S => U.map e.toMonoidHom) hc
  rw [map_commutator,he,MonoidHom.map_zpowers,MonoidHom.map_zpowers] at hcomm
  obtain ⟨u,hu⟩ : e t∈baseMap.range := by
    rw [←he]
    exact mem_map_of_mem _ htV
  have huo : orderOf (baseMap u)=2 := by rw [hu,e.orderOf_eq,ht]
  change ⁅baseMap.range,zpowers (e f)⁆=zpowers (e t) at hcomm
  rw [←hu] at hcomm
  have hfc : Nat.card (centralizer ({e f} : Set PlaneWreath))=32 :=
    (Nat.card_congr (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e f).symm.toEquiv).trans hcard
  have hzc : e z∈center PlaneWreath := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨v,rfl⟩ := e.surjective y
    exact (map_mul e v z).symm.trans
      ((congrArg e (mem_center_iff.mp hz v)).trans (map_mul e z v))
  have hzn : e z≠1 := fun hh => hz1 (e.injective (hh.trans e.map_one.symm))
  have hxp : e x*e x=1 := by rw [←map_mul,hx,map_one]
  have hxo : (embedding (e x)).right ∉ alternatingGroup (Fin 5) := by
    rw [hcomp]
    intro hh
    apply hxodd
    rw [Equiv.Perm.mem_alternatingGroup] at hh ⊢
    change Equiv.Perm.sign (a.right * x.val.right * a.right⁻¹)=1 at hh
    simp only [map_mul,map_inv] at hh
    rwa [mul_comm (Equiv.Perm.sign a.right) (Equiv.Perm.sign x.val.right),mul_inv_cancel_right] at hh
  have h := outer_classes (e f) (e z) u ((e.orderOf_eq f).trans hf) huo hcomm hfc hzc hzn (e x) hxp hxo
  have hback {v w : Model} (hh : IsConj ((MulAut.conj a) v) ((MulAut.conj a) w)) : IsConj v w := by
    have hh' := (MulAut.conj a).symm.toMonoidHom.map_isConj hh
    change IsConj ((MulAut.conj a).symm ((MulAut.conj a) v))
      ((MulAut.conj a).symm ((MulAut.conj a) w)) at hh'
    simpa only [MulEquiv.symm_apply_apply] using hh'
  rcases h with h | h
  · exact Or.inl (hback (by simpa only [hcomp] using h))
  · apply Or.inr
    apply hback
    simpa only [←map_mul,hcomp,Subgroup.coe_mul] using h

end BinaryPermutation.AlternatingFiveExtension.OuterClasses
