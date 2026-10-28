module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.DihedralCubic.SmallSpanEndpoints
public import Theory.Representation.BinaryConjugationSection.QuotientActor
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.ElementaryAbelian.ExtraspecialEquiv

/-!
# The literal cubic small-span action

For a normal section L/Z, conjugation through H/C_H(L/Z) gives a faithful
binary representation on the original quotient. Restricting to the join of
the images of K and V provides the local actor required by the small-support
classification. If V has image of order two, its generator is an actual
involution of that join.

The identities K = [K,V] and L = [L,K] give the actor and module commutators.
The order of the image of [L,V] in H/Z bounds the literal displacement space,
so it bounds the involution's fixed codimension. The marked endpoint rows
then transport from K's subgroup inside the join to K's original quotient
image. No faithful action or module-generation witness is assumed separately.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, the cubic
small-span step of E.2.17, using the small-support classification D.2.17.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterE.DihedralCubic
universe u
variable {G W : Type u} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

private theorem representation_join_rows
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (R A : Subgroup G) [R.Normal] (hp : IsPGroup 3 R)
    (ha : Nat.card A = 2) (hc : ⁅R,A⁆ = R)
    (hm : subspaceCommutator ρ ⊤ R = ⊤)
    (hd : Nat.card (subspaceCommutator ρ ⊤ A) ≤ 4)
    (hsize : 16 ≤ Nat.card W) :
    (Nat.card W = 16 ∧ (Nat.card R = 3 ∨ Nat.card R = 9)) ∨
      (Nat.card W = 64 ∧ IsExtraspecial 3 R ∧ Nat.card R = 27) := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let D := R ⊔ A
  let R₀ := R.subgroupOf D
  let A₀ := A.subgroupOf D
  let τ := ρ.comp D.subtype
  have hr : R₀.map D.subtype = R := map_subgroupOf_eq_of_le le_sup_left
  have ha' : A₀.map D.subtype = A := map_subgroupOf_eq_of_le le_sup_right
  let e : R₀ ≃* R := subgroupOfEquivOfLe le_sup_left
  have he : Nat.card R₀ = Nat.card R := Nat.card_congr e.toEquiv
  have ha₀ : Nat.card A₀ = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe le_sup_right).toEquiv).trans ha
  obtain ⟨t,ht⟩ := A₀.isCyclic_iff_exists_zpowers_eq_top.mp (isCyclic_of_prime_card ha₀)
  have ht2 : orderOf t = 2 := by rw [← Nat.card_zpowers,ht,ha₀]
  have hgen : R₀ ⊔ zpowers t = ⊤ := by
    apply map_injective D.subtype_injective
    rw [Subgroup.map_sup,hr,ht,ha',←MonoidHom.range_eq_map,D.range_subtype]
  have hcomm : ⁅R₀,zpowers t⁆ = R₀ := by
    apply map_injective D.subtype_injective
    rw [map_commutator,hr,ht,ha',hc]
  have hmove : subspaceCommutator τ ⊤ R₀ = ⊤ := by
    rw [subspaceCommutator_comp_map,hr,hm]
  have hn : R₀ ≠ ⊥ := by
    intro hzero
    have hbot : subspaceCommutator τ ⊤ R₀ = ⊥ := by
      apply (subspaceCommutator_eq_bot_iff τ ⊤ R₀).mpr
      intro v hv a
      have haone : (a : D) = 1 := by simpa [hzero] using a.property
      change τ (a : D) v = v
      rw [haone,map_one]
      rfl
    have hz : ∀ v : W, v = 0 := by
      intro v
      have hv : v ∈ subspaceCommutator τ ⊤ R₀ := by rw [hmove]; trivial
      simpa only [hbot,Submodule.mem_bot] using hv
    let : Subsingleton W := ⟨fun x y => (hz x).trans (hz y).symm⟩
    have hone : Nat.card W = 1 := Nat.card_unique
    omega
  have hsmall : fixedCodim τ (zpowers t) ≤ 2 := by
    have hrank : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) ≤ 2 := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hd
      by_contra h
      have hl := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 3 ≤
        Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ A) by omega)
      norm_num at hl
      omega
    rw [fixedCodim_zpowers_eq_displacement_rank]
    apply (Submodule.finrank_mono ?_).trans hrank
    rintro _ ⟨v,rfl⟩
    change τ t v - v ∈ subspaceCommutator ρ ⊤ A
    apply Submodule.subset_span
    exact ⟨(t : G),by
      have hta : t ∈ A₀ := ht ▸ mem_zpowers t
      exact hta,v,Submodule.mem_top,rfl⟩
  have hfaith : Function.Injective τ := hf.comp D.subtype_injective
  have hp₀ : IsPGroup 3 R₀ := hp.of_equiv e.symm
  have rows := small_span_representation_cardinalities R₀ hn hp₀ t ht2 hgen hcomm
    hmove hsmall hfaith hsize
  rcases rows with h | h
  · exact Or.inl (by simpa only [he] using h)
  · exact Or.inr ⟨h.1,IsExtraspecial.of_mulEquiv e h.2.1,he ▸ h.2.2⟩

end CFSG.Quasithin.ChapterE.DihedralCubic

namespace CFSG.Quasithin.ChapterE.DihedralCubic
universe u
variable {H : Type u} [Group H] [Finite H]

/-- The cubic rows for the literal section action through its full pointwise kernel. -/
theorem small_span_section_action
    (K L Z V : Subgroup H) [K.Normal] [L.Normal] [Z.Normal]
    (hZL : Z ≤ L) [IsElementaryAbelian 2 (L ⧸ Z.subgroupOf L)]
    (hK : K = ⁅K,V⁆) (hL : L = ⁅L,K⁆)
    (hd : Nat.card (⁅L,V⁆.map (QuotientGroup.mk' Z)) ≤ 4)
    (hsize : 16 ≤ Nat.card (L ⧸ Z.subgroupOf L)) :
    letI := centralizerModulo_top_normal L Z
    let q := QuotientGroup.mk' (centralizerModulo ⊤ L Z)
    IsPGroup 3 (K.map q) → Nat.card (V.map q) = 2 →
      (Nat.card (L ⧸ Z.subgroupOf L) = 16 ∧
        (Nat.card (K.map q) = 3 ∨ Nat.card (K.map q) = 9)) ∨
      (Nat.card (L ⧸ Z.subgroupOf L) = 64 ∧
        IsExtraspecial 3 (K.map q) ∧ Nat.card (K.map q) = 27) := by
  let := centralizerModulo_top_normal L Z
  let C := centralizerModulo ⊤ L Z
  let q := QuotientGroup.mk' C
  dsimp only
  intro hp ha
  let π : (⊤ : Subgroup H) →* H ⧸ C := q.comp (⊤ : Subgroup H).subtype
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk'_surjective C).comp topEquiv.surjective
  have hk : ∀ a : (⊤ : Subgroup H), π a = 1 ↔ ∀ u ∈ L, ⁅(a : H),u⁆ ∈ Z := by
    intro a
    change ((a : H) : H ⧸ C) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    change (a : H) ∈ centralizerModulo ⊤ L Z ↔ _
    rw [mem_centralizerModulo_iff]
    constructor
    · rintro ⟨_,hc⟩ u hu
      simpa only [commutatorElement_inv] using Z.inv_mem (hc u hu)
    · intro hc
      refine ⟨mem_top _,fun u hu => ?_⟩
      simpa only [commutatorElement_inv] using Z.inv_mem (hc u hu)
  obtain ⟨ρ,c,hfaith,_⟩ := BinaryConjugationSection.exists_faithful_quotient_actor
    (⊤ : Subgroup H) L Z le_top hZL le_normalizer_of_normal le_normalizer_of_normal π hπ hk
  have hmap (X : Subgroup H) : (X.subgroupOf ⊤).map π = X.map q := by
    rw [show π = q.comp (⊤ : Subgroup H).subtype from rfl,←map_map,
      map_subgroupOf_eq_of_le le_top]
  have hfull : c.imageSpace L = ⊤ := by
    apply top_unique
    intro v hv
    obtain ⟨u,hu⟩ := c.onto (Multiplicative.ofAdd v)
    exact (c.mem_imageSpace_iff L v).mpr ⟨u,u.property,congrArg Multiplicative.toAdd hu⟩
  have hmove : subspaceCommutator ρ ⊤ (K.map q) = ⊤ := by
    have hh := c.imageSpace_commutator K L le_top le_rfl
    rw [commutator_comm K L,←hL,hfull,subspaceCommutator_comp_map,hmap] at hh
    exact hh.symm
  have hdisplacement : Nat.card (subspaceCommutator ρ ⊤ (V.map q)) ≤ 4 := by
    have hh : Nat.card (c.imageSpace ⁅L,V⁆) ≤ 4 := by
      rw [c.imageSpace_card_eq_relIndex _ (commutator_le_left L V)]
      rw [←QuotientGroup.ker_mk' Z,relIndex_ker]
      exact hd
    rw [commutator_comm L V,c.imageSpace_commutator V L le_top le_rfl,
      hfull,subspaceCommutator_comp_map,hmap] at hh
    exact hh
  let : (K.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective C)
  have hcomm : ⁅K.map q,V.map q⁆ = K.map q := by rw [←map_commutator,←hK]
  exact representation_join_rows ρ hfaith (K.map q) (V.map q) hp ha hcomm hmove
    hdisplacement hsize
end CFSG.Quasithin.ChapterE.DihedralCubic
