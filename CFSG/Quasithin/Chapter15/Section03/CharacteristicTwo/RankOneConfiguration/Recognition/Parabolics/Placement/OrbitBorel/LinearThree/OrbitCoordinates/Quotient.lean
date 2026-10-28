module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.Reduction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Parabolics.Placement.OrbitBorel.LinearThree.Coordinates
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Coordinates for two exchanged linear-three components

Two distinct C-components exchanged by an automorphism, and generating their
ambient group, give a product after quotienting by the ambient two-core.
The intrinsic two-core quotient identifies the first image as PSL₃(2);
the automorphism identifies the second. The simple subnormal images commute
and are disjoint, so multiplication gives the actual product isomorphism.
No radical-free hypothesis on an ambient quotient is used.

Transporting a supplied Sylow subgroup gives the product of its coordinate
Sylow subgroups. Both this product and the transported exchanging automorphism
preserve the image of the same specified subgroup. The automorphism need not
have order two.

Source: Aschbacher–Smith, proof of 15.3.27, printed p.1130 (PDF p.1147),
combined manuscript of 1 March 2004. The actual orbit assembly is in the
parent module `OrbitCoordinates`.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearThree.OrbitCoordinates
universe u
variable {H : Type u} [Group H] [Finite H]

omit [Finite H] in
private theorem model_simple (hm : ClassicalGroup.IsPSL H 3 2) : IsSimpleGroup H := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let _ := Atlas.psl_simple_high_rank (F := F) 3 (by decide)
  exact e.isSimpleGroup

private theorem sylow_eq_prod {A B : Type u} [Group A] [Finite A]
    [Group B] [Finite B] (S : Sylow 2 (A × B)) :
    (S : Subgroup (A × B)) = ((S : Subgroup _).map (MonoidHom.fst A B)).prod
      ((S : Subgroup _).map (MonoidHom.snd A B)) := by
  let S₁ := S.mapSurjective (show Function.Surjective (MonoidHom.fst A B) from
    fun g => ⟨(g, 1), rfl⟩)
  let S₂ := S.mapSurjective (show Function.Surjective (MonoidHom.snd A B) from
    fun k => ⟨(1, k), rfl⟩)
  change (S : Subgroup _) = (S₁ : Subgroup A).prod (S₂ : Subgroup B)
  apply Eq.symm
  apply S.is_maximal'
  · obtain ⟨a, ha⟩ := S₁.isPGroup'.exists_card_eq
    obtain ⟨b, hb⟩ := S₂.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := a + b)
    rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, ha, hb, pow_add]
  · intro x hx
    exact ⟨mem_map_of_mem _ hx, mem_map_of_mem _ hx⟩

set_option backward.isDefEq.respectTransparency false in
/-- The two conjugate components give literal product coordinates modulo the
orbit span's two-core. A Sylow subgroup and the moving automorphism retain
their action on the specified subgroup. -/
theorem of_component_pair (B Y : Subgroup H) (hB : B.IsCComponent)
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 3 2)
    (a : MulAut H) (hne : B ≠ B.map a.toMonoidHom)
    (hgen : B ⊔ B.map a.toMonoidHom = ⊤)
    (hswap : (B.map a.toMonoidHom).map a.toMonoidHom = B)
    (hY : Y.map a.toMonoidHom = Y)
    (T : Sylow 2 H) (hTY : (T : Subgroup H) ≤ normalizer (Y : Set H)) :
    Nonempty (ProductCoordinates B Y) := by
  let N := pCore 2 H
  let _ := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  let q := QuotientGroup.mk' N
  let A := B.map q
  let C := (B.map a.toMonoidHom).map q
  let b := quotientAut N a
  have hqa : q.comp a.toMonoidHom = b.toMonoidHom.comp q := by
    ext x
    exact (quotientAut_apply_mk N a x).symm
  have hAb : A.map b.toMonoidHom = C := by
    change (B.map q).map b.toMonoidHom = (B.map a.toMonoidHom).map q
    rw [map_map, map_map, hqa]
  have hCb : C.map b.toMonoidHom = A := by
    change ((B.map a.toMonoidHom).map q).map b.toMonoidHom = B.map q
    rw [map_map, ← hqa, ← map_map, hswap]
  have hmodelA : ClassicalGroup.IsPSL A 3 2 :=
    hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hB).symm
  have hmodelC : ClassicalGroup.IsPSL C 3 2 :=
    hmodelA.of_mulEquiv ((b.subgroupMap A).trans (MulEquiv.subgroupCongr hAb)).symm
  let _ : IsSimpleGroup A := model_simple hmodelA
  let _ : IsSimpleGroup C := model_simple hmodelC
  have hAc := hB.map_quotient N
  have hCc := (hB.map_equiv a).map_quotient N
  let _ : Group.IsPerfect A := hAc.perfect
  have hneAC : A ≠ C := by
    intro he
    exact hne (hB.eq_of_map_quotient_eq (hB.map_equiv a) N he)
  have hcomm : ⁅A, C⁆ = ⊥ :=
    simple_subnormal_commute_of_ne A C hAc.subnormal hCc.subnormal hneAC
  have hz : center A = ⊥ := by
    rcases (inferInstance : (center A).Normal).eq_bot_or_eq_top with hz | ht
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp ht)).elim
  have hdisj : Disjoint A C := by
    apply Subgroup.disjoint_def.mpr
    intro x hxA hxC
    have hc : (⟨x, hxA⟩ : A) ∈ center A := by
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      exact ((commutator_eq_bot_iff_le_centralizer.mp hcomm y.property) x hxC).symm
    have hx : (⟨x, hxA⟩ : A) = 1 := mem_bot.mp (hz ▸ hc)
    exact congrArg Subtype.val hx
  have htop : A ⊔ C = ⊤ := by
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective q (QuotientGroup.mk'_surjective N)]
  obtain ⟨e₀, he₀⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A C hdisj
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  let e : A × C ≃* (H ⧸ N) :=
    e₀.trans ((MulEquiv.subgroupCongr htop).trans topEquiv)
  have he (x : A) (y : C) : e (x, y) = (x : H ⧸ N) * (y : H ⧸ N) := he₀ x y
  have hAaxis : ((⊤ : Subgroup A).prod (⊥ : Subgroup C)).map e.toMonoidHom = A := by
    ext x
    constructor
    · rintro ⟨⟨l, k⟩, hk, rfl⟩
      have hk1 : k = 1 := hk.2
      change e (l, k) ∈ A
      simpa only [hk1, he, Subgroup.coe_one, mul_one] using l.property
    · intro hx
      refine ⟨(⟨x, hx⟩, 1), ⟨mem_top _, mem_bot.mpr rfl⟩, ?_⟩
      simp [he]
  have hCaxis : ((⊥ : Subgroup A).prod (⊤ : Subgroup C)).map e.toMonoidHom = C := by
    ext x
    constructor
    · rintro ⟨⟨l, k⟩, hl, rfl⟩
      have hl1 : l = 1 := hl.1
      change e (l, k) ∈ C
      simpa only [hl1, he, Subgroup.coe_one, one_mul] using k.property
    · intro hx
      refine ⟨(1, ⟨x, hx⟩), ⟨mem_bot.mpr rfl, mem_top _⟩, ?_⟩
      simp [he]
  have hAback : A.map e.symm.toMonoidHom = (⊤ : Subgroup A).prod (⊥ : Subgroup C) := by
    have hh := congrArg (Subgroup.map e.symm.toMonoidHom) hAaxis
    simpa [map_map] using hh.symm
  have hCback : C.map e.symm.toMonoidHom = (⊥ : Subgroup A).prod (⊤ : Subgroup C) := by
    have hh := congrArg (Subgroup.map e.symm.toMonoidHom) hCaxis
    simpa [map_map] using hh.symm
  let f := e.symm.toMonoidHom.comp q
  have hf : Function.Surjective f := e.symm.surjective.comp (QuotientGroup.mk'_surjective N)
  let U := T.mapSurjective hf
  let a' : MulAut (A × C) := (e.trans b).trans e.symm
  have hfe : e.toMonoidHom.comp a'.toMonoidHom = b.toMonoidHom.comp e.toMonoidHom := by
    ext x
    exact e.apply_symm_apply (b (e x))
  refine ⟨{
    First := A
    Second := C
    firstModel := hmodelA
    secondModel := hmodelC
    quotient := f
    surjective := hf
    kernel_two := ?_
    first_image := ?_
    firstSylow := U.mapSurjective (f := MonoidHom.fst A C) (fun x => ⟨(x, 1), rfl⟩)
    secondSylow := U.mapSurjective (f := MonoidHom.snd A C) (fun x => ⟨(1, x), rfl⟩)
    sylow_invariant := ?_
    exchange := a'
    exchange_first := ?_
    exchange_second := ?_
    exchange_invariant := ?_
  }⟩
  · have hk : f.ker = N :=
      (MonoidHom.ker_comp_of_injective q e.symm.toMonoidHom e.symm.injective).trans
        (QuotientGroup.ker_mk' N)
    exact pCore_isPGroup.of_equiv (MulEquiv.subgroupCongr hk.symm)
  · exact (map_map _ _ _).symm.trans hAback
  · change ((U : Subgroup _).map (MonoidHom.fst A C)).prod
      ((U : Subgroup _).map (MonoidHom.snd A C)) ≤ _
    rw [← sylow_eq_prod U]
    exact (map_mono hTY).trans (Y.le_normalizer_map f)
  · apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_map, hfe, ← map_map, hAaxis, hAb, hCaxis]
  · apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_map, hfe, ← map_map, hCaxis, hCb, hAaxis]
  · have hfa : a'.toMonoidHom.comp f = f.comp a.toMonoidHom := by
      apply MonoidHom.ext
      intro x
      change e.symm (b (e (e.symm (q x)))) = e.symm (q (a x))
      rw [e.apply_symm_apply]
      exact congrArg e.symm (quotientAut_apply_mk N a x)
    rw [map_map, hfa, ← map_map, hY]


end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Parabolics.Placement.OrbitBorel.LinearThree.OrbitCoordinates
