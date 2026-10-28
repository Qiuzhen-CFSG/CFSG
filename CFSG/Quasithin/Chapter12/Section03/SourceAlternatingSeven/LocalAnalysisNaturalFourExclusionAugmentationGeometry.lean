module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisNaturalFourExclusionPointQuotient
public import Theory.Representation.BinaryPermutationEightCover.FixedLine
public import Theory.Representation.BinaryPermutationEightCover.CodeGeometry

/-!
# The original four-dimensional V in augmentation coordinates

The actual residual D=C_L(z)∞ maps onto the point stabilizer of z and
is transitive on the fourteen vectors of V outside its fixed line.
Any full augmentation marking intertwining original K-conjugation sends z
to the constant word. Transitivity and complementation force the other
fourteen vectors to have weight four. Their literal image is a self-dual
four-dimensional code with eight distinct coordinate evaluations.

The full marking is constructed in the separate C.2.7 A₈ application;
selecting that row and the final contradiction remain with
qt-d-1233-natural-coordinates.
Source: Aschbacher–Smith Lemma 12.3.3, printed pp.807–808.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
namespace Setup
variable (S : Setup T L V)

theorem four_componentPointPerfect_transitive
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z x y : G} (hz : z ∈ V) (hx : x ∈ V) (hy : y ∈ V)
    (hz1 : z ≠ 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ l ∈ S.fourComponentPointPerfect z, l * x * l⁻¹ = y := by
  let := S.chosen.actionCentralizer_normal
  let z' : V := ⟨z,hz⟩
  let x' : V := ⟨x,hx⟩
  let y' : V := ⟨y,hy⟩
  have hval (v : V) :
      S.chosen.spaceEquiv (Multiplicative.ofAdd (S.fourPointVector v)) = v :=
    S.chosen.spaceEquiv.apply_symm_apply v
  have hn (v : V) (hv : (v : G) ≠ 1) : S.fourPointVector v ≠ 0 := by
    intro hh
    apply hv
    have he := hval v
    rw [hh,ofAdd_zero,map_one] at he
    exact congrArg Subtype.val he.symm
  have hsep (v : V) (hv : (v : G) ≠ z) : S.fourPointVector v ≠ S.fourPointVector z' := by
    intro he
    apply hv
    exact congrArg Subtype.val ((hval v).symm.trans
      ((congrArg (fun w => S.chosen.spaceEquiv (Multiplicative.ofAdd w)) he).trans (hval z')))
  obtain ⟨g,hg⟩ := BinaryAlternatingSevenControl.pointStabilizer_transitive
    (S.fourFaithfulAction e) (S.chosen.faithfulAction_injective.comp e.symm.injective)
    hd (hn z' hz1) (hn x' hx1) (hn y' hy1) (hsep x' hxz) (hsep y' hyz)
  have hm := S.four_componentPointPerfect_image e hd z'
    (fun he => hz1 (congrArg Subtype.val he))
  obtain ⟨l,hl,he⟩ := hm.ge g.property
  have hact : S.chosen.chosenAction l (S.fourPointVector x') = S.fourPointVector y' := by
    have hh : S.fourFaithfulAction e (S.fourFaithfulProjection e l) =
        S.chosen.chosenAction l := by
      change S.chosen.faithfulAction (e.symm (e (QuotientGroup.mk' _ l))) = _
      rw [e.symm_apply_apply]
      rfl
    rw [← hh,he]
    exact hg
  refine ⟨l,hl,?_⟩
  have ha := congrArg (fun w => (S.chosen.spaceEquiv (Multiplicative.ofAdd w) : G)) hact
  have hc : (S.chosen.spaceEquiv (Multiplicative.ofAdd
      (S.chosen.chosenAction l (S.fourPointVector x'))) : G) =
      (l : G) * x * (l : G)⁻¹ := by
    rw [S.chosen.spaceEquiv_apply]
    change (l : G) * _ * (l : G)⁻¹ = _
    congr 1
    congr 1
    exact (S.chosen.spaceEquiv_apply (S.fourPointVector x')).symm.trans
      (congrArg Subtype.val (hval x'))
  exact hc.symm.trans (ha.trans (congrArg Subtype.val (hval y')))

/-- In augmentation coordinates the original fixed line is the constant
line, and every other nonzero vector of the original V has weight four. -/
theorem four_augmentation_weights
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    {K W : Subgroup G} (hDK : S.fourComponentPointPerfect z ≤ K)
    (hV : V ≤ W) (hzK : z ∈ centralizer (K : Set G))
    (π : K →* alternatingGroup (Fin 8)) (hπ : Function.Surjective π)
    (E : W ≃* Multiplicative (BinaryPermutation.core (Fin 8)))
    (ha : ∀ (k : K) (v w : W), (w : G) = (k : G) * (v : G) * (k : G)⁻¹ →
      (E w).toAdd = BinaryPermutation.alternatingCoreRepresentation (Fin 8) (π k) (E v).toAdd) :
    (E ⟨z,hV hz⟩).toAdd = BinaryPermutation.EightCore.oneWord ∧
      ∀ v : V, (v : G) ≠ 1 → (v : G) ≠ z →
        BinaryPermutation.wordWeight (E (inclusion hV v)).toAdd.val = 4 := by
  have hfix : ∀ a : alternatingGroup (Fin 8),
      BinaryPermutation.alternatingCoreRepresentation (Fin 8) a (E ⟨z,hV hz⟩).toAdd =
        (E ⟨z,hV hz⟩).toAdd := by
    intro a
    obtain ⟨k,rfl⟩ := hπ a
    apply (ha k ⟨z,hV hz⟩ ⟨z,hV hz⟩ ?_).symm
    rw [hzK k k.property,mul_inv_cancel_right]
  have hone : (E ⟨z,hV hz⟩).toAdd = BinaryPermutation.EightCore.oneWord := by
    apply BinaryPermutation.EightCore.fixed_nonzero_eq_oneWord hfix
    intro he
    apply hz1
    have he' : E ⟨z,hV hz⟩ = E 1 := by
      rw [map_one]
      exact congrArg Multiplicative.ofAdd he
    exact congrArg Subtype.val (E.injective he')
  refine ⟨hone,?_⟩
  let := S.chosen.elementary
  let f : Additive V →ₗ[ZMod 2] BinaryPermutation.core (Fin 8) :=
    (E.toMonoidHom.comp (inclusion hV)).toAdditiveLeft.toZModLinearMap 2
  let z' : Additive V := Additive.ofMul ⟨z,hz⟩
  have ht (x y : Additive V) (hx0 : x ≠ 0) (hy0 : y ≠ 0) (hxz : x ≠ z') (hyz : y ≠ z') :
      ∃ a : alternatingGroup (Fin 8),
        BinaryPermutation.alternatingCoreRepresentation (Fin 8) a (f x) = f y := by
    have hn (v : Additive V) (hv : v ≠ 0) : (v.toMul : G) ≠ 1 := by
      intro hh
      exact hv (Additive.toMul.injective (Subtype.ext hh))
    have hs (v : Additive V) (hv : v ≠ z') : (v.toMul : G) ≠ z := by
      intro hh
      exact hv (Additive.toMul.injective (Subtype.ext hh))
    obtain ⟨k,hk,hxy⟩ := S.four_componentPointPerfect_transitive e hd hz
      x.toMul.property y.toMul.property hz1 (hn x hx0) (hn y hy0) (hs x hxz) (hs y hyz)
    exact ⟨π ⟨k,hDK hk⟩,(ha ⟨k,hDK hk⟩ (inclusion hV x.toMul)
      (inclusion hV y.toMul) hxy.symm).symm⟩
  intro v hv hvz
  exact BinaryPermutation.EightCore.weight_four_of_transitive_off_line f hone ht
    (fun hh => hv (congrArg (fun t : Additive V => (t.toMul : G)) hh))
    (fun hh => hvz (congrArg (fun t : Additive V => (t.toMul : G)) hh))

/-- The image of the original V is a four-dimensional self-dual code, and
its eight coordinate evaluations are distinct. -/
theorem four_augmentation_code
    (e : letI := S.chosen.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) S.chosen.space = 4)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    {K W : Subgroup G} (hDK : S.fourComponentPointPerfect z ≤ K)
    (hV : V ≤ W) (hzK : z ∈ centralizer (K : Set G))
    (π : K →* alternatingGroup (Fin 8)) (hπ : Function.Surjective π)
    (E : W ≃* Multiplicative (BinaryPermutation.core (Fin 8)))
    (ha : ∀ (k : K) (v w : W), (w : G) = (k : G) * (v : G) * (k : G)⁻¹ →
      (E w).toAdd = BinaryPermutation.alternatingCoreRepresentation (Fin 8) (π k) (E v).toAdd) :
    letI := S.chosen.elementary
    let f := (E.toMonoidHom.comp (inclusion hV)).toAdditiveLeft.toZModLinearMap 2
    Module.finrank (ZMod 2) f.range = 4 ∧
      BinaryPermutation.EightCore.oneWord ∈ f.range ∧
      (∀ v ∈ f.range, v ≠ 0 → v ≠ BinaryPermutation.EightCore.oneWord →
        BinaryPermutation.wordWeight v.val = 4) ∧
      Function.Injective (fun i : Fin 8 => fun v : f.range => v.val.val i) := by
  let := S.chosen.elementary
  let f := (E.toMonoidHom.comp (inclusion hV)).toAdditiveLeft.toZModLinearMap 2
  let b := S.chosen.spaceEquiv.symm
  let B : Additive V ≃ₗ[ZMod 2] S.chosen.space :=
    LinearEquiv.ofBijective (b.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) b.bijective
  have hvdim : Module.finrank (ZMod 2) (Additive V) = 4 := B.finrank_eq.trans hd
  have hf : Function.Injective f := by
    intro x y he
    apply Additive.toMul.injective
    apply (inclusion_injective hV)
    apply E.injective
    exact congrArg Multiplicative.ofAdd he
  have hdim : Module.finrank (ZMod 2) f.range = 4 :=
    (LinearMap.finrank_range_of_inj hf).trans hvdim
  obtain ⟨h1,hwt⟩ := S.four_augmentation_weights e hd hz hz1 hDK hV hzK π hπ E ha
  have hone : BinaryPermutation.EightCore.oneWord ∈ f.range := ⟨Additive.ofMul ⟨z,hz⟩,h1⟩
  have hw : ∀ v ∈ f.range, v ≠ 0 → v ≠ BinaryPermutation.EightCore.oneWord →
      BinaryPermutation.wordWeight v.val = 4 := by
    rintro _ ⟨v,rfl⟩ hv0 hv1
    apply hwt v.toMul
    · intro he
      have hv : v = 0 := Additive.toMul.injective (Subtype.ext he)
      exact hv0 (hv ▸ f.map_zero)
    · intro he
      have hv : v = Additive.ofMul ⟨z,hz⟩ := Additive.toMul.injective (Subtype.ext he)
      exact hv1 (hv ▸ h1)
  exact ⟨hdim,hone,hw,BinaryPermutation.EightCore.code_evaluation_injective f.range hdim hw⟩

end Setup
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
