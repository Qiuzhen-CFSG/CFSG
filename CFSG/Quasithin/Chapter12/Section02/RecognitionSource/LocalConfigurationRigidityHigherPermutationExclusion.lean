module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationRigidityHigherSections
public import Theory.Representation.BinaryRepeatedNaturalSections

/-!
# The marked permutation-module contradiction in 12.2.25

The earlier displacement calculation gives the same natural SL₃(2) marking
on W=U∩V and on R/(W C_T(L)), where R=C_T(U). The deleted permutation
module on seven letters is self-dual, whereas that natural three-space is
not. Pulling back its form and descending through the displacement map
therefore excludes a marked permutation quotient R/C_T(L).

The second source application constructs the quotient map itself from
R=U×C_T(L). Thus an actual permutation-module marking on the original U
is impossible. All conjugation equations use the literal residual Y and
its original action; neither equal dimensions nor an abstract A₇ label
is used to identify the restriction.

The containing-component sieve and recognition of its exceptional module
still belong to qt-d-12213-local-rigidity. These exclusion theorems do not
assert Y=Y_R or completion of 12.2.25--26.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
original 12.2.25, printed p.805.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V H P U : Subgroup G}

/-- The actual radical cannot cover the six-dimensional permutation module
with kernel C_T(L) and its literal Y-action. This retains the matrix marking
on both natural sections instead of identifying constituents by dimension. -/
theorem source_no_marked_permutation_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 4) (C : CyclicLocalAnalysis T L V 4 H P U)
    (hnone : NoEscape L V)
    (a : rigidityHyperplaneResidual L U V →* Equiv.Perm (Fin 7))
    (f : sectionRadical T U →* Multiplicative (BinaryPermutation.natural (Fin 7)))
    (hf : Function.Surjective f)
    (hker : f.ker = ((T : Subgroup G) ⊓ centralizer (L : Set G)).subgroupOf
      (sectionRadical T U))
    (hact : ∀ (y : rigidityHyperplaneResidual L U V) (r : sectionRadical T U),
      f ((sectionRadical T U).normalizerMonoidHom
        ⟨y,(RigidityKernel.source_centralizers h D structural A C hnone).residual_normalizes
          y.property⟩ r) = Multiplicative.ofAdd
            (BinaryPermutation.naturalRepresentation (Fin 7) (a y) (f r).toAdd)) : False := by
  let R := sectionRadical T U
  let Y := rigidityHyperplaneResidual L U V
  let W := U ⊓ V
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  let : IsElementaryAbelian 2 R := B.elementary
  have hWR : W ≤ R := le_inf (inf_le_left.trans C.core_le_sylow)
    (by let := C.elementary; exact inf_le_left.trans (le_centralizer U))
  have hZR : Z ≤ R := le_sup_right.trans B.centralizer_split.symm.le
  obtain ⟨q,c,δ,hq,hδ,hδker,hc,e,he,hquot⟩ := source_radical_natural_sections h D structural A C hnone
    (by decide : 3 < 4)
  let β : Y →* MulAut R := R.normalizerMonoidHom.comp (inclusion B.residual_normalizes)
  let σ : Representation (ZMod 2) Y (Additive R) := {
    toFun y := (β y).toMonoidHom.toAdditive.toZModLinearMap 2
    map_one' := by
      apply LinearMap.ext
      intro r
      change β 1 r.toMul = r.toMul
      rw [map_one]
      rfl
    map_mul' y z := by
      apply LinearMap.ext
      intro r
      change β (y*z) r.toMul = β y (β z r.toMul)
      rw [map_mul]
      rfl }
  let iw : Multiplicative BinaryLinearThree.Vector →* R :=
    (inclusion hWR).comp c.symm.toMonoidHom
  have hiw (y : Y) (v : BinaryLinearThree.Vector) :
      iw (Multiplicative.ofAdd (BinaryLinearThree.W (q y) v)) =
        β y (iw (Multiplicative.ofAdd v)) := by
    apply Subtype.ext
    change (c.symm (Multiplicative.ofAdd (BinaryLinearThree.W (q y) v)) : G) =
      (y : G) * (c.symm (Multiplicative.ofAdd v) : G) * (y : G)⁻¹
    have he := hc y (c.symm (Multiplicative.ofAdd v))
    rw [c.apply_symm_apply] at he
    exact congrArg (fun w : W => (w : G)) ((c.symm_apply_eq).mpr he.symm)
  let i : Representation.IntertwiningMap (BinaryLinearThree.W.comp q) σ := {
    toLinearMap := iw.toAdditiveRight.toZModLinearMap 2
    isIntertwining' := by
      intro y
      apply LinearMap.ext
      intro v
      exact congrArg Additive.ofMul (hiw y v) }
  let pw := c.toMonoidHom.comp δ
  let p : σ.IntertwiningMap (BinaryLinearThree.W.comp q) := {
    toLinearMap := pw.toAdditiveLeft.toZModLinearMap 2
    isIntertwining' := by
      intro y
      apply LinearMap.ext
      intro r
      change (c (δ (β y r.toMul))).toAdd =
        BinaryLinearThree.W (q y) (c (δ r.toMul)).toAdd
      have hh := hquot y r.toMul
      rw [he,he] at hh
      exact congrArg Multiplicative.toAdd hh }
  have hp : Function.Surjective p := c.surjective.comp hδ
  let τ := (BinaryPermutation.naturalRepresentation (Fin 7)).comp a
  let F : σ.IntertwiningMap τ := {
    toLinearMap := f.toAdditiveLeft.toZModLinearMap 2
    isIntertwining' := by
      intro y
      apply LinearMap.ext
      intro r
      exact congrArg Multiplicative.toAdd (hact y r.toMul) }
  have hF : Function.Surjective F := hf
  have hpk : p.toLinearMap.ker ≤ i.toLinearMap.range ⊔ F.toLinearMap.ker := by
    intro r hr
    have hdr : δ r.toMul = 1 := c.injective (by
      change c (δ r.toMul) = c 1
      rw [map_one]
      exact congrArg Multiplicative.ofAdd hr)
    have hmem : (r.toMul : G) ∈ W ⊔ Z := by
      change r.toMul ∈ (W ⊔ Z).subgroupOf R
      rw [← hδker]
      exact MonoidHom.mem_ker.mpr hdr
    have hn : Z ≤ normalizer (W : Set G) :=
      ((hZR.trans inf_le_right).trans (centralizer_le inf_le_left)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hprod : (r.toMul : G) ∈ (W : Set G) * (Z : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left W Z hn]
      exact hmem
    obtain ⟨w,hw,z,hz,he⟩ := hprod
    refine Submodule.mem_sup.mpr ⟨Additive.ofMul (⟨w,hWR hw⟩ : R),?_,
      Additive.ofMul (⟨z,hZR hz⟩ : R),?_,?_⟩
    · refine ⟨(c ⟨w,hw⟩).toAdd,?_⟩
      change Additive.ofMul (iw (c ⟨w,hw⟩)) = _
      simp only [iw,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply]
      rfl
    · change (f ⟨z,hZR hz⟩).toAdd = 0
      exact congrArg Multiplicative.toAdd (MonoidHom.mem_ker.mp (hker.symm ▸ hz))
    · exact congrArg Additive.ofMul (Subtype.ext he)
  have hFi : F.comp i ≠ 0 := by
    intro he
    let v : BinaryLinearThree.Vector := Pi.single 0 1
    have hz := congrArg (fun b : Representation.IntertwiningMap (BinaryLinearThree.W.comp q) τ => b v) he
    have hk : iw (Multiplicative.ofAdd v) ∈ f.ker :=
      MonoidHom.mem_ker.mpr (congrArg Multiplicative.ofAdd hz)
    have hzZ : (iw (Multiplicative.ofAdd v) : G) ∈ Z := by
      change iw (Multiplicative.ofAdd v) ∈ Z.subgroupOf R
      rwa [← hker]
    have hwU : (iw (Multiplicative.ofAdd v) : G) ∈ U :=
      (c.symm (Multiplicative.ofAdd v)).property.1
    have hone : c.symm (Multiplicative.ofAdd v) = 1 :=
      Subtype.ext (disjoint_def.mp B.centralizer_disjoint hwU hzZ)
    have hm : Multiplicative.ofAdd v = (1 : Multiplicative BinaryLinearThree.Vector) := by
      simpa only [c.apply_symm_apply,map_one] using congrArg c hone
    have hv0 : v = 0 := congrArg Multiplicative.toAdd hm
    have h01 := congrFun hv0 0
    simp [v] at h01
  exact BinaryLinearThree.no_permutation_cover_of_repeated_natural_sections
    q hq σ a i p hp F hF hpk hFi

/-- In particular, the original six-space U cannot be the marked permutation
module in the exceptional A₇ branch. The projection R → U and its kernel
are constructed from the proved centralizer splitting. -/
theorem source_no_marked_permutation_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V) (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V 4) (C : CyclicLocalAnalysis T L V 4 H P U)
    (hnone : NoEscape L V)
    (hn : rigidityHyperplaneResidual L U V ≤ normalizer (U : Set G))
    (a : rigidityHyperplaneResidual L U V →* Equiv.Perm (Fin 7))
    (e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 7)))
    (he : ∀ (y : rigidityHyperplaneResidual L U V) (u : U),
      e (U.normalizerMonoidHom ⟨y,hn y.property⟩ u) = Multiplicative.ofAdd
        (BinaryPermutation.naturalRepresentation (Fin 7) (a y) (e u).toAdd)) : False := by
  let R := sectionRadical T U
  let Y := rigidityHyperplaneResidual L U V
  let Z := (T : Subgroup G) ⊓ centralizer (L : Set G)
  let B := RigidityKernel.source_centralizers h D structural A C hnone
  have hZR : Z ≤ R := le_sup_right.trans B.centralizer_split.symm.le
  have hc : U ≤ centralizer (Z : Set G) := le_centralizer_iff.mp (hZR.trans inf_le_right)
  obtain ⟨b,hb⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting U Z
    B.centralizer_disjoint hc
  let E : U × Z ≃* R := b.trans (MulEquiv.subgroupCongr B.centralizer_split.symm)
  have hE (u : U) (z : Z) : (E (u,z) : G) = (u : G) * (z : G) := hb u z
  let π : R →* U := (MonoidHom.fst U Z).comp E.symm.toMonoidHom
  have hπ (u : U) (z : Z) : π (E (u,z)) = u := by
    change (E.symm (E (u,z))).1 = u
    rw [E.symm_apply_apply]
  let f := e.toMonoidHom.comp π
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨u,rfl⟩ := e.surjective w
    exact ⟨E (u,1),congrArg e (hπ u 1)⟩
  have hk : f.ker = Z.subgroupOf R := by
    ext r
    obtain ⟨⟨u,z⟩,rfl⟩ := E.surjective r
    change e (π (E (u,z))) = 1 ↔ (E (u,z) : G) ∈ Z
    rw [hπ,hE]
    constructor
    · intro hu
      have hu1 : u = 1 := e.injective (hu.trans (map_one e).symm)
      rw [hu1,coe_one,one_mul]
      exact z.property
    · intro hz
      have huZ : (u : G) ∈ Z := by
        have hh := Z.mul_mem hz (Z.inv_mem z.property)
        simpa only [mul_inv_cancel_right] using hh
      have hu1 : u = 1 := Subtype.ext (disjoint_def.mp B.centralizer_disjoint u.property huZ)
      rw [hu1,map_one]
  have hYZ : Y ≤ centralizer (Z : Set G) :=
    le_centralizer_iff.mp (inf_le_right.trans (centralizer_le ((map_subtype_le _).trans inf_le_left)))
  have hconj (y : Y) (u : U) (z : Z) :
      R.normalizerMonoidHom ⟨y,B.residual_normalizes y.property⟩ (E (u,z)) =
        E (U.normalizerMonoidHom ⟨y,hn y.property⟩ u,z) := by
    apply Subtype.ext
    change (y : G) * (E (u,z) : G) * (y : G)⁻¹ = _
    rw [hE,hE]
    change (y : G) * ((u : G) * (z : G)) * (y : G)⁻¹ =
      ((y : G) * (u : G) * (y : G)⁻¹) * (z : G)
    have hz : Commute (z : G) (y : G) := hYZ y.property z z.property
    calc
      _ = (y : G) * (u : G) * ((z : G) * (y : G)⁻¹) := by group
      _ = (y : G) * (u : G) * ((y : G)⁻¹ * (z : G)) := by
        rw [hz.inv_right.eq]
      _ = _ := by group
  apply source_no_marked_permutation_quotient h D structural A C hnone a f hf hk
  intro y r
  obtain ⟨⟨u,z⟩,rfl⟩ := E.surjective r
  change e (π (R.normalizerMonoidHom ⟨y,B.residual_normalizes y.property⟩ (E (u,z)))) = _
  rw [hconj,hπ]
  change e (U.normalizerMonoidHom ⟨y,hn y.property⟩ u) = Multiplicative.ofAdd
    (BinaryPermutation.naturalRepresentation (Fin 7) (a y) (e (π (E (u,z)))).toAdd)
  rw [hπ]
  exact he y u

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.HigherRigidity
