module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.AmbientTorus
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.FixedModel.CoverComparison
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.FixedModel.Automorphisms

/-!
# The fixed subgroup of the second distinguished unitary centralizer

Let B be the actual ambient fixed torus and F its distinguished centralizer.
The assumed local identity C_{Lᵤ}(B) = L B places the distinguished-generated
linear group L in F ∩ C_G(u), so that fixed group is nonsolvable. Comparing
the two unitary covers excludes a trivial action of u. The inner-centralizer
and graph-fixed calculations then identify the actual fixed subgroup as
PSL₂(2ⁿ), for both SU₃ and PSU₃ covers.

No fixed-group equality, noninnerness or second-centralizer record is assumed.
The conclusion is the exact implication consumed by `AmbientAssembly` after
it recognizes F using the independent additional linear subgroup.
Source: GLS4, Chapter 2, final paragraph of Lemma 13.2; Chapter 4, 3.4(b,c).
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup Theory.GroupTheory _root_.BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t u : G} {n : ℕ}

/-- Fixed-subgroup recognition for the literal ambient second centralizer.
The two independent geometric premises are exactly its unitary-cover model
and C_{Lᵤ}(B) = L ⊔ B. This implication supplies the `hfixed` argument of
`secondCentralizerData_of_ambient_geometry`; the parent assembly retains the
discharge of these two premises. -/
public theorem ambientFixedTorus_fixed_model
    (h : IsProductDisconnected Z M) (hz : z ∈ Z) (ht : t ∈ Z) (hn : 2 ≤ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hCB : centralizerClosure Z u ⊓ centralizer (ambientFixedTorus Z M t u : Set G) =
      residualGenerated M z t ⊔ ambientFixedTorus Z M t u)
    (hc : IsUnitaryCentralizerCoverAt n
      (distinguishedCentralizer Z (ambientFixedTorus Z M t u))) :
    Nonempty ((distinguishedCentralizer Z (ambientFixedTorus Z M t u) ⊓
      centralizer ({u} : Set G) : Subgroup G) ≃* PSL2BinaryMatrixGroup n) := by
  let F := distinguishedCentralizer Z (ambientFixedTorus Z M t u)
  let B := ambientFixedTorus Z M t u
  let L := residualGenerated M z t
  have hLC : L ≤ centralizer (B : Set G) := by
    intro x hx
    exact (show x ∈ centralizerClosure Z u ⊓ centralizer (B : Set G) from
      hCB.symm ▸ (mem_sup_left hx : x ∈ L ⊔ B)).2
  have hLF : L ≤ F := by
    change residualGenerated M z t ≤ closure (Z ∩ (centralizer (B : Set G) : Set G))
    rw [← closure_Z_inter_residualGenerated h hz ht]
    apply Subgroup.closure_mono
    intro x hx
    exact ⟨hx.1, hLC hx.2⟩
  have hLu : L ≤ centralizer ({u} : Set G) :=
    (hunitary u huD hu).1.le.trans (centralizerClosure_le Z u)
  let un : normalizer (F : Set G) := ⟨u, ambientFixedTorus_second_normalizes h⟩
  let a : MulAut F := F.normalizerMonoidHom un
  have has : a ^ 2 = 1 := by
    have hu2 : un ^ 2 = 1 := Subtype.ext hu.sq_eq_one
    rw [← map_pow, hu2, map_one]
  have han : a ≠ 1 := FixedModel.second_action_nontrivial h hn hunitary huD hu hCB hc
  have hns : ¬ Group.IsSolvable a.fixedSubgroup := by
    intro hs
    let f : L →* a.fixedSubgroup :=
      ((inclusion hLF).codRestrict a.fixedSubgroup (by
        intro x
        apply (MulAut.mem_fixedSubgroup _ _).mpr
        apply Subtype.ext
        change u * x.val * u⁻¹ = x.val
        rw [← mem_centralizer_singleton_iff.mp (hLu x.property), mul_inv_cancel_right]))
    let := hs
    let : Group.IsSolvable L := Group.isSolvable_of_isSolvable_injective (f := f) (by
      intro x y he
      exact Subtype.ext (congrArg (fun w : a.fixedSubgroup => w.val.val) he))
    have hmodel : IsSimpleBenderGroupAtExponent n L := .isPSL2 ⟨eL⟩
    let : IsSimpleGroup L := hmodel.isSimple hn
    let : Group.IsPerfect L := ⟨hmodel.isPerfect hn⟩
    exact Group.IsPerfect.not_isSolvable L inferInstance
  obtain ⟨ea⟩ := FixedModel.unitary_cover_nonsolvable_fixed hn hc a has han hns
  let e : a.fixedSubgroup ≃* (F ⊓ centralizer ({u} : Set G) : Subgroup G) := {
    toFun := fun x => ⟨x.val.val, x.val.property, mem_centralizer_singleton_iff.mpr (by
      have hx := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp x.property)
      exact (mul_inv_eq_iff_eq_mul.mp hx).symm)⟩
    invFun := fun x => ⟨⟨x.val, x.property.1⟩, (MulAut.mem_fixedSubgroup _ _).mpr (by
      apply Subtype.ext
      change u * x.val * u⁻¹ = x.val
      rw [← mem_centralizer_singleton_iff.mp x.property.2, mul_inv_cancel_right])⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_mul' := fun _ _ => rfl }
  exact ⟨e.symm.trans ea⟩
end BenderSuzuki.ZD.UnitaryExclusion
