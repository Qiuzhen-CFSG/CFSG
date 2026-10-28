module
public import CFSG.Quasithin.ChapterG.Section11.Multiplicity
public import Theory.Representation.BinaryPermutation.FiveDoubleNormalizer
public import Theory.SpecificGroups.SymmetricFive.TensorRecognition

/-!
# Reconstructing the original orthogonal A₅ double

The component coordinates place the full faithful action in S₅ × S₃. The
original low-rank witness has trivial S₃ coordinate and is a transposition
in S₅. G.10.2 forces actor rank at least three; trivial two-core then makes
the embedding surjective. This constructs the group isomorphism and the
whole tensor intertwiner in the same coordinates.

The proper marked-constituent application uses the already proved double
coordinates and discharges G.11.2(9) once that constituent is recognized as
the orthogonal A₅ module. Selection of that row from G.6.4 is separate.
Source: Aschbacher--Smith G.11.7--8, printed pp.366--368.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11
open BinaryPermutation
open RankTwo.TensorModels
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- Whole-group tensor recognition from the orthogonal double. All ambient
actions use the same constituent and tensor coordinates; no whole-group
classification or centralizer realization is assumed. -/
theorem orthogonal_double_recognition
    (h : Section10.Hypothesis ρ B v W X X₀) (hw : LowRankWitness ρ v X)
    (H : Subgroup G) [H.Normal] (e : H ≃* alternatingGroup (Fin 5))
    (f : V ≃ₗ[ZMod 2] (core (Fin 5) × core (Fin 5)))
    (he : ∀ (k : H) w, f (ρ k w) =
      (alternatingCoreRepresentation (Fin 5) (e k) (f w).1,
       alternatingCoreRepresentation (Fin 5) (e k) (f w).2)) :
    ∃ j : G ≃* (Equiv.Perm (Fin 5) × S3),
    ∃ t : V ≃ₗ[ZMod 2] OrthogonalTensorSpace,
      (∀ g w, t (ρ g w) = orthogonalTensor (j g) (t w)) ∧
      ∀ k : H, j k = ((e k).val,1) := by
  obtain ⟨j,t,hj,ht,hje⟩ :=
    FiveTensorNormalizer.exists_tensor_embedding_of_double ρ h.faithful H e f he
  change ∀ g w, t (ρ g w) = orthogonalTensor (j g) (t w) at ht
  have hd : finrank (ZMod 2) V = 8 :=
    t.finrank_eq.trans finrank_orthogonalTensorSpace
  have hr : 3 ≤ Group.rank X := by
    have hdim := h.dimension_bound.1
    have hle := Group.rank_le_of_surjective (QuotientGroup.mk' X₀)
      (QuotientGroup.mk'_surjective X₀)
    rw [hd] at hdim
    omega
  have hrank (a : G) : finrank (ZMod 2) (RankTwo.movedSpace ρ a) =
      finrank (ZMod 2) (RankTwo.movedSpace orthogonalTensor (j a)) := by
    exact RankTwo.finrank_movedSpace_transport ρ (orthogonalTensor.comp j.range.subtype)
      (MonoidHom.ofInjective hj) t ht a
  obtain ⟨a,ha,ha2,hapos,har,hav⟩ := hw.exists_involution h.point_ne_zero
  have hja2 : j a * j a = 1 := by
    rw [← map_mul]
    have he : a * a = 1 := by simpa only [pow_two,ha2] using pow_orderOf_eq_one a
    rw [he,map_one]
  have hs : (j a).2 = 1 := by
    by_contra hn
    have hh := ThreeTensor.dimension_le_displacement Orthogonal.representation (j a) hn
    change finrank (ZMod 2) Orthogonal.Space ≤
      finrank (ZMod 2) (RankTwo.movedSpace orthogonalTensor (j a)) at hh
    rw [Orthogonal.finrank_space,← hrank] at hh
    omega
  have htwo : finrank (ZMod 2) (RankTwo.movedSpace orthogonalTensor (j a)) = 2 := by
    have hjap : j a = ((j a).1,1) := Prod.ext rfl hs
    have hh := ThreeTensor.displacement_first Orthogonal.representation (j a).1
    change finrank (ZMod 2) (RankTwo.movedSpace orthogonalTensor ((j a).1,1)) =
      2 * finrank (ZMod 2) (LinearMap.range (Orthogonal.representation (j a).1 - 1)) at hh
    rw [← hjap,← hrank] at hh
    rw [← hrank]
    omega
  have hswap := ((orthogonal_rank_two_iff (j a) hja2).mp htwo).2
  have hsurj : Function.Surjective j := by
    apply Theory.SpecificGroups.SymmetricFive.tensor_embedding_surjective j hj
      (hcore := h.twoCore_eq_bot) (X := X) (hr := hr)
    · intro s hs
      obtain ⟨k,hk⟩ := e.surjective ⟨s,hs⟩
      exact ⟨k,(hje k).trans (by rw [hk])⟩
    · exact ⟨(j a).1,hswap.sign_eq,a,Prod.ext rfl hs⟩
  exact ⟨MulEquiv.ofBijective j ⟨hj,hsurj⟩,t,ht,hje⟩

/-- In the proper marked branch, recognizing the constituent as the
orthogonal A₅ module recognizes the original whole action as G.11.2(9). -/
theorem proper_marked_orthogonal_conclusion
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable G) {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ (componentOrbit L ⊤) I) (hv : v ∈ I) (hp : I ≠ ⊤)
    (hc : Section09.Quasiequivalent
      (invariantSubspace ρ (componentOrbit L ⊤) I hI.choose).toRepresentation
      (alternatingCoreRepresentation (Fin 5))) :
    Conclusion ρ B X := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let R := invariantSubspace ρ H I hI.choose
  have hmdata := marked_constituent_alternative h cover hw hS hn hL hm hI hv
  obtain ⟨_,_,⟨d⟩,_⟩ := hmdata.2.2.2.resolve_left (fun he => hp he.1)
  obtain ⟨e,c,hc⟩ := hc
  let f := d.toLinearEquiv.trans (c.prodCongr c)
  have hf (k : H) (w : V) : f (ρ k w) =
      (alternatingCoreRepresentation (Fin 5) (e k) (f w).1,
       alternatingCoreRepresentation (Fin 5) (e k) (f w).2) := by
    have hh := LinearMap.congr_fun (d.isIntertwining' k) w
    change d (ρ k w) = (R.toRepresentation k (d w).1,R.toRepresentation k (d w).2) at hh
    change (c (d (ρ k w)).1,c (d (ρ k w)).2) = _
    rw [hh,hc,hc]
    rfl
  obtain ⟨j,t,ht,_⟩ := orthogonal_double_recognition h hw H e f hf
  have hcase : CaseNine ρ :=
    ⟨t.finrank_eq.trans finrank_orthogonalTensorSpace,Or.inl ⟨j,t,ht⟩⟩
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcase))))))))
end CFSG.Quasithin.ChapterG.Section11
