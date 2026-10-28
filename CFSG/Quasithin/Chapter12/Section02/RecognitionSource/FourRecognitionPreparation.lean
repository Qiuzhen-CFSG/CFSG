module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.SplitModel
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.PointFusion
public import Theory.SpecificGroups.BinaryLinear.AffinePointMarking
public import Theory.GroupTheory.Recognition.TransvectionFive.LocalData

/-!
# The original translation subgroup in dimension-four recognition

The split local group supplies a centralizer equivalence marking every element
of the original V, not only its chosen nonidentity point z. The element of L
moving z then proves that N_G(V) is larger than C_G(z). Consequently, once
the affine coordinates identify V with either distinguished root group in
the degree-five model, the Held normalizer pattern 40.5(3) is impossible.

This is the preparation and type-exclusion step of Aschbacher--Smith
12.2.27(1), p.807, using Aschbacher, *Sporadic Groups* (1994), 39.1(2)
and 40.5(3), pp.213,219. The model comparison, local fusion classification,
and uniqueness theorem remain separate prerequisites; no recognition result
is inferred merely from an abstract centralizer isomorphism.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {d : ℕ}
namespace SplitLinearConfiguration
variable (C : SplitLinearConfiguration L V d) (D : ChosenModule T L V)
include C D

omit [Finite G] in
/-- The local equivalence marks the whole original translation subgroup. -/
theorem exists_point_marking (hnone : NoEscape L V)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    Nonempty (BinaryLinear.Affine.PointMarking d z V) := by
  obtain ⟨f, e, he⟩ := C.exists_affine_equiv
  have hVL : V ≤ L := by rw [← C.core_eq]; exact map_subtype_le _
  have heV (u : V) : e ⟨u, hVL u.property⟩ = SemidirectProduct.inl (f u) := by
    let k := C.coreEquiv.symm u
    have hk : (((k : pCore 2 L) : L) : G) = u :=
      (C.coreEquiv_apply k).symm.trans
        (congrArg Subtype.val (C.coreEquiv.apply_symm_apply u))
    rw [show (⟨u, hVL u.property⟩ : L) = (k : L) from Subtype.ext hk.symm, he]
    simp only [k, C.coreEquiv.apply_symm_apply]
  have hCL : centralizer ({z} : Set G) ≤ L := by
    rw [C.point_centralizer_eq hnone hz hz1]
    exact inf_le_left
  let zL : L := ⟨z, hVL hz⟩
  have hlocal : (centralizer ({z} : Set G)).subgroupOf L =
      centralizer ({zL} : Set L) := by
    ext x
    simp only [mem_subgroupOf, mem_centralizer_singleton_iff]
    exact ⟨fun hh => Subtype.ext hh, fun hh => congrArg Subtype.val hh⟩
  let E := (subgroupOfEquivOfLe hCL).symm.trans
    ((MulEquiv.subgroupCongr hlocal).trans
      (((centralizer ({zL} : Set L)).equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr (CentralizerSmallKernelTransport.map_centralizer e zL))))
  have hez : e zL = SemidirectProduct.inl (f ⟨z, hz⟩) := heV ⟨z, hz⟩
  let F := E.trans (MulEquiv.subgroupCongr
    (congrArg (fun a : BinaryLinear.Affine.Model d => centralizer ({a} : Set _)) hez))
  have hVC : V ≤ centralizer ({z} : Set G) :=
    (C.seed_le_point_core D hnone hz hz1).trans (map_subtype_le _)
  refine ⟨{ point_mem := hz
            seed_le := hVC
            vectorEquiv := f
            centralizerEquiv := F
            on_seed := ?_ }⟩
  intro u
  change e ⟨u, hCL (hVC u.property)⟩ = _
  exact heV u

/-- The source fusion condition retains the original point and two-core. -/
theorem point_core_fusion (hnone : NoEscape L V)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    TransvectionFive.PointCoreFusion z := by
  obtain ⟨g, _, hg, hgz⟩ := C.point_fused_in_core D hnone hz hz1
  exact ⟨g, hg, hgz⟩

/-- The original L supplies an element of N_G(V) outside C_G(z). -/
theorem seed_normalizer_not_le_point_centralizer (hnone : NoEscape L V)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1) :
    ¬ normalizer (V : Set G) ≤ centralizer ({z} : Set G) := by
  intro hle
  obtain ⟨g, hg, _, hgz⟩ := C.point_fused_in_core D hnone hz hz1
  have hc := mem_centralizer_singleton_iff.mp (hle (D.normalizes hg))
  apply hgz
  calc
    g * z * g⁻¹ = z * g * g⁻¹ := by rw [hc]
    _ = z := by simp only [mul_assoc, mul_inv_cancel, mul_one]

/-- Identification of V with either literal model root subgroup excludes
the Held local normalizer pattern without an additional no-Held premise. -/
theorem not_held_normalizer_pattern (hnone : NoEscape L V)
    {z : G} (hz : z ∈ V) (hz1 : z ≠ 1)
    (F : TransvectionFive.MarkedCentralizer z)
    (hV : V = F.row ∨ V = F.column) : ¬ F.HeldNormalizerPattern := by
  intro hheld
  apply C.seed_normalizer_not_le_point_centralizer D hnone hz hz1
  rcases hV with hV | hV
  · rw [hV, hheld.1]
  · rw [hV, hheld.2]

end SplitLinearConfiguration
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
