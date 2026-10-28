module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.Basic
public import Theory.SpecificGroups.BinaryLinear.Affine
public import Theory.GroupTheory.SplitExtensionCoordinates.Marked
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# The marked affine local group in 12.2.26--27

The split local configuration identifies the original L with the binary affine
group, retaining each original two-core element as a translation. No escape
then identifies C_G(v) with C_L(v). Restriction of the actual equivalence
carries the distinguished v to its specified nonzero translation.

This constructs the local model used by the recognition branches. In rank
four the centralizer model alone also permits Held; the full local configuration
must be retained when applying the recognition theorem.
Source: Aschbacher--Smith, 12.2.26--27, printed pp.806--807; Aschbacher,
Sporadic Groups, Sections 39--41, especially the hypotheses on p.213.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource

variable {G : Type*} [Group G] {L V : Subgroup G} {d : ℕ}
namespace SplitLinearConfiguration
variable (C : SplitLinearConfiguration L V d)
include C

/-- The original two-core included in G, identified with the original V. -/
@[expose] def coreEquiv : pCore 2 L ≃* V :=
  ((pCore 2 L).equivMapOfInjective L.subtype L.subtype_injective).trans
    (MulEquiv.subgroupCongr C.core_eq)

@[simp] theorem coreEquiv_apply (u : pCore 2 L) :
    (C.coreEquiv u : G) = ((u : L) : G) := rfl

/-- Splitting and the original natural coordinates reconstruct the actual L,
with every original two-core element marked as a translation. -/
theorem exists_affine_equiv :
    ∃ (f : V ≃* Multiplicative (Fin d → ZMod 2)) (e : L ≃* BinaryLinear.Affine.Model d),
      ∀ u : pCore 2 L, e u = SemidirectProduct.inl (f (C.coreEquiv u)) := by
  obtain ⟨a, f, hf⟩ := C.natural
  obtain ⟨S, hS⟩ := C.split
  let eQ := C.coreEquiv.trans f
  have he (l : L) (u : pCore 2 L) :
      eQ (MulAut.conjNormal l u) =
        BinaryLinear.Affine.action d (a (QuotientGroup.mk' (pCore 2 L) l)) (eQ u) := by
    apply f.symm.injective
    simp only [eQ, MulEquiv.trans_apply, f.symm_apply_apply]
    apply Subtype.ext
    exact (hf l (C.coreEquiv u)).symm
  obtain ⟨e, heu, _⟩ := exists_marked_semidirect_equiv_of_split_coordinates
    (pCore 2 L) S hS a eQ (BinaryLinear.Affine.action d) he
  exact ⟨f, e, heu⟩

/-- No escape and N(L)=L identify the full point centralizer with its local one. -/
theorem point_centralizer_eq (hnone : NoEscape L V)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    centralizer ({v} : Set G) = L ⊓ centralizer ({v} : Set G) := by
  apply (inf_eq_right.mpr ?_).symm
  rw [← C.self_normalizing]
  exact hnone v hv hv1

/-- Each actual point centralizer is the centralizer of a nonzero translation
in the split affine model; both the group and its distinguished element are marked. -/
theorem exists_point_centralizer_model (hnone : NoEscape L V)
    {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) :
    ∃ w : Multiplicative (Fin d → ZMod 2), w ≠ 1 ∧
      ∃ E : centralizer ({v} : Set G) ≃*
          centralizer ({(SemidirectProduct.inl w : BinaryLinear.Affine.Model d)} : Set (BinaryLinear.Affine.Model d)),
        (E ⟨v, mem_centralizer_singleton_iff.mpr rfl⟩ : BinaryLinear.Affine.Model d) =
          SemidirectProduct.inl w := by
  obtain ⟨f,e,he⟩ := C.exists_affine_equiv
  let u := C.coreEquiv.symm ⟨v,hv⟩
  have hu : (((u : pCore 2 L) : L) : G) = v :=
    (C.coreEquiv_apply u).symm.trans
      (congrArg Subtype.val (C.coreEquiv.apply_symm_apply ⟨v,hv⟩))
  let vL : L := u
  have hvL : (vL : G) = v := hu
  have hCL : centralizer ({v} : Set G) ≤ L := by
    rw [C.point_centralizer_eq hnone hv hv1]
    exact inf_le_left
  have hlocal : (centralizer ({v} : Set G)).subgroupOf L =
      centralizer ({vL} : Set L) := by
    ext x
    simp only [mem_subgroupOf, mem_centralizer_singleton_iff]
    constructor
    · intro hh
      apply Subtype.ext
      simpa only [coe_mul, hvL] using hh
    · intro hh
      simpa only [coe_mul, hvL] using congrArg Subtype.val hh
  let E := (subgroupOfEquivOfLe hCL).symm.trans
    ((MulEquiv.subgroupCongr hlocal).trans
      (((centralizer ({vL} : Set L)).equivMapOfInjective e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr (CentralizerSmallKernelTransport.map_centralizer e vL))))
  refine ⟨f ⟨v,hv⟩, ?_, ?_⟩
  · intro hh
    exact hv1 (congrArg Subtype.val (f.map_eq_one_iff.mp hh))
  · have hev : e vL = SemidirectProduct.inl (f ⟨v,hv⟩) := by
      rw [show vL = (u : L) from rfl, he]
      simp only [u, C.coreEquiv.apply_symm_apply]
    let F := E.trans (MulEquiv.subgroupCongr
      (congrArg (fun a : BinaryLinear.Affine.Model d => centralizer ({a} : Set (BinaryLinear.Affine.Model d))) hev))
    refine ⟨F, ?_⟩
    change e ⟨v, hCL (mem_centralizer_singleton_iff.mpr rfl)⟩ = _
    exact (congrArg e (Subtype.ext hvL.symm)).trans hev

end SplitLinearConfiguration
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
