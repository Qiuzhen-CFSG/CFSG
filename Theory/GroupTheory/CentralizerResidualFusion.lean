module

public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Fusion of involutions in centralizer residuals

Conjugation embeds a subgroup centralizing `s` into the centralizer of a
conjugate `t`. Functoriality of the prime residual sends its two-residual
into the two-residual of that centralizer. A prescribed involution class
therefore transports back to every such local residual. This gives a
fusion obstruction when a local residual contains an involution in a
different ambient class. A separate elementary obstruction transports
the p-group property of centralizers along the same actual conjugation.

Application: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 13.9.5, printed pp.970–971 (PDF pp.987–988). The residual
here is `O²`, not the two-core `O₂`; no ambient normality is assumed.
-/

public section

open Subgroup
namespace Theory.GroupTheory

variable {G : Type*} [Group G]

/-- Fusion of the involutions in an element-centralizer residual also controls
involutions of local residuals at a conjugate element. -/
theorem isConj_of_mem_local_residual
    {s t x : G} (H : Subgroup G) (hH : H ≤ centralizer ({s} : Set G))
    (hst : IsConj s t)
    (hx : x ∈ (pResidual 2 H).map H.subtype) (horder : orderOf x = 2)
    (hclass : ∀ y ∈ (pResidual 2 (centralizer ({t} : Set G))).map
        (centralizer ({t} : Set G)).subtype, orderOf y = 2 → IsConj t y) :
    IsConj t x := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hst
  let C := centralizer ({t} : Set G)
  let f : H →* C :=
    ((MulAut.conj g).toMonoidHom.comp H.subtype).codRestrict C (by
      intro a
      apply mem_centralizer_singleton_iff.mpr
      change (g * (a : G) * g⁻¹) * t = t * (g * (a : G) * g⁻¹)
      have he := congrArg (MulAut.conj g)
        (mem_centralizer_singleton_iff.mp (hH a.property))
      simpa only [map_mul, MulAut.conj_apply, hg] using he)
  obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
  have hares : f a ∈ pResidual 2 C :=
    map_pResidual_le 2 f (mem_map.mpr ⟨a, ha, rfl⟩)
  have hag : IsConj (a : G) ((f a : C) : G) := isConj_iff.mpr ⟨g, rfl⟩
  exact (hclass _ (mem_map.mpr ⟨f a, hares, rfl⟩)
    ((MulAut.conj g).orderOf_eq (a : G) |>.trans horder)).trans hag.symm

/-- An involution in a local residual obstructs fusion of its centralizing
involution with an element whose centralizer residual has a different class. -/
theorem not_isConj_of_local_residual_classes
    {s t z : G} (H : Subgroup G) (hH : H ≤ centralizer ({s} : Set G))
    (htz : ¬ IsConj t z)
    (hlocal : ∃ x ∈ (pResidual 2 H).map H.subtype,
      orderOf x = 2 ∧ IsConj z x)
    (hclass : ∀ y ∈ (pResidual 2 (centralizer ({t} : Set G))).map
        (centralizer ({t} : Set G)).subtype, orderOf y = 2 → IsConj t y) :
    ¬ IsConj s t := by
  intro hst
  obtain ⟨x, hx, ho, hz⟩ := hlocal
  exact htz ((isConj_of_mem_local_residual H hH hst hx ho hclass).trans hz.symm)

/-- A subgroup centralized by x with non-p-group order prevents x from fusing
to an element with p-group centralizer. -/
theorem not_isConj_of_non_pGroup_centralized
    {p : ℕ} {z x : G} (H : Subgroup G)
    (hz : IsPGroup p (centralizer ({z} : Set G)))
    (hH : ¬ IsPGroup p H) (hx : H ≤ centralizer ({x} : Set G)) :
    ¬ IsConj z x := by
  intro hc
  obtain ⟨g, rfl⟩ := isConj_iff.mp hc
  have hp := hz.of_equiv
    (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) z)
  exact hH (hp.of_injective (inclusion hx) (inclusion_injective hx))

end Theory.GroupTheory
