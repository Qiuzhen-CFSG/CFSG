module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.Rigidity
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.CoreTransfer

/-!
# Two-cores in faithful diagram-preserving symplectic extensions

Embed the actual symplectic group as a normal subgroup `N` of an overgroup
with trivial centralizer. For either local factor, adjoining a subgroup that
normalizes its embedded image leaves its two-core unchanged. This applies in
particular to the source's Sylow two-subgroup in an extension by a two-group.

A normal two-core in the local join acts trivially on the local core quotient.
Transport through the embedding and the actual SL₂ quotient identifies this
with the kernel calculated in `Rigidity`. Faithfulness then places every
core element in the embedded local factor. `CoreTransfer` proves the required
relative normality inside the join and both inclusions of the core equality.
All final comparisons are mapped into the same ambient group.

Source: Aschbacher--Smith F.1.12, printed p.264 of `refs/quasithin.pdf`.
-/

public section
noncomputable section
open scoped commutatorElement
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
variable {F G : Type*} [Field F] [Group G]
variable (N : Subgroup G) [N.Normal] (e : Sp F ≃* N)

private theorem action_inner (x : Sp F) :
    extensionAction N e (e x).val = MulAut.conj x := by
  apply MulEquiv.ext
  intro y
  apply e.injective
  apply Subtype.ext
  rw [extensionAction_apply]
  simp

private theorem action_map (L : Subgroup (Sp F)) (g : G)
    (hg : g ∈ Subgroup.normalizer (L.map (N.subtype.comp e.toMonoidHom) : Set G)) :
    L.map (extensionAction N e g).toMonoidHom = L := by
  let f := N.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := N.subtype_injective.comp e.injective
  apply Subgroup.map_injective hf
  rw [Subgroup.map_map]
  have he : f.comp (extensionAction N e g).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp f := by
    ext x
    exact extensionAction_apply N e g x
  rw [he, ← Subgroup.map_map]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hg

omit [N.Normal] in
private theorem embedded_core (L : Subgroup (Sp F)) :
    (pCore 2 (L.map (N.subtype.comp e.toMonoidHom))).map
        (L.map (N.subtype.comp e.toMonoidHom)).subtype =
      ((pCore 2 L).map L.subtype).map (N.subtype.comp e.toMonoidHom) := by
  let f := N.subtype.comp e.toMonoidHom
  let t := L.equivMapOfInjective f (N.subtype_injective.comp e.injective)
  rw [← pCore_map_iso 2 t, Subgroup.map_map, Subgroup.map_map]
  rfl

private theorem action_difference (L : Subgroup (Sp F)) (g : G)
    (hL : L.map (extensionAction N e g).toMonoidHom = L)
    (hc : ∀ l : L.map (N.subtype.comp e.toMonoidHom),
      ⁅g, l.val⁆ ∈ (pCore 2 (L.map (N.subtype.comp e.toMonoidHom))).map
        (L.map (N.subtype.comp e.toMonoidHom)).subtype) (l : L) :
    restrict (extensionAction N e g) L hL l / l ∈ pCore 2 L := by
  let f := N.subtype.comp e.toMonoidHom
  have hf : Function.Injective f := N.subtype_injective.comp e.injective
  have h := hc ⟨f l.val, Subgroup.mem_map_of_mem f l.property⟩
  rw [embedded_core N e] at h
  have he : f (restrict (extensionAction N e g) L hL l / l).val = ⁅g, f l.val⁆ := by
    simp only [Subgroup.coe_div, map_div, restrict_apply]
    rw [show f (extensionAction N e g l.val) = g * f l.val * g⁻¹ from
      extensionAction_apply N e g l.val]
    simp only [div_eq_mul_inv, commutatorElement_def]
  rw [← he] at h
  exact (Subgroup.mem_map_iff_mem L.subtype_injective).mp
    ((Subgroup.mem_map_iff_mem hf).mp h)

private theorem join_core (L : Subgroup (Sp F))
    (hC : Subgroup.centralizer (N : Set G) = ⊥)
    (hdiagram : ∀ g : G, PreservesDiagram (extensionAction N e g))
    (hdetect : ∀ (a : MulAut (Sp F)), PreservesDiagram a →
      ∀ (hL : L.map a.toMonoidHom = L), (∃ k : ℕ, a ^ (2 ^ k) = 1) →
      (∀ l : L, restrict a L hL l / l ∈ pCore 2 L) →
      ∃ l : L, a = MulAut.conj l.val)
    (S : Subgroup G)
    (hnorm : S ≤ Subgroup.normalizer (L.map (N.subtype.comp e.toMonoidHom) : Set G)) :
    (pCore 2 (L.map (N.subtype.comp e.toMonoidHom) ⊔ S : Subgroup G)).map
        (L.map (N.subtype.comp e.toMonoidHom) ⊔ S).subtype =
      (pCore 2 (L.map (N.subtype.comp e.toMonoidHom))).map
        (L.map (N.subtype.comp e.toMonoidHom)).subtype := by
  let f := N.subtype.comp e.toMonoidHom
  let K := L.map f
  apply Subgroup.join_pCore_eq_of_quotient_action_detection 2 K S hnorm
  intro g hg htwo hc
  have hgnorm : g ∈ Subgroup.normalizer (K : Set G) :=
    (sup_le K.le_normalizer hnorm) hg
  have hL := action_map N e L g hgnorm
  have hatwo : ∃ k : ℕ, extensionAction N e g ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := htwo
    exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  obtain ⟨l, hl⟩ := hdetect _ (hdiagram g) hL hatwo (action_difference N e L g hL hc)
  have he : g = f l.val := extensionAction_injective N e hC
    (hl.trans (action_inner N e l.val).symm)
  rw [he]
  exact Subgroup.mem_map_of_mem f l.property

variable [Finite F] [CharP F 2]
variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
include hcard hn

/-- The point-local two-core is unchanged on adjoining any normalizing subgroup
in a faithful diagram-preserving normal extension. Both sides lie in `G`.
In particular this applies to a Sylow two-subgroup in a finite extension by a
two-group; neither restriction on the supplement is needed for this identity. -/
theorem pointLocal_join_core_eq
    (hC : Subgroup.centralizer (N : Set G) = ⊥)
    (hdiagram : ∀ g : G, PreservesDiagram (extensionAction N e g))
    (S : Subgroup G)
    (hnorm : S ≤ Subgroup.normalizer
      (pointLocal.map (N.subtype.comp e.toMonoidHom) : Set G)) :
    (pCore 2 (pointLocal.map (N.subtype.comp e.toMonoidHom) ⊔ S : Subgroup G)).map
        (pointLocal.map (N.subtype.comp e.toMonoidHom) ⊔ S).subtype =
      (pCore 2 (pointLocal.map (N.subtype.comp e.toMonoidHom))).map
        (pointLocal.map (N.subtype.comp e.toMonoidHom)).subtype := by
  apply join_core N e pointLocal hC hdiagram ?_ S hnorm
  intro a ha hL htwo hc
  apply pointSL2Action_kernel_of_preservesDiagram hcard hn a ha hL htwo
  apply MulEquiv.ext
  intro A
  obtain ⟨l, rfl⟩ := pointQuotient_surjective A
  rw [pointSL2Action_quotient]
  change pointQuotient (restrict a pointLocal hL l) = pointQuotient l
  rw [← pointLocalCoreQuotientEquiv_mk hcard hn,
    ← pointLocalCoreQuotientEquiv_mk hcard hn]
  exact congrArg (pointLocalCoreQuotientEquiv hcard hn)
    (QuotientGroup.eq_iff_div_mem.mpr (hc l))

/-- The plane-local two-core is unchanged in the same faithful extension,
with normality used only inside the displayed local join. -/
theorem planeLocal_join_core_eq
    (hC : Subgroup.centralizer (N : Set G) = ⊥)
    (hdiagram : ∀ g : G, PreservesDiagram (extensionAction N e g))
    (S : Subgroup G)
    (hnorm : S ≤ Subgroup.normalizer
      (planeLocal.map (N.subtype.comp e.toMonoidHom) : Set G)) :
    (pCore 2 (planeLocal.map (N.subtype.comp e.toMonoidHom) ⊔ S : Subgroup G)).map
        (planeLocal.map (N.subtype.comp e.toMonoidHom) ⊔ S).subtype =
      (pCore 2 (planeLocal.map (N.subtype.comp e.toMonoidHom))).map
        (planeLocal.map (N.subtype.comp e.toMonoidHom)).subtype := by
  apply join_core N e planeLocal hC hdiagram ?_ S hnorm
  intro a ha hL htwo hc
  apply planeSL2Action_kernel_of_preservesDiagram hcard hn a ha hL htwo
  apply MulEquiv.ext
  intro A
  obtain ⟨l, rfl⟩ := Plane.quotientMap_surjective A
  rw [planeSL2Action_quotient]
  change Plane.quotientMap (restrict a planeLocal hL l) = Plane.quotientMap l
  rw [← planeLocalCoreQuotientEquiv_mk hcard hn,
    ← planeLocalCoreQuotientEquiv_mk hcard hn]
  exact congrArg (planeLocalCoreQuotientEquiv hcard hn)
    (QuotientGroup.eq_iff_div_mem.mpr (hc l))

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
