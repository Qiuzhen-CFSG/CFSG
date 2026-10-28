module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Recognition.Basic
public import Theory.Representation.BinaryCoinvariantCommutator
public import Theory.Representation.SL2OrthogonalCover.Universal

/-!
# Natural extension data from a marked central cover

An elementary normal kernel with a specified SL₂ action is recognized from
its binary central covering of the natural plane. The kernel of the covering
map is exactly its intersection with the group center: the reverse inclusion
uses the absence of fixed vectors in the natural plane. Full coinvariants
lift to literal group commutator generation.

The natural plane and the three-dimensional orthogonal cover supply the two
concrete constructors. These are the fixed-block recognition inputs in
Aschbacher--Smith, Lemma 2.4.12(2), printed p.532.
-/

public section
noncomputable section
open Subgroup Representation Representation.OneCohomology
namespace Theory.SpecificGroups.SymplecticFour
variable {F L V : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
  [Group L] [Finite L] [AddCommGroup V] [Module (ZMod 2) V]
  {Q : Subgroup L} [Q.Normal]

/-- A marked central cover determines the actual central quotient and commutator layer. -/
def naturalExtensionOfCover
    (hQ : IsElementaryAbelian 2 Q)
    (actor : L →* Matrix.SpecialLinearGroup (Fin 2) F)
    (ha : Function.Surjective actor) (hk : actor.ker = Q)
    (ρ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) V)
    (p : ρ.IntertwiningMap (SL2OrthogonalCover.binaryNatural (F := F)))
    (hp : IsCover p)
    (e : Q ≃* Multiplicative V)
    (he : ∀ (l : L) (u : Q),
      (e (extensionConjugate Q l u)).toAdd = ρ (actor l) (e u).toAdd) :
    NaturalExtension (F := F) Q := by
  letI := hQ
  let f : Q →* Multiplicative (Fin 2 → F) :=
    p.toLinearMap.toAddMonoidHom.toMultiplicative.comp e.toMonoidHom
  have hf : Function.Surjective f := by
    intro v
    obtain ⟨w,hw⟩ := hp.1 v.toAdd
    obtain ⟨u,hu⟩ := e.surjective (Multiplicative.ofAdd w)
    exact ⟨u, by change Multiplicative.ofAdd (p (e u).toAdd)=v; rw [hu]; exact congrArg Multiplicative.ofAdd hw⟩
  have hfk : f.ker = (center L).subgroupOf Q := by
    ext u
    change p (e u).toAdd = 0 ↔ (u:L) ∈ center L
    constructor
    · intro hu
      rw [Subgroup.mem_center_iff]
      intro l
      have hh := (hp.2.1 hu) (actor l)
      have hc : extensionConjugate Q l u = u := e.injective (Multiplicative.toAdd.injective ((he l u).trans hh))
      have hv := congrArg Subtype.val hc
      exact mul_inv_eq_iff_eq_mul.mp hv
    · intro hu
      have hh : p (e u).toAdd ∈ fixed (SL2OrthogonalCover.binaryNatural (F := F)) := by
        intro g
        obtain ⟨l,rfl⟩ := ha g
        rw [←p.isIntertwining,←he]
        have hc : extensionConjugate Q l u = u := by
          apply Subtype.ext
          change l * (u:L) * l⁻¹=(u:L)
          rw [Subgroup.mem_center_iff.mp hu l,mul_inv_cancel_right]
        rw [hc]
      rw [SL2OrthogonalCover.natural_fixed] at hh
      exact hh
  let em : (Q ⧸ (center L).subgroupOf Q) ≃* Multiplicative (Fin 2 → F) :=
    (QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hem (u:Q) : em (QuotientGroup.mk' ((center L).subgroupOf Q) u)=f u := rfl
  have hfull : Coinvariants.ker (ρ.comp ((⊤:Subgroup L).map actor).subtype) = ⊤ := by
    rw [map_top_of_surjective _ ha]
    apply top_unique
    intro v _
    have hs : Coinvariants.ker ρ ≤ Coinvariants.ker (ρ.comp (⊤:Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subtype) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,w⟩,rfl⟩
      exact Coinvariants.sub_mem_ker (ρ := ρ.comp (⊤:Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)).subtype) ⟨g,mem_top g⟩ w
    exact hs (hp.2.2 ▸ Submodule.mem_top)
  have hcomm : Q = ⁅Q,⊤⁆ :=
    subgroup_eq_commutator_of_full_coinvariants Q ⊤ hQ.isPGroup actor ρ e.toMonoidHom e.surjective
      (by rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective,commutator_eq_bot])
      (by
        intro l u u' hh
        have hu' : u'=extensionConjugate Q l u := Subtype.ext hh
        rw [hu']
        exact he l u) hfull
  refine ⟨hQ,actor,ha,hk,hcomm.symm,em,?_⟩
  intro l u
  rw [hem,hem]
  change p (e (extensionConjugate Q l u)).toAdd = _
  rw [he,p.isIntertwining]
  rfl

/-- The orthogonal cover is a natural elementary extension under its literal action. -/
def naturalExtensionOfOrthogonal
    (hQ : IsElementaryAbelian 2 Q)
    (actor : L →* Matrix.SpecialLinearGroup (Fin 2) F)
    (ha : Function.Surjective actor) (hk : actor.ker = Q)
    (hF : 2 < Nat.card F)
    (e : Q ≃* Multiplicative (SL2OrthogonalCover.Space F))
    (he : ∀ (l : L) (u : Q),
      (e (extensionConjugate Q l u)).toAdd = SL2OrthogonalCover.action (actor l) (e u).toAdd) :
    NaturalExtension (F := F) Q :=
  naturalExtensionOfCover hQ actor ha hk SL2OrthogonalCover.binaryAction
    SL2OrthogonalCover.binaryProjection (SL2OrthogonalCover.binaryProjection_isCover hF) e he

/-- The natural plane itself supplies the same extension data. -/
def naturalExtensionOfNatural
    (hQ : IsElementaryAbelian 2 Q)
    (actor : L →* Matrix.SpecialLinearGroup (Fin 2) F)
    (ha : Function.Surjective actor) (hk : actor.ker = Q)
    (hF : 2 < Nat.card F)
    (e : Q ≃* Multiplicative (Fin 2 → F))
    (he : ∀ (l : L) (u : Q),
      (e (extensionConjugate Q l u)).toAdd = (actor l).val.mulVec (e u).toAdd) :
    NaturalExtension (F := F) Q := by
  have hfull : Coinvariants.ker (SL2OrthogonalCover.binaryNatural (F := F)) = ⊤ := by
    have h := map_coinvariants_of_surjective (SL2OrthogonalCover.binaryProjection (F := F))
      (SL2OrthogonalCover.binaryProjection_isCover hF).1
    rw [(SL2OrthogonalCover.binaryProjection_isCover hF).2.2] at h
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr (SL2OrthogonalCover.binaryProjection_isCover hF).1] at h
    exact h.symm
  exact naturalExtensionOfCover hQ actor ha hk SL2OrthogonalCover.binaryNatural
    (Representation.IntertwiningMap.id _) ⟨Function.surjective_id,by simp,hfull⟩ e he
end Theory.SpecificGroups.SymplecticFour
