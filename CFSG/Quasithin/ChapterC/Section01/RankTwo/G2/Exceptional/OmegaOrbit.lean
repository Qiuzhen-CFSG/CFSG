module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.G2.Exceptional.WholeQuotient
public import Theory.Representation.G2BinaryNaturalNormalizer
public import Theory.Representation.G2.RestrictedModules.NaturalCoordinates

/-!
Adapted from the checked Chapter15 MarkedMS.G2Reconstruction proof to the
exceptional MS2(b) input. Only the two-group and core-containment consequences
of MS2 are used; the original SmallMSPair interface is unchanged.

# Natural coordinates on the entire original omega orbit

The full binary linear normalizer of the derived G₂ action extends the
marked component action to a faithful ambient quotient embedding. The
original omega orbit contains the central-omega moved space. Since that
space supplements the fixed space, restricting the natural projection to
the original orbit remains onto, with exactly its residual centralizer as
kernel. Every action equation retains literal original conjugation.

Source: AS C.1.31–32; MS93 (3.2)(vii), printed pp.863–866.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
local notation "H" => (L ⊔ R : Subgroup G)
local notation "C" => quotientComponent (L := L) (R := R)
local notation "X" => omegaCenterIn (pCore 2 H)
variable (h : Pair KnownSimple.IsKnownSimple L R)
  (e : (L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2)))
include h e

theorem centralOmega_natural_coordinates :
    ∃ f : (H ⧸ pCore 2 H) →* Atlas.G2.Model (ZMod 2),
      Function.Injective f ∧ (C).map f = commutator (Atlas.G2.Model (ZMod 2)) ∧
      ∃ p : Additive X →ₗ[ZMod 2] (Fin 6 → ZMod 2),
        Function.Surjective p ∧ p.ker = fixedSpace (centralOmegaAction h e) C ∧
        ∀ g v, p (centralOmegaAction h e g v) =
          Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2) (f g) (p v) := by
  let := (quotientComponent_structure h e).1
  let ρ := centralOmegaAction h e
  let ψ := fixedQuotient ρ C
  obtain ⟨E⟩ := centralOmega_whole_natural h e
  have hfψ : Function.Injective ψ := by
    apply MovedSection.faithful_of_faithful_centric_restriction (L := C) _ ?_
      (quotientComponent_structure h e).2.2.2
    intro a b hab
    apply E.groupEquiv.injective
    apply Atlas.G2.Natural.BinaryNormalizer.faithful
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := E.linearEquiv.surjective w
    exact (E.intertwines a v).symm.trans
      ((congrArg E.linearEquiv (LinearMap.congr_fun hab v)).trans (E.intertwines b v))
  obtain ⟨f,hf,hfc,hact⟩ := Atlas.G2.Natural.BinaryNormalizer.ambient_embedding
    ψ C E.groupEquiv E.linearEquiv E.intertwines hfψ
  have hmap : (C).map f = commutator (Atlas.G2.Model (ZMod 2)) := by
    ext x
    constructor
    · rintro ⟨c,hc,rfl⟩
      rw [hfc ⟨c,hc⟩]
      exact (E.groupEquiv ⟨c,hc⟩).property
    · intro hx
      refine ⟨E.groupEquiv.symm ⟨x,hx⟩,(E.groupEquiv.symm ⟨x,hx⟩).property,?_⟩
      exact (hfc (E.groupEquiv.symm ⟨x,hx⟩)).trans
        (congrArg Subtype.val (E.groupEquiv.apply_symm_apply ⟨x,hx⟩))
  let Q := (fixedSubrepresentation ρ C).toSubmodule
  let c := Atlas.G2.Restricted.NaturalCoordinates.equiv (ZMod 2)
  let p : Additive X →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
    c.toLinearMap.comp (E.linearEquiv.toLinearMap.comp Q.mkQ)
  refine ⟨f,hf,hmap,p,c.surjective.comp (E.linearEquiv.surjective.comp Q.mkQ_surjective),?_,?_⟩
  · ext v
    change c (E.linearEquiv (Q.mkQ v)) = 0 ↔ v ∈ Q
    rw [c.map_eq_zero_iff,E.linearEquiv.map_eq_zero_iff,
      Submodule.mkQ_apply,Submodule.Quotient.mk_eq_zero]
  · intro g v
    change c (E.linearEquiv (ψ g (Q.mkQ v))) =
      Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2) (f g)
        (c (E.linearEquiv (Q.mkQ v)))
    rw [hact g (Q.mkQ v)]
    exact (Atlas.G2.Restricted.NaturalCoordinates.repEquiv (ZMod 2)).isIntertwining _ _

local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => R.subgroupOf (L ⊔ R)
local notation "W" => ChapterC.MSCentralOrbit.omegaOrbit T

/-- Coordinates on the entire original omega orbit, with literal conjugation. -/
theorem omegaOrbit_natural_coordinates :
    ∃ a : H →* Atlas.G2.Model (ZMod 2), a.ker = pCore 2 H ∧
      (K).map a = commutator (Atlas.G2.Model (ZMod 2)) ∧
      ∃ π : W →* Multiplicative (Fin 6 → ZMod 2),
        Function.Surjective π ∧ π.ker.map (W).subtype =
          W ⊓ centralizer (K : Set H) ∧
        ∀ (g : H) (v : W),
          π ⟨g * v.val * g⁻¹, Subgroup.Normal.conj_mem inferInstance _ v.property g⟩ =
          Multiplicative.ofAdd (Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2)
            (a g) (π v).toAdd) := by
  let : IsElementaryAbelian 2 W :=
    ChapterC.MSCentralOrbit.omegaOrbit_elementary T (core_le_edge h) (core_self_centralizing h)
  let hWX := ChapterC.MSCentralOrbit.omegaOrbit_le_centralOmega T
    (core_le_edge h) (core_self_centralizing h)
  let i := NormalElementaryQuotient.inclusionLinear W X hWX
  obtain ⟨f,hf,hfC,p,hp,hpk,hact⟩ := centralOmega_natural_coordinates h e
  let q := QuotientGroup.mk' (pCore 2 H)
  let a := f.comp q
  let π : W →* Multiplicative (Fin 6 → ZMod 2) :=
    (p.comp i).toAddMonoidHom.toMultiplicative
  have hp0 (v : Additive X) : p v = 0 ↔ v ∈ fixedSpace (centralOmegaAction h e) C := by
    change v ∈ p.ker ↔ _
    rw [hpk]
  have hsurj : Function.Surjective π := by
    intro v
    obtain ⟨x,hx⟩ := hp v.toAdd
    obtain ⟨w,hw,z,hz,heq⟩ := Submodule.mem_sup.mp
      ((centralOmega_moved_sup_fixed h e) ▸
        (Submodule.mem_top : x ∈ (⊤ : Submodule (ZMod 2) (Additive X))))
    have hwK : (w.toMul : H) ∈ ⁅X,K⁆ := by
      have hw0 : w ∈ NormalElementaryQuotient.commutatorSpace X (K) := by
        rw [NormalElementaryQuotient.commutatorSpace_eq X q
        (QuotientGroup.mk'_surjective _) ((QuotientGroup.ker_mk' _).trans
          (central_omega_centralizer h e).symm) (K)]
        exact hw
      exact hw0
    have hwW : (w.toMul : H) ∈ W := by
      rw [← initialCore_eq h e] at hwK
      exact (commutator_le_left W K) hwK
    refine ⟨⟨w.toMul,hwW⟩,?_⟩
    apply Multiplicative.toAdd.injective
    change p (i (Additive.ofMul ⟨w.toMul,hwW⟩)) = v.toAdd
    have hi : i (Additive.ofMul ⟨w.toMul,hwW⟩) = w := rfl
    rw [hi,←hx,←heq,map_add,(hp0 z).mpr hz,add_zero]
  have hk : π.ker.map (W).subtype = W ⊓ centralizer (K : Set H) := by
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩
      refine ⟨w.property,?_⟩
      have hz : p (i (Additive.ofMul w)) = 0 := hw
      exact (NormalElementaryQuotient.mem_fixedSpace_image X q
        (QuotientGroup.mk'_surjective _) ((QuotientGroup.ker_mk' _).trans
          (central_omega_centralizer h e).symm) K _).mp ((hp0 _).mp hz)
    · rintro ⟨hv,hc⟩
      refine ⟨⟨v,hv⟩,?_,rfl⟩
      change p (i (Additive.ofMul ⟨v,hv⟩)) = 0
      exact (hp0 _).mpr ((NormalElementaryQuotient.mem_fixedSpace_image X q
        (QuotientGroup.mk'_surjective _) ((QuotientGroup.ker_mk' _).trans
          (central_omega_centralizer h e).symm) K _).mpr hc)
  refine ⟨a,?_,?_,π,hsurj,hk,?_⟩
  · ext g
    change f (q g) = 1 ↔ _
    rw [←f.map_one,hf.eq_iff]
    exact QuotientGroup.eq_one_iff g
  · change (K).map (f.comp q) = _
    rw [←map_map]
    exact hfC
  · intro g v
    apply Multiplicative.toAdd.injective
    change p (i (Additive.ofMul _)) =
      Atlas.G2.Restricted.NaturalCoordinates.action (ZMod 2) (f (q g))
        (p (i (Additive.ofMul v)))
    rw [←hact (q g) (i (Additive.ofMul v))]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (centralOmegaAction_apply h e g (i (Additive.ofMul v))).symm

end CFSG.Quasithin.ChapterC.G2Exceptional.Reconstruction
