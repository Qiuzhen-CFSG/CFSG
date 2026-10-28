module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.Quotients
public import Theory.Representation.FirstCohomologyDuality
public import Theory.Representation.SLHigherNaturalFirstCohomology.SLThreeBinary
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual

/-!
# The one-copy moving kernel has order at most two

The universal-cover kernel is dual to the first cohomology of the dual
natural module. The checked binary H¹ computation bounds its dimension by
one. Untwisting the common marking applies that bound to any fully moving
one-copy quotient, and the group-to-linear comparison identifies its kernel
with the literal intersection C ∩ U.

The universal-cover argument is adapted from the private helpers in
AbelianCore/FixedKernel/OneCopy.lean; its old MS-input interface is not assumed.
Source: Aschbacher–Smith B.4.8(1), I.1.5–6, pp.91,408; this supplies the
central-kernel clause of Meierfrankenfeld–Stellmacher (1993), (3.2)(iv), p.863.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives

private theorem dual_natural_h1 :
    Module.finrank (ZMod 2) (H1 (specialLinearNatural (k := ZMod 2) 3).dual) = 1 := by
  let e := BinaryLinearThree.AutomorphismAction.graphNaturalDual
  let a := BinaryLinearThree.AutomorphismAction.graph
  have he : ∀ g v, e.symm (BinaryLinearThree.W.dual g v) =
      BinaryLinearThree.W (a g) (e.symm v) := by
    intro g v
    change e.symm (BinaryLinearThree.W.dual g v) =
      (BinaryLinearThree.W.comp a.toMonoidHom) g (e.symm v)
    exact LinearMap.congr_fun (e.symm.isIntertwining' g) v
  exact (H1Congr _ _ a e.symm.toLinearEquiv he).finrank_eq.trans
    SLHigherNatural.finrank_H1_sl3_two

private theorem cover_kernel_bound {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {σ : Representation (ZMod 2) SL W}
    (p : σ.IntertwiningMap (specialLinearNatural (k := ZMod 2) 3))
    (hp : IsCover p) : Nat.card p.toLinearMap.ker ≤ 2 := by
  let ρ := specialLinearNatural (k := ZMod 2) 3
  obtain ⟨t, ht, htp⟩ := exists_universalCover_quotient p hp
  let s : (universalCoverProjection ρ).toLinearMap.ker →ₗ[ZMod 2] p.toLinearMap.ker :=
    (t.toLinearMap.comp (universalCoverProjection ρ).toLinearMap.ker.subtype).codRestrict
      p.toLinearMap.ker (by
        intro u
        change p (t u.val) = 0
        rw [htp]
        exact u.property)
  have hs : Function.Surjective s := by
    intro w
    obtain ⟨u, hu⟩ := ht w.val
    have hu0 : u ∈ (universalCoverProjection ρ).toLinearMap.ker := by
      change universalCoverProjection ρ u = 0
      rw [← htp, hu]
      exact w.property
    exact ⟨⟨u, hu0⟩, Subtype.ext hu⟩
  have hdim : Module.finrank (ZMod 2) p.toLinearMap.ker ≤ 1 := by
    have hd := LinearMap.finrank_le_finrank_of_surjective hs
    rw [finrank_ker_universalCoverProjection, dual_natural_h1] at hd
    exact hd
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact (Nat.pow_le_pow_right (by decide : 0 < 2) hdim).trans_eq (by norm_num)

/-- A fully moving one-copy natural quotient has fixed kernel of order at most two,
with arbitrary marking and without assuming the extension splits. -/
theorem oneCopy_kernel_card_le_two {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) SL W)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (q : AbelianCore.QuotientRecognition.ModuleQuotient ρ 1) :
    Nat.card q.projection.ker ≤ 2 := by
  let σ : Representation (ZMod 2) SL W := ρ.comp q.marking.symm.toMonoidHom
  let p : σ.IntertwiningMap (specialLinearNatural (k := ZMod 2) 3) := {
    toLinearMap := (LinearMap.proj (0 : Fin 1)).comp q.projection
    isIntertwining' g := by
      ext v : 1
      change q.projection (ρ (q.marking.symm g) v) 0 =
        specialLinearNatural 3 g (q.projection v 0)
      rw [q.equivariant, MulEquiv.apply_symm_apply] }
  have hpker : p.toLinearMap.ker = q.projection.ker := by
    ext v
    change q.projection v 0 = 0 ↔ q.projection v = 0
    constructor
    · intro h
      funext i
      change q.projection v i = 0
      simpa only [Subsingleton.elim i 0] using h
    · intro h
      exact congrFun h 0
  have hp : IsCover p := by
    refine ⟨?_, ?_, ?_⟩
    · intro v
      obtain ⟨w, hw⟩ := q.surjective (fun _ => v)
      exact ⟨w, congrFun hw 0⟩
    · intro v hv g
      have hvq : v ∈ q.projection.ker := hpker ▸ hv
      rw [q.kernel] at hvq
      exact hvq ⟨q.marking.symm g, mem_top _⟩
    · apply top_unique
      rw [← hfull]
      apply Submodule.span_le.mpr
      rintro _ ⟨g, _, v, _, rfl⟩
      have h := Coinvariants.sub_mem_ker (ρ := σ) (q.marking g) v
      change ρ (q.marking.symm (q.marking g)) v - v ∈ _ at h
      rw [MulEquiv.symm_apply_apply] at h
      exact h
  rw [← hpker]
  exact cover_kernel_bound p hp

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Group coordinates on U give the corresponding linear quotient with the
same marking and the same exact fixed kernel. -/
noncomputable def MovingQuotient.linear (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) {m : ℕ} (q : MovingQuotient source m) :
    letI := geometry.U_elementary hb (alpha R) rfl
    AbelianCore.QuotientRecognition.ModuleQuotient (Offenders.linearize (uAction source)) m := by
  letI := geometry.U_elementary hb (alpha R) rfl
  let p := q.projection.toAdditiveLeft.toZModLinearMap 2
  refine { marking := q.marking, projection := p, surjective := ?_, kernel := ?_, equivariant := ?_ }
  · intro v
    obtain ⟨u, hu⟩ := q.onto (Multiplicative.ofAdd v)
    exact ⟨Additive.ofMul u, hu⟩
  · ext v
    change q.projection v.toMul = 1 ↔ _
    change v.toMul ∈ q.projection.ker ↔ _
    rw [q.kernel]
    have hf := layerAction_fixed_iff source (U R (alpha R)) (U_normalized (alpha R))
      (Q_centralizes_U (alpha R) rfl) v.toMul
    constructor
    · intro hv g
      exact congrArg Additive.ofMul ((hf.mpr hv.2) g.val)
    · intro hv
      refine ⟨(U_le_Z (alpha R)).trans (geometry.omega_bound (alpha R) rfl hb) v.toMul.property,
        hf.mp ?_⟩
      intro g
      exact congrArg Additive.toMul (hv ⟨g, mem_top _⟩)
  · intro g v i
    obtain ⟨a, rfl⟩ := source.projection_surjective g
    exact q.action a v.toMul (uAction source (source.projection a) v.toMul)
      (layerAction_apply source _ _ _ a v.toMul) i

/-- The kernel retained in the one-copy source branch has order at most two. -/
theorem MovingQuotient.one_kernel_card_le_two (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) (q : MovingQuotient source 1) :
    Nat.card (fixedPart R ⊓ U R (alpha R) : Subgroup (FreeAmalgam R)) ≤ 2 := by
  let := geometry.U_elementary hb (alpha R) rfl
  let := finite_Z R (alpha R)
  let : Finite (U R (alpha R)) :=
    Finite.of_injective (inclusion (U_le_Z (R := R) (alpha R))) (inclusion_injective _)
  let p := q.linear source geometry hb
  let e : (fixedPart R ⊓ U R (alpha R) : Subgroup (FreeAmalgam R)) ≃ p.projection.ker := {
    toFun := fun u => ⟨Additive.ofMul ⟨u, u.property.2⟩, by
      change q.projection ⟨u, u.property.2⟩ = 1
      change (⟨u, u.property.2⟩ : U R (alpha R)) ∈ q.projection.ker
      rw [q.kernel]
      exact u.property.1⟩
    invFun := fun u => ⟨u.val.toMul, by
      have h : u.val.toMul ∈ q.projection.ker := u.property
      rw [q.kernel] at h
      exact ⟨h, u.val.toMul.property⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact oneCopy_kernel_card_le_two _ (uAction_full source geometry hb) p

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
