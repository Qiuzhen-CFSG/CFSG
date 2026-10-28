module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Conjugation
public import Theory.Representation.G2OrthogonalCover.Universal

/-!
# The entire intrinsic module of a binary G₂ block

Conjugation on U descends through O₂(K), and the given natural module
marking turns U → U/C_U(K) into a central cover of the actual derived
G₂ natural six-space. The universal-cover theorem supplies an equivariant
surjection from the trace-zero seven-space, over that same projection.
Rank-nullity therefore gives natural and Weyl alternatives on the whole U.
No vanishing of C_U(K) or ambient full-G₂ action is presumed.

Source: Aschbacher--Smith C.1.7, C.1.30 and I.1.6(5), printed
pp.123,135,408; applied to original 14.6.10(5), p.1029.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.G2SecondParabolic
open ChapterC ChapterC.ExceptionalRestrictions Atlas.G2.Natural
variable {L : Type*} [Group L]
variable [IsElementaryAbelian 2 (blockU L)]

/-- The actual action on the entire intrinsic U, using the model's actor mark. -/
def intrinsicAction (h : IsShort L) (m : BlockModuleModel L g2TwoNaturalAction) :
    Representation (ZMod 2) (commutator (Atlas.G2.Model (ZMod 2)))
      (Additive (blockU L)) :=
  (uRepresentation h).comp m.quotientIso.symm.toMonoidHom

/-- The central projection as an additive homomorphism. -/
def intrinsicProjectionHom (m : BlockModuleModel L g2TwoNaturalAction) :
    Additive (blockU L) →+ Space (ZMod 2) where
  toFun v := (m.moduleIso (QuotientGroup.mk' (blockFixed L) v.toMul)).toAdd
  map_zero' := by
    change (m.moduleIso (QuotientGroup.mk' (blockFixed L) 1)).toAdd = 0
    simp only [map_one]
    rfl
  map_add' v w := congrArg Multiplicative.toAdd
    (map_mul (m.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (blockFixed L))) v.toMul w.toMul)

/-- The original central projection, with canonical six-dimensional target. -/
def intrinsicProjection (m : BlockModuleModel L g2TwoNaturalAction) :
    Additive (blockU L) →ₗ[ZMod 2] Space (ZMod 2) :=
  (intrinsicProjectionHom m).toZModLinearMap 2

theorem intrinsicProjection_apply (m : BlockModuleModel L g2TwoNaturalAction)
    (v : Additive (blockU L)) :
    intrinsicProjection m v =
      (m.moduleIso (QuotientGroup.mk' (blockFixed L) v.toMul)).toAdd := rfl

/-- The transported action agrees with the original conjugation on every lift. -/
theorem intrinsicAction_apply (h : IsShort L) (m : BlockModuleModel L g2TwoNaturalAction)
    (l : L) (v : Additive (blockU L)) :
    intrinsicAction h m (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)) v =
      Additive.ofMul (blockConjugate L l v.toMul) := by
  change uRepresentation h (m.quotientIso.symm (m.quotientIso _)) v = _
  rw [m.quotientIso.symm_apply_apply]
  rfl

theorem intrinsicProjection_equivariant (h : IsShort L)
    (m : BlockModuleModel L g2TwoNaturalAction)
    (g : commutator (Atlas.G2.Model (ZMod 2))) (v : Additive (blockU L)) :
    intrinsicProjection m (intrinsicAction h m g v) =
      OrthogonalCover.binaryNatural (ZMod 2) g (intrinsicProjection m v) := by
  obtain ⟨l, rfl⟩ := m.quotientIso.surjective.comp
    (QuotientGroup.mk'_surjective (pCore 2 L)) g
  dsimp only [Function.comp_apply]
  rw [intrinsicAction_apply]
  exact m.g2_intertwining l v.toMul

/-- The whole U is a central cover, not merely an unrelated module quotient. -/
def intrinsicCover (h : IsShort L) (m : BlockModuleModel L g2TwoNaturalAction) :
    (intrinsicAction h m).IntertwiningMap (OrthogonalCover.binaryNatural (ZMod 2)) :=
  ⟨intrinsicProjection m, fun g => LinearMap.ext (intrinsicProjection_equivariant h m g)⟩

theorem intrinsicCover_isCover (h : IsShort L)
    (m : BlockModuleModel L g2TwoNaturalAction) : IsCover (intrinsicCover h m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w
    obtain ⟨v, hv⟩ := m.moduleIso.surjective.comp
      (QuotientGroup.mk'_surjective (blockFixed L)) (Multiplicative.ofAdd w)
    exact ⟨Additive.ofMul v, congrArg Multiplicative.toAdd hv⟩
  · intro v hv g
    have hz : v.toMul ∈ blockFixed L := by
      apply (QuotientGroup.eq_one_iff _).mp
      apply m.moduleIso.injective
      exact (Multiplicative.toAdd.injective hv).trans m.moduleIso.map_one.symm
    exact (uRepresentation_fixed h v).mpr hz (m.quotientIso.symm g)
  · apply top_unique
    rw [← uRepresentation_moved h]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    have hh := Coinvariants.sub_mem_ker (ρ := intrinsicAction h m) (m.quotientIso g) v
    change uRepresentation h (m.quotientIso.symm (m.quotientIso g)) v - v ∈
      Coinvariants.ker (intrinsicAction h m) at hh
    rw [m.quotientIso.symm_apply_apply] at hh
    exact hh

/-- The Weyl cover maps onto the whole intrinsic U over its literal projection. -/
theorem intrinsic_weyl_cover (h : IsShort L)
    (m : BlockModuleModel L g2TwoNaturalAction) :
    ∃ f : (OrthogonalCover.binaryAction (ZMod 2)).IntertwiningMap (intrinsicAction h m),
      Function.Surjective f ∧
        ∀ w, intrinsicProjection m (f w) = mk (ZMod 2) w := by
  let := h.finite
  let : Module.Finite (ZMod 2) (Additive (blockU L)) := Module.Finite.of_finite
  exact OrthogonalCover.exists_quotient (ZMod 2) (intrinsicCover h m)
    (intrinsicCover_isCover h m)

/-- Natural or Weyl coordinates on the entire U, retaining the original
actor mark and its natural projection in either alternative. -/
theorem intrinsic_natural_or_weyl (h : IsShort L)
    (m : BlockModuleModel L g2TwoNaturalAction) :
    (∃ E : Additive (blockU L) ≃ₗ[ZMod 2] Space (ZMod 2),
      (∀ a v, E (intrinsicAction h m a v) =
        OrthogonalCover.binaryNatural (ZMod 2) a (E v)) ∧
      ∀ v, E v = intrinsicProjection m v) ∨
    (∃ E : TraceZero (ZMod 2) ≃ₗ[ZMod 2] Additive (blockU L),
      (∀ a w, E (OrthogonalCover.binaryAction (ZMod 2) a w) =
        intrinsicAction h m a (E w)) ∧
      ∀ w, intrinsicProjection m (E w) = mk (ZMod 2) w) := by
  let := h.finite
  let : Module.Finite (ZMod 2) (Additive (blockU L)) := Module.Finite.of_finite
  obtain ⟨f, hf, he⟩ := intrinsic_weyl_cover h m
  have hp : Function.Surjective (intrinsicProjection m) := (intrinsicCover_isCover h m).1
  by_cases hk : (intrinsicProjection m).ker = ⊥
  · let E := LinearEquiv.ofBijective (intrinsicProjection m) ⟨LinearMap.ker_eq_bot.mp hk, hp⟩
    exact Or.inl ⟨E, intrinsicProjection_equivariant h m, fun _ => rfl⟩
  · have hd := (intrinsicProjection m).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hp, finrank_top, finrank_space] at hd
    have hpos : 0 < Module.finrank (ZMod 2) (intrinsicProjection m).ker := by
      have hn : Module.finrank (ZMod 2) (intrinsicProjection m).ker ≠ 0 :=
        fun hz => hk (Submodule.finrank_eq_zero.mp hz)
      omega
    have hle := LinearMap.finrank_le_finrank_of_surjective (f := f.toLinearMap) hf
    rw [OrthogonalCover.finrank_traceZero] at hle
    have hdim : Module.finrank (ZMod 2) (TraceZero (ZMod 2)) =
        Module.finrank (ZMod 2) (Additive (blockU L)) := by
      rw [OrthogonalCover.finrank_traceZero]
      omega
    let E := LinearEquiv.ofBijective f.toLinearMap
      ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hf, hf⟩
    exact Or.inr ⟨E, fun a w => LinearMap.congr_fun (f.isIntertwining' a) w, he⟩

end CFSG.Quasithin.Chapter14.Section06.G2SecondParabolic
