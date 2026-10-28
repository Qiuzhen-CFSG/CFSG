module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.LinearActions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.LocalLayers
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The specified binary quotient acting on the moving layer

The base stabilizer quotient is identified with the SL₃(2) quotient already
specified by `LocalSource`. Its conjugation actions on X, Z and U use this
same identification. Full group commutation on U gives full linear
commutation; simplicity proves faithfulness, and restriction of a Z offender
proves that the literal U action is an FF-module. No module shape, splitting,
or equality between [X,Ltilde] and U is assumed.

Source: Meierfrankenfeld–Stellmacher (1993), the module input to (3.2),
printed pp.857, 863. These action results precede its four binary alternatives.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
variable {M : Type*} [Group M] {L R : Subgroup M}

noncomputable def baseEquiv : M ≃* stabilizer R (alpha R) :=
  (MonoidHom.ofInjective (embedM_injective R)).trans
    (MulEquiv.subgroupCongr (stabilizer_m_base R).symm)

@[simp] theorem baseEquiv_val (m : M) :
    (baseEquiv (R := R) m : FreeAmalgam R) = embedM R m := rfl

noncomputable def baseProjection (source : LocalSource L R) :
    stabilizer R (alpha R) →* SL :=
  source.projection.comp (baseEquiv (R := R)).symm.toMonoidHom

theorem baseProjection_surjective (source : LocalSource L R) :
    Function.Surjective (baseProjection source) :=
  source.projection_surjective.comp (baseEquiv (R := R)).symm.surjective

@[simp] theorem baseProjection_baseEquiv (source : LocalSource L R) (m : M) :
    baseProjection source (baseEquiv m) = source.projection m := by
  simp [baseProjection]

variable [Finite M]

theorem baseProjection_kernel (source : LocalSource L R) :
    (baseProjection source).ker = (Q R (alpha R)).subgroupOf (stabilizer R (alpha R)) := by
  ext g
  obtain ⟨m, rfl⟩ := (baseEquiv (R := R)).surjective g
  change baseProjection source (baseEquiv m) = 1 ↔ embedM R m ∈ Q R (alpha R)
  rw [baseProjection_baseEquiv, Q_alpha R source.two_group source.core_le]
  change m ∈ source.projection.ker ↔ _
  rw [source.projection_kernel, mem_map_iff_mem (embedM_injective R)]

noncomputable def quotientMarking (source : LocalSource L R) :
    letI := Q_normal R (alpha R)
    stabilizer R (alpha R) ⧸ (Q R (alpha R)).subgroupOf (stabilizer R (alpha R)) ≃* SL := by
  letI := Q_normal R (alpha R)
  exact (QuotientGroup.quotientMulEquivOfEq (baseProjection_kernel source).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (baseProjection_surjective source))

@[simp] theorem quotientMarking_mk (source : LocalSource L R)
    (g : stabilizer R (alpha R)) :
    letI := Q_normal R (alpha R)
    quotientMarking source (QuotientGroup.mk' _ g) = baseProjection source g := rfl

/-- The action on a normalized subgroup of X, through the specified quotient. -/
noncomputable def layerAction (source : LocalSource L R)
    (Y : Subgroup (FreeAmalgam R))
    (hn : stabilizer R (alpha R) ≤ normalizer (Y : Set (FreeAmalgam R)))
    (hc : Q R (alpha R) ≤ centralizer (Y : Set (FreeAmalgam R))) : SL →* MulAut Y := by
  letI := Q_normal R (alpha R)
  exact (Offenders.quotientConjugation _ _ Y (Q_normal R (alpha R)) hn hc).comp
    (quotientMarking source).symm.toMonoidHom

@[simp] theorem layerAction_apply (source : LocalSource L R)
    (Y : Subgroup (FreeAmalgam R))
    (hn : stabilizer R (alpha R) ≤ normalizer (Y : Set (FreeAmalgam R)))
    (hc : Q R (alpha R) ≤ centralizer (Y : Set (FreeAmalgam R)))
    (m : M) (y : Y) :
    (layerAction source Y hn hc (source.projection m) y : FreeAmalgam R) =
      embedM R m * (y : FreeAmalgam R) * (embedM R m)⁻¹ := by
  let := Q_normal R (alpha R)
  have hm : (quotientMarking source).symm (source.projection m) =
      QuotientGroup.mk' _ (baseEquiv (R := R) m) := by
    apply (quotientMarking source).injective
    rw [MulEquiv.apply_symm_apply]
    exact ((quotientMarking_mk source _).trans (baseProjection_baseEquiv source m)).symm
  change (Offenders.quotientConjugation _ _ Y (Q_normal R (alpha R)) hn hc
    ((quotientMarking source).symm (source.projection m)) y : FreeAmalgam R) = _
  rw [hm, Offenders.quotientConjugation_apply, baseEquiv_val]

theorem layerAction_fixed_iff (source : LocalSource L R)
    (Y : Subgroup (FreeAmalgam R))
    (hn : stabilizer R (alpha R) ≤ normalizer (Y : Set (FreeAmalgam R)))
    (hc : Q R (alpha R) ≤ centralizer (Y : Set (FreeAmalgam R))) (y : Y) :
    (∀ g, layerAction source Y hn hc g y = y) ↔
      (y : FreeAmalgam R) ∈ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) := by
  constructor
  · intro hy l hl
    have hlS := Ltilde_le_stabilizer (R := R) (alpha R) hl
    obtain ⟨m, hm⟩ := (baseEquiv (R := R)).surjective ⟨l, hlS⟩
    have he := congrArg Subtype.val (hy (source.projection m))
    rw [layerAction_apply] at he
    have hm' : embedM R m = l := congrArg Subtype.val hm
    rw [hm'] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hy g
    obtain ⟨m, rfl⟩ := source.projection_surjective g
    apply Subtype.ext
    rw [layerAction_apply]
    have hgen : Ltilde R (alpha R) ⊔ Q R (alpha R) ≤
        centralizer ({(y : FreeAmalgam R)} : Set (FreeAmalgam R)) := by
      apply sup_le
      · intro l hl
        exact mem_centralizer_singleton_iff.mpr (hy l hl)
      · intro q hq
        exact mem_centralizer_singleton_iff.mpr ((hc hq y y.property).symm)
    rw [source.local_generation (alpha R) rfl] at hgen
    have he := mem_centralizer_singleton_iff.mp (hgen (baseEquiv (R := R) m).property)
    change embedM R m * (y : FreeAmalgam R) = y * embedM R m at he
    rw [he, mul_inv_cancel_right]

/-- Restriction to an invariant subspace preserves the offender inequality. -/
theorem fixedCodim_le_of_injective {G V W : Type*} [Group G]
    [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G V) (σ : Representation (ZMod 2) G W)
    (f : V →ₗ[ZMod 2] W) (hf : Function.Injective f)
    (he : ∀ g v, f (ρ g v) = σ g (f v)) (A : Subgroup G) :
    fixedCodim ρ A ≤ fixedCodim σ A := by
  have hc : (fixedSpace σ A).comap f = fixedSpace ρ A := by
    ext v
    constructor
    · intro h a
      apply hf
      change f (ρ a.val v) = f v
      rw [he]
      exact h a
    · intro h a
      change σ a.val (f v) = f v
      rw [← he]
      exact congrArg f (h a)
  let q := (fixedSpace ρ A).mapQ (fixedSpace σ A) f (by rw [hc])
  have hi : Function.Injective q := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.ker_mapQ, hc, Submodule.mkQ_map_self]
  exact LinearMap.finrank_le_finrank_of_injective hi

/-- The fixed subgroup of Q acts trivially on every subgroup of Z. -/
theorem Q_centralizes_U (a : Vertex R) (ha : color R a = false) :
    Q R a ≤ centralizer (U R a : Set (FreeAmalgam R)) :=
  (le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q R a ha))).trans (centralizer_le (U_le_Z a))

noncomputable def uAction (source : LocalSource L R) : SL →* MulAut (U R (alpha R)) :=
  layerAction source (U R (alpha R)) (U_normalized (alpha R)) (Q_centralizes_U (alpha R) rfl)

noncomputable def zAction (source : LocalSource L R) : SL →* MulAut (Z R (alpha R)) :=
  layerAction source (Z R (alpha R)) (Z_normalized R (alpha R))
    (le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R (alpha R) rfl)))

noncomputable def xAction (source : LocalSource L R) : SL →* MulAut (X R (alpha R)) :=
  layerAction source (X R (alpha R)) (X_normalized R (alpha R))
    (Q_le_centralizer_X R (alpha R))

/-- The moving subgroup cannot vanish: otherwise the faithful local quotient
would centralize Z. This argument uses no natural-module conclusion. -/
theorem U_ne_bot (source : LocalSource L R) (geometry : Geometry R) :
    U R (alpha R) ≠ ⊥ := by
  intro hU
  have hL : Ltilde R (alpha R) ≤ Q R (alpha R) := by
    rw [← source.C_eq_Q geometry.radical_ne_bot (alpha R) rfl]
    exact le_inf (Ltilde_le_stabilizer (alpha R))
      (le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp hU))
  have hS : stabilizer R (alpha R) ≤ Q R (alpha R) := by
    rw [← source.local_generation (alpha R) rfl]
    exact sup_le hL le_rfl
  have hone (g : SL) : g = 1 := by
    obtain ⟨m, rfl⟩ := source.projection_surjective g
    have hm : baseEquiv (R := R) m ∈ (baseProjection source).ker := by
      rw [baseProjection_kernel]
      exact hS (baseEquiv m).property
    change baseProjection source (baseEquiv m) = 1 at hm
    simpa only [baseProjection_baseEquiv] using hm
  let : Subsingleton SL := ⟨fun g k => (hone g).trans (hone k).symm⟩
  have hcard : Nat.card SL = 1 := Nat.card_unique
  rw [Matrix.PSL3Two.card_SL] at hcard
  omega

/-- Full commutation on the literal subgroup U becomes full linear commutation
for its action through the given SL₃ quotient. -/
theorem uAction_full (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) :
    letI := geometry.U_elementary hb (alpha R) rfl
    subspaceCommutator (Offenders.linearize (uAction source)) ⊤ ⊤ = ⊤ := by
  let := geometry.U_elementary hb (alpha R) rfl
  let ρ := Offenders.linearize (uAction source)
  let W := subspaceCommutator ρ ⊤ ⊤
  let J : Subgroup (U R (alpha R)) := Subgroup.toAddSubgroup.symm W.toAddSubgroup
  have hU : U R (alpha R) ≤ J.map (U R (alpha R)).subtype := by
    conv_lhs => rw [← geometry.U_full_commutation hb (alpha R) rfl, commutator_comm]
    apply commutator_le.mpr
    intro l hl u hu
    obtain ⟨m, hm⟩ := (baseEquiv (R := R)).surjective
      ⟨l, Ltilde_le_stabilizer (alpha R) hl⟩
    have hm' : embedM R m = l := congrArg Subtype.val hm
    let v : U R (alpha R) := ⟨u, hu⟩
    refine ⟨uAction source (source.projection m) v * v⁻¹, ?_, ?_⟩
    · change Additive.ofMul (uAction source (source.projection m) v * v⁻¹) ∈ W
      exact Submodule.subset_span ⟨source.projection m, mem_top _,
        Additive.ofMul v, Submodule.mem_top, by simp only [sub_eq_add_neg]; rfl⟩
    · change (uAction source (source.projection m) v : FreeAmalgam R) * u⁻¹ = _
      rw [uAction, layerAction_apply, hm']
      rfl
  apply top_unique
  intro v _
  obtain ⟨w, hw, he⟩ := hU v.toMul.property
  have he' : w = v.toMul := Subtype.ext he
  subst w
  exact hw

/-- Simplicity of the actual matrix quotient and full nonzero commutation
prove faithfulness on U before identifying any module shape. -/
theorem uAction_injective (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) :
    letI := geometry.U_elementary hb (alpha R) rfl
    Function.Injective (Offenders.linearize (uAction source)) := by
  let := geometry.U_elementary hb (alpha R) rfl
  let ρ := Offenders.linearize (uAction source)
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  apply ρ.ker_eq_bot_iff.mp
  rcases (inferInstance : ρ.ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact hk
  exfalso
  have hfix : (⊤ : Submodule (ZMod 2) (Additive (U R (alpha R)))) ≤ fixedSpace ρ ⊤ := by
    intro v _ g
    have hg : ρ g.val = 1 := by
      change g.val ∈ ρ.ker
      rw [hk]
      exact mem_top _
    change ρ g.val v = v
    rw [hg]
    rfl
  have hz := (subspaceCommutator_eq_bot_iff ρ ⊤ ⊤).mpr hfix
  rw [uAction_full source geometry hb] at hz
  apply U_ne_bot source geometry
  apply le_bot_iff.mp
  intro u hu
  have hv : Additive.ofMul (⟨u, hu⟩ : U R (alpha R)) = 0 := hz.le Submodule.mem_top
  exact congrArg (fun v : Additive (U R (alpha R)) => (v.toMul : FreeAmalgam R)) hv

/-- Transport the actual Z offender through the specified quotient marking. -/
theorem zAction_isFFModule (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) :
    letI := geometry.Z_elementary hb (alpha R) rfl
    IsFFModule (Offenders.linearize (zAction source)) := by
  let := Q_normal R (alpha R)
  let := geometry.Z_elementary hb (alpha R) rfl
  apply IsFFModule.map_equivariant (Offenders.linearize (Z_quotientConjugation R (alpha R) rfl))
    (Offenders.linearize (zAction source)) (quotientMarking source).toMonoidHom
    (quotientMarking source).injective (LinearEquiv.refl (ZMod 2) _) ?_
    (source.Z_quotient_isFFModule geometry hb (alpha R) rfl)
  intro g v
  change Additive.ofMul (Z_quotientConjugation R (alpha R) rfl g v.toMul) =
    Additive.ofMul (Z_quotientConjugation R (alpha R) rfl
      ((quotientMarking source).symm (quotientMarking source g)) v.toMul)
  rw [MulEquiv.symm_apply_apply]

/-- An actual Z offender remains an offender on U by restriction. -/
theorem uAction_isFFModule (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) :
    letI := geometry.U_elementary hb (alpha R) rfl
    IsFFModule (Offenders.linearize (uAction source)) := by
  let := geometry.U_elementary hb (alpha R) rfl
  let := geometry.Z_elementary hb (alpha R) rfl
  let := finite_Z R (alpha R)
  let f := (Subgroup.inclusion (U_le_Z (R := R) (alpha R))).toAdditive.toZModLinearMap 2
  have hf : Function.Injective f := Subgroup.inclusion_injective (U_le_Z (alpha R))
  have he : ∀ g v, f (Offenders.linearize (uAction source) g v) =
      Offenders.linearize (zAction source) g (f v) := by
    intro g v
    obtain ⟨m, rfl⟩ := source.projection_surjective g
    apply Additive.toMul.injective
    apply Subtype.ext
    change (uAction source (source.projection m) v.toMul : FreeAmalgam R) =
      (zAction source (source.projection m) (Subgroup.inclusion (U_le_Z _) v.toMul) : FreeAmalgam R)
    rw [uAction, zAction, layerAction_apply, layerAction_apply]
    rfl
  obtain ⟨A, hA⟩ := zAction_isFFModule source geometry hb
  exact ⟨A, hA.1, (fixedCodim_le_of_injective _ _ f hf he A).trans hA.2⟩

/-- The X action is faithful after transport through the same quotient marking. -/
theorem xAction_injective (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) :
    letI := X_elementary R (alpha R)
    Function.Injective (Offenders.linearize (xAction source)) := by
  let := X_elementary R (alpha R)
  let := Q_normal R (alpha R)
  apply Offenders.linearize_injective
  exact (source.X_quotientConjugation_injective geometry hb (alpha R) rfl).comp
    (quotientMarking source).symm.injective

/-- The actual X offender is transported to the specified SL₃(2). -/
theorem xAction_isFFModule (source : LocalSource L R) (geometry : Geometry R)
    (hb : 0 < geometry.b R) :
    letI := X_elementary R (alpha R)
    IsFFModule (Offenders.linearize (xAction source)) := by
  let := Q_normal R (alpha R)
  let := X_elementary R (alpha R)
  apply IsFFModule.map_equivariant (Offenders.linearize (X_quotientConjugation R (alpha R)))
    (Offenders.linearize (xAction source)) (quotientMarking source).toMonoidHom
    (quotientMarking source).injective (LinearEquiv.refl (ZMod 2) _) ?_
    (source.X_quotient_isFFModule geometry hb (alpha R) rfl)
  intro g v
  change Additive.ofMul (X_quotientConjugation R (alpha R) g v.toMul) =
    Additive.ofMul (X_quotientConjugation R (alpha R)
      ((quotientMarking source).symm (quotientMarking source g)) v.toMul)
  rw [MulEquiv.symm_apply_apply]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.ModuleAlternatives
