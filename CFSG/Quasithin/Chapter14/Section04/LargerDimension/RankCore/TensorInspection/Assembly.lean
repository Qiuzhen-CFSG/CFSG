module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.TensorInspection.Natural
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.TensorInspection.SylowLine
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.FamilyAnalysis.Constituents.Intersection.Deleted.Extension
public import Theory.Representation.SL2NaturalOffenders.Semilinear

/-!
# Inspection of the source tensor alternatives

The group and vector markings are those of 14.4.2(5): the actual H/O₂(H)
is S₃ × D, with D = S₅ or A₅, and its faithful action on U/Z(U) is the
external tensor action. Only the restriction of the four-dimensional
constituent to A₅ is marked, as either the natural SL₂(4) action or the
deleted five-point action. No extension-action or rank conclusion is assumed.

Normality of A₅ forces the natural extension to be semilinear, so every
nonidentity tensor actor moves at least four binary dimensions. The scalar
commutant makes the deleted-module marking equivariant for the whole D.
The checked tensor rank calculation then forces D = S₅ and a pure
transposition, of moved rank exactly two.

The earlier 12.8/14.3 inputs are the actual Sylow normalization of V₂ and
binary dimension one of its quotient image. Normalization fixes the unique
nonzero vector. Mapping that Sylow through the literal two-core quotient
produces nonzero pure tensor coordinates with singular first factor, and
hence excludes the marked line from the transposition displacement.

This completes the tensor inspection (a), under precisely these local
consequences of genuine Hypothesis 14.3.10 and its extraspecial case. The
ambient hypothesis and the other cases of 14.4.2 remain with the parent
14.4.6 assembly; the theorem here works under the weaker explicit local
inputs and does not use the later equality U = O₂(H).

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Hypothesis 14.3.10, 14.4.2(5) and 14.4.6(a), printed pp.993,1006,1008.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
open TensorProduct Module Subgroup BinaryPermutation
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor
variable {H V W : Type*} [Group H] {U : Subgroup H} [U.Normal]
  [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  {D : Subgroup Five} {hAD : AltFive ≤ D}

private noncomputable def reverseCoordinates
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (f : W ≃ₗ[ZMod 2] X) :
    (core (Fin 3) ⊗[ZMod 2] W) ≃ₗ[ZMod 2] (X ⊗[ZMod 2] core (Fin 3)) :=
  (TensorProduct.comm (ZMod 2) _ _).trans
    (TensorProduct.congr f (LinearEquiv.refl (ZMod 2) _))

private theorem reverseCoordinates_equivariant
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (σ : Representation (ZMod 2) D W) (τ : Representation (ZMod 2) D X)
    (f : W ≃ₗ[ZMod 2] X) (hf : ∀ g w, f (σ g w) = τ g (f w))
    (g : Three × D) (z : core (Fin 3) ⊗[ZMod 2] W) :
    reverseCoordinates f (sourceTensorAction σ g z) =
      ThreeTensor.action τ (g.2, g.1) (reverseCoordinates f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul n w =>
    change f (σ g.2 w) ⊗ₜ[ZMod 2] coreRepresentation (Fin 3) g.1 n =
      τ g.2 (f w) ⊗ₜ[ZMod 2] coreRepresentation (Fin 3) g.1 n
    rw [hf]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Normality of the marked natural A₅ layer forces the entire constituent
action to be semilinear. Faithfulness of the literal star action then gives
binary moved rank at least four for every nonidentity tensor actor. -/
theorem SourceAction.tensor_natural_extension_rank
    (d : SourceAction H U V) (σ : Representation (ZMod 2) D W)
    (hnat : IsNaturalFour hAD σ)
    (e : (H ⧸ pCore 2 H) ≃* Three × D)
    (f : V ≃ₗ[ZMod 2] (core (Fin 3) ⊗[ZMod 2] W))
    (hf : ∀ a v, f (d.representation a v) = sourceTensorAction σ (e a) (f v))
    (a : H ⧸ pCore 2 H) (ha : a ≠ 1) : 4 ≤ d.movedRank a := by
  obtain ⟨κ, c, hc⟩ := hnat
  let τ : Representation (ZMod 2) D Representation.SL2FourNatural.V :=
    c.conjRingEquiv.toMonoidHom.comp σ
  have hτ (g : D) (w : W) : c (σ g w) = τ g (c w) := by
    change c (σ g w) = c (σ g (c.symm (c w)))
    rw [c.symm_apply_apply]
  have hsemi (g : D) : ∃ φ : Representation.SL2FourNatural.F →+*
      Representation.SL2FourNatural.F, ∀ b v, τ g (b • v) = φ b • τ g v := by
    obtain ⟨φ, hφ⟩ := Representation.SL2NaturalOffenders.normalizer_semilinear
      (AltFive.subgroupOf D) ((subgroupOfEquivOfLe hAD).trans κ) τ
      (fun k v => by
        change c (σ (inclusion hAD ((subgroupOfEquivOfLe hAD) k)) (c.symm v)) = _
        rw [hc, c.apply_symm_apply]
        rfl) g
    exact ⟨φ.toRingHom, hφ⟩
  apply d.tensor_natural_semilinear_rank U
    (F := Representation.SL2FourNatural.F) (QuadraticAlgebra.finrank_eq_two 1 1)
    (le_of_eq Representation.SL2FourNatural.finrank_vector.symm) τ hsemi
    (e.trans MulEquiv.prodComm) (f.trans (reverseCoordinates c)) _ a ha
  intro b v
  change reverseCoordinates c (f (d.representation b v)) = _
  rw [hf]
  exact reverseCoordinates_equivariant σ τ c hτ (e b) (f v)

private theorem exists_fixed_lift (d : SourceAction H U V)
    (V₂ : Subgroup H) (hdim : finrank (ZMod 2) (d.image V₂) = 1)
    (T : Subgroup H) (hnorm : T ≤ normalizer (V₂ : Set H)) :
    ∃ s : U, (s : H) ∈ V₂ ∧ s ∉ center U ∧
      ∀ t ∈ T, QuotientGroup.mk' (center U) (MulAut.conjNormal t s) =
        QuotientGroup.mk' (center U) s := by
  have hex : ∃ s : U, (s : H) ∈ V₂ ∧ d.vector s ≠ 0 := by
    by_contra! hh
    have hbot : d.image V₂ = ⊥ := by
      apply le_bot_iff.mp
      apply Submodule.span_le.mpr
      rintro v ⟨u, hu, rfl⟩
      exact (Submodule.mem_bot (ZMod 2)).mpr (hh u hu)
    rw [hbot] at hdim
    simp at hdim
  obtain ⟨s, hs, hs0⟩ := hex
  refine ⟨s, hs, ?_, ?_⟩
  · intro hz
    apply hs0
    change (d.coordinates (QuotientGroup.mk' (center U) s)).toAdd = 0
    rw [show (QuotientGroup.mk' (center U)) s = 1 from
      (QuotientGroup.eq_one_iff s).mpr hz, map_one]
    rfl
  · intro t ht
    have hmem : d.vector (MulAut.conjNormal t s) ∈ d.image V₂ := by
      apply d.vector_mem_image
      exact (Subgroup.mem_normalizer_iff.mp (hnorm ht) (s : H)).mp hs
    have hne : d.vector (MulAut.conjNormal t s) ≠ 0 := by
      rw [d.conjugation]
      exact fun hh => hs0 ((d.representation.apply_bijective _).injective
        (hh.trans (map_zero _).symm))
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hdim
      (d.vector_mem_image V₂ s hs) hs0
    rw [hspan] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hfix : d.vector (MulAut.conjNormal t s) = d.vector s := by
      fin_cases c
      · change (0 : ZMod 2) • d.vector s = d.vector (MulAut.conjNormal t s) at hc
        exact (hne (by simpa only [zero_smul] using hc.symm)).elim
      · change (1 : ZMod 2) • d.vector s = d.vector (MulAut.conjNormal t s) at hc
        simpa only [one_smul] using hc.symm
    apply d.coordinates.injective
    exact congrArg Multiplicative.ofAdd hfix

/-- Sylow normalization of the actual binary quotient line supplies a nonzero
singular tensor marking, without a fixed-vector or coordinate premise. -/
theorem SourceAction.tensor_normalized_line_coordinates [Finite H]
    (d : SourceAction H U V)
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3))
    (f : V ≃ₗ[ZMod 2] FiveTensorLowRank.Space)
    (hf : ∀ a v, f (d.representation a v) = FiveTensorLowRank.action (e a) (f v))
    (T : Sylow 2 H) (V₂ : Subgroup H)
    (hnorm : (T : Subgroup H) ≤ normalizer (V₂ : Set H))
    (hdim : finrank (ZMod 2) (d.image V₂) = 1) :
    ∃ s : U, (s : H) ∈ V₂ ∧ ∃ u : core (Fin 5), ∃ w : core (Fin 3),
      u ≠ 0 ∧ w ≠ 0 ∧ FiveGeometry.form u = 0 ∧
        f (d.vector s) = u ⊗ₜ[ZMod 2] w := by
  obtain ⟨s, hs, hs0, hfix⟩ := exists_fixed_lift d V₂ hdim T hnorm
  exact ⟨s, hs, d.tensor_sylow_fixed_coordinates U e f hf T s hs0 hfix⟩

/-- The complete marked-line inspection for the deleted S₅ tensor model. -/
theorem SourceAction.tensor_symmetric_inspection [Finite H]
    (d : SourceAction H U V)
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3))
    (f : V ≃ₗ[ZMod 2] FiveTensorLowRank.Space)
    (hf : ∀ a v, f (d.representation a v) = FiveTensorLowRank.action (e a) (f v))
    (T : Sylow 2 H) (V₂ : Subgroup H)
    (hnorm : (T : Subgroup H) ≤ normalizer (V₂ : Set H))
    (hdim : finrank (ZMod 2) (d.image V₂) = 1)
    (a : H ⧸ pCore 2 H) (ha : a ≠ 1) (hr : d.movedRank a ≤ 2) :
    (∃ i j : Fin 5, i ≠ j ∧ e a = (Equiv.swap i j, 1)) ∧
      d.movedRank a = 2 ∧ ¬ d.image V₂ ≤ d.moved a := by
  obtain ⟨s, hs, hs0, hfix⟩ := exists_fixed_lift d V₂ hdim T hnorm
  exact d.tensor_sylow_fixed_exclusion U e f hf T V₂ s hs hs0 hfix a ha hr

/-- Inspection of all four group/module alternatives in 14.4.2(5).
Only the earlier-source Sylow normalization and rank-one marked image remain
as geometric parameters. The constituent marking is required only on A₅;
its entire extending action, the singular coordinates and exclusion are proved. -/
theorem SourceAction.tensor_inspection [Finite H]
    (d : SourceAction H U V) (σ : Representation (ZMod 2) D W)
    (hD : D = ⊤ ∨ D = AltFive) (hmodel : IsSourceConstituent hAD σ)
    (e : (H ⧸ pCore 2 H) ≃* Three × D)
    (f : V ≃ₗ[ZMod 2] (core (Fin 3) ⊗[ZMod 2] W))
    (hf : ∀ a v, f (d.representation a v) = sourceTensorAction σ (e a) (f v))
    (T : Sylow 2 H) (V₂ : Subgroup H)
    (hnorm : (T : Subgroup H) ≤ normalizer (V₂ : Set H))
    (hdim : finrank (ZMod 2) (d.image V₂) = 1)
    (a : H ⧸ pCore 2 H) (ha : orderOf a = 2) (hr : d.movedRank a ≤ 2) :
    D = ⊤ ∧ IsDeletedFour hAD σ ∧
      (∃ i j : Fin 5, i ≠ j ∧ (e a).1 = 1 ∧ (e a).2.val = Equiv.swap i j) ∧
      d.movedRank a = 2 ∧ ¬ d.image V₂ ≤ d.moved a := by
  have hne : a ≠ 1 := by intro he; simp [he] at ha
  have hdel : IsDeletedFour hAD σ := by
    rcases hmodel with hn | hd
    · have hb := d.tensor_natural_extension_rank σ hn e f hf a hne
      omega
    · exact hd
  obtain ⟨c, hc⟩ := hdel
  let τ : Representation (ZMod 2) D (core (Fin 5)) :=
    (coreRepresentation (Fin 5)).comp D.subtype
  have hτ (g : D) (w : W) : c (σ g w) = τ g (c w) :=
    deleted_extension_equivariant σ c hc g w
  let F := f.trans (reverseCoordinates c)
  have hF (b : H ⧸ pCore 2 H) (v : V) :
      F (d.representation b v) =
        FiveTensorLowRank.action ((e b).2.val, (e b).1) (F v) := by
    change reverseCoordinates c (f (d.representation b v)) = _
    rw [hf]
    exact reverseCoordinates_equivariant σ τ c hτ (e b) (f v)
  have hnot : ((e a).2.val, (e a).1) ≠ (1 : Five × Three) := by
    intro he
    apply hne
    apply e.injective
    rw [map_one]
    exact Prod.ext (congrArg Prod.snd he) (Subtype.ext (congrArg Prod.fst he))
  have hb := FiveTensorLowRank.inspection ((e a).2.val, (e a).1) hnot
    ((d.movedRank_eq_of_equivariant a F _ (hF a)) ▸ hr)
  obtain ⟨⟨i, j, hij, hijact⟩, _⟩ := hb
  have htop : D = ⊤ := by
    rcases hD with h | h
    · exact h
    · have hp : (e a).2.val ∈ AltFive := (le_of_eq h) (e a).2.property
      rw [Equiv.Perm.mem_alternatingGroup,
        show (e a).2.val = Equiv.swap i j from congrArg Prod.fst hijact,
        Equiv.Perm.sign_swap hij] at hp
      exact ((by decide : (-1 : ℤˣ) ≠ 1) hp).elim
  let e5 : (H ⧸ pCore 2 H) ≃* Five × Three :=
    e.trans ((MulEquiv.prodCongr (MulEquiv.refl Three)
      ((MulEquiv.subgroupCongr htop).trans topEquiv)).trans MulEquiv.prodComm)
  have hf5 (b : H ⧸ pCore 2 H) (v : V) :
      F (d.representation b v) = FiveTensorLowRank.action (e5 b) (F v) := hF b v
  obtain ⟨_, hrank, hexcl⟩ :=
    d.tensor_symmetric_inspection e5 F hf5 T V₂ hnorm hdim a hne hr
  exact ⟨htop, ⟨c, hc⟩, ⟨i, j, hij, congrArg Prod.snd hijact,
    congrArg Prod.fst hijact⟩, hrank, hexcl⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
