module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.SylowNormalizer.NaturalConstruction.BaseEquivalence
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.SylowNormalizer.NaturalConstruction.BaseModel
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.SylowNormalizer.NaturalConstruction.DihedralModel

/-!
# Transport from the actual orthogonal actor to the local groups

The quotient Y/R supplies exactly nine cubic elements in the image. Once
the concrete cubic subgroup has order nine, this identifies the whole image
of Y. Sylow restriction and surjective transport identify the image of T,
and the given plane-stabilizer identity identifies the image of S. The
concrete base-generation calculation then identifies the image of YS.

Factoring through the two injective model maps constructs both quotient
surjections with their exact relative kernels. Compatibility with the same
natural action transfers the half-turn's inversion and the reflection's
fixed plane, and transfers the cubic group's trivial fixed space.

`exists_of_model_facts` separates this transport from the concrete model
calculations. `exists_coordinates` discharges both model contracts using
`BaseModel` and `DihedralModel`, so only the preceding local hypotheses remain.
No section or normalizer result is assumed here; the source-theorem assembly
remains with `SylowNormalizer`.

Source: Aschbacher--Smith, proof of 15.3.38, combined manuscript
(1 March 2004), printed p.1136.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.SylowNormalizer.NaturalConstruction

variable {G : Type*} [Group G] {M V : Subgroup G}

@[expose] def restrictedActor (a : NaturalOrthogonalAction M V) {U : Subgroup G}
    (hUM : U ≤ M) : U →* OrthogonalActor := a.actor.comp (inclusion hUM)

theorem restrictedActor_ker (a : NaturalOrthogonalAction M V) {U R : Subgroup G}
    (hUM : U ≤ M) (hker : U ⊓ centralizer (V : Set G) = R) :
    (restrictedActor a hUM).ker = R.subgroupOf U := by
  ext u
  change a.actor (inclusion hUM u) = 1 ↔ (u : G) ∈ R
  change inclusion hUM u ∈ a.actor.ker ↔ (u : G) ∈ R
  rw [a.ker_actor]
  constructor
  · intro h
    exact hker ▸ (show (u : G) ∈ U ⊓ centralizer (V : Set G) from ⟨u.property, h⟩)
  · intro h
    exact (show (u : G) ∈ U ⊓ centralizer (V : Set G) from hker.symm ▸ h).2

theorem restrictedActor_range (a : NaturalOrthogonalAction M V) {U : Subgroup G}
    (hUM : U ≤ M) :
    (restrictedActor a hUM).range = (U.subgroupOf M).map a.actor := by
  rw [restrictedActor, MonoidHom.range_comp, inclusion_range]

private theorem cube_eq_one (x : Multiplicative (Fin 2 → ZMod 3)) : x ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  change 3 • x.toAdd = 0
  funext i
  change 3 • x.toAdd i = 0
  exact (by decide : ∀ z : ZMod 3, 3 • z = 0) _

variable [Finite G]
omit [Finite G] in
theorem image_Y_eq_cubic (b : BaseModelFacts) (a : NaturalOrthogonalAction M V)
    {Y R : Subgroup G} (hYM : Y ≤ M)
    [(R.subgroupOf Y).Normal]
    (e : (Y ⧸ R.subgroupOf Y) ≃* Multiplicative (Fin 2 → ZMod 3))
    (hker : Y ⊓ centralizer (V : Set G) = R) :
    (restrictedActor a hYM).range = cubicBase := by
  let f := restrictedActor a hYM
  have hk : f.ker = R.subgroupOf Y := restrictedActor_ker a hYM hker
  let er : f.range ≃* Multiplicative (Fin 2 → ZMod 3) :=
    (QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans e)
  have hc : Nat.card f.range = 9 := by
    rw [Nat.card_congr er.toEquiv]
    norm_num [Nat.card_eq_fintype_card]
  apply eq_of_le_of_card_ge ?_ (by rw [b.card_cubic, hc])
  intro y hy
  apply Subgroup.subset_closure
  change y ^ 3 = 1
  have he : (⟨y, hy⟩ : f.range) ^ 3 = 1 := by
    apply er.injective
    rw [map_pow, map_one, cube_eq_one]
  exact congrArg f.range.subtype he

omit [Finite G] in
private theorem factor_through_embedding {H D : Type*} [Group H] [Group D]
    (f : H →* OrthogonalActor) (j : D →* OrthogonalActor)
    (hj : Function.Injective j) (hr : f.range = j.range) :
    ∃ p : H →* D, Function.Surjective p ∧ p.ker = f.ker ∧
      ∀ x, f x = j (p x) := by
  let e : D ≃* f.range := (MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hr.symm)
  let p : H →* D := e.symm.toMonoidHom.comp f.rangeRestrict
  have hc (x : H) : f x = j (p x) := by
    exact (congrArg f.range.subtype (e.apply_symm_apply (f.rangeRestrict x))).symm
  refine ⟨p, e.symm.surjective.comp f.rangeRestrict_surjective, ?_, hc⟩
  ext x
  change p x = 1 ↔ f x = 1
  rw [hc, ← j.map_one]
  exact ⟨congrArg j, fun h => hj h⟩

/-- The image of a Sylow subgroup under the given onto actor map. -/
@[expose] noncomputable def actorSylow (T : Sylow 2 G) (a : NaturalOrthogonalAction M V)
    (hTM : (T : Subgroup G) ≤ M) : Sylow 2 OrthogonalActor :=
  (T.subtype hTM).mapSurjective a.onto

theorem actorSylow_range (T : Sylow 2 G) (a : NaturalOrthogonalAction M V)
    (hTM : (T : Subgroup G) ≤ M) :
    (restrictedActor a hTM).range = (actorSylow T a hTM : Subgroup OrthogonalActor) := by
  rw [restrictedActor_range]
  rfl

theorem image_S_eq (T : Sylow 2 G) (a : NaturalOrthogonalAction M V)
    {S : Subgroup G} (hTM : (T : Subgroup G) ≤ M) (hST : S ≤ T)
    (hS : ∀ t : T, (t : G) ∈ S ↔ (a.actor (inclusion hTM t)).right = 1) :
    (restrictedActor a (hST.trans hTM)).range =
      (actorSylow T a hTM : Subgroup OrthogonalActor) ⊓ planeBase := by
  rw [← actorSylow_range]
  ext g
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨⟨⟨s, hST s.property⟩, rfl⟩, (hS ⟨s, hST s.property⟩).mp s.property⟩
  · rintro ⟨⟨t, rfl⟩, ht⟩
    exact ⟨⟨t, (hS t).mpr ht⟩, rfl⟩

theorem image_YS_eq (b : BaseModelFacts) (T : Sylow 2 G)
    (a : NaturalOrthogonalAction M V) {Y S : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hYSM : Y ⊔ S ≤ M) (hST : S ≤ T)
    (hY : (restrictedActor a (le_sup_left.trans hYSM : Y ≤ M)).range = cubicBase)
    (hS : ∀ t : T, (t : G) ∈ S ↔ (a.actor (inclusion hTM t)).right = 1) :
    (restrictedActor a hYSM).range = planeBase := by
  rw [restrictedActor_range, subgroupOf_sup (le_sup_left.trans hYSM)
    (le_sup_right.trans hYSM), Subgroup.map_sup,
    ← restrictedActor_range a (le_sup_left.trans hYSM),
    ← restrictedActor_range a (hST.trans hTM), hY, image_S_eq T a hTM hST hS]
  exact b.generate _

omit [Finite G] in
private theorem fixed_vectors_of_image (b : BaseModelFacts)
    (a : NaturalOrthogonalAction M V) {Y : Subgroup G} (hYM : Y ≤ M)
    (hY : (restrictedActor a hYM).range = cubicBase) :
    V ⊓ centralizer (Y : Set G) = ⊥ := by
  let _ := orthogonalAction
  apply le_antisymm _ bot_le
  intro v hv
  have he : a.coordinates ⟨v, hv.1⟩ = 1 := by
    apply b.fixed
    intro g hg
    obtain ⟨y, rfl⟩ := hY.ge hg
    rw [show restrictedActor a hYM y = a.actor (inclusion hYM y) from rfl,
      ← a.compatible]
    congr 1
    apply Subtype.ext
    change (y : G) * v * (y : G)⁻¹ = v
    exact mul_inv_eq_iff_eq_mul.mpr (hv.2 y y.property)
  have he' : (⟨v, hv.1⟩ : V) = 1 := a.coordinates.injective (he.trans a.coordinates.map_one.symm)
  exact congrArg V.subtype he'
omit [Finite G] in
private theorem centralizes_plane_of_actor (a : NaturalOrthogonalAction M V)
    (m : M) (i : OrthogonalPlaneIndex)
    (hfix : letI := orthogonalAction
      ∀ w ∈ orthogonalCoordinatePlane i, a.actor m • w = w) :
    (m : G) ∈ centralizer (a.plane i : Set G) := by
  let _ := orthogonalAction
  rintro v ⟨w, hw, rfl⟩
  have he := (a.compatible m w).trans (hfix _ hw)
  have hv := congrArg V.subtype (a.coordinates.injective he)
  change (m : G) * (w : G) * (m : G)⁻¹ = w at hv
  exact (mul_inv_eq_iff_eq_mul.mp hv).symm

/-- Transport of the two concrete model calculations. The model premises are
discharged in `exists_coordinates` below. The action, its relative kernels,
the cubic quotient, and the plane stabilizer are the only ambient-group inputs. -/
theorem exists_of_model_facts
    (b : BaseModelFacts)
    (models : ∀ P : Sylow 2 OrthogonalActor, Nonempty (SylowModelCoordinates P))
    (T : Sylow 2 G) (M Y S R V V₁ : Subgroup G)
    (a : NaturalOrthogonalAction M V) (hTM : (T : Subgroup G) ≤ M)
    (hYSM : Y ⊔ S ≤ M) (hST : S ≤ T) (hRY : R ≤ Y)
    [(R.subgroupOf Y).Normal]
    (e : (Y ⧸ R.subgroupOf Y) ≃* Multiplicative (Fin 2 → ZMod 3))
    (hTK : (T : Subgroup G) ⊓ centralizer (V : Set G) = R)
    (hYSK : (Y ⊔ S) ⊓ centralizer (V : Set G) = R)
    (hV₁ : V₁ = a.plane 1)
    (hS : ∀ t : T, (t : G) ∈ S ↔ (a.actor (inclusion hTM t)).right = 1) :
    Nonempty (NaturalCoordinates T M Y S R V V₁ a hTM hYSM) := by
  let hYM : Y ≤ M := le_sup_left.trans hYSM
  have hYK : Y ⊓ centralizer (V : Set G) = R := by
    apply le_antisymm
    · exact (inf_le_inf_right _ le_sup_left).trans hYSK.le
    · exact le_inf hRY (hYSK.ge.trans inf_le_right)
  have hY := image_Y_eq_cubic b a hYM e hYK
  let d : SylowModelCoordinates (actorSylow T a hTM) := Classical.choice (models _)
  obtain ⟨pt, hpt, hkpt, hcpt⟩ := factor_through_embedding
    (restrictedActor a hTM) d.embedding d.injective
    ((actorSylow_range T a hTM).trans d.range_eq.symm)
  let j : (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) →* OrthogonalActor :=
    planeBase.subtype.comp planeBaseEquiv.symm.toMonoidHom
  have hj : Function.Injective j := Subtype.val_injective.comp planeBaseEquiv.symm.injective
  have hrj : j.range = planeBase := by
    rw [MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr planeBaseEquiv.symm.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hYS := image_YS_eq b T a hTM hYSM hST hY hS
  obtain ⟨pys, hpys, hkpys, hcpys⟩ := factor_through_embedding
    (restrictedActor a hYSM) j hj (hYS.trans hrj.symm)
  have hs (t : T) : (t : G) ∈ S ↔ pt t ∈ baseFour := by
    rw [hS, ← d.base_preimage, ← hcpt]
    rfl
  refine ⟨{ tProjection := pt
            tOnto := hpt
            tKernel := hkpt.trans (restrictedActor_ker a hTM hTK)
            tEmbedding := d.embedding
            tInjective := d.injective
            tCompatible := hcpt
            ysProjection := pys
            ysOnto := hpys
            ysKernel := hkpys.trans (restrictedActor_ker a hYSM hYSK)
            ysEmbedding := j
            ysInjective := hj
            ysCompatible := hcpys
            s_preimage := hs
            inverts_modulo := ?_
            fixes_plane := ?_
            fixed_vectors := fixed_vectors_of_image b a hYM hY }⟩
  · intro t ht y hy
    have htS : (t : G) ∈ S := (hs t).mpr (ht ▸ Or.inr (Or.inr (Or.inl rfl)))
    have hm : (t : G) * y * (t : G)⁻¹ * y ∈ Y ⊔ S :=
      mul_mem (mul_mem (mul_mem (mem_sup_right htS) (mem_sup_left hy))
        (inv_mem (mem_sup_right htS))) (mem_sup_left hy)
    apply hYSK.le
    refine ⟨hm, ?_⟩
    let m : M := inclusion hTM t
    let n : M := inclusion hYM ⟨y, hy⟩
    have hyc : a.actor n ∈ cubicBase := hY.le ⟨⟨y, hy⟩, rfl⟩
    have hact : a.actor m = d.embedding (.r 2) := (hcpt t).trans (congrArg d.embedding ht)
    have hk : m * n * m⁻¹ * n ∈ a.actor.ker := by
      change a.actor (m * n * m⁻¹ * n) = 1
      rw [map_mul, map_mul, map_mul, map_inv, hact, d.inverts _ hyc, inv_mul_cancel]
    rw [a.ker_actor] at hk
    exact hk
  · intro t ht
    rw [hV₁]
    apply centralizes_plane_of_actor a (inclusion hTM t) 1
    intro w hw
    rw [show a.actor (inclusion hTM t) = d.embedding (.sr 2) from
      (hcpt t).trans (congrArg d.embedding ht)]
    exact d.fixes_first w hw

/-- Compatible dihedral and symmetric-square coordinates for the genuine natural
action, with both concrete model calculations discharged. The quotient and
kernel hypotheses use relative subgroups; `R ≤ T` already follows from `hTK`.
The marked dihedral model places the first reflection on the first plane,
the half-turn on both planes, and their product on the second plane. -/
theorem exists_coordinates
    (T : Sylow 2 G) (M Y S R V V₁ : Subgroup G)
    (a : NaturalOrthogonalAction M V) (hTM : (T : Subgroup G) ≤ M)
    (hYSM : Y ⊔ S ≤ M) (hST : S ≤ T) (hRY : R ≤ Y)
    [(R.subgroupOf Y).Normal]
    (e : (Y ⧸ R.subgroupOf Y) ≃* Multiplicative (Fin 2 → ZMod 3))
    (hTK : (T : Subgroup G) ⊓ centralizer (V : Set G) = R)
    (hYSK : (Y ⊔ S) ⊓ centralizer (V : Set G) = R)
    (hV₁ : V₁ = a.plane 1)
    (hS : ∀ t : T, (t : G) ∈ S ↔ (a.actor (inclusion hTM t)).right = 1) :
    Nonempty (NaturalCoordinates T M Y S R V V₁ a hTM hYSM) :=
  exists_of_model_facts baseModelFacts sylowModelCoordinates_nonempty
    T M Y S R V V₁ a hTM hYSM hST hRY e hTK hYSK hV₁ hS

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.SylowNormalizer.NaturalConstruction
