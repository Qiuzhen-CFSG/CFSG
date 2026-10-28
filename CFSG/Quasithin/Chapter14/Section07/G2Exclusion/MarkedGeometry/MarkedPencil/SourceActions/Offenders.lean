module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.Stability
public import Theory.Representation.BinaryOffender.SubspaceAction

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup

/-!
# Best offenders and the full binary G₂ actor

The binary rank and fixed-space bounds exclude an offender in the derived
subgroup. Its index two then forces an actor containing that subgroup to be
all of G₂(2). Equivariant linear coordinates preserve fixed-space dimensions
and every subgroup weight comparison, hence best offenders. Transporting the
marked elementary-eight conjugacy class identifies the source H-conjugates
of its actual pencil-span centralizer.

The numerical model bounds and the classification at the concrete root
subgroup BinaryCore.elementary are precise earlier-model inputs retained for
qt-b-04-g2 (B.4.6). The pencil centralizer identification is supplied by the
sibling clause-(4) calculation. This is a conditional source deduction, not
a proof of those earlier model inputs. IsBestOffender is the FF-star notion
in the source; no minimality restriction is added.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 14.7.55(5),
printed p.1066, and B.4.6, printed pp.88–90. Existing root coordinates are
from the attributed ATLAS port (LICENSES/ATLAS.txt).
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions
open Representation Representation.BinaryOffender Subgroup
open Atlas.G2
variable {D V W : Type*} [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- The rank-one and rank-two fixed-space estimates exclude offenders contained
in the actual derived G₂(2). These numerical local inputs are the binary
specializations of the involution and root-group calculations in B.4.6. -/
theorem model_offender_not_le_derived
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (hRank : ∀ A : Subgroup (Model (ZMod 2)), A ≤ commutator (Model (ZMod 2)) →
      IsElementaryTwo A → rank A ≤ 2)
    (hOne : ∀ A : Subgroup (Model (ZMod 2)), IsElementaryTwo A →
      rank A = 1 → 2 ≤ fixedCodim σ A)
    (hTwo : ∀ A : Subgroup (Model (ZMod 2)), A ≤ commutator (Model (ZMod 2)) →
      IsElementaryTwo A → rank A = 2 → 3 ≤ fixedCodim σ A)
    {A : Subgroup (Model (ZMod 2))} (hA : IsOffender σ A) :
    ¬ A ≤ commutator (Model (ZMod 2)) := by
  intro hAD
  have hr := hRank A hAD hA.1
  have hp := hA.1.rank_pos
  have hc := hA.2
  have hcases : rank A = 1 ∨ rank A = 2 := by omega
  rcases hcases with h | h
  · have hbound := hOne A hA.1 h
    omega
  · have hbound := hTwo A hAD hA.1 h
    omega

/-- In the actual G₂ model, a subgroup containing the derived group and any
FF-offender is the whole group. The index-two argument proves surjectivity;
no full-group recognition is assumed. -/
theorem source_full_actor_of_ff
    (ρ : Representation (ZMod 2) D V)
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (i : D →* Model (ZMod 2)) (hi : Function.Injective i)
    (e : V ≃ₗ[ZMod 2] W) (he : ∀ g v, e (ρ g v) = σ (i g) (e v))
    (hderived : commutator (Model (ZMod 2)) ≤ i.range)
    (hRank : ∀ A : Subgroup (Model (ZMod 2)), A ≤ commutator (Model (ZMod 2)) →
      IsElementaryTwo A → rank A ≤ 2)
    (hOne : ∀ A : Subgroup (Model (ZMod 2)), IsElementaryTwo A →
      rank A = 1 → 2 ≤ fixedCodim σ A)
    (hTwo : ∀ A : Subgroup (Model (ZMod 2)), A ≤ commutator (Model (ZMod 2)) →
      IsElementaryTwo A → rank A = 2 → 3 ≤ fixedCodim σ A)
    (hff : IsFFModule ρ) : Function.Surjective i ∧ Nonempty (D ≃* Model (ZMod 2)) := by
  obtain ⟨A,hA⟩ := hff
  have hm := hA.map_equivariant ρ σ i hi e he
  have hnot := model_offender_not_le_derived σ hRank hOne hTwo hm
  have hlt : commutator (Model (ZMod 2)) < i.range := by
    refine lt_of_le_of_ne hderived ?_
    intro heq
    exact hnot (heq ▸ Subgroup.map_le_range i A)
  have hindex : (commutator (Model (ZMod 2))).index = 2 := by
    rw [BinaryParabolicPair.commutator_eq_longRootClosure, BinaryException.index_H]
  have hm := Subgroup.relIndex_mul_index hderived
  rw [hindex] at hm
  have hp : ((commutator (Model (ZMod 2))).relIndex i.range * i.range.index).Prime :=
    by rw [hm]; exact Nat.prime_two
  have hr : i.range = ⊤ := by
    rcases Nat.prime_mul_iff.mp hp with ⟨_,hr⟩ | ⟨_,hr⟩
    · exact Subgroup.index_eq_one.mp hr
    · exact (hlt.not_ge (Subgroup.relIndex_eq_one.mp hr)).elim
  have hs := MonoidHom.range_eq_top.mp hr
  exact ⟨hs, ⟨MulEquiv.ofBijective i ⟨hi,hs⟩⟩⟩
end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions


namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions
open Representation Representation.BinaryOffender Subgroup
variable {D K V W : Type*} [Group D] [Group K]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

private theorem weight_equivariant
    (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) K W)
    (i : D ≃* K) (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (ρ g v) = σ (i g) (e v)) (A : Subgroup D) :
    weight ρ A = weight σ (A.map i.toMonoidHom) := by
  unfold weight
  rw [rank_map_injective i.toMonoidHom i.injective]
  congr 1
  rw [← fixedSpace_map_equivariant ρ σ i.toMonoidHom e he A,
    e.finrank_map_eq]

private theorem best_map
    (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) K W)
    (i : D ≃* K) (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (ρ g v) = σ (i g) (e v)) (A : Subgroup D)
    (hA : IsBestOffender ρ A) : IsBestOffender σ (A.map i.toMonoidHom) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.1.2
  refine ⟨⟨?_, IsElementaryAbelian.map i.toMonoidHom⟩, ?_⟩
  · intro hb
    apply hA.1.1
    apply Subgroup.map_injective (f := i.toMonoidHom) i.injective
    simpa only [Subgroup.map_bot] using hb
  · intro B hB
    have hmap : (B.comap i.toMonoidHom).map i.toMonoidHom = B := by
      rw [Subgroup.map_comap_eq, (MonoidHom.range_eq_top.mpr i.surjective : i.toMonoidHom.range = ⊤), top_inf_eq]
    have hBA : B.comap i.toMonoidHom ≤ A := by
      intro a ha
      obtain ⟨b,hb,heq⟩ := hB ha
      exact i.injective heq ▸ hb
    have hw := hA.2 _ hBA
    rw [weight_equivariant ρ σ i e he, weight_equivariant ρ σ i e he, hmap] at hw
    exact hw

/-- Best offenders transport under the actual equivariant identification,
including every subgroup weight comparison in `P(G,V)`. -/
theorem bestOffender_equivariant_iff
    (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) K W)
    (i : D ≃* K) (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (ρ g v) = σ (i g) (e v)) (A : Subgroup D) :
    IsBestOffender ρ A ↔ IsBestOffender σ (A.map i.toMonoidHom) := by
  constructor
  · exact best_map ρ σ i e he A
  · intro h
    have he' : ∀ g w, e.symm (σ g w) = ρ (i.symm g) (e.symm w) := by
      intro g w
      apply e.injective
      simpa only [e.apply_symm_apply, i.apply_symm_apply] using
        (he (i.symm g) (e.symm w)).symm
    have hh := best_map σ ρ i.symm e.symm he' _ h
    have hi : i.symm.toMonoidHom.comp i.toMonoidHom = MonoidHom.id D := by
      ext d
      exact i.symm_apply_apply d
    simpa only [Subgroup.map_map, hi, Subgroup.map_id] using hh

private theorem map_conjugate (i : D →* K) (A : Subgroup D) (g : D) :
    (A.map (MulAut.conj g).toMonoidHom).map i =
      (A.map i).map (MulAut.conj (i g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply]

/-- A source actor cover gives precisely the conjugates in the faithful actor,
not subgroups containing its kernel. This is the orbit convention in (5). -/
theorem source_bestOffender_family
    {H : Type*} [Group H] (π : H →* D) (hπ : Function.Surjective π)
    (ρ : Representation (ZMod 2) D V) (σ : Representation (ZMod 2) K W)
    (i : D ≃* K) (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (ρ g v) = σ (i g) (e v))
    (A : Subgroup D) (A₀ : Subgroup K)
    (hA : A.map i.toMonoidHom = A₀)
    (hmodel : ∀ B : Subgroup K, IsBestOffender σ B ↔
      ∃ g : K, A₀.map (MulAut.conj g).toMonoidHom = B) :
    {B : Subgroup D | IsBestOffender ρ B} =
      Set.range (fun h : H => A.map (MulAut.conj (π h)).toMonoidHom) := by
  ext B
  change IsBestOffender ρ B ↔ ∃ h : H, A.map (MulAut.conj (π h)).toMonoidHom = B
  rw [bestOffender_equivariant_iff ρ σ i e he B, hmodel]
  constructor
  · rintro ⟨g,hg⟩
    obtain ⟨h,hh⟩ := hπ (i.symm g)
    refine ⟨h, Subgroup.map_injective (f := i.toMonoidHom) i.injective ?_⟩
    rw [map_conjugate, hA, hh]
    change A₀.map (MulAut.conj (i (i.symm g))).toMonoidHom = _
    rw [i.apply_symm_apply]
    exact hg
  · rintro ⟨h,rfl⟩
    exact ⟨i (π h), by rw [map_conjugate, hA]; rfl⟩

private theorem conjugate_twice (A : Subgroup K) (a b : K) :
    (A.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      A.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
    MulAut.conj_apply]
  group

private theorem model_family_at_conjugate
    (σ : Representation (ZMod 2) K W) (A₀ : Subgroup K) (a : K)
    (hmodel : ∀ B : Subgroup K, IsBestOffender σ B ↔
      ∃ g : K, A₀.map (MulAut.conj g).toMonoidHom = B) :
    ∀ B : Subgroup K, IsBestOffender σ B ↔
      ∃ g : K, (A₀.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj g).toMonoidHom = B := by
  intro B
  rw [hmodel]
  constructor
  · rintro ⟨g,hg⟩
    exact ⟨g * a⁻¹, by rw [conjugate_twice, inv_mul_cancel_right]; exact hg⟩
  · rintro ⟨g,hg⟩
    exact ⟨g * a, by rwa [conjugate_twice] at hg⟩

/-- The full-actor pencil centralizer is the actual kernel on its span. The
centralizer identification is supplied by clause (4); the model premise is
B.4.6(13) at its marked root subgroup, supplied by `qt-b-04-g2`. -/
theorem source_pencil_bestOffenders
    {H : Type*} [Group H] (π : H →* D) (hπ : Function.Surjective π)
    (ρ : Representation (ZMod 2) D V)
    (σ : Representation (ZMod 2) (Atlas.G2.Model (ZMod 2)) W)
    (i : D ≃* Atlas.G2.Model (ZMod 2)) (e : V ≃ₗ[ZMod 2] W)
    (he : ∀ g v, e (ρ g v) = σ (i g) (e v))
    (f : SingularMap W) (p : Atlas.G2.SingularPoints (ZMod 2))
    (S : Submodule (ZMod 2) V) (hS : S.map e.toLinearMap = pencilSpan f p)
    (a : Atlas.G2.Model (ZMod 2))
    (hcentralizer : (subspaceKernel σ (pencilSpan f p) ⊤) =
      Atlas.G2.BinaryCore.elementary.map (MulAut.conj a).toMonoidHom)
    (hB46 : ∀ B : Subgroup (Atlas.G2.Model (ZMod 2)), IsBestOffender σ B ↔
      ∃ g : Atlas.G2.Model (ZMod 2), Atlas.G2.BinaryCore.elementary.map (MulAut.conj g).toMonoidHom = B) :
    {B : Subgroup D | IsBestOffender ρ B} =
      Set.range (fun h : H =>
        (subspaceKernel ρ S ⊤).map (MulAut.conj (π h)).toMonoidHom) := by
  apply source_bestOffender_family π hπ ρ σ i e he _
    (Atlas.G2.BinaryCore.elementary.map (MulAut.conj a).toMonoidHom) _
    (model_family_at_conjugate σ Atlas.G2.BinaryCore.elementary a hB46)
  rw [← hcentralizer, ← hS]
  ext g
  constructor
  · rintro ⟨d,hd,rfl⟩
    refine ⟨Subgroup.mem_top _, ?_⟩
    rintro w ⟨v,hv,rfl⟩
    change σ (i d) (e v) = e v
    rw [← he, hd.2 v hv]
  · intro hg
    refine ⟨i.symm g, ⟨Subgroup.mem_top _, ?_⟩, i.apply_symm_apply g⟩
    intro v hv
    apply e.injective
    rw [he, i.apply_symm_apply]
    exact hg.2 (e v) (Submodule.mem_map_of_mem hv)
/-- Combined clause-(5) deduction: the FF hypothesis forces the full actor,
then B.4.6(13) and the computed centralizer identify the H-conjugate family.
The representation and marked pencil coordinates are the same throughout. -/
theorem source_ff_pencil_bestOffenders
    {H : Type*} [Group H] (π : H →* D) (hπ : Function.Surjective π)
    (ρ : Representation (ZMod 2) D V)
    (σ : Representation (ZMod 2) (Atlas.G2.Model (ZMod 2)) W)
    (i : D →* Atlas.G2.Model (ZMod 2)) (hi : Function.Injective i)
    (e : V ≃ₗ[ZMod 2] W) (he : ∀ g v, e (ρ g v) = σ (i g) (e v))
    (hderived : commutator (Atlas.G2.Model (ZMod 2)) ≤ i.range)
    (hRank : ∀ A : Subgroup (Atlas.G2.Model (ZMod 2)),
      A ≤ commutator (Atlas.G2.Model (ZMod 2)) → IsElementaryTwo A → rank A ≤ 2)
    (hOne : ∀ A : Subgroup (Atlas.G2.Model (ZMod 2)), IsElementaryTwo A →
      rank A = 1 → 2 ≤ fixedCodim σ A)
    (hTwo : ∀ A : Subgroup (Atlas.G2.Model (ZMod 2)),
      A ≤ commutator (Atlas.G2.Model (ZMod 2)) → IsElementaryTwo A →
      rank A = 2 → 3 ≤ fixedCodim σ A)
    (f : SingularMap W) (p : Atlas.G2.SingularPoints (ZMod 2))
    (S : Submodule (ZMod 2) V) (hS : S.map e.toLinearMap = pencilSpan f p)
    (a : Atlas.G2.Model (ZMod 2))
    (hcentralizer : subspaceKernel σ (pencilSpan f p) ⊤ =
      Atlas.G2.BinaryCore.elementary.map (MulAut.conj a).toMonoidHom)
    (hB46 : ∀ B : Subgroup (Atlas.G2.Model (ZMod 2)), IsBestOffender σ B ↔
      ∃ g : Atlas.G2.Model (ZMod 2),
        Atlas.G2.BinaryCore.elementary.map (MulAut.conj g).toMonoidHom = B)
    (hff : IsFFModule ρ) :
    (∃ j : D ≃* Atlas.G2.Model (ZMod 2), ∀ d, j d = i d) ∧
      {B : Subgroup D | IsBestOffender ρ B} =
        Set.range (fun h : H =>
          (subspaceKernel ρ S ⊤).map (MulAut.conj (π h)).toMonoidHom) := by
  obtain ⟨hs,_⟩ := source_full_actor_of_ff ρ σ i hi e he hderived hRank hOne hTwo hff
  let j : D ≃* Atlas.G2.Model (ZMod 2) := MulEquiv.ofBijective i ⟨hi,hs⟩
  exact ⟨⟨j,fun _ => rfl⟩,
    source_pencil_bestOffenders π hπ ρ σ j e he f p S hS a hcentralizer hB46⟩

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions
