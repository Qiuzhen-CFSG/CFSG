module

public import GorensteinWalter.SL2UniversalCover
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.SpecificGroups.SL2.EvenSubgroup

/-!
# Recognition of perfect central double covers of A₅

The universal SL₂(5) projection, composed with the actual PSL₂(5) ≃ A₅
comparison, maps onto every perfect central double cover of A₅. Equal
kernel orders make that map an isomorphism, with its projection triangle
retained. An element with square one maps trivially to A₅, since a
square-one matrix in odd-characteristic SL₂ is scalar.

Source application: Aschbacher--Smith I.2.2(5), printed pp.411--412.
The universal-cover input is the prime-field theorem already established
in `SL2UniversalCover`; no new multiplier calculation is required.
-/

@[expose] public section
noncomputable section
open Theory.GroupTheory Subgroup
open scoped MatrixGroups
namespace GorensteinWalter.AlternatingFiveDoubleCover

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (3 < Nat.card (ZMod 5)) := ⟨by norm_num⟩

/-- The fixed, proved projective comparison used by the double cover. -/
def comparison : PSL(2, ZMod 5) ≃* alternatingGroup (Fin 5) :=
  Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some

local instance : IsQuasisimple (alternatingGroup (Fin 5)) :=
  IsQuasisimple.of_surjective comparison.toMonoidHom comparison.surjective

/-- The actual SL₂(5) projection to the five-letter alternating group. -/
def projection : SL(2, ZMod 5) →* alternatingGroup (Fin 5) :=
  comparison.toMonoidHom.comp (sl2ProjectiveProjection (ZMod 5))

def cover : Covering SL(2, ZMod 5) (alternatingGroup (Fin 5)) :=
  (Covering.ofMulEquiv comparison).comp (PSL2Cover.cover (ZMod 5))

theorem cover_isUniversal : Covering.IsUniversal cover :=
  (PSL2Cover.isUniversal_of_card_prime (ZMod 5) (by norm_num)).comp_ofMulEquiv comparison

theorem projection_kernel_card : Nat.card projection.ker = 2 := by
  rw [projection, MonoidHom.ker_comp_of_injective _ _ comparison.injective]
  exact sl2ProjectiveProjection_ker_card (ZMod 5) (by norm_num)

private theorem card_eq (E B : Type*) [Group E] [Group B] [Finite E] [Finite B]
    (f : E →* B) (hf : Function.Surjective f) :
    Nat.card E = Nat.card f.ker * Nat.card B := by
  have h := f.ker.card_mul_index
  rw [Subgroup.index_eq_card, Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at h
  exact h.symm

/-- Recognition preserves the actual projection to A₅. -/
theorem exists_equiv {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (alternatingGroup (Fin 5)))
    (hk : Nat.card f.toMonoidHom.ker = 2) :
    ∃ d : E ≃* SL(2, ZMod 5), projection.comp d.toMonoidHom = f.toMonoidHom := by
  let : IsQuasisimple E := f.isQuasisimple
  let g := cover_isUniversal.lift f.toCovering
  have hg := cover_isUniversal.lift_fac f.toCovering
  have hc : Nat.card SL(2, ZMod 5) = Nat.card E := by
    rw [card_eq _ _ projection cover.surjective, projection_kernel_card,
      card_eq _ _ f.toMonoidHom f.surjective, hk]
  let d := (MulEquiv.ofBijective g.toMonoidHom
    (g.surjective.bijective_of_nat_card_le hc.le)).symm
  refine ⟨d, ?_⟩
  apply MonoidHom.ext
  intro x
  have h := congrArg (fun k : Covering SL(2, ZMod 5) (alternatingGroup (Fin 5)) =>
    k (d x)) hg
  change f.toMonoidHom (d.symm (d x)) = projection (d x) at h
  change projection (d x) = f.toMonoidHom x
  simpa only [d.symm_apply_apply] using h.symm

/-- Every element of square one in a perfect double cover lies over the identity. -/
theorem map_eq_one_of_square_eq_one {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E (alternatingGroup (Fin 5)))
    (hk : Nat.card f.toMonoidHom.ker = 2) {x : E} (hx : x ^ 2 = 1) :
    f.toMonoidHom x = 1 := by
  obtain ⟨d, hd⟩ := exists_equiv f hk
  have hs : d x ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  have hdet : (Matrix.SpecialLinearGroup.toGL (d x)).det = 1 := by
    apply Units.ext
    exact (d x).property
  have hscalar := Matrix.GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one
    (by decide : (2 : ZMod 5) ≠ 0) (Matrix.SpecialLinearGroup.toGL (d x))
    (by rw [← map_pow, hs, map_one]) hdet
  have hcentral : d x ∈ center SL(2, ZMod 5) := by
    rcases hscalar with h | h
    · have he : d x = 1 := Matrix.SpecialLinearGroup.toGL_injective (by simpa using h)
      rw [he]
      exact one_mem _
    · have he : d x = -1 := Subtype.ext (congrArg Units.val h)
      rw [he]
      apply mem_center_iff.mpr
      intro y
      apply Subtype.ext
      change (y : Matrix (Fin 2) (Fin 2) (ZMod 5)) * (-1) =
        (-1) * (y : Matrix (Fin 2) (Fin 2) (ZMod 5))
      simp
  rw [← hd]
  change comparison (QuotientGroup.mk' (center SL(2, ZMod 5)) (d x)) = 1
  have hq : QuotientGroup.mk' (center SL(2, ZMod 5)) (d x) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hcentral
  rw [hq, map_one]

/-- A central order-two complement to the chosen denominator gives the
literal quotient its SL₂(5) recognition and excludes involutions outside
the kernel of the original A₅ map. -/
theorem quotient_of_central_supplement {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (a : E →* alternatingGroup (Fin 5))
    (ha : Function.Surjective a) (D Z : Subgroup E) [D.Normal]
    (hZ : Z ≤ center E) (hcard : Nat.card Z = 2)
    (hsup : a.ker = D ⊔ Z) (hdis : Disjoint D Z) :
    (∃ d : (E ⧸ D) ≃* SL(2, ZMod 5),
      (projection.comp d.toMonoidHom).comp (QuotientGroup.mk' D) = a) ∧
    (∀ x : E, x ^ 2 = 1 → a x = 1) := by
  let q := QuotientGroup.mk' D
  have hD : D ≤ a.ker := hsup ▸ le_sup_left
  let b := QuotientGroup.lift D a hD
  have hb : Function.Surjective b := QuotientGroup.lift_surjective_of_surjective D a ha hD
  have hk : b.ker = Z.map q := by
    rw [QuotientGroup.ker_lift, hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
  have hbc : b.ker ≤ center (E ⧸ D) := by
    rw [hk]
    rintro _ ⟨z, hz, rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective D y
    simpa only [map_mul] using congrArg q (mem_center_iff.mp (hZ hz) y)
  have hqi : Function.Injective (q.subgroupMap Z) := by
    apply (q.subgroupMap Z).ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hxD : x.val ∈ D := (QuotientGroup.eq_one_iff _).mp (Subtype.ext_iff.mp hx)
    have hxbot : x.val ∈ (⊥ : Subgroup E) := by
      rw [← disjoint_iff.mp hdis]
      exact ⟨hxD, x.property⟩
    exact Subgroup.mem_bot.mp hxbot
  have hkcard : Nat.card b.ker = 2 := by
    rw [hk, ← Nat.card_congr
      (MulEquiv.ofBijective (q.subgroupMap Z) ⟨hqi, q.subgroupMap_surjective Z⟩).toEquiv]
    exact hcard
  let f : PerfectCentralCovering.Cover (E ⧸ D) (alternatingGroup (Fin 5)) := {
    toMonoidHom := b
    surjective := hb
    isPerfect := inferInstance
    ker_le_center := hbc }
  constructor
  · obtain ⟨d, hd⟩ := exists_equiv f hkcard
    refine ⟨d, ?_⟩
    rw [hd]
    exact QuotientGroup.lift_comp_mk' D a hD
  · intro x hx
    exact map_eq_one_of_square_eq_one f hkcard (by rw [← map_pow q, hx, map_one])

end GorensteinWalter.AlternatingFiveDoubleCover
